package org.terraform.tree;

import org.jetbrains.annotations.NotNull;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Works out which leaves lose their support when a log is broken.
 * <p>
 * TerraformGenerator trees are much bigger than vanilla trees. Their branches are thick,
 * so when somebody cuts the trunk, a lot of branch logs are left hanging in the air.
 * Vanilla leaf decay only asks "is there a log within 6 blocks?", so those floating logs
 * keep the whole canopy alive, and the tree never visibly goes away.
 * <p>
 * This solver uses a stricter rule: a leaf is supported if a log within 6 leaf-steps is still
 * connected to the ground. Logs that were cut away from the ground by the break don't count.
 * <p>
 * This class has no Bukkit dependencies on purpose, so that it can be tested on its own.
 * {@link LeafDecayListener} adapts a real world to {@link WorldView}.
 */
public final class LeafDecaySolver {

    /**
     * The only things the solver needs to know about a block.
     */
    public enum Cell {
        /**
         * Air, water, plants. Anything that is not solid.
         */
        EMPTY,
        LOG,
        /**
         * A leaf that can decay. Leaves that must never decay (e.g. placed by a player)
         * should be reported as SOLID.
         */
        LEAF,
        /**
         * Any other solid block. A log standing on one of these is considered to be on the ground.
         */
        SOLID
    }

    @FunctionalInterface
    public interface WorldView {
        @NotNull Cell at(int x, int y, int z);
    }

    public record Pos(int x, int y, int z) {
        @NotNull Pos offset(int dx, int dy, int dz) {
            return new Pos(x + dx, y + dy, z + dz);
        }
    }

    /**
     * The same limit as vanilla. A leaf this many steps from a log is fine, one more step and it decays.
     */
    public static final int MAX_LEAF_DISTANCE = 6;
    /**
     * If a connected group of logs is bigger than this, assume that it is attached to the ground.
     * This keeps huge player builds from being scanned on every break.
     */
    static final int MAX_LOGS = 4000;
    /**
     * Safety limit for the leaf search. If it is hit, nothing is decayed and vanilla is left to deal with it.
     */
    static final int MAX_LEAVES = 20000;

    private static final int[][] FACES = {{0, -1, 0}, {0, 1, 0}, {1, 0, 0}, {-1, 0, 0}, {0, 0, 1}, {0, 0, -1}};

    private LeafDecaySolver() {
    }

    /**
     * Call this when a log is about to be removed (or has just been removed).
     *
     * @param world  the world, as it is at the moment of the break
     * @param broken the position of the log that was broken. It is treated as empty.
     * @return every leaf that was held up by the broken log, or by the logs that were cut off from the ground
     * by it, and that has no other support left. These should decay.
     */
    public static @NotNull Set<Pos> findOrphanedLeaves(@NotNull WorldView world, @NotNull Pos broken) {
        // The same block is looked at many times, and looking at a real world is not free.
        Map<Pos, Cell> cache = new HashMap<>();
        WorldView view = (x, y, z) -> {
            if (x == broken.x() && y == broken.y() && z == broken.z()) {
                return Cell.EMPTY;
            }
            Pos pos = new Pos(x, y, z);
            Cell cell = cache.get(pos);
            if (cell == null) {
                cell = world.at(x, y, z);
                cache.put(pos, cell);
            }
            return cell;
        };

        // 1. Which of the logs next to the break are no longer connected to the ground?
        Set<Pos> severed = new HashSet<>();
        Set<Pos> classified = new HashSet<>();
        for (int dx = -1; dx <= 1; dx++) {
            for (int dy = -1; dy <= 1; dy++) {
                for (int dz = -1; dz <= 1; dz++) {
                    if (dx == 0 && dy == 0 && dz == 0) {
                        continue;
                    }
                    Pos next = broken.offset(dx, dy, dz);
                    if (classified.contains(next) || view.at(next.x(), next.y(), next.z()) != Cell.LOG) {
                        continue;
                    }
                    LogGroup group = exploreLogs(view, next);
                    classified.addAll(group.logs());
                    if (group.severed()) {
                        severed.addAll(group.logs());
                    }
                }
            }
        }

        // 2. Find the leaves around the break and the severed logs.
        // Anything that could have lost its support is within MAX_LEAF_DISTANCE steps of them.
        // We look twice as far, as those leaves may be supported by a log that is as far again.
        Map<Pos, Integer> reach = new HashMap<>();
        ArrayDeque<Pos> queue = new ArrayDeque<>();
        seedLeaves(view, broken, reach, queue);
        for (Pos log : severed) {
            seedLeaves(view, log, reach, queue);
        }
        if (reach.size() > MAX_LEAVES) {
            return new HashSet<>();
        }
        while (!queue.isEmpty()) {
            Pos leaf = queue.poll();
            int steps = reach.get(leaf);
            if (steps >= 2 * MAX_LEAF_DISTANCE) {
                continue;
            }
            for (int[] face : FACES) {
                Pos next = leaf.offset(face[0], face[1], face[2]);
                if (!reach.containsKey(next) && view.at(next.x(), next.y(), next.z()) == Cell.LEAF) {
                    reach.put(next, steps + 1);
                    queue.add(next);
                    if (reach.size() > MAX_LEAVES) {
                        return new HashSet<>();
                    }
                }
            }
        }

        // 3. Which of them can still reach a log that is still standing?
        Map<Pos, Integer> support = new HashMap<>();
        for (Pos leaf : reach.keySet()) {
            for (int[] face : FACES) {
                Pos next = leaf.offset(face[0], face[1], face[2]);
                if (view.at(next.x(), next.y(), next.z()) == Cell.LOG && !severed.contains(next)) {
                    support.put(leaf, 1);
                    queue.add(leaf);
                    break;
                }
            }
        }
        while (!queue.isEmpty()) {
            Pos leaf = queue.poll();
            int steps = support.get(leaf);
            if (steps >= MAX_LEAF_DISTANCE) {
                continue;
            }
            for (int[] face : FACES) {
                Pos next = leaf.offset(face[0], face[1], face[2]);
                if (reach.containsKey(next) && !support.containsKey(next)) {
                    support.put(next, steps + 1);
                    queue.add(next);
                }
            }
        }

        // 4. Leaves close enough to the break to have been affected, with no support left.
        Set<Pos> orphans = new HashSet<>();
        for (Map.Entry<Pos, Integer> entry : reach.entrySet()) {
            if (entry.getValue() <= MAX_LEAF_DISTANCE && !support.containsKey(entry.getKey())) {
                orphans.add(entry.getKey());
            }
        }
        return orphans;
    }

    private static void seedLeaves(@NotNull WorldView view,
                                   @NotNull Pos source,
                                   @NotNull Map<Pos, Integer> reach,
                                   @NotNull ArrayDeque<Pos> queue)
    {
        for (int[] face : FACES) {
            Pos next = source.offset(face[0], face[1], face[2]);
            if (!reach.containsKey(next) && view.at(next.x(), next.y(), next.z()) == Cell.LEAF) {
                reach.put(next, 1);
                queue.add(next);
            }
        }
    }

    private record LogGroup(@NotNull Set<Pos> logs, boolean severed) {
    }

    /**
     * Flood fills the logs connected to start (diagonals count, as the thin branches of
     * TerraformGenerator trees are not always face to face).
     * Stops early as soon as it finds a log standing on the ground. Goes downwards first,
     * as that is where the ground usually is.
     */
    private static @NotNull LogGroup exploreLogs(@NotNull WorldView view, @NotNull Pos start) {
        Set<Pos> seen = new HashSet<>();
        ArrayDeque<Pos> stack = new ArrayDeque<>();
        seen.add(start);
        stack.push(start);
        while (!stack.isEmpty()) {
            Pos log = stack.pop();
            if (view.at(log.x(), log.y() - 1, log.z()) == Cell.SOLID) {
                return new LogGroup(seen, false); // Standing on the ground.
            }
            for (int dy = 1; dy >= -1; dy--) {
                for (int dx = -1; dx <= 1; dx++) {
                    for (int dz = -1; dz <= 1; dz++) {
                        Pos next = log.offset(dx, dy, dz);
                        if (view.at(next.x(), next.y(), next.z()) == Cell.LOG && seen.add(next)) {
                            if (seen.size() > MAX_LOGS) {
                                return new LogGroup(seen, false); // Too big. Assume it is fine.
                            }
                            stack.push(next);
                        }
                    }
                }
            }
        }
        return new LogGroup(seen, true);
    }
}
