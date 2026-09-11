# Radix/wreath dependency-cascade powering probe

This probe keeps composed bimachine context sets as hash-consed hierarchical dependency functions instead of flat Cartesian tuples.

## Exact T2

- one step: **86 left / 12 right** states
- two steps: **1156 left / 1138 right** states
- T2 left determinized subsets: 11,551 flat triples -> 4,273 cascade edges + 1,546 shared dependency nodes
- T2 right determinized subsets: 95,509 flat triples -> 95,601 cascade edges + 1,230 shared dependency nodes

Every cascade relation was decoded and the underlying deterministic automata are the same exact T2 construction used by the previous randomized power checks.

## Capped T4 local context universe

- left: 100,000 discovered triples after 6,752 processed; represented by 80,932 dependency edges / 712 nodes; capped=True
- right: 100,000 discovered triples after 6,429 processed; represented by 29,599 dependency edges / 2,567 nodes; capped=True

The cascade representation removes substantial flat-product duplication, but this probe does **not** yet establish a polylogarithmic full-J operator: the number of distinct top-level dependency states may still grow. The next composition must operate directly on dependency functions instead of enumerating their member triples.
