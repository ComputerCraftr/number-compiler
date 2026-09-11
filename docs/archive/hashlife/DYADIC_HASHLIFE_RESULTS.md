# v0.59.9 dyadic HashLife results

Spatial identity is `DyadicTile(level,left,right)` independent of absolute origin and logical field length. The raw `SpacetimeBoundary` temporal carrier has been deleted.

Production now uses the dyadic tree for **spatial payload**, while temporal application state is family-specific and bounded:

- reverse/add: fixed H=20 carry-cut state;
- Collatz: bounded residue/local phase plus symbolic affine/event transport.

Construction-order `node_id` is diagnostic only. Parent interning, directed action traversal, mirror/uniform analysis, and finite-action traversal use canonical tile objects or semantic action keys. An adversarial test gives two different sibling tiles the same diagnostic ID and verifies that their actions remain distinct.

Exact output width may grow without becoming temporal identity. For N=256 the production application reaches 9,626 reverse/add spatial tile nodes and 40 Collatz spatial tile nodes, while generic recursive temporal application nodes remain zero.

The open reverse/add issue is not tree depth or noncanonical IDs: it is composing the exact spatial forcing action so cold forcing evaluations grow sublinearly instead of approximately one per generation.
