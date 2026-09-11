# v0.54.0 spatial prefix monoid — concise results

- **196 slab removed:** the fixed-height carry-slab modules, slab-only tests/probe, and their legacy Formula IR nodes are deleted.
- **Canonical 196 state:** each pair coefficient keeps `delta=S-(b-1)` in the exact finite alphabet `[-(b-1), b-1]`; its sign is the LT/EQ/GT carry domain. Decimal therefore has 19 exact domain symbols independent of digit width.
- **Carry action:** LT/EQ/GT map to the three-element carry-function monoid `CONST0 / ID / CONST1`. A Hillis-Steele formula prefix doubles covered distance each stage. Width `D` therefore uses `ceil(log2 D)` prefix stages.
- **Random access:** `ReverseAddSpatialIndex` projects one carry boundary, next pair coefficient or next digit without constructing a carry vector. The 196 controls at source widths 3, 5, 8 and 10 use 2, 3, 3 and 4 stages respectively and agree exactly with the scalar orbit.
- **Public digit path:** `NumberCompiler.project_digit("196",5,4)` returns the high digit of 52514 while the complete final digit formula is patched to fail in the regression test.
- **Collatz digit formulas:** generic digit transducers now use the same `prefix_monoid.py` owner; there is no second private prefix implementation.
- **Collatz explicit parity:** a 4096-symbol parity word is pre-summarized into 64 blocks. Physical-time queries use 12 summary/leaf binary-search probes and inspect at most one 64-bit leaf; the old repeated scan of successively larger integer prefixes is gone.
- **Compressed Collatz events:** `CollatzValuationSchedule` remains the preferred representation when the parity coordinate is already run-compressed; a valuation of one million still stays one event rather than one million parity symbols.
- **Validation boundary:** this release fixes **spatial** prefix work. It does not claim logarithmic temporal nth-generation evolution for 196 or Collatz; genuinely new future defect/event states remain the temporal research frontiers.

- **v0.54.0 Collatz endpoint:** Boolean sentinel equality now uses the shared prefix monoid plus logarithmic first-failure select; the power-of-four formula endpoint no longer scans the sentinel run.
