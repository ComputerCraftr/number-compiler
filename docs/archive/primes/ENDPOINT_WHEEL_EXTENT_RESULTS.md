# v0.54.0 endpoint / recursive-wheel / symbolic-extent results

- **Collatz endpoint:** for power-of-four radix, the sentinel predicate is compiled once into the same associative prefix engine used by 196. First failure is monotone, so endpoint selection takes `O(log D)` prefix probes rather than `q` digit probes for a sentinel run of length `q`. The regression uses a 256-digit sentinel run and permits only constant post-select digit reads.
- **Prime one-extension index:** old length `N`, new prime `q`; retained deletion metadata contains exactly `N` positions grouped over `q` copies. The historical `q*N` Boolean bitmap is gone. Full `N*(q-1)` gaps are produced only if the caller explicitly requests materialization.
- **Prime recursive index:** a wheel is represented by `(p_1,...,p_k)`. Exact prefix count uses `C_a(x)=C_(a-1)(x)-C_(a-1)(floor(x/p_a))`; binary rank descent selects residues without constructing any ancestor residue/gap carrier. Nested extension through `(2,3,5,7,11,13)` is covered by exact tests.
- **Fermat extent:** `F_n` semantic width is `DyadicExtent(n,+1)` and cyclotomic order is `DyadicExtent(n+1,0)`. Comparisons use bit-length/power-of-two logic; lowering to a Python integer is explicit. A regression compiles `F_1,000,000` while forbidding large `DyadicExtent.materialize()` calls.
- **Boundary:** these changes close the spatial/source-carrier blockers named above. They do not manufacture a temporal Collatz/196 closure, a polylog wheel-depth theorem for nth-prime, or a theorem-free Fermat primality classifier.

Machine-readable smoke metrics are in `results/endpoint_wheel_extent_metrics.json`.
