# Shadow recovery component audit

Release remains BLOCKED. These are component checks during active, separately
owned work; they are not a frozen-source full-release certificate.

- Admission and production regression selection: 71 passed (2.31s pytest,
  2.84s process guard).
- Candidate recovery through API and CLI: 8 failed (0.55s pytest, 1.08s guard).
  Both routes remain unresolved on F4, F5, M11, M13.
- Isabelle Etale_Primary_Carry: passed, including the exact M11 normalized zero
  key `(False,-1,(14,5))` and compositeness, with theorem oracle checks enabled;
  19.93s guard, 3.51GB sampled peak under the 4GiB cap.

The Isabelle result refutes only zero-root/key-implies-primality without
candidate binding. It does not refute or construct a terminal shadow publisher.
The corresponding Python numeric regression matches the actual ArithmeticTile
key. That regression is not Isabelle extraction or an executor refinement proof.

The 196/Collatz construction and performance gates remain open. Named owners
and required evidence are in docs/cylinder-p0-release-gates-2026-09-12.md.

## Conditional terminal defect bridge

`Special_Frobenius_Defect_Bridge.thy` also passes in Etale_Primary_Carry, with
oracle checks enabled. Its local support invariant implies the exact
prime/divisibility/gcd equivalences and conditional proper-factor output.
It assumes that invariant for the constructed E; it does not construct E or
prove the powered implementation satisfies the invariant.

This later build used the same 35-second/4GiB guard and the supported Java entry
point with `-Xms128m -Xmx768m -Xss16m`, avoiding the launcher's default 4GiB JVM
maximum competing with Poly/ML. No persistent Isabelle settings changed.
Outcome: passed in 18.72s, sampled peak 1.03GB. Earlier timeout/memory-limit
attempts remain in `/tmp/special-defect-bridge-isabelle-0912-v{1,2}.*` and are
not evidence of a passing run.

## Latest transverse and bounded-support checkpoint

- Transverse_Frobenius_Holonomy now passes Etale_Primary_Carry with all theorem
  oracle checks: exact binomial neighbor/modular transport, finite holonomy
  unit criterion under explicit family progression completeness, and proper
  factor/cofactor from any nonunit admitted slot. Guard 16.22s, sampled peak
  1.012GB. This does not prove the compact constructor or discharge the family
  order/congruence premise.
- Expanded integration selection: 219 tests passed. This is a component
  selection, not a full-release run. A competing subagent validation process
  was terminated during this phase; timing is not used to clear a performance
  gate. Source logic was frozen for the run.
- Strict mypy on authored src/tests/devtools: 1,263 files pass. An earlier
  `mypy .` invocation instead encountered duplicate generated validation_driver
  module names under results; those generated evidence scripts are outside the
  canonical authored-source selection.
- The unchanged Collatz N256/N64 release tests still fail: temporal leaves are
  used and the actual radix4 source morphism remains disconnected. Both failures
  were captured under the 35s/1GiB guard (32.41s pytest, 33.03s guard).

The transverse oracle control report separately records F4/F5/M11/M13 and M29,
including the exact M11 coefficient 89 and FULL-root descent to proper factor
233 for M29. Production performs no hidden progression enumeration and remains
unresolved for these nontrivial prime-bit requests.

## Installed artifact check

The fresh 0.59.9 wheel passes exact source-content inventory and isolated
installation checks. Removed production recurrence modules are absent; the
installed CLI prints the checked M11 factor 23 when explicitly requested.
Build v2 took 1.79s and isolated verification 4.29s, both below the unchanged
35s/1GiB guards. Build v1 failed because the local environment lacked the
setuptools backend; v2 used normal isolated build dependencies. Wheel SHA-256:
`3db84dab5604a09199b5fdc79e0fb60359a6de767447c723daf566efee44cb1f`.
This packaging check does not certify the missing transverse evaluator.

## Closed family progression admission

`Special_Factor_Progressions.thy` passes the full Etale_Primary_Carry session
with oracle-dependency checks (v29): 15.84s, 459.4MB sampled peak under the
unchanged 35s/4GiB guard. The theorems derive `2p | q-1` for odd prime
Mersenne exponents and `2^(n+2) | q-1` for Fermat n>=2 from prime-divisor
assumptions. No factor list or assumed progression membership appears.

The session now inherits standard HOL-Number_Theory; its separate dependency
setup completed in 136.87s under a 300s/4GiB setup guard. This did not change
the 35s project-proof gate or any CLI performance gate.

## Final combined semantic proof

Combined v43 passes the complete Etale_Primary_Carry session: 21.4065s,
479,038,368 bytes sampled peak, unchanged 35s/4GiB guard. It includes
closed family admission, exact slot/index-product correspondence, public
Fermat/Mersenne `prime N iff gcd(indexed_H mod N,N)=1`, and nonzero ring
annihilator including full-gcd cases. All theorem oracle audits pass.

This build used per-process `ISABELLE_TOOL_JAVA_OPTIONS=-Xms64m -Xmx256m
-Xss4m` and `ML_OPTIONS32=--minheap 100 --maxheap 450` through `isabelle env`,
with `build -v -j 1 -o threads=1 -o timeout=20 -d devtools/proofs/isabelle
Etale_Primary_Carry`. No persistent Isabelle settings changed. The compact
cylinder evaluator and its CLI/cost refinement remain P0.

## Final runtime and artifact checkpoint

The first frozen full-unit run hit its unchanged 300-second/1GiB guard at
300.065s, with 636.5MB sampled peak. It recorded 4,649 outcomes from the
4,777-test unit manifest, including eight failures. Seven were support
integration regressions, now repaired: proved-cycle support budget exhaustion,
two missing metric projections, and non-factory persistent stores. The existing
F4 `require_concrete=True` assertion remains unchanged and failing because
prime-bit recovery is absent.

Adversarial review rejected an intermediate noncanonical entry/cycle seam.
The final construction uses canonical dyadic blocks and a boundary spine;
bounded tests match atom-by-atom interned nodes, including a later temporal
append. Store-ledger redirection is rejected by the payload audit.

On the final source, 126 focused regressions passed in 15.46s (16.12s guard,
507.4MB peak), and strict mypy passed all 1,263 files. Ruff and diff checks pass.
The unexecuted 128-test tail of the original run was checked separately: its
first selection timed out at 35s after 40 successful tests with no failure
printed; the remaining 88 passed in 16.12s (16.92s guard). These selected runs
are not a successful full-suite time gate. The full run was not repeated after
the support repair and its time gate remains uncleared.

The final production coverage selection has 9 failures: the eight unchanged
F4/F5/M11/M13 API/CLI release assertions and the existing concrete-output F4
unit assertion. No assertion was weakened to accept UNKNOWN or GUARDED.

The rebuilt 0.59.9 wheel passes exact source inventory and isolated installation,
including absence of production LL/Pépin modules and checked M11 factor 23
output. Build 2.31s; verification 4.70s, both inside 35s/1GiB. Final wheel SHA-256:
`7e82ff4c9d7d59c66947b2749655a81eb94213908b7f68a99b866730279f369d`.
The earlier wheel hash above records the pre-repair artifact. The final source
fingerprint is in `final-component-source-0912.json`; it is a component snapshot,
not a release certificate. The compact transverse evaluator and CLI refinement,
general Collatz/196 source constructors and powered gates remain P0.
