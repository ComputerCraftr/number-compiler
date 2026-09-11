# Collatz carry-domain and Hensel validation

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

Reconstructed locally from the supplied September 10 test description.
The named ZIP and patch were not available in the workspace, Downloads or
attachments at implementation time. This checkpoint therefore does not claim
a byte-for-byte import or verification of the supplied archive/patch hashes.
The independently reproduced mathematical counts and witnesses agree.

The only authored-code addition is
`tests/validation/research/collatz/test_carry_domain_hensel_quotient.py`.
Production code and quotient admission are unchanged. The module remains in
the validation partition, and no ordinary unit tests are moved or removed.

## Locked results

Eight tests cover:

1. The five carry actions on 64 digits, with fibers `21/1/20/1/21`.
2. Complete adjacent-position domain factorization for all six residual
   division phases: `(5,1), (5,2), (5,4), (5,5), (4,5), (2,5)`.
3. The EQ witness 58723: `(35,21,14)` becomes `(21,32,21)`, then frame cropping
   gives `(32,21)`. EQ remains at position one after the complete operation.
4. All positive odd 16-bit sources: phase zero grows only with digit 1 or 2,
   phase one only with digit 1, and later phases never grow. Every growth
   digit is LT. An all-sentinel source has zero normalized active cells.
5. Source-word Hensel pullback `v2(9*m+3+2**e)-e`, using the existing rational
   root germ while successor-word construction is poisoned. Independent
   scalar arithmetic checks the result.
6. The 15/19 refinement witness (next valuations 1 and 3), followed by the
   stronger 129/385 collision. Their finite angular coordinates are both
   `(2,36,1)`; their targets 97 and 289 split under the same observer.
7. Gauge-free measurement on 1,984 positive odd sources below 4,096 with
   low digit different from 21. Domain-output keys yield 792 classes, with
   1,707 sources in 522 conflicted classes. Hensel refinement yields 1,024
   classes, with 1,476 sources in 524 conflicted classes.
8. All six residual phases at frame depths 1, 193 and 385: identical semantic
   keys and exact targets, with valuation differences 1152.

The domain-output record includes residual phase, current domain geometry,
raw-domain output and carry exit for each of three carry ports, growth,
next frame crop and cropped successor geometry. The Hensel addition contains
next valuation and the finite angular multiplier/offset. The exact source,
successor integer and current frame depth do not enter these keys.

Fewer sources in conflicted fibers does not mean successor congruence:
both the explicit witness and the complete finite measurement reject it.
The required next object is a recursive/self-advancing value-output morphism,
with an authenticated complete context transition graph. These tests do not
prove the existence or scaling of such an object.

## Verification

All runs use the unchanged 35-second/1 GiB guard, one process at a time.
`manifest.json` records final counts, source fingerprints, and evidence hashes.
The 17-test focused validation includes the eight new tests, the two existing
radix-4 word-transducer tests and seven symbolic-action proof tests. Ordinary
dependencies cover the existing frame, raw-field and output-morphism tests.

| Check | Result |
|---|---|
| New validation module | 8 passed in 1.55 seconds |
| Focused validation/proofs, including the new module | 17 passed in 1.86 seconds |
| Ordinary Collatz dependencies | 51 passed, 9 validation cases deselected, in 2.40 seconds |
| Structural policy and proof/production boundary | 41 passed, 1 validation case deselected, in 6.02 seconds |
| Strict nonincremental mypy | 1,099 source files passed |
| Changed-file Ruff and formatting | Passed |

`source-comparison.json` confirms that removing only the new test from the
current source fingerprint reproduces the preceding local checkpoint exactly.
This comparison uses the existing fingerprint owner and a temporary source
view; it does not alter the workspace. It covers authored files in `src`,
`tests`, `devtools` and `pyproject.toml`, with the owner's usual cache exclusions.

`carry-domain-hensel.patch` contains only the new test module and can be applied
from a matching repository root using `patch -p1`. It is a newly generated
local patch, not the unavailable patch whose hash was supplied in the request.

No full unit or broad exhaustive validation run is claimed for this
test/documentation-only update. The preceding 4,167-test unit checkpoint
remains associated with its own source fingerprint.

Run the new tests from the repository root with fresh evidence destinations:

```bash
.venv/bin/python -m devtools.checks.process_guard \
  --output /tmp/collatz-hensel.log --report /tmp/collatz-hensel.guard.json -- \
  .venv/bin/python -m pytest -q -m validation \
  tests/validation/research/collatz/test_carry_domain_hensel_quotient.py
```
