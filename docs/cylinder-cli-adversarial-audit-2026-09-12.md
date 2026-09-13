# Cylinder, CLI and Isabelle adversarial audit — 2026-09-12

This is the pre-fix audit snapshot. See [the follow-up fixes and remaining
release obligations](cylinder-cli-release-fixes-2026-09-12.md) for current status.

Three read-only explorer agents audited CLI work, formal theorem coverage, and
consumer connectivity. The parent independently checked the principal algebra,
call sites and work counts. Scope is the current uncommitted integration over
HEAD `92afb957c54689fc004982a1a0f4bb132a18697a`; findings include both new changes
and pre-existing limitations that the new acceptance evidence does not close.
This audit changes documentation only.

The delivered state is production **library observers and conditional factor
consumers**, with a separate CLI Frobenius factor probe. It does not yet deliver
the requested shared quotient powering and factor recovery throughout the CLI.
Earlier descriptions of this as completed production integration were too broad.
No unsound Isabelle theorem or incorrect printed factor was found; the main
formal issue is missing refinement and reachability of the proved objects.

## P1 — Observers do not reach the requested CLI consumers

The numeric CLI was exercised with individual new methods replaced by functions
that raise immediately if called:

| Command | Disabled method | Result |
| --- | --- | --- |
| `nth collatz 3 --seed 27 --output-base 10` | `CollatzClockObservers.modular` | `124`, exit 0 |
| Same | `TwistedCylinderProjection.observe` | `124`, exit 0 |
| `nth 196 3 --output-base 10` | `ArithmeticTile.step_with_primary_carry_jet` | `7436`, exit 0 |
| Same | `ReverseAddPoweredTerm.mirror_obstruction` | `7436`, exit 0 |
| `classify mersenne 131 --factor --allow-classical-ceiling` | `factor_from_etale_root` | composite, factor 263, exit 0 |

These bounded poison checks alone establish non-use on those inputs. Source
search additionally finds no compiler/CLI consumers of the new
`CollatzClockObservers`, primary-jet tile method, reverse/add mirror method or
supplied-root factor helper. Their direct consumers are tests, research and docs.

The factor command follows `api/cli.py:354` to
`sequences/power_numbers/theorem_query.py:213`, then a separate probe in
`sequences/power_numbers/etale_factor.py:111`. Adding library files under `src`
does not establish a CLI optimization. Simply calling an otherwise unused
observer would not fix this: a demanded output must consume its result and avoid
the work it replaces.

## P1 — The root theorem does not certify the CLI defect construction

`devtools/proofs/isabelle/etale/Etale_Primality_Bridge.thy:242` proves proper
factor recovery from a supplied canonical nontrivial scalar root satisfying
`N dvd D*(D+2)`. The CLI computes coefficients of an additive Frobenius defect
instead. The missing bridge is concrete:

```text
M11: N = 2047
CLI probe defect = (391, 1474)
D*(D+2) mod N for these coordinates = (138, 1710)
proper coefficient gcd = 23
```

Neither coefficient satisfies the root premise. The factor 23 is still valid:
the generic proper-gcd theorem at `Etale_Primality_Bridge.thy:164` supports that
arithmetic conclusion. What is absent is a proof that the CLI constructs the
root variety used in the carry-jet experiment, or a proof that this different
probe always finds a proper split. The supplied-root API at
`etale_factor.py:178` checks the correct premise but is disconnected from CLI
discovery.

`Mersenne_Etale_Zero_Section.thy:198` assumes the root, normalization equations,
canonical remainder and abstract key; it proves zero from the deck and seam.
The jet coordinates are explicitly unnecessary for that theorem. It does not
prove Python sign selection and carry construction satisfy those premises,
injectivity on nonzero roots, Fermat separation, or a terminal clock bridge.
The 320 factor-backed CRT rows supply roots externally and cannot close the
candidate-derived construction obligation.

Observed CLI limits reinforce this distinction: `classify fermat 5 --factor`
and `classify mersenne 131 --factor` return unknown, exit 3. Allowing the
classical ceiling yields composite in both cases, but only M131 yields a factor
(263). F5 still has no factor. These are correctly bounded outcomes, not universal
free factor recovery.

## P1 — Repeated-program compression does not establish a semantic quotient

`sequences/collatz/power.py:503` interns concat by the two child node IDs. In a
fresh arena, for `a,b,c = event(1),event(2),event(3)`:

```text
concat(concat(a,b),c).node_id = 6
concat(a,concat(b,c)).node_id = 8
materialized cocycles are equal
```

This is a pre-existing syntactic arena behavior, not a newly introduced wrong
answer. It shows that generic matrix associativity in
`Skew_Cylinder_Observers.thy:18` does not establish canonical action identity or
semantic alias reduction in that arena. Reassociation alone also does not
establish all the source and consumer equivalences a real quotient requires.

`devtools/proofs/cylinder_skew_probe.py:15` supplies
`arena.power(arena.event(2), duration)`. Its A1024 and larger analogues demonstrate
efficient observation of an already shared repeated program. They do not measure
discovery and normalization of actual input rays through `nth`, or prove genuine
source aliases preserve successors and demanded consumers. The existing docs
correctly disclose this boundary; those tests cannot serve as the missing CLI
acceptance gate.

## P2 — Factor collection adds CLI work beyond the primality bit

`sequences/power_numbers/certificate.py:195` and `:253` now pass
`collect_gcd_packet=True` unconditionally to the classical ceiling. HEAD did not.
A spy on `_proper_gcd_packet` confirms one invocation for
`classify mersenne 11 --allow-classical-ceiling --format json` without `--factor`.
The result reports `gcd_witnesses=0`: that field counts successful witnesses,
not gcd operations. This is a real new default-path work regression when the
classical ceiling is allowed; no material wall-time penalty is established by
the small example.

When a composite has no existing factor, `with_etale_factor` additionally calls
`_quadratic_power_pair` (`etale_factor.py:90`). This loops through the bits of the
candidate N, after any classical Pepin/Lucas-Lehmer computation. For F12 the
extra probe reports 4098 quadratic ring multiplications. It is not a constant
cost projection of an already computed terminal object. The CLI documents the
separate witness query and exposes its product count, but has no distinct
factor-work budget; its candidate-size cap is not a latency guarantee.

A fresh-process parent check of `classify fermat 12 --allow-classical-ceiling
--format json` measured 0.784 seconds wall / 0.706 seconds CPU without `--factor`
and 1.569 seconds wall / 1.528 seconds CPU with it. Both returned composite with
no factor. These are single local samples, not a stable benchmark distribution;
the exact additional 4098 ring products establish the extra work independently
of timing noise.

The remedy is to keep witness demand explicit through certificate construction,
reuse a proved existing observation when available, and charge/bound any
fallback probe separately. Removing the probe without a replacement would
remove the currently available Mersenne factor functionality.

## P2 — Some formal observers prove a weaker or different predicate

`Twisted_Support_Observers.thy:70`–`:90` proves that a nonzero **scalar evaluated
sum** implies a mirror mismatch. `first_mirror_obstruction`
(`arithmetic/polynomials/twisted_observer.py:100`) returns on a nonzero folded
**coefficient vector**. A vector `(1,-1)` can evaluate to zero at radix 1.
Consequently the existing scalar lemma is not the complete refinement of the
returned vector predicate. The zero result also needs the degree-bound argument
for the final sheet, which is present as Python logic but not as that theorem.
This is missing proof coverage; it is not a counterexample to the Python result.

Likewise, the gcd saturation lemmas do not formalize the min-plus matrices in
`CollatzClockObservers.tropical`, and the rational product identity does not
formalize the full `SArithmeticClock` norm interpretation. Generic transport and
modular demand laws are useful components, but no Python DAG-to-observer
refinement is supplied. These distinctions should remain explicit in proof
coverage and release claims.

## P2 — Multiple views repeat work before any future CLI wiring

`CollatzClockObservers._fold` allocates a new local node cache for every query
(`clock_observers.py:79`), so repeated identical views traverse the action again.
Both `ArithmeticTile.step_with_twisted_projection` and
`step_with_primary_carry_jet` call `_step_with_field` separately
(`arithmetic_tile.py:385`, `:396`), repeating the square when callers ask for both.
These are library scaling limitations, not observed current CLI regressions.

The optional mirror ladder also rescans all digits per sheet. An all-ones target
produces the following exact digit callback counts:

| Target width | Callback calls | Result |
| --- | ---: | --- |
| 16 | 192 | no obstruction |
| 128 | 2304 | no obstruction |
| 1024 | 24576 | no obstruction |

The width-1024 case takes 24 reads per digit; an ordinary mirrored comparison
needs 1024 total reads for this palindrome. The source explicitly keeps that
cheaper default. Wiring the ladder everywhere would introduce a slowdown;
integration needs demand-based sheet choice and shared coefficient/digit work.

## Existing CLI slow paths confirmed against HEAD

The performance explorer also identified costs unchanged by this integration:

- `classify mersenne 18446744073709551629 --max-candidate-bits
  18446744073709551629 --format json` exceeded a three-second probe while checking
  the exponent, both here and in HEAD. `numbers.py:274` calls `smallest_factor`
  above the 64-bit predicate range; `sequences/prime/set.py:209` scans odd trial
  divisors through the square root. The default CLI cap rejects this input, but
  explicitly raising it exposes an unbounded-in-practice exact gate. A bounded
  exact gate with an unresolved outcome is needed for adversarial large inputs.
- `classify mersenne 20011 --allow-classical-ceiling --format json` exceeded a
  ten-second CLI probe. Its isolated classical ceiling took about 21 seconds
  for 20,009 nonlinear squarings. This is explicitly requested recurrence work.
- `nth collatz 50 --seed 27 --radix 6 --format value --max-output-bits 100000`
  took 4.39 seconds here and 4.37 seconds in HEAD. At 100 steps the current tree
  exceeded an eight-second probe. The path materializes an endpoint through
  `PoweredCollatzTermPayload.digits` (`collatz/block_power.py:595`); the new
  observers do not replace it.

These bounded samples establish exposed slow paths, not new observer-induced
regressions. They should be included in actual CLI growth acceptance rather than
replaced by supplied-program observer timings.

## Evidence and completion criteria

Checks used the local Python environment at
`/tmp/number-compiler-restore-venv/bin/python` with `PYTHONPATH=src`, source traces,
numeric CLI poison checks, exact coefficient/root checks and operation counts.
Fresh-process CLI timing invoked
`python -c 'from number_compiler.api.cli import main; raise SystemExit(main())'`
with the listed arguments; importing the CLI module alone does not invoke it.
The performance explorer also ran 95 focused API/CLI/factor tests successfully.
The audit did not rerun the entire unit suite or Isabelle session. Earlier
kernel builds and differential tests remain evidence for their stated scope,
not for the missing production bridges. Existing worktree changes were preserved.

Completion requires CLI tests that demand and consume the new quotient outputs,
actual-input growth tests including discovery/normalization costs, and Isabelle
refinements matching those exact runtime objects. Each admitted alias needs
successor and consumer agreement. Factor tests must construct observations from
the candidate without supplied factors and distinguish verified available
witnesses from a universal discovery theorem. Shared-view costs and fallback
work must be visible in the same CLI accounting used for acceptance.
