# Isabelle validation of reverse/add residual closure

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

The full active 196 contextual quotient is **not completed or admitted**.
This checkpoint adds kernel-checked proofs, a counterexample to extending the
previous finite merges, and an exhaustive observability diagnostic. It does
not present a conditional theorem as a concrete 196 quotient certificate.

## Machine-checked results

Isabelle2025-2 successfully builds the session in
[`devtools/proofs/isabelle`](../../../devtools/proofs/isabelle/ROOT).
`quick_and_dirty` is false. Each principal result is checked for an empty
oracle dependency list; no `sorry`, skipped proof or evaluation oracle is
used. The final build takes 9.60 seconds under the unchanged 35-second,
1 GiB process guard, with 450,547,240 bytes sampled peak physical footprint.

* `carry_from_domain` and `carry_depends_only_on_domains`: carry is determined
  by the existing three actions, without another carry state variable.
* `seven_bands_suffice`: the seven bands suffice for the declared no-growth
  carry observation for every pair value and both incoming Boolean carries.
  `growth_edge_separates_seven_band` proves the 16/18 growth-edge counterexample.
* `valid_pair_successor`, `initial_196_valid` and `all_196_pair_fields_valid`:
  the exact nonempty, symmetric, bounded pair-field invariant contains
  `[7,18,7]`, the 196 seed, and is preserved for every number of steps.
  This invariant retains exact pair values; it is not the requested quotient.
* `factor_through_iff` and `contextual_successor_iff`: exact criteria for a
  residual successor on a specified admitted domain.
* `iterate_commutes` and `invariant_quotient_exists`: invariant closure plus
  successor congruence suffices for all-time commutation. Their congruence
  premise is **not discharged for an active 196 contextual representation**.
* `two_event_key_has_no_total_successor`: the earlier two-event observation,
  including domains, growth and width, has no total successor on all fields.
* `five_examples_separated_by_three_events`: all five source values from the
  earlier positive example become distinct after three events.
* `two_cell_four_event_injective`: for the two-cell fields `[s,s]`, all 19
  values of s are distinguished by observations at times zero through four.
  Hence preserving all future observations forces exact s in this family.

The concrete two-event counterexample is:

| Initial pair field | First successor | Second successor | Third successor |
|---|---|---|---|
| `(10)` | `(1,1)` | `(2,2)` | `(4,4)` |
| `(12)` | `(3,3)` | `(6,6)` | `(12,12)` |

The initial and first two domain/growth/width observations agree. The third
domain observations differ. The compiler regression now checks that extending
the old three-class residual to this observation is rejected, and that
compiling the longer continuation requires five classes for the five values.
Its existing source-free finite transport check remains intact.

## Exhaustive finite diagnostic

`devtools.proofs.reverse_domain_observability` refines sources by their exact
domain observation histories. Equalities use interned tuples, not digest
comparisons. It uses the canonical exact pair-step oracle and retains only
the current field for each source. These diagnostic labels never enter a
production future-state cache.

| Initial width | Valid symmetric fields | First horizon separating all sources |
|---|---:|---:|
| 1 | 10 | 3 |
| 2 | 19 | 4 |
| 3 | 190 | 5 |
| 4 | 361 | 5 |
| 5 | 3,610 | 6 |
| 6 | 6,859 | 5 |
| 7 | 68,590 | 6 |
| 8 | 130,321 | 5 |

All **209,960** valid fixed-width symmetric pair fields are distinguished by
current and future domain observations within these horizons. Odd centers
are constrained to even pair values; active zero cells remain admissible.
This is an exhaustive Python computation over the listed finite domains,
not an Isabelle proof for arbitrary widths or the unbounded 196 trajectory.
The max-width-eight run takes 5.35 seconds with 121,799,160 bytes sampled peak.

These findings rule out the tested merges under a complete current-and-future
domain observation. They do not rule out consumer-specific function sharing,
geometry-parametric representations, or an as-yet unproved 196-specific grammar.
The stronger arbitrary-width separation argument considered during this work
has not been formalized and is not claimed as a proved impossibility theorem.

## Reproduction

Run from the repository root, one process group at a time, with fresh log paths:

```bash
.venv/bin/python -m devtools.checks.process_guard \
  --output /tmp/reverse-isabelle.log --report /tmp/reverse-isabelle.json -- \
  /Applications/Isabelle2025-2.app/bin/isabelle env \
  'ISABELLE_TOOL_JAVA_OPTIONS=-Xms64m -Xmx256m -Xss4m' \
  'ML_OPTIONS32=--minheap 100 --maxheap 450' \
  /Applications/Isabelle2025-2.app/bin/isabelle build \
  -v -j 1 -o timeout=20 -D devtools/proofs/isabelle

.venv/bin/python -m devtools.checks.process_guard \
  --output /tmp/reverse-observability.log --report /tmp/reverse-observability.json -- \
  .venv/bin/python -m devtools.proofs.reverse_domain_observability --max-width 8
```

The `build-*` logs retain intermediate proof-script errors and bounded tactic
timeouts. `isabelle.log` and `isabelle.guard.json` contain the successful final
session build. The general proof was made explicit where unconstrained tactic
search was slow; no theorem assumptions or resource guards were weakened.

## Compiler verification

The focused compiler suite passes **78 tests in 6.57 seconds** (8.14 seconds
under the guard). Strict nonincremental mypy passes for 1,093 files; Ruff
checks, formatting and structural policy pass. The first typing run found a
test-only fixed-tuple inference error, corrected with an explicit variable
length tuple annotation. Production execution code is unchanged. The full
serial Python unit suite was not rerun for this proof/test-only checkpoint;
the preceding 4,156-test result remains attached to its original fingerprint.

No active future-class admission, new public powered execution path, full
196 quotient certificate or speedup is claimed. The implementation request
remains incomplete. `manifest.json` records the exact source and evidence
identities for these results.
