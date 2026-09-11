# Alternating-radix carry harmonic port research

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

The [research note](../../../docs/carry-harmonic-port-actions.md) defines the
port-conditioned carry occupancy action, its spatial composition, the
border-flux projection, and its exact whole-field F5 forcing observation.
This update adds documentation, research proof code, tests, and an Isabelle
theory. It makes no production routing or quotient-admission change.

## Results and corrected identity convention

Complete three-generator exploration reproduces the supplied fixed-length
counts without enumerating exponentially many domain words:

| Length | Domain words | Occupancy actions | Border actions |
|---:|---:|---:|---:|
| 1 | 3 | 3 | 3 |
| 2 | 9 | 7 | 7 |
| 4 | 81 | 27 | 15 |
| 6 | 729 | 69 | 21 |
| 8 | 6,561 | 141 | 21 |
| 12 | 531,441 | 335 | 21 |
| 16 | 43,046,721 | 473 | 21 |
| 18 | 387,420,489 | 501 | 21 |

The occupancy count **501 is length-indexed**. The all-EQ carry function is
identity, but its incoming-one harmonic emissions depend on length modulo ten.
For example, lengths two and four have equal parity and different emissions.
Across lengths there are **510** row functions and **1,010** phase-typed
reachable states. All **3,030** generator edges close. The exact reachable
layers repeat after ten from length 18, establishing continuing saturation
under deterministic generator expansion.

For a zero-based first decisive index j, the differing incoming carry prefix
has length **j+1**. The implementation consistently uses `(j+1) mod10` for the
occupancy code and `j mod2` for the border code. The border-flux action is
derived from occupancy plus width parity and is not stored independently.

The 501/21 counts are spatial-action counts, not a claim that the number of
temporal value/threshold bindings becomes bounded. The counterexample
`(GT,LT,LT,LT)` versus `(LT,LT,GT,LT)` shares the action but differs at C1.
The pair-field counterexample `(4,4)` versus `(8,8)` shares the action but has
different next actions. A32 was not rerun or modified by this documentation
and proof update.

## Executable controls

The reference owner is `devtools/proofs/carry_harmonic_ports.py`. Spatial
composition never scans a carry or digit field; exact word scans are confined
to the independent validation oracle, which imports the existing carry owner.

`devtools/proofs/carry_harmonic_port_probe.py` provides four reproducible modes:

- `finite`: fixed-length counts and complete phase-typed generator closure;
- `spatial`: every LT/EQ/GT word through width eight, every split including
  empty ends, both carry-occupancy and signed-border composition;
- `parameterization`: full two-port-function/code equivalence through width
  ten, including the decisive-index convention and border projection;
- `trajectory`: 1,024 exact 196 transitions, aligned complete blocks from
  states S1..S1024, and whole-action successor conflicts from S0..S1023.

Run each through the unchanged process guard, for example:

```sh
.venv/bin/python -m devtools.checks.process_guard \
  --output results/current/carry-harmonic-ports-2026-09-10/recheck-spatial.log \
  --report results/current/carry-harmonic-ports-2026-09-10/recheck-spatial.guard.json \
  -- .venv/bin/python -m devtools.proofs.carry_harmonic_port_probe spatial
```

Use fresh output paths on subsequent runs. Expensive/exhaustive checks remain
in the explicit validation partition. The ordinary tests cover finite closure,
the all-EQ length distinction, the harmonic-kernel witness, arbitrary interior
port loss, temporal conflict, and nonmaterializing spatial doubling to width
2^128.

## Formal proof scope

`devtools/proofs/isabelle/Reverse_Carry_Harmonic_Ports.thy` is registered in the
existing `Reverse_Residuals` session. It states general spatial concatenation,
carry coalescence, the first-decisive prefix difference, ten-periodicity,
population projection/inversion, and code-space cardinalities. Cardinalities
of the proposed code spaces are separate from their finite reachability proof.
Neither this theory nor the finite experiments establish general temporal
closure, arbitrary pointwise consumer factorization, or a verified refinement
of the Python implementation.

The **full Isabelle session passes**, with no oracle dependencies, in
**11.456 seconds**, with a sampled peak of **458,852,968 bytes**. The accepted
evidence is `isabelle-thirteenth.log` and its guard report. Earlier failed and
timed-out proof attempts remain recorded; they are not counted as successful
validation. The unchanged guard is 35 seconds and 1 GiB.

The isolated local profile
`/Users/john/.isabelle/number-compiler-ports-proof/etc/settings` uses Java
`-Xms64m -Xmx256m -Xss4m` and ML `--minheap 100 --maxheap 450`. Build with
`ISABELLE_IDENTIFIER=number-compiler-ports-proof` and
`isabelle build -v -o naproche_server=false -D devtools/proofs/isabelle`,
through the same process guard. The unused Naproche server is disabled;
the HOL proof obligations and oracle check are unchanged.

## Final validation and 196 measurements

Final source fingerprint:
`edd4c1dc915298508223bdb1727cbd9047c98b3a342e21ab52b5a40d15cdcee3`.
`validation-summary.json` records this fingerprint, the theory SHA-256, and
the checked results. The `*-verified` logs are the final Python evidence.

- **46/46** focused and repository-policy tests pass in **5.662 seconds**
  JUnit time. Both source fingerprints match the final tree.
- **209,960/209,960** admissible symmetric pair fields through width eight
  reproduce the exact signed forcing harmonics. All eight width partitions
  pass in **6.469 seconds** JUnit time, with matching source fingerprints.
- **167,304** spatial composition comparisons have zero mismatches.
- **88,572** domain words through width ten verify the length-indexed
  occupancy parameterization and the global 21-code border parameterization.
- Complete generator closure yields 510 emission functions, 1,010 phase-typed
  states, and 3,030 checked transitions. Fixed-length layers 18 and 28 agree
  exactly at the same phase, certifying the ten-layer periodic continuation.
- Strict mypy passes all **1,149** source files; Ruff and changed-file
  formatting pass. No full ordinary-suite rerun is claimed for this update.

Aligned complete blocks from **S1..S1024**, after the indicated number of
exact 196 successors, reproduce the supplied measurements:

| Block length | Exact domain words | Occupancy actions | Border actions |
|---:|---:|---:|---:|
| 8 | 3,868 | 120 | 20 |
| 16 | 13,432 | 182 | 20 |
| 32 | 6,524 | 166 | 20 |
| 64 | 3,021 | 125 | 20 |
| 128 | 1,268 | 105 | 20 |

The whole-state comparison uses transition sources **S0..S1023** and records
**134** phase/action keys, **110** with conflicting next keys. The original
`trajectory.log` sampled aligned blocks at S0..S1023 instead and therefore had
slightly smaller raw word counts. The final probe makes both index ranges
explicit; `trajectory-verified.log` is the matching comparison.

The trajectory probe reports all 1,024 oracle successors. Neither the spatial
compression ratios nor the Isabelle spatial laws are evidence of a powered
temporal speedup. The next required proof remains consumer factorization
before replacing pointwise carry bindings inside temporal composition.
