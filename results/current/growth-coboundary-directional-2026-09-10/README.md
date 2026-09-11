# Growth coboundary and directional quotient update

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

See [the design and integration scope](../../../docs/growth-coboundary-directional-quotients.md).

## 196 experiment

The new twelve-symbol growth chart consumes the residue and two carry ports
derived from the existing geometry. Its radius-one emitter produces domain,
F5, and F2 outputs directly. The canonical occurrence has no source-domain
decoder. A local one-variable chart fusion also recognizes the varying
LT-1/GT-10 gauge as the constant symbol `(q,delta)=(1,0)`.

The complete width-four through width-eight growth audit confirms:

| Width | Growth sources | Quotient images | Largest fiber |
|---|---:|---:|---:|
| 4 | 180 | 99 | 2 |
| 5 | 1,805 | 1,040 | 2 |
| 6 | 3,429 | 1,080 | 4 |
| 7 | 34,295 | 11,705 | 4 |
| 8 | 65,160 | 12,429 | 8 |

Every quotient output matches `pair_step`. The equality of image and quotient
counts is finite evidence for the converse; only forward factorization is the
formal proof target.

At capacity nine, the separate-chart candidate (`a16-first.log`) retained
8,855 nodes. Fusing quotient views with their affine value transport reduces
that to 8,085 (`a16-fused.log`, `a16-mode.log`). This is still worse than the
preceding residue checkpoint's 7,784. Keeping the residue lowering as default
also removes unused growth construction on the capacity-overflow branch,
giving 7,769 (`a16-default.log`). The new mode is explicitly selected by
`--growth-coboundary`; it is not presented as a production speedup.

The source-independent A16 probe records no gauge-fusion hits despite the
positive local regression. This distinguishes a sound quotient from a
general compiler normalizer that finds all of its aliases. A32 still reaches
the 30,000-node limit. Complete midpoint planes remain in the general action
interface; zero intermediate Gamma/residue publication is not established.

`growth_source_binding_families` counts native chart operand tuples;
`growth_coboundary_families` counts retained reachable chart functions, not a
learned semantic partition. `growth_gauge_alias_hits` counts one-variable
chart compositions that fold to a constant. The no-growth and growth residual
counts are reported separately. All native nodes and projections remain in
the total node, edge, and range accounts.

## Collatz and power numbers

The Collatz changes consume carry geometry before exact value views, reduce
left/right streams independently, and pair them without an exact intermediate
target digit. Fixed domain tables are generated from 384 directional pairs
across all six phases. See
[the Collatz evidence](../collatz-directional-views-2026-09-10/README.md).

The power-number audit removes an unused per-level controller and separates
cyclic/negacyclic angular actions from their demanded étale selector output.
It does not register an uncertified tile family or synthesize a prime bit.
See [the applicability note](../../../docs/research/power-numbers/GEOMETRY_FIRST_ETALE_TILE_APPLICABILITY.md).

## Verification

Final verification passes **287 unique selected tests**:

- 160 ordinary focused/dependency/policy tests, with one opt-in validation
  test deselected from that ordinary selection;
- 9 Collatz validation tests, including all 32,768 odd 16-bit sources and eight
  successors for each of seven control seeds;
- 25 power-number research tests, including the new étale scheduler-boundary
  audit (the earlier estimate of 26 selected tests was corrected by collection);
- 5 complete growth-fiber audits; and
- 88 exhaustive geometry partitions: all 209,960 admissible symmetric fields
  through width eight in **each** of the default and coboundary modes.

All JUnit collection manifests are complete and unique. Their before/after
source fingerprints match the final tree, with no failures, errors, or skips.
The selected suite times sum to 185.015 seconds; this is not a full-suite
measurement. Exhaustive work remains behind the validation marker.

Strict mypy passes for all 1,160 source files. Ruff and formatting checks pass.
The complete Isabelle `Reverse_Residuals` session passes with the new growth
theory and its oracle-dependency audit. It derives the even-center carry
equality from the recurrence and symmetry, and proves forward factorization
without claiming the converse. The guarded build took 16.663 seconds and
peaked at 435,211,216 bytes; see
`isabelle-final-corrected.log` (local artifact: `../growth-coboundary-2026-09-10/isabelle-final-corrected.log`)
and its adjacent guard report. Diagnostic attempts remain separate.

Final A16 measurements (`final/a16-*.log`) include all retained storage:

| Lowering | Nodes | Argument edges | Possible-value atoms | Native + unary consumers |
|---|---:|---:|---:|---:|
| Default residue | 7,769 | 19,123 | 25,930 | 1,604 |
| Coboundary | 8,085 | 18,599 | 27,715 | 2,740 |

The coboundary action has 320 chart functions, 192 growth-domain residuals,
and 384 no-growth residuals. The consumer total includes the fused native
value-plane morphisms; it is not a count solely of nonlinear predicates.
All completed checkpoints retain `primitive_successors=1`, zero full-19
growth fallbacks, and zero generic parity transport tables. The A32 probes
both report **budget_exceeded at 30,000 nodes**, not completed actions.
Their last completed A16 checkpoints at capacity 16 retain respectively
20,941 and 21,505 nodes.

All heavy checks ran serially under the existing 35-second / 1-GiB guard.
The `preformat/` run predates the last formatting change and was rejected by
the source-freeze check; it contributes no final evidence.

The complete machine-readable record is
`final/validation-summary.json` (local artifact: `final/validation-summary.json`).
Final source fingerprint:
`48144c963551e89f2b2a39ac7218697bfc080c64c3571fd58f42c367106ecc94`.
Growth theory SHA-256:
`208bcfcaf2e5785dca35f02bc0b1cbe708489246469decc0b8623c91d1c8bf5f`.
