# Historical reports

These reports describe their original checkpoints. They are not current release claims.

For current navigation, use the [documentation index](index.md). Superseded
authored notes and their maintained destinations are listed in the
[migration and provenance index](provenance.md). Reviewed implementation
checkpoints are consolidated in the [2026-W37](../results/current/2026-W37/README.md)
and [2026-W38](../results/current/2026-W38/README.md) sprint records.

The supplied [decimal pair quotient research](archive/reverse-add/DECIMAL_PAIR_QUOTIENT_RESEARCH.md)
is preserved verbatim (SHA-256 `023599ebc89d1f17601bb84f4fda49c2daaff3308a39e3a7179630cd41683cbe`).
Its current-path interpretation and theorem boundaries are recorded in the
[reverse/add research synthesis](research/reverse-add.md); its older path
names and proposed backend are not instructions to restore deleted execution.

The supplied [v0.12.0 carry-slab jump report](archive/reverse-add/CARRY_SLAB_JUMP_RESULTS.md)
is also preserved verbatim (SHA-256
`e5a4e9bb00d4391b6c6e99c35b3fb1ef8570d75dbf13189ed349338a9a6bc310`).
It records historical D4/D8 representation sizes and guarded jump results;
its executable and raw measurement environment have not been recovered.
The [comparison](research/reverse-add.md#comparison-with-the-current-output-morphism-gates)
separates those results from current production cutover acceptance.

Original generated measurements remain under [results](../results/). Reviewed
checkpoint prose is consolidated by ISO week, while ignored logs, profiles and
fingerprints retain their original evidence paths. Current validation is
recorded separately in [release status](release-status.md).

The retained archive is a mixed-provenance collection. The decimal pair
paper and carry-slab jump report identified above are externally supplied.
The other entries are authored
historical research; they are retained only where a derivation, measurement,
or design boundary is not fully reproduced in the maintained syntheses.  In
particular, a filename ending in `RESULTS` does not make a report external or a
current release result.

The archive is grouped by purpose: `collatz/` records early raw-field
and character experiments; `hashlife/` records the evolution of powered DAG and
causal execution designs; `power-numbers/` records special-number terminal and
Frobenius experiments; `primes/` records wheel and clock studies;
`repository-and-algebra/` records shared representation and cleanup history;
and `reverse-add/` records carry and pair-quotient investigations. These files
remain available at their existing paths, but this maintained page does not
recreate an index of every obsolete report.

Representative cornerstone records are:

- Collatz: [canonical formula integration](archive/collatz/CANONICAL_FORMULA_COLLATZ_INTEGRATION.md)
  and [raw-field results](archive/collatz/COLLATZ_RAW_FIELD_RESULTS.md).
- HashLife: [state/action growth](archive/hashlife/HASHLIFE_STATE_ACTION_GROWTH_RESULTS.md),
  [metrics integrity](archive/hashlife/HASHLIFE_METRICS_INTEGRITY_RESULTS.md), and
  [spacetime execution audit](archive/hashlife/SPACETIME_EXECUTION_AUDIT.md).
- Special numbers: [transverse-jet results](archive/power-numbers/SPECIAL_TRANSVERSE_JET_RESULTS.md)
  and [terminal constructor frontier](archive/power-numbers/TERMINAL_SECTION_CONSTRUCTOR_FRONTIER.md).
- Primes: [prime coordinates](archive/primes/PRIME_COORDINATE_RESULTS.md) and
  [clock quotient results](archive/primes/PRIME_CLOCK_QUOTIENT_RESULTS.md).
- Shared algebra: [canonical compiler audit](archive/repository-and-algebra/CANONICAL_COMPILER_AUDIT.md),
  [production transfer boundary](archive/repository-and-algebra/PRODUCTION_TRANSFER_BOUNDARY.md),
  and [radial innovation results](archive/repository-and-algebra/RADIAL_INNOVATION_RESULTS.md).
- Reverse/add: [carry event formulas](archive/reverse-add/CARRY_EVENT_FORMULA_RESULTS.md)
  and the supplied [decimal pair quotient paper](archive/reverse-add/DECIMAL_PAIR_QUOTIENT_RESEARCH.md).

Use repository search for a specific retained filename. The maintained
[research syntheses](index.md#research-syntheses) remain the entry point for
current claim boundaries.
