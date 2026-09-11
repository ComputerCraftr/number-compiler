# Binary special-germ support checkpoint

This checkpoint implements the prime-clock-inspired decomposition of the
terminal Fermat/Mersenne certificate into a deterministic binary transport and
one support-sensitive observer.

## Implemented production algebra

`src/number_compiler/special_germ.py` adds two production-safe objects:

```text
SpecialGermTransfer
SpecialGermPlan
```

`SpecialGermTransfer` retains only the family and dyadic section span.  Its
endpoint operator is the shared `QuadraticPower`, so an `r`-level conductor
advance is constructed by the canonical binary monoid in

```text
bit_count(r) + bit_length(r) - 1
```

semantic compositions.  It stores no root tree, branch itinerary, carrier, or
per-level recurrence state.

`SpecialGermPlan` binds that transport to one `SpecialFrobeniusChunkSpec` and
requires exactly one endpoint support observation for the whole chunk.  The
production observation remains the existing fail-closed
`special_frobenius_chunk_probe()`: no source selector was invented by this
refactor.

## Non-cancelling support composition

For a valid Frobenius defect `d`, every passing local component sees `d=0` and
every failing component sees a unit.  For adjacent packets the exact passing
support therefore composes by

```text
D = gcd(N, d_left, d_right).
```

A prime component divides `D` iff both blocks pass there.  This law is
associative and idempotent at the support level and cannot suffer the
`(-1)*(-1)=+1` cancellation that defeats Jacobi/Artin characters.

`compose_support_packets()` implements this law and returns another
`SpecialFrobeniusDefectPacket`, so the existing one-gcd result lattice remains
canonical:

```text
gcd(D,N) = N        -> ALL_PASS
gcd(D,N) = 1        -> ALL_FAIL
1 < gcd(D,N) < N    -> SPLIT(g)
```

## Factor-backed differential audit

`research/special_binary_germ.py` constructs the desired support generator from
bounded factor truth only to verify the new algebra.  It is never imported by
production.

The prime-decision controls are exact:

| candidate | chunk | binary compositions | support observations | truth |
|---|---:|---:|---:|---|
| F4 | levels 2..3 | 2 | 1 | ALL_PASS |
| F5 | levels 2..10 | 5 | 1 | ALL_FAIL |
| M11 | levels 1..2 | 2 | 1 | ALL_FAIL |
| M13 | levels 1..3 | 3 | 1 | ALL_PASS |

For every control, directly constructing the endpoint support and intersecting
all one-level truth supports give the same result.  In particular F5 and M11
remain failing even though their scalar local characters can cancel.

## What this closes

The following pieces are now executable and single-sourced:

```text
binary dyadic transport                     CLOSED
prime-clock-style support/transport split    CLOSED
zero/unit support intersection by gcd        CLOSED
one-observer terminal plan                   CLOSED
F4/F5/M11/M13 support differential           CLOSED (factor truth only)
```

The new production path is

```text
terminal_threshold_probe
  -> build_special_germ_plan
     -> binary SpecialGermTransfer
     -> one support observation
        -> SpecialFrobeniusDefectPacket
```

and contains zero factor enumeration, zero root-tree nodes, zero one-level
replay, and zero raw Pépin/Lucas--Lehmer squarings.

## Remaining theorem

This checkpoint does **not** close the source projection.  The sole remaining
operation is still

```text
unfactored sparse Fermat/Mersenne candidate
    -> zero/unit endpoint support defect D
       (or an equivalent natural gcd packet)
    -> existing SpecialFrobeniusDefectPacket classifier.
```

The prime-clock analogy tells us what the observer must preserve, but prime
clock gets its lane support from explicitly known wheel divisors.  Fermat and
Mersenne have hidden CRT support.  A candidate-derived factor-free extractor
for `D` has not been proved here, and production therefore remains `UNKNOWN`
on unresolved candidates.

## Validation

- core germ/threshold/layout cone: **45/45 PASS**;
- broader affected certificate/compiler cone: **123/123 PASS**;
- canonical compiler architecture audit: **127/127 PASS**;
- production modules: **104**;
- sequence-compiler-reachable modules: **53**;
- selftest: **PASS**;
- compileall: **PASS**;
- full-suite completed tests: **553 PASS** of **569 collected**;
- `test_special_successor_generators.py`: **19 collected**, first 3 pass and the
  unchanged long-running fourth test exceeds the execution window, matching the
  pre-existing stress-test behavior recorded by earlier releases.

Machine-readable metrics are in `results/special_binary_germ_metrics.json`.
