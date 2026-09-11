# v0.53.0 — constrained special-source theorem pullback

v0.53.0 removes the last production dependency on the historical exponential tropical/factor-slot construction.  The unresolved Fermat/Mersenne theorem coordinate is now a **result accumulated during output construction**, not a support object that must be exhaustively discovered before the powered computation can run.

## Production state

Each special source owns at most one constant-rank constraint state:

```text
SpecialGermConstraintState
    mask          # two bits: PASS / FAIL survivors
    support_gcd   # optional single candidate-ring support ideal
    modulus       # only when a support defect was actually produced
```

There is no vector of local factors, no support-slot bitmap, and no per-checkpoint state list.  Repeated constraints compose by Boolean intersection and one `gcd` of support ideals.  Proven downstream constraints are therefore pulled back to the original source sheet and persist for all later projections.

`CanonicalSequenceCompiler.project_special_digit/parity/length/carry/boundary_sign()` all refine this persistent state.  `pullback_special_defect()` is the candidate-ring path for a powered theorem-sensitive block: it validates that the supplied modulus is the requested Fermat/Mersenne source, computes one `gcd(N, defect)`, and intersects that support with the existing state.

A proper support immediately proves the candidate composite.  The F5 control demonstrates this without Pépin:

```text
N = F5 = 4294967297
pulled-back defect support = gcd(N, 641) = 641
surviving theorem sheet = FAIL
later guarded output (3 | 7) = 7
Pépin squarings = 0
theorem-cache entries = 0
```

The same persistence works for source-shape masks.  On F4, the exact top digit, odd parity, canonical length, independent carry checkpoint, and negacyclic boundary all select the PASS sheet.  A later separating output is resolved from that cached sheet without asking the theorem again.

## Constrained dyadic germ

`SpecialGermPlan` no longer performs one detached support observation after its dyadic transport.  A block carries:

```text
(transport, constraints)
```

and adjacent blocks compose both objects.  For two adjacent blocks A then B:

```text
T_AB = T_B o T_A
K_AB = K_A AND pullback(T_A, K_B)
D_AB = gcd(D_A, pullback(T_A, D_B))
```

For the current PASS/FAIL source coordinate the sheet itself is invariant under deterministic dyadic transport, so the Boolean pullback is exact mask intersection.  Candidate CRT components are likewise preserved componentwise, so the support ideal is represented by one GCD.  The representation is constant-rank even after thousands of constraints; method provenance is collapsed to a constant-size tag rather than storing a history.

`SpecialGermPlan.support_observations == 0`.  Production does not call `special_frobenius_chunk_probe()` from the germ and never asks `research.tropical_ghost_flux` to manufacture a first support packet.

## Hard classical ceiling

If every cheap/pulled-back constraint still leaves both theorem sheets alive and the caller actually demands a concrete theorem-sensitive coordinate, production falls back to the exact classical special-form recurrence.  It does **not** fall back to factor-slot enumeration.

For Fermat:

```text
Pépin target: 3^(2^(2^n - 1)) == -1 mod F_n
nonlinear modular squarings = 2^n - 1 = bit_length(F_n) - 2
```

For Mersenne with prime exponent candidate p:

```text
s_0 = 4
s_(j+1) = s_j^2 - 2 mod M_p
nonlinear modular squarings = p - 2 = bit_length(M_p) - 2
```

The default fallback does no final GCD, no factor prepass, no carrier enumeration, and no factor-slot enumeration.  A final support GCD is an explicit optional diagnostic only.  Therefore the production theorem arithmetic is bounded by the ordinary Pépin/Lucas–Lehmer recurrence, plus logarithmic symbolic germ bookkeeping that performs no modular recurrence squarings.

Measured controls:

| candidate | exact result | classical fallback squarings |
|---|---:|---:|
| F4 | prime | 15 |
| F5 | composite | 31 |
| M11 | composite | 9 |
| M13 | prime | 11 |
| M31 | prime | 29 |
| M15 | composite exponent | 0 LL steps |

Small-factor projection remains available only by explicit `use_factor_projection=True`.  With the default `False`, `factor_limit` is normalized out of theorem-cache identity so an unused policy knob cannot duplicate the same theorem work.

## What this does and does not prove

The exponential tropical kernel is no longer a production algorithm or fallback.  It remains research-only as a recorded negative result.

This release also does **not** claim that source shape alone proves primality.  A prime and composite instance of the same Fermat/Mersenne integer have the same raw digits, length, and ordinary representation carries.  Cheap source constraints resolve the theorem sheet only when a **proved theorem-dependent branch reconstruction** disagrees with those independently known facts.  Candidate-ring defects likewise must come from a proved theorem-sensitive powered block.

The next performance question is narrower and honest: whether the nonlinear Pépin/LL transition itself admits a constant/polylogarithmic successor-closed quotient under binary powering.  Until that closure is proved, v0.53.0 has a classical linear-step worst case rather than hiding the work in an exponential support scan.

Reproduce the release metrics with:

```text
PYTHONPATH=src python bench/special_constraint_pullback_probe.py
```

The generated metrics are stored in `results/special_constraint_pullback_metrics.json`.
