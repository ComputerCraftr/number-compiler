# Shared Fermat/Mersenne terminal-threshold integration — research checkpoint

## Release reduction

The full splitting histogram is no longer a prerequisite for the **prime/composite**
release path.  Both special-number families reduce to one all-local terminal
threshold, followed by the existing zero-enumeration pure filtration theorem.

| family | local excess depth | terminal level | all-local PASS consequence |
|---|---|---:|---|
| Fermat `F_n` | `v2(q-1)-(n+1)` | `2^n-n-1` | every `q|F_n` is `F_n` |
| Mersenne `M_p` | `max(0,v2(q-(12/q))-2)` | `p-2` | every `q|M_p` is `M_p` |

For Fermat, terminal PASS gives `2^(2^n) | q-1`, so the least possible passing
prime is `1+2^(2^n)=F_n`.

For an odd Mersenne exponent, terminal PASS gives
`2^p | q-(12/q)`.  The `+1` character branch forces `q>=2^p+1>M_p` and is
impossible; the `-1` branch forces `q>=2^p-1=M_p`.

Thus in both families:

```text
terminal ALL_PASS
    -> prime
    -> pure_two_primary_image_filtration()
       with zero carrier enumeration
```

The complete `c_k` / image-rank histogram remains necessary only if the release
also promises the exact stable residual of arbitrary **composite** candidates.
It is not needed for primality or for prime binary reconstruction after PASS.

## Sparse candidate quotients

The candidate rings now have symmetric sparse principal presentations:

```text
F_n:  Z[zeta_(2^(n+1))] / (1-2*zeta)  ~= Z/F_n Z
M_p:  Z[zeta_p]         / (2-zeta)    ~= Z/M_p Z   (prime exponent p)
```

Their principal norms are exactly the candidates:

```text
Norm(1-2*zeta_(2^(n+1))) = Phi_(2^(n+1))(2) = F_n
Norm(2-zeta_p)            = Phi_p(2)          = M_p
```

For Mersenne, base change to `R[s]/(s^2-3)` carries the Lucas--Lehmer torus
source `y0=2+s`, with trace four and norm one.  The desired terminal order is
`2^p`.  Global candidate powering is still blind: `M_p == -1 mod 2^p`, so it
acts by the already-known inversion rather than local split/nonsplit Frobenius.

## Production integration

`special_terminal_threshold.py` now owns the one canonical release choke point:

```text
ALL_PASS | ALL_FAIL | SPLIT(g,N/g) | UNKNOWN
```

`special_certificate.py` queries it as the sole number-level production certificate.
A terminal PASS promotes directly to the closed pure filtration. A terminal
FAIL/SPLIT is a scalable composite result. `UNKNOWN` is terminal and never
falls through to the bounded carrier or recurrence/reference classifiers.

Current scalable terminal coverage remains intentionally small:

```text
F2 -> ALL_PASS (terminal level 1, explicit sqrt(2))
F3/F4/F5 -> UNKNOWN at their terminal levels 4/11/26
M5/M11/M13 -> UNKNOWN at their terminal levels 3/9/11
```

Composite Mersenne exponents are rejected before the number-level selector by
the symbolic exponent-factor theorem.

## Remaining P0 theorem

The one shared hard blocker is now:

```text
sparse candidate principal support
    -> locality-preserving terminal Kummer/Artin decision
       or a natural nontrivial gcd packet
    -> ALL_PASS / ALL_FAIL / SPLIT
```

It must not be implemented by recurrence-equivalent Pépin/Lucas--Lehmer replay,
ambient carrier enumeration, factor/CRT reconstruction, a supplied prime label,
or hidden discrete-log work.

The bounded carrier remains available only through explicit oracle/research imports
for differential validation. It is unreachable from production. Exact composite
stable-residual recovery is a separate, stronger optional theorem.

## Validation

The frozen v0.51 cutover validates the stricter oracle boundary:

```text
modified/oracle dependency cone          124/124 PASS
isolated pytest modules                  63/64 PASS
completed-module tests                   480/480 PASS
historical successor-generator module   baseline timeout
compiler architecture audit              125/125 PASS
sequence compiler reachable modules      50
slow special production reachability     0
slow special root exports                0
selftest                                 PASS
compileall                               PASS
```

The non-completing successor-generator research module hits the same watchdog on the untouched pre-cutover checkpoint and is not counted as a v0.51 pass.


## r-level Frobenius chunk integration

The production threshold now builds one `SpecialFrobeniusChunkSpec` spanning
all terminal levels and queries `special_frobenius_chunk_probe()`.  The local
block theorem is exact: for `q=eps+m*k`, an r-level chunk retains only
`rho=k mod 2^r`, and the folded coefficient of `X` in the corresponding
negacyclic Frobenius action is `+1` exactly when `rho=0`.  Thus the whole
terminal conjunction is one zero-class query rather than a per-level itinerary.

The unfactored candidate-derived coefficient extractor is not yet proved, so
F4/F5/M11/M13 remain `UNKNOWN` in production with method
`frobenius-chunk-zero-class-extractor-unavailable` and zero carrier/replay work.
Factor-backed local/composition proofs are isolated under `research/` and are
unreachable from production.  See `TERMINAL_FROBENIUS_CHUNK_RESULTS.md`.
