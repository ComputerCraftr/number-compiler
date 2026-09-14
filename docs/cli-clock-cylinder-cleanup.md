# CLI lowering and clock-cylinder checkpoint — September 10

This checkpoint removes avoidable work from explicit CLI output and extends the
bounded clock-cylinder evidence for 196, Collatz, Fermat and Mersenne. Carry
geometry is a projection of the all-port cylinder when that cylinder is already
required. A carry-only consumer can still use the smaller carry-monoid
specialization; constructing an unused five-component emission would add work.

## Production changes

`number-compiler FAMILY --nth` now renders power-of-two output bases 2, 4, 8, 16 and 32
without reconstructing an endpoint integer when the payload permits it.
Collatz streams its native binary image, independently of the requested digit
view radix. Reverse/add regroups source digits when its source radix is a power
of two. Fermat emits its two nonzero bits directly; Mersenne emits a uniform
ones field. Native reverse/add text consumes its digit iterator once.

For 196/reverse-add, a symbolic upper bound admits output without an extra
exact-width traversal when it fits `--max-output-bits`. Tight caps retain the
existing exact-width decision. Collatz already uses a conservative symbolic
cap and continues to do so. Scalar fallback formatting uses Python's native
binary/octal/hex conversion; decimal formatting restores the process digit
limit after conversion. JSON fields, accounting and output caps are preserved.

The decimal primary clock has exact order 128 in
`(Z/32)[y]/(y^5)`, where `z=y-1`. `DecimalCarryJetBlock.clock` now looks up
`z^(width mod 128)` in a fixed immutable table. It no longer repeats binary
powering for every spatial occurrence. Tests check minimal period, agreement
with the independent power operation, a width of `10^100`, and lookup with that
power operation poisoned. This changes clock evaluation cost; it does not
turn the physical CLI result cache into a clock quotient.

The fresh lookup probe checks widths 0–1023: 1,024 former power calls become
zero per-request power calls after table initialization. The measured lookup
portion falls from 68.0 ms to 0.065 ms on this run; this excludes import/table
construction and is not an end-to-end speedup claim. CLI probes for 196 N8,
Collatz N8, F14 and M16384 record zero materialization and explicit width
method calls on the selected native/power-of-two render paths. F14 and M16384
emit 4,097 and 4,096 hexadecimal characters respectively.

## Clock ownership and research results

| Family | Implemented ownership / new bounded result | Remaining execution boundary |
|---|---|---|
| 196 | Two-port occupancy cylinder owns carry exits, reset and forcing views; 19 leaves → 3 classes; clock lookup uses 128 phases | Phase-neutral live value/forcing substitution across arbitrary temporal blocks |
| Collatz | Shared all-port Mealy owner; threshold and output clocks use mod-8/mod-4 phases; normalized Hensel occurrences share suffix/action representations | Publish and rebase accelerated Hensel images into the physical future-tile scheduler |
| Fermat | Terminal-preserving deck splits `+1` from `-1`, merges `0~1`; F4 has 32,769 classes from 65,537 residues | Descend the full demanded germ to a smaller clock while preserving the Pépin terminal observer |
| Mersenne | Sign deck gives 4,096 classes from 8,191 residues at M13; existing circle Hensel lift has a sign-invariant view | Compose live fold/carry/germ consumers and certify the Lucas–Lehmer terminal scheduler |

The decimal audit reproduces 3,936 exact transitions across seeds 176–216,
88,930 source positions and 84,994 internal spatial compositions. Both incoming
ports are checked, and seed 196 separately passes 4,096 carry-owned births.
The evaluated initial jet contribution disappears within eight transitions in
this corpus; the phase-neutral operator can require nine. These are different
claims. The attachment's aggregate 3,854→2,277 empirical live-cylinder count is
not reproduced here: it does not specify an executable orbit normalization for
the neutral live germ. The exact spatial image and accumulated live innovation
remain legitimate occurrence payloads to test; current carry forcing alone is
not their substitute.

Collatz retains the previously validated affine occurrence normalization:
`2^a*3^h*M+b` becomes `2*3^h*M'+b'`, with the offset quotient and removed factor
of two absorbed into the counted suffix. Its bounded probe had 3,160 raw
requests, 1,280 retained occurrences and 1,880 actual interner hits. This is
carrier reuse, not a claimed gain in the physical CLI point-result cache.
The [shared owner report](port-valued-mealy-actions.md) records the full
odd-16-bit differential gate and the exact distinction between spatial and
temporal closure.

## Deck-first Fermat and Mersenne audit

| Candidate | Complete ring | Terminal deck classes |
|---|---:|---:|
| F2 | 17 | 9 |
| F3 | 257 | 129 |
| F4 | 65,537 | 32,769 |
| M5 | 31 | 16 |
| M7 | 127 | 64 |
| M11 | 2,047 | 1,024 |
| M13 | 8,191 | 4,096 |

Every row has `(N+1)/2` classes, zero current-terminal conflicts and zero class
transition conflicts at powers 1, 2, 4, 8, 16 and 32 of its family recurrence
(`x^2` or `x^2-2`). These are complete bounded rings, not trajectory samples.
The partition is not asserted minimal: composite M11 already has only 540
one-step images. Class counts alone do not establish the stronger proposed
full clock/germ quotient.

Fermat's merged zero/one pair also agrees under the existing arithmetic tile's
carry and order-4/mod-2 harmonic consumer on its observed incoming interval
`[0,0]`. That small check is not a full-ring carry-port or multi-prime
Newton/Hasse-germ proof. The proposed full five-dimensional germ, its tangent
and tropical observers are not constructed by this audit, so their descent
and claimed trajectory alias counts are not reported as freshly verified.

`cyclotomic_binary_lift_marker(..., sign_invariant=True)` is the existing circle
Hensel lift view relevant to Mersenne. Its sign identification cannot be copied
unchanged across Fermat's current `-1` terminal observer. Related Hensel algebra
can be shared while each consumer keeps its actual terminal contract. See the
[power-family audit](research/power-numbers/square-consumer-congruence.md).

## Where growth still comes from

For 196 and physical Collatz, fresh N8/16/32 indexed queries test the existing
future-tile result arena. At N32 it still retains 2,305 and 1,024 entries,
respectively. Boundary/input occurrence contexts dominate; normalized clock
or phase labels are not duplicate fields waiting to be removed from those
keys. Earlier key-ablation controls produce conflicting outputs when those
required operands are omitted. Repeated identical point queries do reuse the
completed result. Cheap clock evaluation and cheap text rendering do not
remove first-use context discovery.

Fermat/Mersenne `nth` constructs the candidate number; it does not run a
primality trajectory. Their actual recurrence tile already uses unordered
square products (36 instead of 64 at width eight), but still constructs a
width-sized folded coefficient field and performs successive nonlinear
squares. The earlier width probe's largest folded coefficient rises from 3
at width eight to 86 at width 256. The bounded half-deck quotient remains
proportional to the residue ring. Reduction to the small terminal order-depth
observer while retaining the demanded forcing action is still unproved.

Full numeral emission necessarily visits the emitted characters. Other radix
conversions retain scalar fallback. JSON output retains its existing complete
ledger schema and therefore still pays diagnostics serialization cost.

## Validation and proof scope

The [frozen evidence](../results/current/cli-clock-deck-2026-09-10/README.md)
contains guarded tests, strict typing, the clock/CLI measurement and a fresh
public cache probe. Poison tests prohibit avoidable materialization and width
queries on the new paths. All commands use the existing 35-second/1-GiB limit.

The previously checked Isabelle `Port_Valued_Mealy.thy` is unchanged and its
hash is rechecked. It proves arbitrary spatial Mealy composition and the
carry-projection homomorphism. This checkpoint adds executable bounded
research checks, not a new Isabelle proof of nonlinear temporal closure,
full-germ descent or a prime-bit scheduler certificate.

The subsequent [temporal theorem checkpoint](temporal-clock-jump-proofs.md)
formalizes the exact jump and rebase interfaces, including the known-order
clock condition, while retaining the unresolved full-germ evaluator boundary.
