> **v0.53.8 note:** the historical fixed-height carry-slab backend described below has been removed. Current 196 spatial carry/digit projection uses the exact finite threshold-defect state and shared logarithmic prefix monoid in `reverse_domain.py` / `prefix_monoid.py`. Historical measurements are retained only as research evidence.

> **v0.10 update:** the exact carry/event theorem restores a fixed-height decimal H=20 binary carry slab; this file remains valid for the legacy exact T⁸+ executor, but that syntax tower is no longer the preferred nonlinear theorem coordinate. See `CARRY_EVENT_FORMULA_RESULTS.md`.

> **v0.9 update:** the v0.8 per-effect `_sparse_roots` shadow indexes are deleted.
> One global `BlockContextBudget.program_word_roots` registry is authoritative. The exact v0.8
> T^1024 baseline had 116,144 layer-local entries for 86,004 unique words (30,140 duplicate
> index entries). See `BEHAVIORAL_DEDUP_RESULTS.md` for the completed T^4 behavioral audit.

# Shared-DAG powered continuation results — v0.8.0

## Architectural change

The production powered evaluator no longer has a T^8+ residual/provenance object at all.
The former `_SparseBoundaryProgram` class has been deleted. Above the complete T^2 finite
kernel and complete T^4 bitset-partition semantic layer, one higher continuation state is
represented only by a globally hash-consed `CanonicalWord`:

```text
EMPTY | RUN(symbol,count) | CONCAT(left,right)
```

The word algebra canonicalizes concatenation associativity, fuses adjacent equal-symbol runs,
shares reverse/slice sub-DAGs, and applies the proved blank-run saturation cap. Demanded
semantic cells are memoized as `(effect, side, canonical_word, argument) -> state`; there is no
parallel anchor/history/residual object.

`apply_block_power()` also no longer allocates `left_before[position]` or
`right_after[position]` vectors. The source is kept as counted runs, and a balanced
shared-DAG traversal derives child prefix/suffix contexts. Only final output positions are
visited.

## Research machinery used

The implementation follows four relevant results conservatively rather than treating them as a
reverse-add theorem:

- Christian Bianchini and Gabriele Puppis, *Minimization of Streaming Transducers*, LICS 2026,
  DOI 10.4230/LIPIcs.LICS.2026.18 — motivates canonical internal memory/term state rather than
  construction-history identity.
- Mikołaj Bojańczyk and Markus Lohrey, *Transducers on Compressed Strings*, ICALP 2026,
  DOI 10.4230/LIPIcs.ICALP.2026.170 — supports applying regular transformations directly to
  grammar-compressed strings instead of expand-then-transduce.
- Rajeev Alur, Taylor Dohmen and Ashutosh Trivedi, *Composing Copyless Streaming String
  Transducers*, arXiv:2209.05448 — motivates the diamond-free/copyless discipline: shared
  update-DAG descendants must not be independently replayed.
- Yahia Idriss Benalioua, Nathan Lhote and Pierre-Alain Reynier, *Minimizing Cost Register
  Automata over a Field*, MFCS 2024, DOI 10.4230/LIPIcs.MFCS.2024.23 — motivates algebraic
  minimization of numeric/register side channels rather than duplicating them into control state.

These papers justify representation boundaries; they do not prove an infinite 196 recurrence.
All reverse-add equalities in production are established by this repository's exact finite
kernel/partition/word algebra and differential tests.

## Decimal 196 at T^1024

```text
binary temporal operator nodes                 10
final pair width                              421
T^2 minimized semantic kernel             757 / 179
T^4 canonical semantic states        43,764 / 5,886
unique canonical T^8+ program roots          86,004
total retained execution nodes              135,654
positional prefix/suffix context vectors           0
provenance-path states                             0
memo entries dropped                               0
intermediate pair words                            0
elementary reverse-add generations                 0
```

The v0.7 release retained 173,658 T^4/T^8+ boundary objects. v0.8 retains 135,654 semantic/
compressed execution nodes, a 21.9% reduction, while eliminating the duplicated provenance
state space entirely. Relative to the v0.4 structural residual count of 474,553, retained
execution nodes are down 71.4%.

The T^8 sublayer itself has 28,697 left and 27,620 right canonical program roots on this
projection. Those are exact canonical *program descriptions*, not yet proved minimal
Myhill--Nerode classes of the induced continuation functions.

## Remaining blocker

The duplicated representation is gone, but the number of distinct canonical program actions is
still growing faster than a bit-length-polynomial release budget. The remaining full-J research
problem is therefore narrower:

```text
canonical compressed program action
 -> output-push / structured residual normalization
 -> exact Myhill--Nerode or proved streaming-transducer closure
 -> compact FormulaRoot jump
```

A partial-demand cache collision, finite suffix sample, or opaque `Power(T,N)` token is not a
proof of whole-function equality. Full `J_0/J_1` remains fail-closed until this last behavioral
quotient is certified.
