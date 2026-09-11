# Collatz directional domain views

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

The radix-64 Collatz output morphism now exposes the exact value split

\[
q_e(n)=n\mathbin{\gg}e,\qquad r_e(n)=n\bmod 2^e
\]

and reconstructs an adjacent target digit as

\[
q_e(n_i)+2^{6-e}r_e(n_{i+1}).
\]

The raw symbolic and streaming paths first derive the outgoing carry from the
five-way domain action, then form `(3*d+c) mod 64`. The earlier 17-way joint observer
remains available as a negative-control observation but is no longer decoded
by those paths.  A streaming stage retains only `q_e(n_i)` across its one-cell
lookahead and consumes `r_e(n_{i+1})` immediately. The six directional theorem
tables are compiled from 64 `q/r` combinations per phase, rather than
enumerating 4,096 raw-digit pairs.

For a domain-only consumer, each stream is reduced independently before the
adjacent pairing.  The exact left/right class counts for residual phases
`e=0..5` are `(5,1)`, `(5,2)`, `(5,4)`, `(5,5)`, `(4,5)`, and `(2,5)`.
Their products give `5,10,20,25,20,10` local value-view classes.  With any
fixed derived multiplication carry, respectively `3,6,12,21,12,6` of those
fibers merge source digits from different current carry domains.

The one-sided theorem tables are now instances of one width-indexed ternary
carry consumer

\[
\mathcal C_{2^w}(x)(c)=\left\lfloor\frac{3x+c}{2^w}\right\rfloor.
\]

The left view at phase `e` uses width `6-e`; the right view uses width `e`, so
`L_e` and `R_{6-e}` are the same canonical class map with opposite spatial
orientation. Their composition `R o L` is the next five-way carry domain and
does not reconstruct the joined radix-64 digit. The left maps have `64 >> e`
entries and the right maps have `2**e` entries. Both are monotone threshold
staircases and are no longer expanded into duplicate 64-entry raw-digit maps.
The palindromic
`5,10,20,25,20,10` profile is therefore one six-phase law; it is not retained
again for each incoming carry or temporal occurrence.

The Hensel angular germ also dropped a derived field.  For radix-four first
mismatches,

\[
\operatorname{phase}=v\bmod2,
\qquad
\operatorname{multiplier}=4\,3^h/2^{\operatorname{phase}}.
\]

At the six two-step Collatz boundaries (`h=2`) this is exactly `36` or `18`.
The multiplier is now a property of `(h, valuation parity)` and is absent from
the dataclass and canonical key.  The complete emitted valuation remains in
the boundary-germ key.  The production `CollatzHenselAction` identity stores
the equivalent exponent `a=2-(valuation mod 2)` together with `h` and the
offset, so even matched-prefix weight is absent from the interned action while
remaining available on the emitted event.  This separates extensional angular
action equality from equality of valuation events without using trajectory
samples.

For those six `h=2` boundaries only, the angular unit `c mod 9` lies in
`{1,2,4,5,7,8}` and one matching radix-four digit advances it by
`c -> 7*c mod 9`. This is a derived angular clock. It does not replace the
Hensel cylinder that detects a match, and it is not applied to arbitrary
denominator powers.

The seven conflicted `domain_hensel_f2harm` workbook fibers are now fixed
regressions at the consumer boundary. Their source pairs differ by 320 and
their unresolved higher radix-64 digits differ by five: `30/35`, `50/55`,
`7/12` at shifts two, three, and four, `8/13`, and `28/33`. In every case the
three incoming-carry evaluations of the directional `(L,R)` action differ.
The regression consumes only that position-bound future action; source,
target, valuation-prefix, and finite `I3` columns remain provenance and are
not added to semantic identity.

The mismatch certificate likewise retains only `(h, matched quarters, source
digit, constant at mismatch)`.  Its root digit, local valuation bit, and
advanced constant are exact functions of those four coordinates and are now
properties rather than stored constructor fields.  This prevents inconsistent
raw/derived certificates and removes the same duplication from cached mismatch
provenance.

The symbolic poison regression compiles the next-domain consumer while the
old exact shift/domain path and the pointwise Phi-5 harmonic observer are
disabled.  The consumer still agrees with the exact scalar law over every one
of the `6 * 64 * 64` adjacent digit/phase cases.  Exact digit output remains a
separate directional value stream and is not part of the domain action ID.

Validation evidence:

The final integrated source is covered by the
[aggregate source-fingerprinted run](../growth-coboundary-directional-2026-09-10/README.md):
160 focused ordinary tests and 9 explicit Collatz validation tests pass there.
The records below also retain intermediate development checks.

- `ordinary-final.log`: 17 passed.
- `ordinary-final.guard.json`: completed in 3.46 seconds, peak 78,119,440 bytes.
- `validation-final2.log`: 9 passed, including every odd 16-bit source and
  eight successors of the seven Hensel controls.
- `validation-final2.guard.json`: completed in 2.47 seconds, peak 72,925,736 bytes.
- `mypy-final.log`: strict mypy passed for all five changed Collatz source/test
  files.
- `mypy-final.guard.json`: completed in 0.63 seconds, peak 87,343,608 bytes.
- `../growth-coboundary-directional-2026-09-10/focused-stabilize2.log`:
  44 focused reverse/add and Collatz tests passed after streaming integration.
- `../growth-coboundary-directional-2026-09-10/mypy-second.log`: strict mypy
  passed for all 1,160 source files after integration.

This establishes the primitive spatial factorization and an interface for
pairing already-composed directional streams.  It does not establish bounded
growth under arbitrary temporal squaring, so the new views are not promoted as
a complete temporal successor identity.
