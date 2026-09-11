# Canonical reuse and ownership cleanup — September 9, 2026

> Historical run summary. Generated payloads and transcripts are no longer
> versioned; artifact paths below describe local outputs. See the
> [retention policy](../../README.md).

This is an implementation checkpoint, not a completed HashLife performance
release. Deep decimal reverse remains superlinear in the measured range.

## Accepted changes

- Point demand probes canonical completed spatial parents before descending.
  A regression warms only an interior result and poisons leaf construction.
  The superseded direct-source-leaf point helpers were deleted.
- Exact reverse output summaries are memoized by canonical tile identity in
  the existing completed-result owner. Warm observations do not rebuild the
  summary. Publication, eviction, retirement, and independent nine-scalar
  inventory checks share that owner's accounting.
- Boundary and result pinning authenticate live application identities through
  an index-owned registry rather than scanning every execution root.
- Warm causal pins test their bounded dependency keys individually. They no
  longer copy the complete dependency store into a set on every hit.
- Application cleanup owns explicit source/root lease references. Abandonment
  releases pins and dependencies during normal garbage collection. Retry
  tests cover failed registry and pin removal. Interpreter shutdown is treated
  separately from normal garbage collection.
- Primitive decimal Frobenius observations consume the authenticated source
  carry-sector summary before requesting a future interface.
- The unused Collatz higher-interface and concrete-port executors were
  physically deleted. Their retained differential, authority, zero-field,
  and resource-limit witnesses now exercise the tile stack.

## Measurements and limitations

`diagnostic-measurements.json` preserves single-process engineering probes of
decimal 196 point zero with response/microblock acceleration bypassed. These
are not five-trial, frozen release measurements. The previous variant changes
only the point traversal methods; it does not restore the entire old tree.

| Point traversal | N | Seconds | Causal frames | Peak canonical tiles |
|---|---:|---:|---:|---:|
| Previous | 32 | 4.468 | 54,475 | 956 |
| Parent first | 32 | 4.597 | 54,648 | 956 |
| Previous | 64 | 16.454 | 187,479 | 3,841 |
| Parent first | 64 | 16.263 | 187,684 | 3,841 |

Parent-first traversal enables a demonstrated interior-parent hit but does
not fix cold scaling: frames grow approximately 3.43 times and peak tiles
approximately 4.02 times from N=32 to N=64.

A prototype retaining parent-backed prefix views passed 80 focused tests but
increased N=32 frames to 67,350, with the same 956 peak tiles. It was rejected
and removed. Its logs remain in `diagnostics`; fewer local concatenation
requests did not compensate for additional total work.

The first frozen unit attempt (`unit.log`, `unit.guard.json`) reached the final
tests without reported assertion failures but was interrupted at 300 seconds.
It is incomplete evidence, not a passing suite. Its source fingerprint was
`710c893634fef79d3a4c915cf104e701fa6b58a886eb08758cba580851b3367c`.
A one-second native sampling diagnostic was taken during that attempt; any
subsequent release timing must be unprofiled. Additional ownership fixes were
made after this attempt.

## Still-open execution blockers

The production tile recurrence executes the local growth and forcing laws;
these values are not missing external inputs. However, the current bound
reverse-output shortcut admits primitive consumers, not arbitrary composed
consumer transfers. Such misses still require exact causal output construction.
The new summary memo does not certify those larger transitions.

Retained sector residues alone cannot justify merging these requests. The
regression comparing sixteen 4s with sixteen 5s has equal retained carry-sector
summaries but different successor fields, sixteen 8s versus sixteen 10s, whose
next carry domains differ. Exact source/tile dependencies preserve correctness.
This is a semantic distinction, not an integer-ID hash collision.

Complete active-consumer discharge, N=16…1024 work/retention envelopes, and
the runtime release remain open. No universal sublinear claim is made.
