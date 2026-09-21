# Scheduler optimization and measurement

The shared `TileScheduler` owns admitted source images. Family arithmetic,
source admission, exact occurrences and demanded observations are distinct.
See [shared research](research/shared.md) for the algebra and
[release status](release-status.md) for current construction coverage.

## Publication contract

- Bind every image to its source, action, boundary, extent, radix and precision.
- Normalize arithmetic structure before interning it. Equal observations never
  authorize substitution of successor occurrences.
- Validate authority before using a warm cache. Reject stale, foreign or mutated
  handles; failed publication releases temporary reservations.
- Keep action interning, source discovery, admitted images and observers in
  separately accounted stores. Eviction may remove reuse, not correctness.
- Request output digits, physical clocks and optional classifiers independently.
  A width query must not render digits; streamed output must reuse construction.
- Count reflected coordinates as chart transport. Reverse/add physical carry
  travels only LSD to MSD.

The removed decimal 757/179 machine has no production or oracle exemption.
Generic finite-effect arithmetic and the separate Collatz resources remain.
Proofs for supplied actions do not establish cheap discovery of those actions.

## Measurements

Use metrics schema 7. Report construction, discovery, observation, rendering,
failed work, retained nodes and peak storage separately. A small final root,
large symbolic exponent or warm cache hit does not establish a construction bound.

Canonical commands:

```console
python -m devtools.benchmarks.causal_tile_growth_runner --output /tmp/NEW-growth.json
python -m devtools.checks.action_morphism_adversarial_audit --help
```

The growth runner preserves horizons 16–1024, five cold trials per sample and
35-second/1-GiB worker guards. Missing samples, refused construction and timeouts
remain failures. Its report distinguishes the requested, observed and missing
manifests; it does not certify the complete production release.

Measure warm and cache-bypassed queries separately from fresh installed CLI
processes. Include discovery and construction in cold cost. Use independent
bounded references at seams, growth boundaries and first failure; poison retired
executors and unrequested observers.

## Proof and release boundary

Each optimization needs a source/admission refinement and an applicable cost
argument. Associativity, supplied-word powering and projection identities alone
are insufficient. Keep the positive CLI and powered-construction assertions
active until they pass. Focused builds and cleanup do not replace the aggregate
Isabelle, full-unit, explicit P0 and installed-wheel checks described in
[development](development.md) and the [proof index](proofs.md).
