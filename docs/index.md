# Documentation

Current claims live in the maintained documents below. Historical reports apply
to their recorded checkout, not later source.

## Usage

- [Family-first CLI](family-first-cli.md)
- [API and metrics migration](api-migration.md)

## Architecture

- [Package ownership and execution](architecture.md)
- [HashLife optimization and construction boundaries](hashlife-optimization.md)

## Research syntheses

Each paper distinguishes definitions, assumptions, checked results, implemented
construction, finite experiments and open obligations. Patch histories,
profiling details and source-fingerprinted validation belong in the weekly
records below; see the [placement guide](development.md#documentation-placement).

- [Shared actions, cylinders, and resource ownership](research/shared.md)
- [Prime ranks, wheel actions, and Goldbach obligations](research/primes-goldbach.md)
- [Reverse/add source-bound temporal construction](research/reverse-add.md)
- [Collatz physical time, events, and Hensel cylinders](research/collatz.md)
- [Antihydra arithmetic, literal machine, and Mahler action](research/antihydra-mahler.md)
- [Fermat and Mersenne square actions and terminal certificates](research/fermat-mersenne.md)
- [Decimal comma cylinders and A367620 prefix certificates](research/comma.md)

## Proofs and development

- [Formal proof index, assumptions and build commands](proofs.md)
- [Balanced dyadic constructor: production refinement map](proofs/balanced-dyadic-refinement.md)
- [Development, validation and resource limits](development.md)

## Current status

- [Release gate table](release-status.md)
- [Hygiene evidence and test-by-test baseline disposition](hygiene-disposition.md)

## Sprint history and provenance

Weeks run **Sunday–Saturday**, named by their Sunday start date. Each weekly
index links to categorized implementation and validation records.

- [September 27–October 3 — current week](../results/current/week-of-2026-09-27/README.md)
- [September 20–26](../results/current/week-of-2026-09-20/README.md)
- [September 13–19](../results/current/week-of-2026-09-13/README.md)
- [September 6–12](../results/current/week-of-2026-09-06/README.md)

Earlier aggregate summaries cross Sunday boundaries; they retain their original
coverage as retrospectives, not weekly records:

- [September 7–13 retrospective](../results/history/2026-09-07--2026-09-13/README.md)
- [September 14–20 retrospective](../results/history/2026-09-14--2026-09-20/README.md)
- [Historical research and preserved external reports](history.md)
- [Document migration and provenance](provenance.md)

The [`archive/`](archive/) retains selected derivations and historical evidence.
The decimal pair paper and carry-slab jump report identified in the history
index are preserved verbatim as external sources. Old proposals do not
authorize restoring retired execution.
The machine-readable current-document catalog is [`catalog.toml`](catalog.toml).
