# Documentation

The release table owns current gate status; sprint topics own dated evidence;
research papers own mathematical definitions and proof scope. Historical reports
apply to their recorded checkout, not later source.

## Usage

- [CLI reference](cli.md)
- [Metrics reference](metrics.md)

## Architecture

- [Package ownership and execution](architecture.md)
- [HashLife optimization and construction boundaries](hashlife-optimization.md)

## Research syntheses

Each paper distinguishes definitions, assumptions, checked results, implemented
construction, finite experiments and open obligations. Patch histories,
profiling details and Git-attributed validation belong in the weekly
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

## Sprint history and provenance

Weeks run **Sunday–Saturday**, named by their Sunday start date. Each weekly
index links to categorized implementation and validation records.

- [October 18–24 — current week](sprints/week-of-2026-10-18/README.md)
- [October 11–17](sprints/week-of-2026-10-11/README.md)
- [October 4–10](sprints/week-of-2026-10-04/README.md)
- [September 27–October 3](sprints/week-of-2026-09-27/README.md)
- [September 20–26](sprints/week-of-2026-09-20/README.md)
- [September 13–19](sprints/week-of-2026-09-13/README.md)
- [September 6–12](sprints/week-of-2026-09-06/README.md)

Earlier aggregate summaries cross Sunday boundaries; they retain their original
coverage as retrospectives, not weekly records:

- [September 7–13 retrospective](sprints/history/2026-09-07--2026-09-13/README.md)
- [September 14–20 retrospective](sprints/history/2026-09-14--2026-09-20/README.md)
- [Historical hygiene evidence and 206-failure baseline](sprints/history/hygiene-disposition-2026-09-20.md)
- [Historical API and CLI migrations](sprints/history/api-cli-migrations.md)
- [Historical research and preserved external reports](history.md)
- [Document migration and provenance](provenance.md)

The [`archive/`](archive/) retains selected derivations and historical evidence.
The decimal pair paper and carry-slab jump report identified in the history
index are preserved verbatim as external sources. Old proposals do not
authorize restoring retired execution.
The machine-readable current-document catalog is [`catalog.toml`](catalog.toml).
