# Number Compiler

Number Compiler provides exact terms and radix projections for reverse-add,
Collatz, Antihydra, prime blocks, Fermat numbers and Mersenne numbers.

```bash
python -m pip install -e '.[dev]'
number-compiler --list-families
number-compiler 196 --nth 8
number-compiler collatz --nth 8 --seed 27
number-compiler antihydra --nth 64 --info ledger --info clock
number-compiler fermat --nth 3 --no-value --info primality --format json
number-compiler mersenne --nth 131 --no-value --info primality --info factor --format json
```

The supported Python entry points are exported from `number_compiler`.
Implementation modules have one canonical owner; historical forwarding imports
have been removed as described in the [API migration guide](docs/api-migration.md).

Each family owns its command: `FAMILY --nth N` emits the candidate or term, while
`--no-value --info primality` requests the admitted compact primality route.
It reports `unknown` and exits 3 when that route cannot decide. Pépin and
Lucas–Lehmer are available only as research oracles. Add `--info factor` to
request a separately budgeted étale coefficient witness; a proper divisor proves
composite, while a non-split does not prove prime. `--max-candidate-bits` bounds
candidate size before theorem work.
Candidate-derived mod-16 shadow-cylinder prime-bit recovery remains a P0
release blocker.

Digits go to stdout; requested information goes to stderr. `--format json`
combines them as `value` and `info` in one stdout object. Information is evaluated
only when requested. Collatz `--nth` counts ordinary iterations; its separate
`--events E` selector requests accelerated-event observations. Antihydra `--nth`
is the total arithmetic sequence starting at 8, even if its ledger crosses −1;
physical TM observations retain their halting boundary.

The old `nth`, `observe`, `classify`, `verify-nonhalting` and `families` command
forms have been removed. See the [CLI migration guide](docs/family-first-cli.md).

A reused `NumberCompiler` keeps up to eight recent powered execution owners.
Repeated requests and Collatz radix views reuse their existing HashLife caches;
metrics remain cumulative per term. `NumberCompiler(max_cached_terms=0)` disables
this reuse. The capacity bounds retained terms, not total DAG memory, and does
not share caches between standalone CLI processes.

- [Documentation index](docs/index.md)
- [Architecture and package ownership](docs/architecture.md)
- [Development and checks](docs/development.md)
- [Current validation status](docs/release-status.md)
- [Research and proof history](docs/history.md)
- [Repository rules](REPOSITORY_RULES.md)

The HashLife production cutover is unfinished. Structural cleanup does not prove
sublinear execution or satisfy the five-minute runtime release gate. The
[current release status](docs/release-status.md) records the remaining blockers.

For development, `pytest` runs the unit suite; `pytest -m validation` runs
exhaustive proofs, research and release workloads. Use `pytest -m ''` for both.
See the [checking guide](docs/development.md) for resource controls and evidence
requirements. A unit pass does not certify the unfinished runtime release.
