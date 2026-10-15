# Number Compiler

Number Compiler provides exact terms and radix projections for reverse-add, decimal double-reversal (`2rev10`),
Collatz, Antihydra, prime blocks, Fermat numbers, Mersenne numbers and the admitted A367620 comma prefix.

```bash
python -m pip install -e '.[dev]'
number-compiler --list-families
number-compiler reverse-add --seed 196 --nth 8
number-compiler collatz --nth 8 --seed 27
number-compiler collatz --nth-power10 6 --seed 27
number-compiler antihydra --nth 64 --info safety.ledger --info temporal.clock
number-compiler a367620 --nth 1
number-compiler fermat --nth 3 --no-value --info number-theory.primality --format json
number-compiler mersenne --nth 131 --no-value --info number-theory.primality --info number-theory.factor --format json
```

Execution uses immutable family-specific queries; presentation stays in the CLI:

```python
from number_compiler import CollatzTermQuery, NumberCompiler, ReverseAddTermQuery

compiler = NumberCompiler()
assert compiler.nth(CollatzTermQuery(8, seed=27)) == 71
term = compiler.project(ReverseAddTermQuery(2, seed=196))
assert term.materialize() == 1675
assert compiler.project_digit(ReverseAddTermQuery(2, seed=196), 0) == 5
```

The public Python entry points are exported from `number_compiler`. See the
[CLI reference](docs/cli.md) and [metrics reference](docs/metrics.md) for current usage and accounting.

Each family owns its command: `FAMILY --nth N` emits the candidate or term, while
`--no-value --info number-theory.primality` requests the admitted compact primality route.
It reports `unknown` and exits 3 when that route cannot decide. Pépin and
Lucas–Lehmer are available only as research oracles. Add `--info number-theory.factor` to
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


A reused `NumberCompiler` keeps up to eight recent powered execution owners.
Repeated requests and Collatz radix views reuse their existing HashLife caches;
metrics remain cumulative per term. CLI `--info metrics` reports read-only schema 8 execution counters; unavailable counters are null. `NumberCompiler(max_cached_terms=0)` disables
this reuse. The capacity bounds retained terms, not total DAG memory, and does
not share caches between standalone CLI processes.

- [Documentation index](docs/index.md)
- [Architecture and package ownership](docs/architecture.md)
- [Development and checks](docs/development.md)
- [Current validation status](docs/release-status.md)
- [Research and proof history](docs/history.md)
- [Executable source policy](devtools/checks/repository_policy.py) and [policy tests](tests/repository/test_repository_policy.py)

The HashLife production cutover is unfinished. Structural cleanup does not prove
sublinear execution or satisfy the five-minute runtime release gate. The
[current release status](docs/release-status.md) records the remaining blockers.

For development, `python -m devtools.checks.release --suite unit` runs the unit
suite; `--suite all` includes exhaustive and release workloads. Repeated
`--select PATH_OR_NODEID` arguments select focused tests. Direct pytest is rejected.
See the [checking guide](docs/development.md) for resource controls and evidence
requirements. A unit pass does not certify the unfinished runtime release.
