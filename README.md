# Number Compiler

Number Compiler provides exact terms and radix projections for reverse-add,
the decimal reversal products `2rev10` and `5rev10`, Collatz, Antihydra, prime
blocks, Fermat numbers, and Mersenne numbers. It also provides an interface
for the A367620 comma sequence.

Comma production output awaits the checked global proof artifact. See the
[current release gates](docs/release-status.md).

```bash
python -m pip install -e '.[dev]'
number-compiler --list-families
number-compiler reverse-add --seed 196 --nth 8
number-compiler collatz --nth 8 --seed 27
number-compiler collatz --nth-power10 6 --seed 27
number-compiler antihydra --nth 64 --info safety.ledger --info temporal.clock
number-compiler fermat --nth 3 --no-value --info number-theory.primality --format json
number-compiler mersenne --nth 131 --no-value --info number-theory.primality --info number-theory.factor --format json
```

The Python API uses immutable family-specific queries. The CLI handles
presentation.

```python
from number_compiler import CollatzTermQuery, NumberCompiler, ReverseAddTermQuery

compiler = NumberCompiler()
assert compiler.nth(CollatzTermQuery(8, seed=27)) == 142
term = compiler.project(ReverseAddTermQuery(2, seed=196))
assert term.materialize() == 1675
assert compiler.project_digit(ReverseAddTermQuery(2, seed=196), 0) == 5
```

The public Python entry points are exported from `number_compiler`. See the
[CLI reference](docs/cli.md) and [metrics reference](docs/metrics.md) for current usage and accounting.

`FAMILY --nth N` requests the indexed term or candidate. For Fermat and
Mersenne numbers, `--no-value --info number-theory.primality` requests the
compact primality check. An inconclusive result reports `unknown` and exits
with status 3. Pépin and Lucas–Lehmer are research oracles. Add
`--info number-theory.factor` to request a separately budgeted étale
coefficient witness. A proper divisor certifies compositeness. An unsplit
witness leaves primality unresolved. `--max-candidate-bits` bounds the candidate
size before theorem work.

Digits go to stdout. Requested information goes to stderr. `--format json`
combines them as `value` and `info` in one stdout object. Information is evaluated
only when requested. Collatz `--nth` counts ordinary iterations, and
`--events E` requests accelerated-event observations. Antihydra `--nth`
indexes the total arithmetic sequence starting at 8, which continues even if
its ledger crosses −1. Physical TM observations retain their halting boundary.

A reused `NumberCompiler` keeps up to eight recent powered execution owners.
Repeated requests and Collatz radix views reuse their existing HashLife caches.
Metrics remain cumulative per term. CLI `--info metrics` reports read-only
schema 8 execution counters, with `null` for unavailable measurements.
`NumberCompiler(max_cached_terms=0)` disables the per-compiler term cache. The
capacity counts retained terms. DAG memory is accounted separately, and each
standalone CLI process has its own cache.

- [Documentation index](docs/index.md)
- [Architecture and package ownership](docs/architecture.md)
- [Development and checks](docs/development.md)
- [Current validation status](docs/release-status.md)
- [Research and proof history](docs/history.md)
- [Executable source policy](devtools/checks/repository_policy.py) and [policy tests](tests/repository/test_repository_policy.py)

The latest default Python suite completed within its five-minute limit. Six
comma CLI assertions remain blocked by the missing global proof artifact.
The [current release status](docs/release-status.md) records the remaining gates.

For development, `python -m devtools.checks.release --suite unit` runs the unit
suite. `--suite all` runs quality checks, the complete Python collection, and
registered Isabelle builds. Use repeated `--select PATH_OR_NODEID` arguments
with the unit runner or within the registered P0 test files. Use the guarded
runner for repository tests. The [checking guide](docs/development.md) describes
resource controls and evidence requirements.
