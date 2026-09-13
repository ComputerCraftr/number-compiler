# Number Compiler

Number Compiler provides exact terms and radix projections for reverse-add,
Collatz, prime blocks, Fermat numbers and Mersenne numbers.

```bash
python -m pip install -e '.[dev]'
number-compiler families
number-compiler nth 196 8
number-compiler nth collatz 8 --seed 27
number-compiler classify fermat 3 --format json
number-compiler classify mersenne 131 --factor --format json
```

The supported Python entry points are exported from `number_compiler`.
Implementation modules have one canonical owner; historical forwarding imports
have been removed as described in the [API migration guide](docs/api-migration.md).

`classify` requests a primality certificate; `nth` emits the candidate itself.
Classification defaults to the admitted compact proof route. It prints `unknown`
and exits 3 when that route cannot decide. Pépin and Lucas–Lehmer are available
only as research oracles. `--factor` requests a separately budgeted étale
coefficient witness; a proper divisor proves composite, while a non-split does
not prove prime. `--max-candidate-bits` bounds candidate size before theorem work.
Candidate-derived mod-16 shadow-cylinder prime-bit recovery remains a P0
release blocker.

A reused `NumberCompiler` keeps up to eight recent powered execution owners.
Repeated requests and Collatz radix views reuse their existing HashLife caches;
metrics remain cumulative per term. `NumberCompiler(max_cached_terms=0)` disables
this reuse. The capacity bounds retained terms, not total DAG memory, and does
not share caches between standalone CLI processes.

- [Architecture and package ownership](docs/architecture.md)
- [Development and checks](docs/development.md)
- [Current validation status](docs/release-status.md)
- [Historical reports](docs/history.md)
- [Repository rules](REPOSITORY_RULES.md)

The HashLife production cutover is unfinished. Structural cleanup does not prove
sublinear execution or satisfy the five-minute runtime release gate.
The [P0 integration report](docs/production-p0-integration.md) records the current
production changes and the remaining release blockers.

For development, `pytest` runs the unit suite; `pytest -m validation` runs
exhaustive proofs, research and release workloads. Use `pytest -m ''` for both.
See the [checking guide](docs/development.md) for resource controls and evidence
requirements. A unit pass does not certify the unfinished runtime release.
