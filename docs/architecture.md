# Architecture and ownership

The supported entry points live in `number_compiler.api`. Package-level exports
are intentional API declarations, not compatibility dispatchers.

| Package | Responsibility |
| --- | --- |
| `arithmetic` | Carry monoids, finite functions, formulas, polynomial/field arithmetic, immutable contracts |
| `hashlife.actions` | Temporal construction and algebra |
| `hashlife.tiles` | Exact canonical content, completed results, bindings and leases |
| `hashlife.interfaces` and `hashlife.behavior` | Certified transfer and observation semantics |
| `hashlife.execution` | Iterative dependency execution |
| `hashlife.observation` | Point and extent observation |
| `sequences` | Reverse-add, Collatz, primes and shared Fermat/Mersenne laws |
| `projection` | Radix conversion, explicit output and capped microblocks |
| `resources` | Budgets, ownership and measured execution accounting |

Fermat and Mersenne share the concrete `sequences.power_numbers` algebra rather
than duplicating it into two implementations. Their public specifications and
compiled terms remain separate.

Public reverse-add, physical Collatz, and supported generic compositions now
construct `TileScheduler` applications. Temporal powers are compiled as a binary
DAG; observations and explicit completion use the same canonical tile/result
arena. Required causal output tiles and completed midpoint results can be reused
without a continuation backend.

Legacy higher-continuation modules remain in the tree for still-unmigrated private
tests and developer comparisons. They are no longer selected by the public index
constructor. Removing those modules and their remaining callers is unfinished;
this routing change does not establish the performance release gate. Radix
consumer migration is tracked in the release status.

Developer checks, independent proof construction, benchmarks and experiments
live in regular `devtools` packages outside the production distribution.
Immutable kernel loading and validation remain in arithmetic contracts where
public execution requires them. Explicitly requested output construction lives
in projection; it does not authorize eager intermediate construction in points.

Package boundaries are checked from imports and the actual file tree. Generated
build inventories and historical migration lists are not sources of truth.

The [cutover optimization plan](hashlife-optimization.md) records remaining
execution and measurement gates. The [reverse/add research synthesis](research/reverse-add.md)
maps the local carry/output and radial research to these owners without reviving
the old image/provider runtime.

The [carry-domain quotient notes](architecture/carry-domain-quotients.md) document
the newer reverse transport/birth collision witnesses, Collatz two-wire carry
law, projected frame characters, and the distinction between those research
results and validated production reuse.
