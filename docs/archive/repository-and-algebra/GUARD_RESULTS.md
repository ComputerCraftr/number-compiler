# Guard and event-selective cleanup results

## Regression suite

- 19 tests pass.
- Adversarial powered backends are rejected when they attempt successor replay,
  growth queries, carry construction, branch compilation, point evaluation,
  materialization, literal construction, or positional summary synthesis.
- `certify_full_jump_backend(MissingJumpBackend(...))` reports release blocked.

## Event-selective ordinary/reference path

The ordinary successor no longer evaluates a full carry prefix to decide growth.
It consumes a cached `BlockSummary`; when missing outside powered execution it
selectively probes the outer threshold run and caches the result.

The closed bit evaluator now truly short-circuits `AND`/`OR`; its previous eager
child evaluation defeated selective reset queries.

Representative 196 formula-construction measurements after the fix:

| iterations | pair width | elapsed |
|---:|---:|---:|
| 100 | 47 | ~0.11 s |
| 200 | 88 | ~0.46 s |
| 300 | 133 | ~0.91 s |
| 500 | 216 | ~2.61 s |

At 500 iterations only 521 coefficient positions were selectively probed for root
summaries (about one per transition).  This is still an ordinary *linear temporal*
constructor, not full J.

## Width-independent powered-operator probe

A research-only symmetric pair-half bimachine represents one exact reverse/add step
without scanning digit width:

- T: left=86, right=12 states; randomized exactness passed.
- T^2: left=1,156, right=1,138 determinized states; randomized exactness passed.
- T^4 capped probe: 100,000 reachable left-NFA triples were generated after only
  6,752 had been processed, so naive direct bimachine powering is not currently a
  compact full-J representation.

The full release remains blocked rather than falling back to successor replay.
