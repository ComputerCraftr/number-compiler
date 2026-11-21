# Reversal carry sheets and palindrome search

Period: 2026-11-15 through 2026-11-21 (Sunday–Saturday).

[Week index](README.md)

## Objective

Connect bounded reversal queries to source-admitted digit and carry actions. This work started on Git `df533a4b45acf41a6df307998e0d8be38ed30956`. The measurements below cover the development checkout.

## Changes

The registry accepts a positive-generation palindrome search for decimal reverse/add and double reverse. Reverse/add can reuse complete first-hit summaries across equal Q19 states. The double-reverse prefix search checks for a first hit before admitting the nine-edge C0 tail. Endpoint requests have no event demand. The two reflected multipliers share the ledgered overlapping-cone evaluator. Reverse/add can pass a twelve-row carry image to its existing output issuer.

## Established results

The reverse/add growth predicate tests all packed Q19 lanes together. A growing palindrome needs outer sum 11, interior sums in {0, 11}, and a zero odd center if present. With one low bit per six-bit lane in `ones`, `packed == 11 * (packed & ones)` checks the interior condition in one word comparison. Native induction proves the absence of cross-lane carries. On 1,024 pairs the five-trial embedded first-hit comparison measured 0.942 ms with the per-lane scan and 0.780 ms through the production packed predicate. Predicate-only medians were 152.02 and 1.97 microseconds. The five samples per path are in `reversal-growth-accepted.log`. The independently expected first generation was one.

The exhaustive local comparison exercised 10,000 base-100 inputs per multiplier. Endpoint fixtures include odd and even horizons, physical trailing zeros and both growth and contraction. Source-bound Q19 tests compare subsequent physical outputs with independently iterated decimal arithmetic.

## CLI measurements

Five interleaved trials compared each constructor on the same source, with the same parser, scheduler, receiving publisher and renderer. For the candidate runs the benchmark selected the padded constructor at the existing composite-action boundary. Every successful call returned the independently iterated decimal value. These are medians in milliseconds for embedded CLI calls with initially empty process caches.

| Family and source | Physical generation | Incumbent | Padded |
| --- | ---: | ---: | ---: |
| Double reverse, seed 73 | 256 | 15.14 | 8.08 |
| Double reverse, seed 73 | 1,024 | 29.17 | 64.65 |
| Double reverse, 600th predecessor of 2 (144 digits) | 256 | 499.73 | 11.22 |
| Five reverse, seed 73 | 256 | 3.14 | 3.15 |
| Five reverse, seed 73 | 1,024 | 33.39 | 30.71 |
| Five reverse, 144-digit source | 256 | 12.48 | 9.83 |
| Five reverse, 144-digit source | 1,024 | 81.56 | 62.69 |

After enabling automatic routing, five interleaved fresh-process CLI trials compared the working tree with the source exported from Git `df533a4b`. Each invocation printed the full decimal endpoint and matched independent literal iteration. The 144-digit double-reverse predecessor at 256 ticks went from 776.84 ms to 216.82 ms. Five reverse on the 144-digit repeated `73149` prefix at 1,024 ticks went from 271.39 ms to 215.83 ms. These times include interpreter startup and rendering. The embedded comparisons above isolate the constructor effects. Individual samples are in `reversal-fresh-production.log`.

On the same receiving sources the enabled embedded CLI took 17.41 ms for double reverse and 62.37 ms for five reverse from empty process caches. With the process cache bypassed, the medians were 17.04 and 62.47 ms. Double reverse checked three prefix steps, evaluated 2,572 distinct cones and reused 964. Five reverse evaluated 22,432 and reused 7,450. Re-reading either endpoint from its original live term left the primitive-transition and cone counters unchanged. These measurements use the actual automatic selector. Raw samples and same-owner timings are in `reversal-automatic-work.log`.

The H12 issuer evaluates the history epimorphism directly on the packed pair state. The kernel equality between the twelve-step physical successor and the mod-32 forcing image lets the producer omit the carry rows and their second fold. The change in physical width counts births and checks the five-no-growth condition. Each source caches its twelve-step binding once across horizons. Equal full pair fields share one continuation for each remaining duration. Independent CLI trials for seed 104 measured the cost of warming the bank with seed 95 separately. When the receiving seed has a different starting field, its own twelve physical steps establish admission on the first request. Each receiver publishes its own occurrence.

| Generation of seed 104 | Cold receiver in existing process | Receiver after seed 95 | Genuine bypass | Cost of warming with 95 |
| ---: | ---: | ---: | ---: | ---: |
| 1,024 | 13.86 | 9.02 | 13.80 | 14.24 |
| 2,048 | 30.06 | 16.55 | 28.24 | 28.55 |

Five interleaved producer-only trials compared the prior wheel and the new packed H12 handoff on identical input states. The median fell from 148 to 21 microseconds for seed 196 and from 934 to 49 microseconds on the 144-digit source. Both producers matched literal decimal iteration. The four-request regression across seeds 95 and 104 at horizons 30 and 34 executed 30, 12, 22 and zero transitions in order. It retained two twelve-step source bindings and two suffix actions.

A completed seed-196 palindrome search through generation 256 took 0.18 ms warm, 2.29 ms with cache bypass, and 135.84 ms in a fresh CLI process. An early hit can be cheaper to recompute. For the seed-104 event request following seed 95, warm execution took 0.28 ms and bypass took 0.14 ms. Event summaries and complete physical endpoint actions have distinct cache laws.

## Rejected approaches

A padded 2rev10 endpoint alone cannot certify palindrome absence at intermediate generations. The search checks the pre-admission prefix and uses the closed C0 edge theorem only for the covered suffix. The long seed-73 measurement also rules out selecting the padded endpoint solely by horizon.

## Validation provenance

The default unit run `20261120T102017Z-4f82f0493b6c4dc59e1cc1c7d8c0ace1` finished in 217.76 seconds (220.10 seconds under the parent guard, sampled peak 445.2 MiB). It recorded 12,795 passes and six failures, all for comma global admission, including its two compact-index CLI cases. All 181 selected reversal tests passed in `20261120T102014Z-f9015b99c24e4a32a2b718ff379bbb89`, including exhaustive local transitions, both endpoint selectors, first-hit coverage and cancellation. All 41 applicable P0 tests passed in `20261120T101945Z-785fbd2fdf9b45dba8dc5fbb736638e4`. In a clean install of the wheel built after the H12 cache change, reverse/add seed 89 returned generation 24, double reverse reported an empty search at horizon zero, and five reverse from seed 10 returned 25 at generation two. The same install checked the full 1,024-step reverse/add endpoints of seeds 95 and 104 against decimal iteration and returned the exact wide-source decimal endpoints at 256 and 1,024 ticks (double and five reverse, respectively).

Before the H12 cache change, quality run `20261120T100700Z-34712b734cb844e6b7d4e8572cd97a3d` passed strict mypy, Ruff, formatting, dependency consistency, source policy and documentation checks. Strict Pyright covered all 2,548 files in 102 serial batches with zero diagnostics. Strict mypy, Pyright and Ruff also passed on the changed H12 producer and test. The repository proof index still rejects a comma audit invocation. The full installed-package gate still reports a missing comma future admission.

The shared carry dynamics session rebuilt in 43 seconds and the five-reversal session in 112 seconds in run `20261120T090840Z-d3a5a0ad522147798783d5d263d0bbc3`. Run `20261120T091819Z-dc50163179a84f5cbafd864cd15c39cd` rebuilt the double-reversal session in 120 seconds with four threads. These sessions check both endpoint parities, including the reflected writer's even inlet and C0 palindrome exclusion. Run `20261120T100327Z-a137f9323d2248aca096f9d8f2063688` rebuilt the complete reverse/add growth session in 15 seconds. Its kernel checked the packed lane predicates and the joint ordinary/XOR binary output and decimal preimage theorem on the same physical source. Run `20261120T100423Z-f5af69eb9b1c412f9a9c5fb13a638031` selected all four sessions together and reused their accepted heaps. The H12 cache change uses the same theorem. Run `20261120T102407Z-bc537948140d4a1b8372b2ce0ee22e87` reused the accepted reverse/add heap. The native H12 continuation was accepted in `20261120T074716Z-4d22723b7718467f84354edea5b71ba2`. Raw trial samples are in the local guarded outputs `reversal-matched-v2.log`, `reversal-matched-long-v2.log`, `reversal-epi-cli.log`, and `reversal-sprint-bench-v2.log`.

## Remaining work

Pumped digit blocks require certified boundary carries and entry phase. Execution resumes the exact bounded path at an uncertified seam. The C0 signal consumer covers the source-issued low-two mask and, for seed 196, four physical low digits on even generations from 16. Wider annular claims require a complete halo certificate. The raw power-of-five suffix and the mod-225 digit field have distinct arithmetic issuers. The current scalar mod-225 CLI observation uses the direct modular formula. The full release wheel check still requires the global comma writer.
