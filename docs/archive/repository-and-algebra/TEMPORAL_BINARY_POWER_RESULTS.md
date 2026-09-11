# v0.59.9 temporal binary-power results

Both iterative public nth-state families still construct their temporal operator in `O(log n)` composition depth:

- reverse/add: powered pair block effect plus digit terminal;
- physical Collatz: powered finite two-sided physical-step transducer.

v0.59.9 also changes application semantics.  Sparse high-order residuals are no longer represented as action/history words.  A temporal child is applied to canonical spatial tiles and returns canonical future tiles, so time squaring and spatial hierarchy share one macrocell result graph.

This proves that production does not perform generation-by-generation construction and no longer retains a duplicate temporal itinerary.  It does not yet prove that the number of distinct semantic macrocell/interface results created on first arbitrary-source application is `O(log n)`.
