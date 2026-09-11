# Finite-lifetime square forcing

Fermat and Mersenne square perturbations satisfy the exact identity

```text
S(X + J) - S(X) = 2 X J + J^2.
```

The existing `PrimaryJetAffineMorphism` now exposes `square_tangent`. It stores
the transport of an old forcing occurrence as `J -> 2 X J + B`, where `B` is a
separately supplied new birth. The quadratic term is never silently discarded:
when a consumer needs it, `J^2` is evaluated and passed as that birth.

In the shared five-component primary algebra modulo 32, every tangent contains
a factor of two. Any composition of five square tangents therefore has zero
source kernel. `source_annihilated` exposes this exact condition, and the
canonical action key already omits provenance step counts. Histories that reach
the same zero-kernel action consequently share one action ID without changing
the spatial `PrimaryJetBlock` identity or its length.

The complete bounded audit covers every residue of F2, F3, M5, and M7 through
nine recurrence steps. All post-depth-five zero-birth tangent occurrences use
one canonical action. This is a real action-key cache opportunity; it is not a
claim that the full square recurrence has become linear or that nonlinear
births stop occurring.

These population measurements embed the current scalar residue as the constant
coefficient of a five-component mod-32 germ. They are scalar tangent controls,
not an exact map from the cyclic/negacyclic digit field into that germ. Digit
normalization and fold forcing still need their own exact transport. The unit
test separately checks annihilation with nonconstant germs.

Source annihilation is intentionally narrower than action annihilation. A
second control injects distinct births on the fifth tangent. The old source
kernel is still zero, while the surviving offsets retain multiple action IDs.
Only dead source provenance merges; live forcing output remains semantic.

There is no production primary-tangent interner today. The audit therefore
reports canonical-key hits separately and leaves `production_interner_present`
false; it does not relabel possible key reuse as measured runtime cache reuse.

Two controls prevent overquotienting. First, equal 2-adic valuation does not
determine a folded response: negacyclic wrap changes the sign at the Fermat
seam, while cyclic position still changes the Mersenne field response. Second,
the exact doubling clock modulo 5 has minimal period four and continues through
all four phases after the old tangent source has died. The clock stamps new forcing and cannot be removed
from birth identity merely because an earlier occurrence was annihilated.

This bounded result does not admit Fermat or Mersenne to `TileScheduler` and
does not alter the external Pépin `-1` or Lucas--Lehmer zero observers. A full
temporal quotient must additionally canonicalize the stream of nonlinear
births together with demanded carry/fold actions.
