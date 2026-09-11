# Symmetric pair-half bimachine powering probe

Research-only width-independent operator experiment.

- One exact step: 86 left states, 12 right states; 1000 randomized half-word checks passed.
- Lazy-output direct composition avoids materializing the ~29M Cartesian output contexts.
- Two exact steps: 1,156 left and 1,138 right determinized states; randomized checks passed.
- Four-step capped probe: 100,000 reachable left-NFA triples generated after only 6,752 processed triples (3.5 s in the capped probe).

The result isolates operator-state growth from digit-width materialization. It does
not prove that an orbit-specialized quotient cannot exist, but naive universal
bimachine powering is not a compact full-J backend.
