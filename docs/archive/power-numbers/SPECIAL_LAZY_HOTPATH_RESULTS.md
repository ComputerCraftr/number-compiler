# v0.52.9 — lazy Fermat/Mersenne source hot path

v0.52.9 removes primality/factor/étale work from the ordinary Fermat/Mersenne source compiler.  The numeric source is compiled first; theorem work exists on a separate demand boundary.

## Corrected dependency order

```text
exact sparse Fermat/Mersenne source
        |
        +--> exact digit / length / parity / cyclic-boundary facts
        |        |
        |        +--> intersect two-sheet branch mask (00/01/10/11)
        |                 |
        |                 +--> one sheet survives: specialize immediately
        |                 +--> both survive and output agrees: Concrete
        |                 +--> both survive and output separates: Guarded
        |                                      |
        |                                      +--> require concrete?
        |                                                |
        |                                                +--> explicit theorem query
        |
        +--> raw symbolic source output (never invokes theorem work)
```

`SpecialSourceShape` supplies theorem-free source geometry:

- Fermat `F_n`: bit length `2^n+1`, support `{0,2^n}`, low bit 1, negacyclic boundary sign `-1`.
- Mersenne `M_p`: bit length `p`, support `[0,p)`, low bit 1, cyclic boundary sign `+1`.
- independent carry checkpoints can be intersected with the same two-bit mask.

The mask is an immutable two-bit object, so repeated constraints never create a growing theorem state.  A caller can retain/intersect the mask across powered checkpoints and pass the surviving mask to the final projection.  The PASS/FAIL guard is constructed only at that projection frontier.

## Removed eager work

`CanonicalSequenceCompiler._compile_fermat()` and `_compile_mersenne()` now perform none of the following:

- `FactoredPrimeAutomaton.build(...)`;
- `factored_word_projection(...)`;
- `fermat_depth_certificate(...)` / `mersenne_depth_certificate(...)`;
- `mersenne_composite_exponent_factor(...)`;
- `SpecialSourceGuard` construction;
- factored residue attachment.

Both semantic and diagnostic raw compilation leave `primality`, `factor_witness`, `source_guard`, and `factored_projection` unset and use `projection_method="deferred"`.

The old work is available only through `CanonicalSequenceCompiler.resolve_special_theorem(...)`, which has a separate theorem cache.  `project_special_branch_values(..., require_concrete=False)` never invokes it.  A separating value invokes it only when `require_concrete=True` and cheap constraints have not already selected a sheet.

## Source-cache correction

`test_through` was theorem policy embedded in source identity.  It is no longer part of `FermatSequenceSpec.canonical_key` or `MersenneSequenceSpec.canonical_key`.  Compiling the same source with `test_through=0` and `test_through=99` aliases the same cached source object; the stored source spec normalizes the legacy field to zero.

## Executable controls

`bench/special_lazy_hotpath_probe.py` regenerates `results/special_lazy_hotpath_metrics.json`.  The probe confirms:

- raw F2/F4/F5/F12 and M11/M13/M15/M31/M8191 attach no theorem/factor state;
- source cache size after those two source compilations is 2 and theorem cache size is 0;
- F4 digit 16, parity, length, independent carry, and boundary-sign constraints all resolve without touching the theorem cache;
- M13 digit/length constraints likewise resolve theorem-free;
- a generic separating `(3,7)` output stays `Guarded` with theorem cache 0;
- asking for that same output concretely creates exactly one lazy theorem-cache entry;
- explicit F5, M15 and M11 theorem queries still recover the previous factor/exponent witnesses.

An adversarial unit test patches every former hot-path theorem/factor entry point to raise.  Raw Fermat/Mersenne semantic and diagnostic compilation still succeeds.

## Remaining theorem boundary

This change does **not** claim that parity/length/source digits decide primality.  They remove impossible reconstructed sheets and keep theorem work off outputs that do not need it.  If a derived coordinate remains branch-sensitive after all available source/carry constraints and the caller requires a concrete value, the existing fail-closed theorem query is still the terminal fallback.
