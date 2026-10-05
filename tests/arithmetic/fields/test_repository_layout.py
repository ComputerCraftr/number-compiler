import ast
from dataclasses import dataclass

import pytest

from devtools.paths import repository_root

ROOT = repository_root()


@dataclass(frozen=True, slots=True)
class _SourceFacts:
    relative_path: str
    imports: tuple[str, ...]
    definitions: tuple[tuple[str, str], ...]


@pytest.fixture(scope="module")
def _production_facts() -> tuple[_SourceFacts, ...]:
    source = ROOT / "src" / "number_compiler"
    rows: list[_SourceFacts] = []
    for path in sorted(source.rglob("*.py")):
        relative = path.relative_to(source).as_posix()
        tree = ast.parse(path.read_text(), filename=str(path))
        imports: list[str] = []
        definitions: list[tuple[str, str]] = []
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom) and node.module:
                imports.append(node.module)
            elif isinstance(node, ast.Import):
                imports.extend(alias.name for alias in node.names)
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                definitions.append((node.name, "function"))
            elif isinstance(node, ast.ClassDef):
                definitions.append((node.name, "class"))
        rows.append(_SourceFacts(relative, tuple(imports), tuple(definitions)))
    return tuple(rows)


def _production_definitions(
    facts: tuple[_SourceFacts, ...], *, functions_only: bool = False
) -> dict[str, list[str]]:
    definitions: dict[str, list[str]] = {}
    for row in facts:
        for name, kind in row.definitions:
            if not functions_only or kind == "function":
                definitions.setdefault(name, []).append(row.relative_path)
    return definitions


def test_repository_uses_canonical_source_and_developer_packages() -> None:
    assert (ROOT / "src" / "number_compiler" / "__init__.py").is_file()
    assert (ROOT / "devtools" / "benchmarks" / "auxiliary_power_probe.py").is_file()
    assert (ROOT / "tests").is_dir()
    assert not (ROOT / "reverse_add").exists()
    assert not (ROOT / "src" / "reverse_add").exists()


def test_production_compiler_keeps_analysis_and_test_code_out_of_runtime_graph(
    _production_facts: tuple[_SourceFacts, ...],
) -> None:
    forbidden_roots = {"tests", "devtools", "bench", "research"}
    for row in _production_facts:
        assert not any(name.split(".")[0] in forbidden_roots for name in row.imports), (
            row.relative_path,
            row.imports,
        )

    src = ROOT / "src" / "number_compiler"
    compiler = (src / "api/sequence_compiler.py").read_text()
    assert "prime_encoding_analysis" not in compiler
    assert "from .release" not in compiler


def test_canonical_arithmetic_primitives_are_not_reimplemented(
    _production_facts: tuple[_SourceFacts, ...],
) -> None:
    defs = _production_definitions(_production_facts, functions_only=True)
    assert defs.get("digits_lsd") == ["arithmetic/fields/radix.py"]
    assert defs.get("smallest_factor") == ["sequences/prime/set.py"]
    assert not defs.get("_bits")
    for stale in ("trial_factor", "pair_successor", "digits_lsd_int"):
        assert not defs.get(stale)


def test_prime_projector_encoding_experiments_are_physically_separated() -> None:
    family = ROOT / "src" / "number_compiler"
    prod = family / "sequences/prime/coordinates.py"
    analysis = family / "sequences/prime/encoding_analysis.py"
    assert prod.is_file() and analysis.is_file()
    text = prod.read_text()
    for name in (
        "_PowerRadixMDD",
        "zeckendorf_bitmap_decision_metrics",
        "pisano_period",
    ):
        assert name not in text


def test_shared_morphism_core_has_no_legacy_parallel_power_types(
    _production_facts: tuple[_SourceFacts, ...],
) -> None:
    definitions = _production_definitions(_production_facts)
    assert definitions.get("binary_power") == ["arithmetic/fields/morphism_core.py"]
    assert definitions.get("LazyLoweringCache") == [
        "arithmetic/fields/morphism_core.py"
    ]
    assert definitions.get("AffineCocycle") == ["arithmetic/fields/morphism_core.py"]
    assert definitions.get("DyadicAffineCocycle") == [
        "arithmetic/fields/morphism_core.py"
    ]
    assert definitions.get("QuadraticPower") == ["arithmetic/fields/morphism_core.py"]
    for legacy in ("SpecialPowerEffect", "SpecialPowerNode", "SpecialPowerArena"):
        assert not definitions.get(legacy)


def test_special_certificate_compiler_path_has_no_classical_recurrence_owner(
    _production_facts: tuple[_SourceFacts, ...],
) -> None:
    src = ROOT / "src" / "number_compiler"
    compiler = (src / "api/sequence_compiler.py").read_text()
    special = src
    certificate = (special / "sequences/power_numbers/certificate.py").read_text()
    for forbidden in (
        "pepin_test",
        "lucas_lehmer_test",
        "pepin_digit_field",
        "lucas_lehmer_digit_field",
    ):
        assert forbidden not in compiler
        assert forbidden not in certificate
    assert "terminal_threshold_probe" in certificate
    assert "_summary_from_classical_ceiling" not in certificate
    assert "power_numbers.classical_ceiling" not in certificate
    threshold = (special / "sequences/power_numbers/terminal_threshold.py").read_text()
    assert "build_compact_transverse_pullback" in threshold
    assert "transverse_pullback" in threshold
    assert "build_special_germ_plan" not in threshold
    assert "bounded_candidate_image_filtration" not in certificate
    assert "tropical_ghost_flux" not in certificate
    production = special / "sequences/power_numbers"
    assert not (production / "classical_ceiling.py").exists()
    assert not (production / "digit_power.py").exists()
    assert (ROOT / "devtools/verification/oracles/classical_ceiling.py").is_file()
    assert (ROOT / "devtools/verification/oracles/digit_power.py").is_file()
    definitions = _production_definitions(_production_facts)
    for recurrence in (
        "fermat_classical_ceiling",
        "mersenne_classical_ceiling",
        "special_classical_ceiling",
        "lucas_lehmer_digit_field",
        "pepin_digit_field",
    ):
        assert not definitions.get(recurrence)
    for path in src.rglob("*.py"):
        assert "devtools.verification.oracles" not in path.read_text()


def test_terminal_frobenius_chunk_is_detached_from_constrained_production_germ() -> (
    None
):
    src = ROOT / "src" / "number_compiler"
    special = src
    chunk = (special / "sequences/power_numbers/frobenius_chunk.py").read_text()
    germ = (special / "sequences/power_numbers/germ.py").read_text()
    threshold = (special / "sequences/power_numbers/terminal_threshold.py").read_text()
    assert "class SpecialFrobeniusChunkSpec" in chunk
    assert "class SpecialFrobeniusChunkResult" in chunk
    assert "frobenius-chunk-zero-class-extractor-unavailable" in chunk
    assert "build_compact_transverse_pullback" in threshold
    assert "transverse_pullback" in threshold
    assert "build_special_germ_plan" not in threshold
    assert "class SpecialGermConstraintState" in germ
    assert "special_frobenius_chunk_probe" not in germ
    assert (
        "return 0"
        in germ[
            germ.index("def support_observations") : germ.index(
                "def binary_compositions"
            )
        ]
    )
    for forbidden in (
        "pepin_test",
        "lucas_lehmer_test",
        "bounded_candidate_image_filtration",
        "special_binary_jump",
        "special_digit_power",
        "oracle_support",
    ):
        assert forbidden not in chunk


def test_special_output_guard_stays_lightweight_on_production_compiler_path() -> None:
    src = ROOT / "src" / "number_compiler"
    compiler = (src / "api/sequence_compiler.py").read_text()
    quotient = (src / "projection/output_quotient.py").read_text()
    assert "from number_compiler.projection.output_quotient import" in compiler
    assert "def pullback_special_defect" in compiler
    assert "_special_constraint_state" in compiler
    # The guard import is local to the explicit projection frontier, not the raw
    # Fermat/Mersenne source constructors.
    source_tail = compiler[compiler.index("def _compile_fermat") :]
    assert "output_quotient" not in source_tail
    assert "special_certificate" not in source_tail
    assert "FactoredPrimeAutomaton" not in source_tail
    assert "idempotent_output" not in compiler
    for forbidden in (
        "digit_convolution",
        "digit_cyclotomic",
        "special_digit_power",
        "special_binary_jump",
        "oracle_support",
        "research",
    ):
        assert forbidden not in quotient


def test_special_source_program_cannot_hide_a_deferred_certificate_or_oracle() -> None:
    text = (ROOT / "devtools/verification/special_source_program.py").read_text()
    for forbidden in (
        "pepin_test",
        "lucas_lehmer_test",
        "oracle_support",
        "special_binary_jump",
        "factorint",
        "crt",
    ):
        assert forbidden not in text
    assert "raise ValueError(self.op)" in text
    assert "theorem_proved: bool = False" in text


def test_special_slow_oracles_are_explicit_opt_in_not_root_exports() -> None:
    root = (ROOT / "src" / "number_compiler" / "__init__.py").read_text()
    for forbidden in (
        "pepin_test",
        "lucas_lehmer_test",
        "pepin_digit_field",
        "lucas_lehmer_digit_field",
        "build_fermat_binary_jump",
        "build_mersenne_binary_jump",
        "bounded_candidate_image_filtration",
    ):
        assert forbidden not in root
    oracle = ROOT / "devtools" / "verification" / "oracles" / "__init__.py"
    assert oracle.is_file()
    production = ROOT / "src" / "number_compiler" / "sequences" / "power_numbers"
    for proof_only in (
        "binary_jump.py",
        "power_monoid.py",
        "source_program.py",
        "classical_ceiling.py",
        "digit_power.py",
    ):
        assert not (production / proof_only).exists()
    assert (
        ROOT / "devtools" / "verification" / "oracles" / "special_binary_jump.py"
    ).is_file()
    assert (ROOT / "devtools" / "verification" / "special_power_monoid.py").is_file()
    assert (ROOT / "devtools" / "verification" / "special_source_program.py").is_file()


def test_shared_cross_family_arithmetic_has_one_owner_per_primitive(
    _production_facts: tuple[_SourceFacts, ...],
) -> None:
    definitions = _production_definitions(_production_facts)

    assert definitions.get("polynomial_multiply") == [
        "arithmetic/polynomials/polynomial.py"
    ]
    assert definitions.get("polynomial_remainder_monic") == [
        "arithmetic/polynomials/polynomial.py"
    ]
    assert definitions.get("MonicPolynomialRing") == [
        "arithmetic/polynomials/polynomial.py"
    ]
    assert definitions.get("CyclotomicRing") == [
        "arithmetic/polynomials/cyclotomic_ring.py"
    ]
    assert definitions.get("TwoPrimaryImageFiltration") == [
        "arithmetic/polynomials/two_primary_filtration.py"
    ]
    assert definitions.get("TwoPrimaryCharacterProbe") == [
        "arithmetic/polynomials/two_primary_filtration.py"
    ]
    assert not definitions.get("PureTwoPrimaryGroupDepth")
    assert definitions.get("CyclotomicAffineMorphism") == [
        "arithmetic/polynomials/cyclotomic_affine.py"
    ]
    assert definitions.get("CarryCyclotomicTransducer") == [
        "arithmetic/polynomials/cyclotomic_carry.py"
    ]
    for legacy in (
        "QuadraticUnit",
        "mersenne_cyclic_square_field",
        "fermat_negacyclic_square_field",
        "_zm_plus_one_mul",
        "_zm_plus_one_power",
        "_poly_multiply_mod_prime",
    ):
        assert not definitions.get(legacy)


def test_196_trace_tower_uses_shared_quadratic_power_representation() -> None:
    from number_compiler.arithmetic.fields.morphism_core import QuadraticPower
    from number_compiler.arithmetic.formula.symmetry_frame import (
        FixedRealCyclotomicGerm,
    )
    from number_compiler.arithmetic.polynomials.polynomial import (
        trace_square_polynomial,
    )

    seed: tuple[int, ...] = (-2, 1)
    assert FixedRealCyclotomicGerm.p8_coefficients() == QuadraticPower(
        1
    ).apply_iterated(
        seed,
        step=trace_square_polynomial,
    )
    assert FixedRealCyclotomicGerm.p16_coefficients() == QuadraticPower(
        2
    ).apply_iterated(
        seed,
        step=trace_square_polynomial,
    )


def test_number_compiler_is_the_only_public_package_namespace() -> None:
    src = ROOT / "src"
    packages = sorted(
        path.name
        for path in src.iterdir()
        if path.is_dir() and (path / "__init__.py").is_file()
    )
    assert packages == ["number_compiler"]


def test_number_compiler_cli_and_projection_api_are_physically_separated() -> None:
    src = ROOT / "src" / "number_compiler"
    compiler = (src / "api/sequence_compiler.py").read_text()
    api = (src / "api/number_api.py").read_text()
    cli = (src / "api/cli.py").read_text()
    requests = (src / "api/cli_requests.py").read_text()
    rendering = (src / "api/cli_render.py").read_text()
    assert "argparse" not in compiler
    assert "argparse" not in api
    assert "NumberCompiler" not in compiler
    assert "materialize" in api
    assert "project_nth" in api
    assert "argparse" not in cli
    assert "argparse" in requests
    assert "parse_request" in cli
    assert "def _render_value" in rendering
    assert "def _render_value" not in cli


def test_duplicate_helper_and_carrier_cleanup_stays_canonical(
    _production_facts: tuple[_SourceFacts, ...],
) -> None:
    src = ROOT / "src" / "number_compiler"
    definitions = _production_definitions(_production_facts)

    # One valuation implementation owns the shared 2-adic primitive.  The
    # public collatz_pair.v2 spelling is an import alias, not a second body.
    assert definitions.get("v2_positive") == ["arithmetic/fields/two_adic.py"]
    assert definitions.get("v2_nonzero") == ["arithmetic/fields/two_adic.py"]
    assert not definitions.get("_v2_positive")
    assert not definitions.get("_v2_nonzero")

    # Hash-consed effect nodes and special compilation wrappers are shared
    # runtime carriers rather than family-specific two-field dataclasses.
    assert definitions.get("InternedEffectNode") == [
        "arithmetic/fields/morphism_core.py"
    ]
    assert not definitions.get("CollatzPowerNode")
    assert not definitions.get("UnaryPowerNode")
    sequence_defs = {
        node.name
        for node in ast.walk(ast.parse((src / "api/sequence_types.py").read_text()))
        if isinstance(node, (ast.ClassDef, ast.FunctionDef))
    }
    assert "SpecialCompilation" in sequence_defs
    assert not definitions.get("FermatCompilation")
    assert not definitions.get("MersenneCompilation")
    assert definitions.get("BimachineTransformResult") == [
        "arithmetic/automata/transducer.py"
    ]
    assert not definitions.get("ComposedBimachine")
    assert not definitions.get("QuotientBimachine")

    # The rejected shape-coefficient/Taylor transport experiment is deleted;
    # shape interning and absolute lowering are the only retained layers.
    poly = (
        ROOT / "devtools" / "experiments" / "algebra" / "polynomial_morphisms.py"
    ).read_text()
    for stale in ("_shape_cache", "_materialize_shape", "shape_coefficient_slots"):
        assert stale not in poly

    # Superseded one-line benchmark aliases are not permanent repository API.
    assert not (ROOT / "bench" / "special_lazy_hotpath_probe.py").exists()


def test_collatz_character_observers_stay_before_exact_valuation_and_germ_paths(
    _production_facts: tuple[_SourceFacts, ...],
) -> None:
    src = ROOT / "src" / "number_compiler"
    character = (src / "sequences/collatz/character.py").read_text()
    raw = (src / "sequences/collatz/raw_field.py").read_text()
    tree = ast.parse(character)
    imported = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module:
            imported.add(node.module.rsplit(".", 1)[-1])
    assert "frame" not in imported
    assert "germ_cache" not in imported
    assert "state_reduction" not in imported
    assert "CollatzValuationState" not in character
    assert "RationalPadicRootGerm" not in character

    # The compatibility growth observer must not reacquire v2 before answering
    # the one-bit chi_4 question.
    raw_tree = ast.parse(raw)
    cls = next(
        n
        for n in raw_tree.body
        if isinstance(n, ast.ClassDef) and n.name == "CollatzSentinelBoundarySummary"
    )
    growth = next(
        n
        for n in cls.body
        if isinstance(n, ast.FunctionDef) and n.name == "accelerated_increases"
    )
    calls = {
        n.func.attr if isinstance(n.func, ast.Attribute) else n.func.id
        for n in ast.walk(growth)
        if isinstance(n, ast.Call)
        if isinstance(n.func, (ast.Attribute, ast.Name))
    }
    assert "power4_valuation" not in calls

    # Shared radix/sentinel arithmetic remains owned by collatz_raw_field; the
    # character layer imports it rather than growing parallel helpers.
    defs = _production_definitions(_production_facts, functions_only=True)
    assert defs.get("power4_radix_bits") == ["sequences/collatz/raw_field.py"]
    assert defs.get("collatz_sentinel_digit") == ["sequences/collatz/raw_field.py"]


def test_digit_generation_observers_stop_before_heavier_carriers() -> None:
    src = ROOT / "src" / "number_compiler"
    api_tree = ast.parse((src / "api/number_api.py").read_text())
    cls = next(
        n
        for n in api_tree.body
        if isinstance(n, ast.ClassDef) and n.name == "NumberCompiler"
    )
    growth = next(
        n
        for n in cls.body
        if isinstance(n, ast.FunctionDef)
        and n.name == "project_reverse_add_growth_state"
    )
    names = {
        n.func.attr if isinstance(n.func, ast.Attribute) else n.func.id
        for n in ast.walk(growth)
        if isinstance(n, ast.Call)
        if isinstance(n.func, (ast.Attribute, ast.Name))
    }
    assert "reverse_add_nth_formula" not in names
    assert "carry_out" not in names
    assert "successor" not in names

    # Sparse special-source digit projection must remain a direct descriptor
    # lookup, not a materialization/certificate path.
    api = (src / "api/elementary_payloads.py").read_text()
    assert "def digit(self, index: int)" in api
    assert "return int(index == 0 or self.spec.exponent_extent == index)" in api
    assert "index == self.spec.exponent)" not in api

    # The support-only research evaluator explicitly disables both factor
    # descent and the linear differential control.
    bend = (
        ROOT / "devtools" / "experiments" / "algebra" / "residue_refined_bend.py"
    ).read_text()
    assert "extract_proper_factor=False" in bend
    assert "include_direct_control=False" in bend


def test_distribution_metadata_owns_number_compiler_cli_without_legacy_package() -> (
    None
):
    import tomllib

    meta = tomllib.loads((ROOT / "pyproject.toml").read_text())["project"]
    assert meta["name"] == "number-compiler"
    assert meta["version"] == "0.60.0"
    assert meta["scripts"] == {"number-compiler": "number_compiler.api.cli:main"}
    assert not (ROOT / "src" / "reverse_add").exists()


def test_reverse_add_slab_removed_and_spatial_prefix_has_one_owner(
    _production_facts: tuple[_SourceFacts, ...],
) -> None:
    src = ROOT / "src" / "number_compiler"
    for removed in (
        "carry_slab_power.py",
        "carry_slab_behavioral.py",
        "carry_slab_jump.py",
        "carry_boundary_power.py",
    ):
        assert not (src / removed).exists(), removed

    definitions = _production_definitions(_production_facts)
    assert definitions.get("FiniteMonoid") == ["arithmetic/carry/prefix_monoid.py"]
    assert definitions.get("FormulaPrefixMonoidProjection") == [
        "arithmetic/carry/prefix_monoid.py"
    ]
    assert definitions.get("compile_formula_prefix_monoid") == [
        "arithmetic/carry/prefix_monoid.py"
    ]
    assert definitions.get("compile_reset_prefix_monoid") == [
        "arithmetic/carry/prefix_monoid.py"
    ]
    assert definitions.get("ReverseAddSpatialIndex") is None
    assert (ROOT / "devtools/experiments/reverse_add/domain.py").is_file()

    formula_sources = "\n".join(
        (src / name).read_text()
        for name in (
            "arithmetic/formula/construction.py",
            "arithmetic/formula/evaluation.py",
            "hashlife/execution/evaluator.py",
            "arithmetic/functions/boolean_residual.py",
        )
    )
    for legacy_kind in (
        "CARRY_SCAN",
        "PREFIX_XOR",
        "SLAB_PAIR_CORE",
        "SLAB_PAIR_BIT",
        "ACTIVE_NEXT",
        "CARRY_EVENT",
        "INTERVAL_TRANSPORT",
        "MODSUM",
    ):
        assert legacy_kind not in formula_sources

    pair = (src / "arithmetic/formula/pair_algebra.py").read_text()
    digit = (src / "arithmetic/fields/digit_formula.py").read_text()
    assert "compile_reset_prefix_monoid" in pair
    assert "compile_formula_prefix_monoid" in digit

    collatz = (src / "sequences/collatz/parity.py").read_text()
    assert definitions.get("CollatzParityPrefixIndex") == [
        "sequences/collatz/parity.py"
    ]
    assert "collatz_parity_prefix_index(word, width)" in collatz
    advance = collatz[
        collatz.index("def advance_collatz_parity") : collatz.index(
            "def valid_physical_branch_count"
        )
    ]
    assert "_prefix_duration(word, mid)" not in advance
    assert "collatz_parity_prefix_index(word, width)" in advance
