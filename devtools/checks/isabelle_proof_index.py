"""Build and validate the Isabelle proof inventory from authored sources."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from devtools.checks.isabelle_oracle_audit import (
    audited_theorems,
    declared_oracle_audit_bundles,
    validate_bundle_members,
)
from devtools.checks.isabelle_ownership_history import ownership_history
from devtools.checks.isabelle_registry import discover_sessions, root_files
from devtools.checks.isabelle_source_analysis import (
    IsabelleAnalysis,
    IsabelleDeclaration,
    analysis_report,
    analyze_isabelle_source,
    extract_isabelle_declarations,
)
from devtools.checks.isabelle_syntax import (
    executable_text,
    first_documentation_scope,
    global_simp_registrations,
    navigation_text,
    parse_theory_header,
    unquoted_matches,
    unquoted_numeric_case_facts,
)
from devtools.checks.ownership_policy import (
    check_isabelle_resource_owner,
    isabelle_ownership_violations,
)
from devtools.paths import isabelle_root, repository_root

ROOT = repository_root()
ISABELLE = isabelle_root(ROOT)

_ML_FILE_COMMAND = re.compile(r"(?m)^[ \t]*ML_file\b")
_ML_FILE_ARGUMENT = re.compile(
    r"""^[ \t]*(?:"((?:\\.|[^"\\])*)"|([^ \t\r\n]+))[ \t]*$"""
)

# These links describe implementation or executable-reference counterparts.  An
# empty mapping is deliberate: a standalone mathematical theory must not be
# presented as a production refinement merely because it is registered.
COUNTERPARTS: dict[str, tuple[str, ...]] = {
    "Homogeneous_Growth_Scale": (
        "src/number_compiler/arithmetic/fields/homogeneous_growth.py",
        "src/number_compiler/arithmetic/fields/mechanical_readout.py",
        "tests/arithmetic/fields/test_homogeneous_growth.py",
    ),
    "Weighted_Partial_Growth_Action": (
        "devtools/verification/reverse_growth_moore.py",
        "tests/sequences/reverse_add/test_growth_moore_verification.py",
    ),
    "Comma_Normalized_Cycle": (
        "src/number_compiler/sequences/comma/cycle_actions.py",
        "src/number_compiler/sequences/comma/action_arena.py",
        "src/number_compiler/sequences/comma/power.py",
        "tests/sequences/comma/test_cycle_action_reuse.py",
    ),
    "Source_Cache_Consumption": (
        "src/number_compiler/sequences/collatz/source_cylinder_cache.py",
        "src/number_compiler/sequences/collatz/temporal_run_quotient.py",
        "src/number_compiler/hashlife/execution/dyadic_return_transport.py",
        "tests/sequences/collatz/test_source_cylinder_cache.py",
    ),
    "Reverse_Uniform_Runs": (
        "devtools/experiments/reverse_add/factored_planes.py",
        "devtools/verification/reverse_run_successor.py",
        "tests/sequences/reverse_add/test_factored_carrier.py",
    ),
    "Maximal_Run_Arithmetic": (
        "src/number_compiler/sequences/collatz/temporal_run_quotient.py",
        "src/number_compiler/sequences/antihydra/arithmetic_images.py",
        "tests/sequences/collatz/test_temporal_run_quotient.py",
    ),
    "Comma_Macro_Constructor": (),
    "Comma_Canonical_Domain": (
        "src/number_compiler/sequences/comma/domain.py",
        "src/number_compiler/sequences/comma/boundary_chart.py",
        "tests/sequences/comma/test_boundary_chart.py",
    ),
    "Comma_Vieta_Root_Frame": (),
    "Comma_Root_Pair_Port": (),
    "Comma_Pair_Field": (),
    "Comma_Native19_Carry": (
        "src/number_compiler/arithmetic/formula/decimal_pair_coordinates.py",
        "tests/arithmetic/formula/test_decimal_cocycle_coordinates.py",
    ),
    "Comma_Reset_Germ": (),
    "Comma_Factored_Port_Carrier": ("tests/sequences/comma/test_punctured_port.py",),
    "Comma_Compact_Decade_Classifier": (),
    "Comma_Decade_Occurrence_Semantic": (),
    "Comma_Decade_Occurrence_Lift": (),
    "Comma_C1_Occurrence": (
        "src/number_compiler/sequences/comma/carry_generator.py",
        "tests/sequences/comma/test_carry_generator.py",
    ),
    "Comma_Recursive_Pair_Language": (
        "devtools/verification/comma_pair_language.py",
        "tests/sequences/comma/test_pair_language.py",
    ),
    "Comma_Radix9_Pair_Word": (
        "devtools/verification/comma_temporal_observers.py",
        "tests/sequences/comma/test_temporal_observers.py",
    ),
    "Comma_Even_Port_Action": ("tests/sequences/comma/test_pair_language.py",),
    "Comma_Temporal_Port_Cover": (
        "src/number_compiler/sequences/comma/temporal_cover.py",
        "tests/sequences/comma/test_temporal_cover.py",
    ),
    "Comma_Temporal_Action": (
        "src/number_compiler/sequences/comma/temporal_cover.py",
        "tests/sequences/comma/test_temporal_cover.py",
    ),
    "Comma_Entry_Port_Anchor": (),
    "Comma_Entry_Port_Refinement": (),
    "Comma_Prefix_Selection": (
        "src/number_compiler/sequences/comma/arithmetic.py",
        "tests/sequences/comma/test_punctured_port.py",
    ),
    "Comma_C1_Phase": (
        "src/number_compiler/sequences/comma/carry_generator.py",
        "tests/sequences/comma/test_carry_generator.py",
    ),
    "Comma_C1_Phase_Power": (
        "src/number_compiler/sequences/comma/carry_generator.py",
        "tests/sequences/comma/test_carry_generator.py",
    ),
    "Comma_C1_Return": (
        "src/number_compiler/sequences/comma/carry_generator.py",
        "tests/sequences/comma/test_carry_generator.py",
    ),
    "Comma_C1_Borrow_Cocycle": (
        "src/number_compiler/sequences/comma/borrow_cocycle.py",
        "tests/sequences/comma/test_borrow_cocycle.py",
    ),
    "Comma_C1_Boundary_Carry": (
        "src/number_compiler/sequences/comma/carry_generator.py",
        "tests/sequences/comma/test_carry_generator.py",
    ),
    "Comma_C1_Carry_Cylinder": (
        "src/number_compiler/sequences/comma/carry_generator.py",
        "tests/sequences/comma/test_carry_generator.py",
    ),
    "Comma_Finite_Transition": (
        "src/number_compiler/sequences/comma/boundary_chart.py",
        "src/number_compiler/sequences/comma/boundary_quotient.py",
        "tests/sequences/comma/test_boundary_chart.py",
    ),
    "Comma_Power_Residue": (
        "src/number_compiler/sequences/comma/arithmetic.py",
        "tests/sequences/comma/test_boundary_chart.py",
    ),
    "Comma_Frobenius_Recurrence": (
        "src/number_compiler/sequences/comma/arithmetic.py",
        "tests/sequences/comma/test_frobenius_recurrence.py",
    ),
    "Comma_Carry_Core_Quotient": (
        "src/number_compiler/sequences/comma/arithmetic.py",
        "tests/sequences/comma/test_frobenius_recurrence.py",
    ),
    "Comma_Cyclotomic_Clock": (
        "src/number_compiler/sequences/comma/cyclotomic_clock.py",
        "src/number_compiler/sequences/comma/arithmetic.py",
        "tests/sequences/comma/test_cyclotomic_clock.py",
    ),
    "Comma_Decisive_Endpoint_Quotient": (
        "src/number_compiler/sequences/comma/decisive_endpoint.py",
        "tests/sequences/comma/test_b1_quotient.py",
    ),
    "Comma_Compact_B1": (),
    "Comma_Terminal_Weight": (),
    "Comma_Chart_Refinement": (
        "src/number_compiler/sequences/comma/boundary_chart.py",
        "tests/sequences/comma/test_boundary_chart.py",
    ),
    "Comma_Weighted_Selection": (
        "src/number_compiler/sequences/comma/boundary_quotient.py",
        "tests/sequences/comma/test_boundary_scheduler.py",
    ),
    "Comma_Macro_Selection": (
        "src/number_compiler/sequences/comma/boundary_quotient.py",
        "tests/sequences/comma/test_boundary_scheduler.py",
    ),
    "Comma_Trace_Regression": (
        "tests/sequences/comma/test_boundary_chart.py",
        "tests/sequences/comma/test_boundary_quotient.py",
    ),
    "Comma_Quotient_Totality": (),
    "Comma_Source_Entry_Witness": (),
    "Comma_Source_Unique": (),
    "Comma_Unique_Path": (),
    "Comma_Round_Closure": (),
    "Comma_Decade_Control": (),
    "Comma_Round_Witness": (),
    "Comma_Decade_Observation": (),
    "Comma_Decade_Rank_Data": (),
    "Comma_Total_Macro": (),
    "Comma_Decade_Residual_Core": (),
    "Comma_Short_Phase": (),
    "Comma_Entry_Arithmetic": (),
    "Comma_Fast_Arithmetic": (),
    "Comma_Fast_Control": (),
    "Comma_Fast_Kernel": (),
    "Comma_Fast_Kernel_Smoke": (),
    "Comma_Sector_Alphabet": (),
    "Comma_Decade_Helix": (),
    "Comma_Decade_Orbit_Quotient": ("devtools/experiments/comma/temporal_masks.py",),
    "Comma_Sparse_Power_Algebra": (),
    "Comma_Sparse_Power_Smoke": (),
    "Comma_Sparse_Power_Instance": (),
    "Comma_Response_Rows": (),
    "Comma_Sector_Rows_Core": (),
    "Comma_Native_Summary": (),
    "Comma_Native_Summary_Instance": (),
    "Comma_Native_Summary_Occurrence": (),
    "Comma_Native_Boundary": (),
    "Comma_Decade_Masks": ("devtools/experiments/comma/temporal_masks.py",),
    "Comma_Orbit_Words": ("devtools/experiments/comma/temporal_masks.py",),
    "Comma_Sector_Response": ("devtools/experiments/comma/temporal_masks.py",),
    "Comma_Sector_Response_Check": ("devtools/experiments/comma/temporal_masks.py",),
    "Comma_Sector_Response_Smoke": ("devtools/experiments/comma/temporal_masks.py",),
    "Comma_Sector_Mask_Constructor": ("devtools/experiments/comma/temporal_masks.py",),
    "Comma_Sector_Base_Masks": ("devtools/experiments/comma/temporal_masks.py",),
    "Comma_Sparse_Temporal_Composition": (
        "devtools/experiments/comma/temporal_masks.py",
    ),
    "Comma_Sector_Mask_Smoke": ("devtools/experiments/comma/temporal_masks.py",),
    "Comma_Sector_Mask_Instance": ("devtools/experiments/comma/temporal_masks.py",),
    "Comma_Mask_Safety": ("devtools/experiments/comma/temporal_masks.py",),
    "Comma_Decade_Blocks": (),
    "Comma_Powered_Boundary": (),
    "Comma_Decade_Layer_Check": (),
    "Comma_Decade_Layer_Smoke": (),
    "Comma_Decade_Layer_Instance": (),
    "Comma_Fast_Decade_Rank": (),
    "Comma_Decade_Summary_Transport": (),
    "Comma_Fast_Rank_Check": (),
    "Comma_Fast_Rank_Smoke": (),
    "Comma_Closed_Near": (),
    "Comma_Near_Period": (),
    "Comma_Fast_Totality_Check": (),
    "Comma_Fast_Totality_Smoke": (),
    "Comma_Fast_Totality": (),
    "Comma_Fast_Future_Check": (),
    "Comma_Future_Cycle_Check": (),
    "Comma_Rank_Data": (),
    "Comma_Rank_Data_N": (),
    "Comma_Rank_Data_Z": (),
    "Comma_Future_Instance": (),
    "Comma_Future_Literal_Bridge": (),
    "Comma_Future_Losing_Lift": (),
    "Comma_Future_Infinite_Lift": (),
    "Comma_Branch_Induction": (),
    "Comma_Branch_Instance": (),
    "Comma_Branch_Period": (),
    "Comma_Selected_Return_Blocks": (),
    "Comma_Selected_Block_Smoke": (),
    "Comma_Branch_Period_Instance": (),
    "Comma_Return_Induction": (),
    "Comma_Return_Engine": (),
    "Comma_Return_Instance": (),
    "Comma_Return_Source": (),
    "Comma_Future_Checked_Instance": (),
    "Comma_Future_Source": (),
    "Comma_Global_Future_Safety": (),
    "Comma_Global_Root_Safety": (
        "devtools/verification/comma_root_entries.py",
        "tests/sequences/comma/test_root_entries.py",
    ),
    "Comma_Round_Phase_Slice": (),
    "Comma_Round_Weights": (),
    "Comma_Weighted_Run_Germ": (),
    "Comma_Weighted_Round": (),
    "Comma_Run_Germ": (
        "src/number_compiler/sequences/comma/boundary_quotient.py",
        "tests/sequences/comma/test_boundary_chart.py",
    ),
    "Comma_Chart_Action": (
        "src/number_compiler/sequences/comma/boundary_chart.py",
        "tests/sequences/comma/test_boundary_chart.py",
    ),
    "Comma_Terminal_Event": (
        "src/number_compiler/sequences/comma/boundary_chart.py",
        "tests/sequences/comma/test_boundary_chart.py",
    ),
    "Comma_Source_Entry": (
        "src/number_compiler/sequences/comma/power.py",
        "tests/sequences/comma/test_comma_power.py",
    ),
    "Comma_Finite_Period": (
        "src/number_compiler/sequences/comma/boundary_quotient.py",
    ),
    "Comma_Boundary_Primitives": (),
    "Comma_Literal_Path": (),
    "Comma_Weighted_Macro": (),
    "Comma_Future_Selector": (),
    "Comma_Future_Safety": (),
    "Comma_Checked_Ranks": (),
    "Comma_Period_Guard": (
        "src/number_compiler/sequences/comma/arithmetic.py",
        "devtools/experiments/comma/macro_lifting.py",
    ),
    "Comma_Exact_Phase_Guard": (
        "src/number_compiler/sequences/comma/arithmetic.py",
        "devtools/experiments/comma/macro_lifting.py",
        "tests/sequences/comma/test_macro_lifting.py",
    ),
    "Comma_Child_Classification": (
        "src/number_compiler/sequences/comma/arithmetic.py",
        "src/number_compiler/sequences/comma/boundary_quotient.py",
        "tests/sequences/comma/test_boundary_quotient.py",
    ),
    "Comma_Affine_Ray": (
        "devtools/experiments/comma/macro_lifting.py",
        "tests/sequences/comma/test_macro_lifting.py",
    ),
    "Comma_Boundary_Quotient": (
        "src/number_compiler/sequences/comma/boundary_quotient.py",
        "devtools/experiments/comma/macro_lifting.py",
        "tests/sequences/comma/test_macro_lifting.py",
    ),
    "Comma_Child_Cylinder": (
        "src/number_compiler/sequences/comma/arithmetic.py",
        "tests/sequences/comma/test_comma_power.py",
    ),
    "Comma_Decimal_Parent": ("devtools/experiments/comma/forest_certificate.py",),
    "Comma_Root_Forest": (
        "devtools/experiments/comma/forest_certificate.py",
        "src/number_compiler/sequences/comma/certificates.py",
    ),
    "S_Arithmetic_Skew": (
        "src/number_compiler/arithmetic/fields/skew_transfer.py",
        "tests/arithmetic/fields/test_integer_cylinder_chart.py",
    ),
    "Dyadic_Source_Lift": (
        "src/number_compiler/hashlife/execution/dyadic_return_reuse.py",
        "src/number_compiler/hashlife/execution/dyadic_return_transport.py",
        "src/number_compiler/hashlife/execution/dyadic_return_observers.py",
        "tests/hashlife/execution/test_dyadic_effect_reuse.py",
        "tests/arithmetic/fields/test_integer_cylinder_chart.py",
    ),
    "Dyadic_Balanced_Worklist": (
        "src/number_compiler/hashlife/execution/dyadic_return_transport.py",
        "tests/hashlife/execution/test_balanced_proof_refinement.py",
    ),
    "Dyadic_Balanced_Arithmetic": (
        "src/number_compiler/hashlife/execution/dyadic_return_transport.py",
        "src/number_compiler/hashlife/execution/dyadic_return_reuse.py",
        "tests/hashlife/execution/test_balanced_proof_refinement.py",
    ),
    "Prefix_Effect": (),
    "Dyadic_Prefix_Summary": (
        "src/number_compiler/hashlife/execution/dyadic_return_transport.py",
        "tests/hashlife/execution/test_balanced_proof_refinement.py",
    ),
    "Dyadic_Support_Descent": (
        "src/number_compiler/hashlife/execution/dyadic_return_observers.py",
        "tests/hashlife/execution/test_balanced_proof_refinement.py",
    ),
    "Balanced_Dyadic_Families": (
        "src/number_compiler/sequences/collatz/physical_images.py",
        "src/number_compiler/sequences/antihydra/arithmetic_images.py",
        "src/number_compiler/sequences/antihydra/mahler_action.py",
        "tests/hashlife/execution/test_balanced_proof_refinement.py",
    ),
    "Collatz_Reduced_Precision": (
        "devtools/experiments/collatz/powered_boundary_germs.py",
        "tests/hashlife/execution/test_powered_boundary_germs.py",
    ),
    "Collatz_Parity_Shift_Germ": (
        "src/number_compiler/arithmetic/fields/two_adic.py",
        "src/number_compiler/sequences/collatz/parity.py",
        "tests/sequences/collatz/test_collatz_parity.py",
    ),
    "Dyadic_Parity_Inverse_Arithmetic": (
        "src/number_compiler/arithmetic/fields/two_adic.py",
        "tests/sequences/collatz/test_collatz_parity.py",
    ),
    "Reverse_Threshold_Cocycle": (
        "devtools/experiments/reverse_add/cocycle_carrier.py",
        "devtools/experiments/reverse_add/factored_power.py",
        "tests/sequences/reverse_add/test_cocycle_carrier.py",
    ),
    "Reverse_Boundary_Germ_Local": (
        "src/number_compiler/arithmetic/formula/decimal_pair_coordinates.py",
        "devtools/experiments/reverse_add/temporal_boundary_germ.py",
        "tests/validation/proofs/reverse_add/test_temporal_boundary_germ.py",
    ),
    "Mahler_Spatial_Carry_Pump": (
        "src/number_compiler/sequences/collatz/root_germs.py",
        "tests/sequences/collatz/test_hensel_prefix_occurrences.py",
        "devtools/experiments/antihydra/spatial_carry.py",
        "devtools/experiments/antihydra/future_grammar.py",
        "tests/validation/proofs/test_mahler_spatial_carry.py",
        "tests/validation/proofs/test_mahler_f5_production_bridge.py",
    ),
    "Reverse_Centered_Future_Grammar": (
        "devtools/experiments/reverse_add/centered_future.py",
        "tests/validation/proofs/reverse_add/test_centered_future_grammar.py",
    ),
    "Reverse_Growth_Run_Admission": (
        "src/number_compiler/arithmetic/polynomials/frobenius_sector.py",
        "tests/validation/proofs/reverse_add/test_source_growth_admission.py",
    ),
    "Mahler_Reachable_Repetition": (
        "devtools/experiments/antihydra/future_grammar.py",
        "tests/validation/proofs/test_mahler_future_grammar.py",
    ),
    "Mahler_Source_Cylinder_Transport": (
        "devtools/experiments/antihydra/source_safety.py",
        "tests/validation/proofs/test_mahler_source_transport.py",
    ),
    "Mahler_Source_Event_Safety": (
        "src/number_compiler/sequences/antihydra/mahler_action.py",
        "tests/api/test_antihydra_mahler_action.py",
        "devtools/experiments/antihydra/source_safety.py",
        "devtools/experiments/antihydra/source_observers.py",
        "tests/validation/proofs/test_mahler_source_observers.py",
    ),
    "Mahler_Joint_Quotient_Algebra": (
        "src/number_compiler/arithmetic/fields/branch_quotients.py",
        "tests/arithmetic/fields/test_branch_quotients.py",
        "tests/validation/proofs/test_mahler_source_observers.py",
    ),
    "Antihydra_Mahler_Associated_Action": (
        "src/number_compiler/sequences/antihydra/arithmetic_images.py",
        "src/number_compiler/sequences/antihydra/mahler_action.py",
        "tests/api/test_antihydra_mahler_action.py",
        "devtools/experiments/antihydra/mahler_predicate.py",
        "tests/validation/proofs/test_mahler_predicate_action.py",
    ),
    "Collatz_Saturated_Threshold_Composition": (
        "src/number_compiler/arithmetic/fields/threshold_envelope.py",
        "src/number_compiler/sequences/collatz/saturated_future.py",
        "tests/arithmetic/fields/test_threshold_envelope.py",
    ),
    "Mahler_Cyclotomic_Boundary": (
        "devtools/experiments/antihydra/source_safety.py",
        "tests/validation/proofs/test_mahler_cyclotomic_boundary.py",
    ),
    "Generated_Mahler_Safety": (
        "tests/validation/proofs/test_mahler_safety_cylinders.py",
    ),
    "Mahler_Safety_Ledger_Separation": (
        "tests/validation/proofs/test_mahler_safety_cylinders.py",
    ),
    "Cylinder_Radial_Event_Clock": (
        "devtools/experiments/reverse_add/radial_event_clock.py",
        "tests/validation/proofs/reverse_add/test_radial_event_clock.py",
    ),
    "Cylinder_Radial_Hypergeometric_Elimination": (),
    "Cylinder_Innovation_Transport": (
        "src/number_compiler/arithmetic/fields/symbolic_innovation.py",
        "src/number_compiler/arithmetic/fields/innovation_substitution.py",
        "tests/arithmetic/fields/test_innovation_pullback.py",
    ),
    "Cylinder_Live_Forcing_Reduction": (
        "src/number_compiler/arithmetic/fields/live_forcing.py",
        "tests/arithmetic/fields/test_live_forcing.py",
    ),
    "Cylinder_Forcing_Alphabet": (
        "src/number_compiler/arithmetic/carry/carry_monoid.py",
        "tests/arithmetic/fields/test_live_carry_projection.py",
    ),
    "Cylinder_Residue_Carry_SLP": (
        "src/number_compiler/arithmetic/automata/residue_carry_slp.py",
        "tests/arithmetic/automata/test_residue_carry_slp.py",
    ),
}


def _scope(text: str) -> str:
    return first_documentation_scope(text)


def _declaration_records(
    declarations: tuple[IsabelleDeclaration, ...],
) -> tuple[dict[str, object], ...]:
    """Render an already parsed lexical inventory for navigation output."""
    rows: list[dict[str, object]] = []
    for declaration in declarations:
        if declaration.command not in {"lemma", "theorem", "corollary"}:
            continue
        body = declaration.body.lstrip().removeprefix(declaration.name)
        proofs = unquoted_matches(re.compile(r"(?m)(?:^|\s)(?:by|proof)\s"), body)
        proof = proofs[0] if proofs else None
        statement = (
            body[: proof.start()] if proof is not None else body.split("\n\n", 1)[0]
        )
        rows.append(
            {
                "name": declaration.name,
                "line": declaration.line,
                "statement_and_assumptions": statement.strip(),
            }
        )
    return tuple(rows)


def _declarations(text: str) -> tuple[dict[str, object], ...]:
    """Lexical navigation inventory; Isabelle remains the authority on statements."""
    return _declaration_records(extract_isabelle_declarations(text))


def _ml_file_references(text: str, path: Path) -> tuple[str, ...]:
    """Read authored ``ML_file`` paths while ignoring quoted fake commands."""
    clean = navigation_text(text)
    references: list[str] = []
    for command in unquoted_matches(_ML_FILE_COMMAND, clean):
        line_end = clean.find("\n", command.start())
        if line_end < 0:
            line_end = len(clean)
        argument = _ML_FILE_ARGUMENT.fullmatch(clean[command.end() : line_end])
        if argument is None:
            raise ValueError(f"{path}: unsupported ML_file target")
        reference = argument.group(1) or argument.group(2)
        if not reference or "\\" in reference:
            raise ValueError(f"{path}: unsupported ML_file target")
        references.append(reference)
    return tuple(references)


def _theory_import_closure(
    theory: str, imports_by_theory: dict[str, tuple[str, ...]]
) -> set[str]:
    reached = {theory}
    pending = [theory]
    while pending:
        source = pending.pop()
        for imported in imports_by_theory[source]:
            target = Path(imported.split(".")[-1]).name
            if target in imports_by_theory and target not in reached:
                reached.add(target)
                pending.append(target)
    return reached


def build_index() -> dict[str, object]:
    sessions = discover_sessions(ISABELLE)
    source_texts: dict[str, str] = {}
    source_texts_by_path: dict[Path, str] = {}
    source_analyses: dict[Path, IsabelleAnalysis] = {}
    declared: dict[
        str, tuple[Path, tuple[str, ...], str, tuple[str, ...], tuple[str, ...]]
    ] = {}
    for path in sorted(ISABELLE.rglob("*.thy")):
        text = path.read_text()
        invalid_case_facts = unquoted_numeric_case_facts(text)
        if invalid_case_facts:
            raise ValueError(
                f"{path}: quote numeric case fact names at lines {invalid_case_facts}"
            )
        # One immutable analysis object serves the per-theory inventory and
        # whole-tree duplicate/unused analysis below. Keeping it local to this
        # build preserves freshness when an authored source changes.
        source_analysis = analyze_isabelle_source(text, path, include_duplicates=False)
        name, imports = parse_theory_header(text, path)
        dangerous = global_simp_registrations(text, "gcd_nat.simps")
        if dangerous:
            raise ValueError(
                f"{path}: recursive gcd rule globally registered as simp at "
                f"lines {dangerous}; use closed ground equations"
            )
        if name in declared:
            raise ValueError(f"duplicate theory declaration: {name}")
        source_texts[name] = text
        source_texts_by_path[path] = text
        source_analyses[path] = source_analysis
        declared[name] = (
            path,
            imports,
            _scope(text),
            (),
            _ml_file_references(text, path),
        )

    bundle_definitions: dict[str, tuple[str, tuple[str, ...]]] = {}
    theorem_owners: dict[str, list[str]] = {}
    for theory, (path, _, _, _, _) in declared.items():
        for declaration in source_analyses[path].declarations:
            if declaration.command in {"lemma", "theorem", "corollary", "proposition"}:
                theorem_owners.setdefault(declaration.name, []).append(theory)
        for bundle_name, members in declared_oracle_audit_bundles(source_texts[theory]):
            if bundle_name in bundle_definitions:
                raise ValueError(
                    f"duplicate oracle audit bundle declaration: {bundle_name}"
                )
            bundle_definitions[bundle_name] = (theory, members)
    bundle_members = validate_bundle_members(
        bundle_definitions,
        {name: tuple(owners) for name, owners in theorem_owners.items()},
    )
    executed_bundle_refs: dict[str, set[str]] = {}
    for theory, (path, imports, scope, _, references) in tuple(declared.items()):
        bundle_refs: set[str] = set()
        audit = audited_theorems(
            source_texts[theory],
            bundle_members=bundle_members,
            executed_bundles=bundle_refs,
        )
        declared[theory] = (path, imports, scope, audit, references)
        if bundle_refs:
            executed_bundle_refs[theory] = bundle_refs

    ownership_errors = isabelle_ownership_violations(
        ROOT,
        sessions=sessions,
        theory_headers={
            path: (name, imports) for name, (path, imports, _, _, _) in declared.items()
        },
    )
    if ownership_errors:
        raise ValueError("invalid proof ownership: " + "; ".join(ownership_errors))
    isabelle_path = ISABELLE.resolve()
    ml_references: dict[Path, list[str]] = {}
    for theory, (path, _, _, _, references) in declared.items():
        for reference in references:
            ml_target = (path.parent / reference).resolve()
            if not ml_target.is_relative_to(isabelle_path):
                raise ValueError(
                    f"{path}: ML_file target escapes theory root: {reference}"
                )
            if not ml_target.is_file():
                raise ValueError(f"{path}: missing ML_file target {ml_target}")
            check_isabelle_resource_owner(isabelle_path, path.resolve(), ml_target)
            ml_references.setdefault(ml_target, []).append(theory)

    authored_ml: set[Path] = set()
    for path in ISABELLE.rglob("*.ML"):
        ml_target = path.resolve()
        if not ml_target.is_relative_to(isabelle_path):
            raise ValueError(f"authored ML path escapes theory root: {path}")
        authored_ml.add(ml_target)
    ml_paths = sorted(authored_ml | set(ml_references))
    ml_entries = [
        {
            "path": path.relative_to(ROOT).as_posix(),
            "referenced_by": tuple(sorted(ml_references.get(path, []))),
        }
        for path in ml_paths
    ]

    canonical_session_dirs: dict[Path, str] = {}
    for session in sessions:
        session_path = (isabelle_path / session.directory).resolve()
        if not session_path.is_relative_to(isabelle_path):
            raise ValueError(
                f"{session.name}: session directory escapes theory root: "
                f"{session.directory}"
            )
        previous = canonical_session_dirs.get(session_path)
        if previous is not None:
            raise ValueError(
                f"duplicate canonical Isabelle session directory {session_path}: "
                f"{previous} and {session.name}"
            )
        canonical_session_dirs[session_path] = session.name

    registered: dict[str, str] = {}
    declared_paths = {row[0].resolve(): name for name, row in declared.items()}
    for session in sessions:
        for reference in session.theories:
            path = (ISABELLE / session.directory / f"{reference}.thy").resolve()
            if not path.is_relative_to(ISABELLE.resolve()):
                raise ValueError(
                    f"{session.name}: theory path escapes theory root: {reference}"
                )
            if not path.is_file():
                raise ValueError(f"{session.name}: missing registered theory {path}")
            registered_name = declared_paths.get(path)
            if registered_name is None or registered_name != path.stem:
                raise ValueError(
                    f"{session.name}: theory declaration differs from file {path}"
                )
            if registered_name in registered:
                raise ValueError(
                    f"theory {registered_name} registered in {registered[registered_name]} and {session.name}"
                )
            registered[registered_name] = session.name

    reverse: dict[str, list[str]] = {name: [] for name in declared}
    for source, (_, imports, _, _, _) in declared.items():
        for imported in imports:
            target = Path(imported.split(".")[-1]).name
            if target in reverse:
                reverse[target].append(source)

    imports_by_theory = {name: row[1] for name, row in declared.items()}
    closure_roots = set(registered) | set(executed_bundle_refs)
    import_closures = {
        theory: _theory_import_closure(theory, imports_by_theory)
        for theory in closure_roots
    }
    reachable: set[str] = set()
    for root_theory in registered:
        reachable.update(import_closures[root_theory])

    unreachable = sorted(set(declared) - reachable)
    if unreachable:
        raise ValueError(f"unregistered and unreachable theories: {unreachable}")

    consumers_by_bundle: dict[str, set[str]] = {
        name: set() for name in bundle_definitions
    }
    for consumer, bundle_refs in executed_bundle_refs.items():
        for bundle_name in bundle_refs:
            owner = bundle_definitions[bundle_name][0]
            if owner not in import_closures[consumer]:
                raise ValueError(
                    f"oracle audit bundle {bundle_name} executed by {consumer}, "
                    f"which does not import its owner {owner}"
                )
            if consumer in registered:
                consumers_by_bundle[bundle_name].add(consumer)
    required_sessions_by_bundle: dict[str, set[str]] = {}
    for bundle_name, (owner, _) in bundle_definitions.items():
        owner_session = registered.get(owner)
        if owner_session is not None:
            required_sessions = {owner_session}
        else:
            owner_path = declared[owner][0].resolve()
            containing_sessions = tuple(
                (len(directory.parts), session_name)
                for directory, session_name in canonical_session_dirs.items()
                if owner_path.is_relative_to(directory)
            )
            if containing_sessions:
                deepest = max(depth for depth, _ in containing_sessions)
                required_sessions = {
                    session_name
                    for depth, session_name in containing_sessions
                    if depth == deepest
                }
            else:
                required_sessions = {
                    registered[root]
                    for root in registered
                    if owner in import_closures[root]
                }
        if not required_sessions:
            raise ValueError(
                f"oracle audit bundle {bundle_name} has no registered owning session"
            )
        required_sessions_by_bundle[bundle_name] = required_sessions
        missing_sessions = sorted(
            session
            for session in required_sessions
            if not any(
                registered.get(consumer) == session
                and owner in import_closures[consumer]
                for consumer in consumers_by_bundle[bundle_name]
            )
        )
        if missing_sessions:
            raise ValueError(
                f"oracle audit bundle {bundle_name} is not executed in its owning "
                f"registered session(s): {missing_sessions}"
            )

    valid_consumers_by_bundle = {
        bundle_name: {
            consumer
            for consumer in consumers
            if registered.get(consumer) in required_sessions_by_bundle[bundle_name]
        }
        for bundle_name, consumers in consumers_by_bundle.items()
    }

    delegated_theories = {
        bundle_definitions[bundle_name][0]
        for bundle_name, consumers in valid_consumers_by_bundle.items()
        if any(consumer != bundle_definitions[bundle_name][0] for consumer in consumers)
    }
    missing_audits = sorted(
        name
        for name in reachable
        if not declared[name][3] and name not in delegated_theories
    )
    if missing_audits:
        raise ValueError(
            f"reachable theories without an oracle audit: {missing_audits}"
        )
    for theory, paths in COUNTERPARTS.items():
        if theory not in declared:
            raise ValueError(f"counterpart mapping names unknown theory {theory}")
        missing = [path for path in paths if not (ROOT / path).is_file()]
        if missing:
            raise ValueError(f"{theory}: missing mapped counterparts {missing}")

    entries = []
    token_uses: dict[str, set[str]] = {}
    for theory, contents in source_texts.items():
        contents = executable_text(contents)
        for token in set(re.findall(r"[A-Za-z][A-Za-z0-9_']*", contents)):
            token_uses.setdefault(token, set()).add(theory)
    for name in sorted(declared):
        path, imports, scope, audit, _ = declared[name]
        text = source_texts[name]
        declarations = _declaration_records(source_analyses[path].declarations)
        uses = {}
        for row in declarations:
            theorem = str(row["name"])
            uses[theorem] = tuple(sorted(token_uses.get(theorem, set()) - {name}))
        entries.append(
            {
                "theory": name,
                "path": path.relative_to(ROOT).as_posix(),
                "session": registered.get(name),
                "imports": imports,
                "imported_by": sorted(reverse[name]),
                "oracle_audit_theorems": audit,
                "delegated_oracle_audit_bundles": tuple(
                    sorted(
                        bundle_name
                        for bundle_name, (owner, _) in bundle_definitions.items()
                        if owner == name
                    )
                ),
                "scope": scope,
                "declarations": declarations,
                "lexical_uses_including_ML_and_attributes": uses,
                "verification_command": (
                    ".venv/bin/python -m devtools.checks.release --suite proofs "
                    f"--session {registered[name]}"
                    if name in registered
                    else "build an importing session"
                ),
                "counterparts": COUNTERPARTS.get(name, ()),
            }
        )
    return {
        "schema_version": 1,
        "ownership_history": ownership_history(
            ROOT, sessions, source_analyses, source_texts_by_path
        ),
        "root": "proofs/isabelle",
        "registrations": [
            path.relative_to(ROOT).as_posix() for path in root_files(ISABELLE)
        ],
        "ml_files": ml_entries,
        "source_analysis": analysis_report(
            ISABELLE, source_texts_by_path, source_analyses
        ),
        "sessions": [
            {
                "session": session.name,
                "directory": session.directory.as_posix(),
                "audit_only": "audit" in session.directory.parts,
                "parent": session.parent,
                "dependencies": session.dependencies,
                "theories": session.theories,
            }
            for session in sessions
        ],
        "theories": entries,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json",
        type=Path,
        help="write the complete generated index; validation always runs",
    )
    options = parser.parse_args()
    index = build_index()
    if options.json is not None:
        options.json.write_text(json.dumps(index, indent=2) + "\n")
    sessions = index["sessions"]
    theories = index["theories"]
    if not isinstance(sessions, list) or not isinstance(theories, list):
        raise TypeError("proof index collections have invalid types")
    print(
        json.dumps(
            {
                "status": "PASS",
                "sessions": len(sessions),
                "theories": len(theories),
                "output": None if options.json is None else str(options.json),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
