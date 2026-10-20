"""Bounded checks for the untrusted semantic FutureCID certificate tooling."""

import base64
import json
import sys
from copy import deepcopy
from dataclasses import replace
from hashlib import sha256
from pathlib import Path
from typing import Literal

import pytest

from devtools.checks.isabelle_source_analysis import extract_isabelle_declarations
from devtools.checks.isabelle_syntax import executable_text
from devtools.paths import isabelle_root, repository_root
from devtools.verification.comma_c1_audit import candidate_c1_return
from devtools.verification.comma_semantic_future_artifact import (
    CANDIDATE_TABLE_NAMES,
    assert_candidate_data_theory_matches,
    candidate_table_definitions,
    canonical_candidate_bytes,
    encode_unsigned_varints,
    runtime_candidate_bytes,
    runtime_candidate_record_from_isabelle_data,
    runtime_candidate_sha256,
)
from devtools.verification.comma_semantic_future_candidate import (
    Control,
    build_semantic_future_candidate,
    class_rank_candidate,
    decode_unsigned_varints,
    reencode_candidate,
    refine_with_witnesses,
    render_candidate_data_theory,
    validate_class_rows,
    verify_runtime_candidate_hol_data_binding,
    write_new,
)
from devtools.verification.comma_semantic_future_candidate import (
    main as candidate_main,
)
from number_compiler.sequences.comma import future_provider
from number_compiler.sequences.comma.boundary_quotient import (
    BoundaryState,
    construct_macro,
)
from number_compiler.sequences.comma.occurrence import (
    BoundaryOccurrence,
    OccurrencePrefixReturn,
)


def _assert_candidate_theory_data_matches(
    checked_text: str,
    checked_path: Path,
    generated_text: str,
    generated_path: Path,
) -> None:
    assert_candidate_data_theory_matches(
        checked_text, checked_path, generated_text, generated_path
    )


def test_candidate_table_comparison_ignores_masked_ml_audit_suffix() -> None:
    definitions = "\n".join(
        f'definition {name} :: "nat list" where "{name} = [{index}]"'
        for index, name in enumerate(CANDIDATE_TABLE_NAMES)
    )

    def theory(suffix: str) -> str:
        return (
            "theory Candidate_Table_Fixture imports Main begin\n\n"
            f"{definitions}\n\n{suffix}end\n"
        )

    checked_path = Path("Candidate_Table_Fixture.thy")
    generated_path = Path("Generated_Candidate_Table_Fixture.thy")
    checked = theory('ML ‹val _ = if true then () else error "audit"›\n')
    generated = theory("")
    _assert_candidate_theory_data_matches(
        checked, checked_path, generated, generated_path
    )


def test_candidate_varint_map_round_trips_and_rejects_forged_values() -> None:
    ids = (0, 127, 128, 4715)
    packed = encode_unsigned_varints(ids, max_value=14783)
    assert decode_unsigned_varints(packed, max_values=4, max_value=14783) == ids

    with pytest.raises(ValueError):
        encode_unsigned_varints((True,), max_value=14783)
    with pytest.raises(ValueError):
        decode_unsigned_varints(b"\x80\x80\x00", max_values=1, max_value=14783)


def test_candidate_class_rows_reject_missing_or_unknown_ordered_slots() -> None:
    controls: tuple[Control, ...] = (("fork", 2), ("landmine", None))
    rows = ((0, 1), (None, None))
    assert validate_class_rows(controls, rows) == (controls, rows)

    for bad_controls, bad_rows in (
        (controls, ((None, 1), (None, None))),
        (controls, ((0,), (None, None))),
        ((("unknown", None),), ((None, None),)),
    ):
        with pytest.raises(ValueError):
            validate_class_rows(bad_controls, bad_rows)


def test_refinement_retains_control_and_rejects_child_order_collision() -> None:
    states = tuple(BoundaryState("N", 2, residue) for residue in range(4))
    controls: tuple[Control, ...] = (
        ("fork", 2),
        ("fork", 2),
        ("landmine", None),
        ("fork", 3),
    )
    rows = ((2, 3), (3, 2), (None, None), (0, 1))

    class_ids, collisions, _ = refine_with_witnesses(rows, controls, states)

    assert class_ids[0] != class_ids[1]
    witness = next(item for item in collisions if item.round_index == 0)
    assert witness.left_state in (states[0], states[1])
    assert witness.right_state in (states[0], states[1])
    assert witness.left_mapped_children != witness.right_mapped_children


def test_candidate_rank_check_has_unique_unranked_child_and_rejects_forged_row() -> (
    None
):
    controls: tuple[Control, ...] = (("fork", 2), ("landmine", None))
    rows = ((0, 1), (None, None))
    assert class_rank_candidate(controls, rows) == (None, 0)

    with pytest.raises(ValueError):
        class_rank_candidate((("fork", 2),), ((None, None),))


@pytest.mark.parametrize("payload", [b"\x80", b"\x80\x00", b"\xff\x7f", b"\x00\x00"])
def test_candidate_decoder_rejects_truncation_aliases_and_excess(
    payload: bytes,
) -> None:
    with pytest.raises(ValueError):
        decode_unsigned_varints(payload, max_values=1, max_value=14783)


def test_candidate_artifact_write_preserves_existing_evidence(tmp_path: Path) -> None:
    artifact = tmp_path / "candidate.json"
    write_new(artifact, "original")
    with pytest.raises(FileExistsError):
        write_new(artifact, "replacement")
    assert artifact.read_text(encoding="utf-8") == "original"


def test_runtime_candidate_bytes_use_the_consumer_digest_contract() -> None:
    record = {
        "format": "comma-semantic-future-candidate-v1",
        "authority": "untrusted-source-derived-candidate",
        "state_universe": "small test fixture",
        "class_of_state_varint_base64": "AA==",
        "controls": [["landmine", None]],
        "ordered_children": [[None, None]],
        "class_rank_candidate": [0],
        "refinement_rounds": 0,
        "refinement_collision_witnesses": [],
        "seam_is_projected_from_cid": True,
        "seam_projection_collision": None,
    }
    payload = runtime_candidate_bytes(record)
    decoded = json.loads(payload)
    assert set(decoded) == {
        "format",
        "authority",
        "state_universe",
        "class_of_state_varint_base64",
        "controls",
        "ordered_children",
        "class_rank_candidate",
    }
    assert decoded["format"] == future_provider.FUTURE_CANDIDATE_FORMAT
    assert decoded["authority"] == "untrusted-source-derived-candidate"
    assert runtime_candidate_sha256(record) == sha256(payload).hexdigest()
    assert (
        future_provider.future_candidate_sha256(decoded) == sha256(payload).hexdigest()
    )
    with pytest.raises(ValueError, match="requires a v1"):
        runtime_candidate_bytes(
            {**record, "format": future_provider.FUTURE_CANDIDATE_FORMAT}
        )


def test_runtime_candidate_hol_binding_checks_complete_source_map(
    tmp_path: Path,
) -> None:
    """Keep source-map and table binding covered without rebuilding the audit."""
    source_classes = (0,) * future_provider.SOURCE_COUNT
    controls: tuple[Control, ...] = (("landmine", None),)
    children = ((None, None),)
    ranks = (0,)
    record: dict[str, object] = {
        "format": future_provider.FUTURE_CANDIDATE_FORMAT,
        "authority": future_provider.FUTURE_CANDIDATE_AUTHORITY,
        "state_universe": future_provider.FUTURE_SOURCE_UNIVERSE,
        "class_of_state_varint_base64": base64.b64encode(bytes(source_classes)).decode(
            "ascii"
        ),
        "controls": [["landmine", None]],
        "ordered_children": [[None, None]],
        "class_rank_candidate": [0],
    }
    checked_path = tmp_path / "Comma_Semantic_Future_Candidate_Data.thy"
    checked_path.write_text(
        render_candidate_data_theory(source_classes, controls, children, ranks),
        encoding="utf-8",
    )

    digest = verify_runtime_candidate_hol_data_binding(record, checked_path)
    assert digest == future_provider.future_candidate_sha256(record)

    changed = deepcopy(record)
    changed["controls"] = [["fork", 2]]
    changed["ordered_children"] = [[0, 0]]
    changed["class_rank_candidate"] = [None]
    with pytest.raises(ValueError, match="candidate table definitions differ"):
        verify_runtime_candidate_hol_data_binding(changed, checked_path)


@pytest.mark.validation
@pytest.mark.parametrize("kind", ["N", "Z"])
@pytest.mark.parametrize("a", [2, 5, 9])
@pytest.mark.parametrize("residue", [1, 5, 13, 923])
def test_candidate_c1_projection_matches_independent_fragment_accumulation(
    kind: Literal["N", "Z"], a: int, residue: int
) -> None:
    state = BoundaryState(kind, a, residue)
    exponent = residue if residue >= 5 else residue + 924
    macro = construct_macro(state, grouped_near=True)
    reference = OccurrencePrefixReturn(BoundaryOccurrence(state, exponent), macro)
    assert candidate_c1_return(state, macro, 10**exponent) == (
        reference.c1_count,
        reference.terminal_low_suffix,
    )
    foreign = BoundaryState(state.kind, 3 if a != 3 else 4, residue)
    with pytest.raises(ValueError, match="another source"):
        candidate_c1_return(foreign, macro, 10**exponent)
    unsealed = replace(macro)
    with pytest.raises(ValueError, match="component seal"):
        candidate_c1_return(state, unsealed, 10**exponent)
    with pytest.raises(ValueError, match="decimal domain"):
        candidate_c1_return(state, macro, 1)


@pytest.mark.validation
def test_reencoded_runtime_bytes_bind_to_the_checked_hol_candidate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Rebuild the complete 14,784-source audit candidate and bind its tables.

    This is an exhaustive development-artifact integration audit, not a
    production runtime contract. The unit selection retains small tests for
    canonical bytes, malformed records, class-row validation, and exact HOL
    table comparison; this full source-derived rebuild remains available in
    the explicit validation selection.
    """
    candidate = build_semantic_future_candidate()
    v1 = candidate.certificate_record()
    occurrence = candidate.occurrence_payload_record()
    assert v1["format"] == "comma-semantic-future-candidate-v1"
    assert v1["authority"] == "untrusted-source-derived-candidate"

    raw = {
        "format": v1["format"],
        "states": [
            [state.kind, state.a, state.exponent_residue] for state in candidate.states
        ],
        "class_of_state": list(candidate.class_ids),
        "controls": v1["controls"],
        "ordered_children": v1["ordered_children"],
        "occurrence_payloads": occurrence["occurrence_payloads"],
        "refinement_rounds": v1["refinement_rounds"],
        "refinement_collision_witnesses": v1["refinement_collision_witnesses"],
        "seam_is_projected_from_cid": v1["seam_is_projected_from_cid"],
        "seam_projection_collision": v1["seam_projection_collision"],
    }
    raw_path = tmp_path / "raw-v1.json"
    write_new(raw_path, json.dumps(raw, sort_keys=True, separators=(",", ":")))
    runtime_path = tmp_path / "runtime-v2.json"
    occurrence_path = tmp_path / "occurrence.json"
    hol_path = tmp_path / "Comma_Semantic_Future_Candidate_Data.thy"
    result = reencode_candidate(raw_path, runtime_path, occurrence_path, hol_path)

    runtime_bytes = candidate.runtime_candidate_bytes()
    runtime_record = json.loads(runtime_bytes)
    assert runtime_path.read_bytes() == runtime_bytes
    assert runtime_bytes == candidate.runtime_candidate_bytes()
    assert candidate.runtime_candidate_sha256() == sha256(runtime_bytes).hexdigest()
    assert result["candidate_sha256"] == future_provider.future_candidate_sha256(
        runtime_record
    )
    assert runtime_record["format"] == future_provider.FUTURE_CANDIDATE_FORMAT
    assert (
        runtime_record["class_of_state_varint_base64"]
        == v1["class_of_state_varint_base64"]
    )
    assert base64.b64decode(runtime_record["class_of_state_varint_base64"]) == (
        encode_unsigned_varints(
            candidate.class_ids, max_value=len(candidate.states) - 1
        )
    )
    assert runtime_record["controls"] == v1["controls"]
    assert runtime_record["ordered_children"] == v1["ordered_children"]
    assert runtime_record["class_rank_candidate"] == v1["class_rank_candidate"]
    assert (
        not {
            "refinement_rounds",
            "refinement_collision_witnesses",
            "seam_is_projected_from_cid",
            "seam_projection_collision",
        }
        & runtime_record.keys()
    )
    assert "theorem_id" not in runtime_record and "instance_id" not in runtime_record

    checked_hol = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Future_Candidate_Data.thy"
    ).read_text(encoding="utf-8")
    generated_hol = hol_path.read_text(encoding="utf-8")
    checked_path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Future_Candidate_Data.thy"
    )
    assert generated_hol == candidate.isabelle_candidate_data()
    _assert_candidate_theory_data_matches(
        checked_hol, checked_path, generated_hol, hol_path
    )
    assert (
        verify_runtime_candidate_hol_data_binding(runtime_record, checked_path)
        == candidate.runtime_candidate_sha256()
    )

    changed_record = deepcopy(runtime_record)
    changed_controls = changed_record["controls"]
    fork_index = next(
        index for index, control in enumerate(changed_controls) if control[0] == "fork"
    )
    old_coefficient = changed_controls[fork_index][1]
    changed_controls[fork_index][1] = 3 if old_coefficient != 3 else 4
    with pytest.raises(ValueError, match="candidate table definitions differ"):
        verify_runtime_candidate_hol_data_binding(changed_record, checked_path)

    changed_raw = deepcopy(raw)
    changed_raw["controls"] = deepcopy(changed_record["controls"])
    changed_raw_path = tmp_path / "changed-raw-v1.json"
    write_new(
        changed_raw_path,
        json.dumps(changed_raw, sort_keys=True, separators=(",", ":")),
    )
    rejected_outputs = (
        tmp_path / "rejected-runtime-v2.json",
        tmp_path / "rejected-occurrence.json",
        tmp_path / "rejected-candidate-data.thy",
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "comma-semantic-future-candidate",
            "--output",
            str(rejected_outputs[0]),
            "--occurrence-output",
            str(rejected_outputs[1]),
            "--isabelle-data-output",
            str(rejected_outputs[2]),
            "--reencode-input",
            str(changed_raw_path),
            "--checked-isabelle-data",
            str(checked_path),
        ],
    )
    with pytest.raises(ValueError, match="candidate table definitions differ"):
        candidate_main()
    assert all(not path.exists() for path in rejected_outputs)

    extra_record = deepcopy(runtime_record)
    extra_record["controls"].append(list(extra_record["controls"][0]))
    extra_record["ordered_children"].append(list(extra_record["ordered_children"][0]))
    extra_record["class_rank_candidate"].append(extra_record["class_rank_candidate"][0])
    with pytest.raises(ValueError):
        verify_runtime_candidate_hol_data_binding(extra_record, checked_path)

    truncated_record = deepcopy(runtime_record)
    for field in ("controls", "ordered_children", "class_rank_candidate"):
        truncated_record[field] = truncated_record[field][:-1]
    with pytest.raises(ValueError):
        verify_runtime_candidate_hol_data_binding(truncated_record, checked_path)

    changed_format = deepcopy(runtime_record)
    changed_format["format"] = "comma-semantic-future-candidate-v1"
    with pytest.raises(ValueError, match="unsupported semantic future candidate"):
        verify_runtime_candidate_hol_data_binding(changed_format, checked_path)

    changed_controls = list(candidate.class_controls)
    first_control = changed_controls[0]
    changed_controls[0] = (
        ("fork", 2) if first_control[0] == "landmine" else ("landmine", None)
    )
    altered_hol = render_candidate_data_theory(
        candidate.class_ids,
        tuple(changed_controls),
        candidate.class_children,
        candidate.class_ranks,
    )
    altered_path = tmp_path / "Altered_Comma_Semantic_Future_Candidate_Data.thy"
    checked_tables = candidate_table_definitions(checked_hol, checked_path)
    altered_tables = candidate_table_definitions(altered_hol, altered_path)
    assert altered_tables.keys() == checked_tables.keys()
    assert (
        altered_tables["comma_semantic_future_candidate_controls"]
        != (checked_tables["comma_semantic_future_candidate_controls"])
    )
    assert {
        name: body
        for name, body in altered_tables.items()
        if name != "comma_semantic_future_candidate_controls"
    } == {
        name: body
        for name, body in checked_tables.items()
        if name != "comma_semantic_future_candidate_controls"
    }
    with pytest.raises(ValueError, match="candidate table definitions differ"):
        _assert_candidate_theory_data_matches(
            checked_hol, checked_path, altered_hol, altered_path
        )


def test_runtime_candidate_exports_authored_hol_tables_without_rebuilding(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Future_Candidate_Data.thy"
    )
    source_text = source.read_text(encoding="utf-8")
    monkeypatch.setattr(
        "devtools.verification.comma_semantic_future_candidate.build_semantic_future_candidate",
        _reject_candidate_rebuild,
    )
    record = runtime_candidate_record_from_isabelle_data(source_text, source)
    assert future_provider.parse_future_candidate(
        record, charge_work=lambda _amount: None
    ).source_classes

    output = tmp_path / "candidate-v2.json"
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "comma-semantic-future-candidate",
            "--output",
            str(output),
            "--from-isabelle-data",
            str(source),
        ],
    )
    candidate_main()
    assert output.read_bytes() == canonical_candidate_bytes(record)
    assert json.loads(output.read_text(encoding="ascii")) == record


def test_runtime_candidate_hol_literal_parser_rejects_computed_or_changed_tables() -> (
    None
):
    source = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Future_Candidate_Data.thy"
    )
    text = source.read_text(encoding="utf-8")
    changed_type = text.replace(
        'comma_semantic_future_candidate_ranks :: "nat option list"',
        'comma_semantic_future_candidate_ranks :: "nat list"',
        1,
    )
    with pytest.raises(ValueError, match="canonical literal list"):
        runtime_candidate_record_from_isabelle_data(changed_type, source)

    computed_map = text.replace(
        "      1432, 1062, 1061,",
        "      1432 + 0, 1062, 1061,",
        1,
    )
    with pytest.raises(ValueError, match="nonliteral natural"):
        runtime_candidate_record_from_isabelle_data(computed_map, source)


def _reject_candidate_rebuild() -> object:
    raise AssertionError("source export rebuilt arithmetic")


def test_template_publication_uses_global_named_column_ids() -> None:
    root = (
        isabelle_root(repository_root()) / "families/comma/comma_semantic_b1_instance"
    )
    publication = executable_text(
        (root / "semantic_b1_occurrence_publication.ML").read_text(encoding="utf-8")
    )
    assert "fun make_column_dag" in publication
    assert "fun artifact_column_dag" in publication
    assert "val column_dag = artifact_column_dag artifact" in publication
    assert "fun serialize_column_block" in publication
    assert "fun define_column_blocks" in publication
    assert "fun define_global_definitions" in publication
    assert "Global_Theory.add_def" in publication
    assert 'define_global_definitions "artifact-data-batch"' in publication
    assert "val column_block_size = 512" in publication
    assert "fun define_column_data" in publication
    assert "comma_semantic_b1_crt_column_node_dag" in publication
    assert "comma_semantic_b1_crt_column_at" in publication
    assert "Array.sub (constants, child_cid)" not in publication
    assert "template_projection dag_constant" in publication
    assert "val map_column_rows" in publication
    assert '"comma_semantic_b1_crt_template_column_ids"' in publication
    conversion = executable_text(
        (root / "semantic_b1_column_conversion.ML").read_text(encoding="utf-8")
    )
    cache = executable_text(
        (root / "semantic_b1_occurrence_check_cache.ML").read_text(encoding="utf-8")
    )
    projection = executable_text(
        (root / "semantic_b1_template_projection.ML").read_text(encoding="utf-8")
    )
    assert "Comma_Semantic_B1_Template_Projection.make" in conversion
    assert '"semantic_b1_selected_template_projection"' in projection
    assert "comma_semantic_b1_crt_column_templates_nth" in projection
    assert "make_template_projection ctxt" in cache
    assert 'select "templates"' not in cache
    assert '"comma_semantic_b1_crt_lift_column_ids"' in publication
    assert '"comma_semantic_b1_crt_grouped_union_steps"' not in publication
    assert '"comma_semantic_b1_crt_grouped_union_start_ids"' not in publication
    assert "union_trace" not in publication
    assert "compress_template_row" not in publication
    assert "column_term_mdd" not in publication
    assert "Candidate.Terminal_Ref (slot, parent)" in publication
    assert "Candidate.Goto_Ref (slot, child, lift_cid)" in publication
    assert "optional_nat parent" not in publication
    assert '"comma_semantic_b1_crt_lift_refs"' in publication
    assert '"comma_semantic_b1_crt_lift_descriptors"' in publication
    assert "slot_child_indices" not in publication

    constructor = executable_text(
        (root / "semantic_b1_template_constructor.ML").read_text(encoding="utf-8")
    )
    assert "column_term_mdd" not in constructor
    assert "Pending_Child" not in constructor
    assert "Pending_Goto" in constructor
    assert "lift_descriptors" in constructor


def test_compact_lift_contract_keeps_rebase_and_binding_authority() -> None:
    root = isabelle_root(repository_root())
    source = executable_text(
        (
            root
            / "families/comma/comma_semantic_b1"
            / "Comma_Semantic_B1_CRT_Lift_Bindings.thy"
        ).read_text(encoding="utf-8")
    )
    assert "Comma_B1_Lift_Goto_Ref nat nat nat" in source
    local_cover = executable_text(
        (
            root
            / "families/comma/comma_semantic_b1"
            / "Comma_Semantic_B1_CRT_Local_Cover.thy"
        ).read_text(encoding="utf-8")
    )
    assert "comma_semantic_b1_crt_occurrence_beta child_occurrence" in local_cover
    assert "zip lifted_columns child_beta" in local_cover
    assert "comma_semantic_b1_crt_occurrence_rebase child_occurrence" in source
    assert "comma_semantic_b1_crt_lift_descriptor_net_shift descriptor < 924" in source
    assert "[0..<924]" not in source
    assert "template_ids" not in source
    assert "distinct descriptors" not in source


def test_b1_reuses_only_checked_closed_equations_and_constructor_values() -> None:
    root = (
        isabelle_root(repository_root()) / "families/comma/comma_semantic_b1_instance"
    )
    operation = (root / "semantic_b1_crt_operation_conversion.ML").read_text(
        encoding="utf-8"
    )
    validation = operation.split("fun validate request theorem", 1)[1].split(
        "fun complete_value", 1
    )[0]
    assert (
        "Comma_Selected_List_Conversion.make_cached_equation_validator ()" in operation
    )
    assert validation.index("validate_equation request theorem") < validation.index(
        "Termtab.defined (!completed_values) rhs"
    )
    assert "if reused_rhs then {complete = true, nodes = 0}" in validation
    assert "else check_value rhs" in validation
    assert "if not reused_rhs andalso #complete status" in validation

    fixture = operation.split("val fixture_checker = make ()", 1)[1].split(
        "in make () end", 1
    )[0]
    assert "fun make () =" in operation
    assert "first_request aconv second_request" in fixture
    assert "#reused_rhs second_checked" in fixture
    assert "#reused_closed second_checked" in fixture
    assert "#nodes (#status second_checked) = 0" in fixture
    assert "Exn.Exn (ERROR message)" in fixture
    assert "Exn.Exn failure => Exn.reraise failure" in fixture


def test_indexed_child_checks_preserve_source_authority_and_slot_shape() -> None:
    path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1"
        / "Comma_Semantic_B1_CRT_Lift_Bindings.thy"
    )
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            path.read_text(encoding="utf-8"), path
        )
    }
    slot = declarations["comma_semantic_b1_crt_lift_slot_valid"].body
    assert "slot < length refs" in slot
    assert "child_index < length sources" in slot
    assert "sources ! child_index = comma_source_continuation_base child" in slot
    assert "occurrence_at child_index" in slot
    assert "comma_semantic_b1_crt_lift_descriptor_template_cid descriptor" in slot
    assert "ref_slot = slot" in slot
    assert "List.find" not in slot
    local_path = path.with_name("Comma_Semantic_B1_CRT_Local_Cover.thy")
    local_declarations = {
        item.name: item
        for item in extract_isabelle_declarations(local_path.read_text(), local_path)
    }
    local = local_declarations["comma_semantic_b1_crt_lift_local_cover_witness"].body
    assert "length refs = comma_decisive_sector_period source" in local
    assert "occurrence_binding_check parent" in local
    assert "occurrence_geometry" not in local
    assert "occurrence_wellformed" not in local
    assert {
        "comma_semantic_b1_crt_lift_slot_rejects_foreign_child",
        "comma_semantic_b1_crt_lift_slot_rejects_out_of_range_child",
        "comma_semantic_b1_crt_lift_slot_rejects_terminal_goto",
    } <= declarations.keys()
    assert (
        "comma_semantic_b1_crt_lift_local_cover_rejects_truncated_refs"
        in local_declarations
    )
    parent_column = local_declarations["comma_semantic_b1_crt_local_parent_column"].body
    assert "comma_semantic_b1_crt_find_result_index beta result" in parent_column
    assert "columns ! index" in parent_column
    assert "comma_semantic_b1_crt_occurrence_rebase parent" in parent_column
    assert "zip" not in parent_column
    assert "comma_crt_apply" not in parent_column
    cover = local_declarations["comma_semantic_b1_crt_local_piece_covered"].body
    assert "comma_crt_admitted 0 candidate" in cover
    assert "comma_crt_admitted 0 parent_column" in cover
    assert "comma_crt_negate parent_column" in cover
    assert "comma_crt_supported candidate" in cover
    local_slot = local_declarations["comma_semantic_b1_crt_lift_local_slot_valid"].body
    assert local_slot.index("lift_cid < length descriptors") < local_slot.index(
        "descriptors ! lift_cid"
    )
    assert "length lifted_columns = length child_beta" in local_slot


def test_local_cover_checker_reuses_exact_requests_without_repainting_parents() -> None:
    proof_root = isabelle_root(repository_root())
    root = proof_root / "families/comma/comma_semantic_b1_instance"
    bindings = (
        proof_root
        / "families/comma/comma_semantic_b1"
        / "Comma_Semantic_B1_CRT_Lift_Bindings.thy"
    ).read_text(encoding="utf-8")
    checker = executable_text(
        (root / "semantic_b1_occurrence_check_cache.ML").read_text(encoding="utf-8")
    )
    for retired in (
        "lift_source_split_action",
        "lift_slot_paint",
        "crt_lift_witness",
        "lift_descriptor_table_valid",
    ):
        assert retired not in checker
        assert retired not in bindings
    assert (
        "comma_semantic_b1_crt_lift_descriptor_valid templates descriptor" in bindings
    )
    assert "comma_semantic_b1_crt_lift_rejects_malformed_descriptor" in bindings
    publication = (root / "Comma_Semantic_B1_Occurrence_Publication.thy").read_text()
    assert "28 * length comma_semantic_b1_crt_sources" in publication
    assert "lift_descriptor_table_valid" not in publication
    # Publication must retain source/result coverage through the compact
    # theorem, independently of the physical certificate serialization.
    compact_refinement = (
        proof_root
        / "families/comma/comma_semantic_b1"
        / "Comma_Semantic_B1_CRT_Compact_Refinement.thy"
    ).read_text(encoding="utf-8")
    assert (
        "comma_semantic_b1_crt_compact_occurrences_candidate_matches"
        in compact_refinement
    )
    assert "comma_semantic_b1_crt_compact_occurrences_candidate_matches" in publication
    assert "comma_semantic_b1_crt_compact_occurrence_check" in checker
    assert "comma_semantic_b1_crt_lift_local_cover_witness" in compact_refinement
    assert "comma_semantic_b1_crt_used_lift_bindings_checked" in publication
    assert "comma_semantic_b1_crt_local_cover_fixtures" in publication
    # B32 still consumes checked split actions; eliminating B1 reconstruction
    # must not remove this separate demanded conversion.
    assert "comma_crt_occurrence_split_action occurrence" in executable_text(
        (root / "semantic_b1_construction_check.ML").read_text()
    )
    assert "Construction_Check.occurrence_cache_patterns" in checker
