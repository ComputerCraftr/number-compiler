"""Source contracts for graph-backed B32 actions and predecessor transport."""

import re
from pathlib import Path

from devtools.checks.isabelle_proof_index import ml_file_references
from devtools.checks.isabelle_registry import discover_sessions
from devtools.checks.isabelle_source_analysis import extract_isabelle_declarations
from devtools.checks.isabelle_syntax import (
    executable_text,
    parse_theory_header,
    session_dependency_closure,
)
from devtools.paths import isabelle_root, repository_root


def test_c1_normalization_consumer_uses_closed_producer_coordinates() -> None:
    owner = isabelle_root(repository_root()) / "families/comma/comma_c1_occurrence"
    source_path = owner / "Comma_C1_Source_Coefficients.thy"
    definitions = {
        item.name: item.body
        for item in extract_isabelle_declarations(source_path.read_text(), source_path)
        if item.command == "definition"
    }
    pending = [
        "comma_c1_source_raw_coefficient",
        "comma_c1_source_normalized_coefficient",
        "comma_c1_source_carry_coefficient",
    ]
    visited: set[str] = set()
    while pending:
        name = pending.pop()
        if name in visited:
            continue
        visited.add(name)
        body = definitions[name]
        # Iteration and carry summation remain valid specifications, but cannot
        # become the executable definition of a supposedly powered result.
        assert not {
            "comma_fixed_iter",
            "comma_period_displacement",
            "comma_c1_carry_wire_total",
        }.intersection(re.findall(r"\b\w+\b", body)), name
        pending.extend(
            child
            for child in definitions
            if child not in visited and re.search(rf"\b{re.escape(child)}\b", body)
        )
    assert "comma_c1_source_closed_endpoint" in visited

    morphism_path = owner / "Comma_C1_Normalization_Morphism.thy"
    declarations = {
        item.name: item.body
        for item in extract_isabelle_declarations(
            morphism_path.read_text(), morphism_path
        )
    }
    contract = declarations["comma_c1_source_mod32_carry_morphism"]
    assert "comma_c1_source_admitted C H p n" in contract
    assert "characteristic:" in contract
    assert "inverse_root:" in contract
    assert "comma_c1_source_carry_coefficient" in contract
    assert "comma_c1_carry_wire_total" not in contract
    assert "comma_c1_phase_mod32_carry_operator" in contract
    operator = declarations["comma_c1_phase_mod32_carry_operator"]
    assert "comma_c1_phase_admitted C" in operator
    assert "comma_c1_source_admitted" not in operator
    assert "headroom" not in operator
    assert "decimal_normalization_mod32_reconstruct_cut" in operator
    assert "comma_c1_source_carry_coefficient (width-1)" in operator


def test_c1_entry_packet_is_derived_before_physical_source_admission() -> None:
    owner = isabelle_root(repository_root()) / "families/comma/comma_c1_occurrence"
    path = owner / "Comma_C1_Entry_Chart_Refinement.thy"
    declarations = {
        item.name: item.body
        for item in extract_isabelle_declarations(path.read_text(), path)
    }
    packet = declarations["comma_c1_entry_euclidean_packet"]
    assert "A div P" in packet
    assert "A mod P" in packet
    assert "comma_c1_count C n" in packet
    assert "comma_finite_period_guard_bound" in packet
    assert "comma_c1_source_admitted" not in packet
    assert "comma_finite_headroom" not in packet
    assert "comma_c1_powered_entry_chart_bridge" not in packet
    count = declarations["comma_c1_powered_entry_count_closed"]
    assert "comma_c1_entry_euclidean_packet" in count
    assert "comma_c1_powered_entry_chart_bridge" not in count
    assert "comma_finite_entry_headroom_admitted" not in count


def test_b32_release_consumes_exact_bellman_summary() -> None:
    root = isabelle_root(repository_root())
    comma = root / "families/comma"
    instance_path = comma / "comma_semantic_b1_instance/Comma_Semantic_B1_Instance.thy"
    image_path = comma / "comma_semantic_b1_instance/Comma_Continue_Image_Instance.thy"
    instance = executable_text(instance_path.read_text(encoding="utf-8"))
    image = executable_text(image_path.read_text(encoding="utf-8"))
    assert "comma_semantic_phase_class_B32_exact_output_checked" in instance
    assert "comma_semantic_b1_action_b32_stop242_checked" in instance
    _, image_imports = parse_theory_header(
        image_path.read_text(encoding="utf-8"), image_path
    )
    assert "Comma_Continue_Frontier24_Source_Bridge" in image_imports
    assert not ml_file_references(image, image_path)
    assert "comma_frontier_m204_bellman_native" in image
    assert "comma_frontier_m204_exact_stop_from_checked_bellman" in image
    assert "comma_decade_exact_summary" in image
    assert "comma_terminal_weight_encode height terminal" in image
    assert "Comma_Semantic_B1_Stop" in image
    assert "height\\<le>26" in image
    assert "\\<le>242" in image
    assert "comma_semantic_phase_continue24_image_certificate_native" not in image
    sessions = discover_sessions(root)
    closure = session_dependency_closure(sessions, ("Comma_Semantic_B1_Instance",))
    assert "Comma_Semantic_Future" in closure


def test_frontier_parent_reuse_precedes_bind_witness_reconstruction() -> None:
    owner = isabelle_root(repository_root()) / "families/comma/comma_semantic_b1"
    replay = executable_text(
        (owner / "crt_mdd_bind_replay.ML").read_text(encoding="utf-8")
    )
    application = replay.split("fun certify_public ", 1)[1].split(
        "val public: replay", 1
    )[0]
    hit, miss = application.split("| NONE =>", 1)
    assert "Key_Table.lookup" in hit
    assert "Utils.exact_prop" in hit
    assert "bind_prop state full_mapping fallback source result_root" in hit
    assert "Store.bind_witness" not in hit
    assert "certify_key" not in hit
    assert "validate_key input_key" in miss
    assert "Store.bind_witness store input_key" in miss
    assert "restrict_mapping labels full_mapping = norm_mapping" in miss
    assert "restrict_certificate" in miss
    assert application.index("Utils.exact_prop") < application.index(
        "Store.bind_witness"
    )

    fixture = executable_text(
        (
            owner.parent / "comma_semantic_b1_smoke/Comma_CRT_MDD_Certificate_Smoke.thy"
        ).read_text(encoding="utf-8")
    )
    assert "comma_mdd_certificate_example_bind_branch_alias" in fixture
    assert "bind_stats = Comma_CRT_MDD_Bind_Replay.statistics bind_replay" in fixture
    assert "Comma_Proof_Dependency_Audit.require_native_clean" in fixture


def test_concrete_bound_consumes_checked_typed_bellman_authority() -> None:
    comma = isabelle_root(repository_root()) / "families/comma"
    path = comma / "comma_semantic_b1_instance/Comma_Continue_Image_Instance.thy"
    declarations = {
        item.name: item.body
        for item in extract_isabelle_declarations(path.read_text(), path)
    }
    checked = declarations["comma_semantic_phase_class_B32_exact_output_checked"]
    assert "phase<924" in checked
    assert "cid<46" in checked
    assert "height\\<le>26" in checked
    assert "comma_decade_exact_summary" in checked
    assert "Comma_Semantic_B1_Stop" in checked
    assert "comma_terminal_weight_encode height terminal\\<le>242" in checked
    assert "comma_frontier_m204_bellman_native" in checked
    assert "comma_frontier_m204_exact_stop_from_checked_bellman" in checked


def test_multiway_source_publisher_uses_authenticated_ordered_actions() -> None:
    comma = isabelle_root(repository_root()) / "families/comma"
    compiler = executable_text(
        (
            comma
            / "comma_semantic_b1_instance/semantic_frontier24_parametric_compiler.ML"
        ).read_text()
    )
    publisher = executable_text(
        (
            comma / "comma_semantic_b1_instance/semantic_frontier24_bundle_publisher.ML"
        ).read_text()
    )
    replay = executable_text(
        (comma / "comma_semantic_b1/crt_mdd_multiway_replay.ML").read_text()
    )
    soundness = (
        comma / "comma_semantic_b1/Comma_Parametric_Typed_Soundness.thy"
    ).read_text()
    assert "Arena.priority_select" in compiler
    assert "Store.priority_witness" in publisher
    assert "Multiway.certify" in publisher
    assert "comma_frontier24_multiways_certified" in publisher
    assert "#shifted_guard_root row" in publisher
    assert "#action_output_root row" in publisher
    assert "Utils.exact_prop" in replay
    assert "Cyclic priority witness" in replay
    assert "comma_frontier24_closures_typed_exact" in soundness
    assert "comma_frontier24_class_roots_typed_exact" in soundness
    assert "comma_frontier24_closure_certified" in soundness


def _assert_direct_bellman_owner(source: str) -> None:
    """Check authored wiring; the native build checks theorem authority."""
    code = executable_text(source)
    assert re.search(
        r"Comma_M204_Direct_Candidate_Publication\.publish\s+"
        r"Comma_Direct_Bellman_Issuer\.prepare\b",
        code,
    )
    assert "comma_frontier_m204_bellman_native" in code
    assert "require_native_clean" in code
    assert (
        re.search(r"\b(?:Direct\.run|M204_Transport\.prove|Publisher\.certify)\b", code)
        is None
    )
    assert re.search(r"0\s+upto\s+923", code) is None


def test_source_publisher_uses_direct_bellman_owner() -> None:
    path = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_b1_instance/Comma_Continue_Frontier24_Source_Bridge.thy"
    )
    source = path.read_text()
    _assert_direct_bellman_owner(source)
    assert "semantic_direct_bellman_issuer.ML" in ml_file_references(source, path)
    issuer = path.with_name("semantic_direct_bellman_issuer.ML")
    code = executable_text(issuer.read_text())
    assert "Comma_Direct_Bellman_Publication.publish" in code
    assert "require_native_clean" in code


def test_direct_bellman_owner_comment_cannot_satisfy_wiring() -> None:
    source = """(* Comma_M204_Direct_Candidate_Publication.publish
      Comma_Direct_Bellman_Issuer.prepare *)
      val _ = comma_frontier_m204_bellman_native
      val _ = require_native_clean
    """
    assert re.search(
        r"Comma_M204_Direct_Candidate_Publication\.publish\s+"
        r"Comma_Direct_Bellman_Issuer\.prepare\b",
        executable_text(source),
    ) is None


def test_shared_selected_list_checks_nested_extent_before_memo_lookup() -> None:
    root = isabelle_root(repository_root())
    path = root / "families/comma/comma_entry_arithmetic/selected_list_conversion.ML"
    source = executable_text(path.read_text(encoding="utf-8"))
    lookup = source.split("fun lookup index_context cterm =", 1)[1].split(
        "and nth index_context cterm index_conversion =", 1
    )[0]
    lookup = re.sub(r"\s+", " ", lookup)

    assert lookup.index("case in_extent index_context cterm") < lookup.index(
        "Termtab.lookup (!memo) key"
    )
    assert lookup.index("lookup index_context table_ct") < lookup.index(
        "nth index_context cterm index_conversion"
    )
    assert "Termtab.lookup (!memo) table" in source
    assert "extent_at extents depth" in source
    assert "fun make_nested" in source
    assert "literal_nested_extents depth" in source
    assert "0 <= value andalso value < extent" in source


def _registered_theory(name: str) -> Path:
    root = isabelle_root(repository_root())
    paths = tuple(
        (root / session.directory / theory).with_suffix(".thy").resolve()
        for session in discover_sessions(root)
        for theory in session.theories
        if Path(theory).name == name
    )
    assert len(paths) == 1
    return paths[0]


def _weighted_data_sources() -> tuple[Path, str, str, str]:
    theory = _registered_theory("Comma_Weighted_CRT_Data")
    owner = theory.parent
    sources = tuple(
        executable_text((owner / name).read_text(encoding="utf-8"))
        for name in ml_file_references(theory.read_text(encoding="utf-8"), theory)
    )
    interface = next(
        source
        for source in sources
        if "signature COMMA_SEMANTIC_WEIGHTED_CRT_DATA =" in source
    )
    implementation = next(
        source
        for source in sources
        if re.search(r"structure Comma_Semantic_Weighted_CRT_Data\s*:\s*>", source)
    )
    builder = next(
        source
        for source in sources
        if "functor Comma_Semantic_Weighted_CRT_Certificate_BuilderFn" in source
    )
    return owner, interface, implementation, builder


def test_weighted_action_cache_authority_precedes_construction() -> None:
    _owner, interface, implementation, builder = _weighted_data_sources()
    assert "type diagram\n" in interface
    assert "type reservation\n" in interface
    assert "release_external" not in interface
    assert "with_reservation" in interface
    certifier = builder.split("fun certify ctxt", 1)[1]
    assert certifier.index("B.validate_request") < certifier.index(
        "fun cached_normalization"
    )
    request = implementation.split("fun validate_request", 1)[1].split(
        "fun native_certify", 1
    )[0]
    assert "check_diagram arena initial" in request
    assert "check_serializer arena payloadT serializer" in request
    assert "#owner cache = #owner arena" in request
    assert "#payloadT cache = payloadT" in request
    assert "Context.subthy" in request
    hit = implementation.split("fun validated_cached_entry", 1)[1].split(
        "fun endpoint_trees", 1
    )[0]
    assert "#source_node entry = node" in hit
    assert "cached_theorem_in_context" in hit
    assert "Context.subthy" in hit
    assert "Goal.prove" not in hit
    assert "certify_normalization" not in hit
    publication = implementation.split("fun check_publication", 1)[1].split(
        "val cached_theorem_context", 1
    )[0]
    assert "native_closed ctxt cache theorem" in publication
    assert "Thm.prop_of theorem aconv proposition" in publication
    assert "(#native_certify cache) theorem" in publication

    compilation_path = _registered_theory("Comma_Weighted_CRT_Guard")
    fixture_path = (
        compilation_path.parent.parent
        / "comma_semantic_b1_instance"
        / "semantic_weighted_crt_data_cache_hit_fixture.ML"
    )
    fixture = executable_text(fixture_path.read_text())
    compilation = executable_text(compilation_path.read_text())
    assert f'ML_file "../comma_semantic_b1_instance/{fixture_path.name}"' in compilation
    assert "Comma_Weighted_CRT_Data_Cache_Hit_Fixture.run @{context}" in compilation
    assert "Data.with_reservation" in fixture
    assert "a foreign-arena reservation use" in fixture_path.read_text()
    assert "a stale reservation use" in fixture_path.read_text()
    # The kernel fixture fills its arena before reuse. An accidental miss or
    # a cache hit that reconstructs data cannot hide behind spare capacity.
    assert "used full = 128" in fixture
    assert "#peak_entries after_repeat = #peak_entries full" in fixture
    assert "handle Late_Cache_Failure" in fixture


def test_weighted_selector_proofs_keep_occurrence_offsets_out_of_cache_keys() -> None:
    owner, _interface, _implementation, builder = _weighted_data_sources()
    selector = builder.split("fun select_completed", 1)[1].split("fun plan_entry", 1)[0]
    assert selector.index("B.offset row - local_common") < selector.index(
        "selector_key axis relative"
    )
    assert "B.make_diagram arena (local_common + B.offset local_result)" in selector
    hit = builder.split("fun cached_normalization", 1)[1].split(
        "fun canonical_normalization", 1
    )[0]
    assert "validated_cached_entry (B.node initial)" in hit
    assert "B.offset initial + B.offset (#result entry)" in hit
    assert "Goal.prove" not in hit
    compilation_path = _registered_theory("Comma_Weighted_CRT_Guard")
    fixture = executable_text(
        (
            compilation_path.parent.parent
            / "comma_semantic_b1_instance"
            / "semantic_weighted_crt_data_cache_hit_fixture.ML"
        ).read_text()
    )
    assert "Data.with_offset arena 17 raw" in fixture
    assert "#proof_entries after_second = #proof_entries after_first" in fixture
    assert "#nodes after_second = #nodes after_first" in fixture
    assert "#serialization_node_visits" in fixture
    path = owner / "Comma_Semantic_Weighted_CRT_Selector_Laws.thy"
    law = {
        item.name: item.body
        for item in extract_isabelle_declarations(path.read_text(), path)
    }["comma_weighted_crt_first_port_action_guarded_offset"]
    assert 'axis: "axis<4"' in law
    assert "slot<comma_crt_axis_radix axis" in law
    assert "comma_weighted_crt_first_port_admissible axis tree" in law
    assert "phase mod comma_crt_axis_radix axis=slot" in law
    assert "comma_weighted_crt_apply (incoming,tree) phase" in law


def test_clock_projection_keeps_exact_bounded_selector_contract() -> None:
    comma = isabelle_root(repository_root()) / "families/comma"
    path = comma / "comma_semantic_b1_smoke/Comma_CRT_Selector_Projection.thy"
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(path.read_text(), path)
    }
    for axis in range(4):
        specialized = declarations[f"comma_crt_select{axis}_skip"].body
        assert "positive:" in specialized
        assert "row_length:" in specialized
        assert "weight_zero:" in specialized
        assert "next_bounded:" in specialized


def test_generic_phase_fold_retains_control_and_guards() -> None:
    root = isabelle_root(repository_root())
    fold_path = (
        root / "families/comma/comma_semantic_b1/Comma_Semantic_Graph_Phase_Fold.thy"
    )
    fold = {
        item.name: item
        for item in extract_isabelle_declarations(fold_path.read_text(), fold_path)
    }
    sound = fold["comma_semantic_b1_stop_mask_iteration_sound"].body
    assert "root_evaluation:" in sound
    assert "transfer_refinement:" in sound
    assert "comma_semantic_b1_stop_within" in sound
    congruence = fold["comma_semantic_b1_graph_completed_cid_result_congruence"].body
    assert "comma_semantic_b1_graph_completed_valid" in congruence
    assert "comma_semantic_b1_graph_completed_eval_refines_endpoint" in congruence
    assert "\\<forall>clock." in congruence
    masks_path = (
        root / "families/comma/comma_decade_orbit/Comma_Phase_Mask_Arithmetic.thy"
    )
    response_path = root / "families/comma/comma_response_base/Comma_Response_Rows.thy"
    mask_owner, mask_imports = parse_theory_header(
        masks_path.read_text(encoding="utf-8"), masks_path
    )
    assert mask_owner == "Comma_Phase_Mask_Arithmetic"
    assert mask_imports == ("Comma_Decade_Masks",)
    mask_names = {
        item.name
        for item in extract_isabelle_declarations(masks_path.read_text(), masks_path)
    }
    response_names = {
        item.name
        for item in extract_isabelle_declarations(
            response_path.read_text(), response_path
        )
    }
    assert "comma_guard_pattern" in mask_names
    assert "comma_guard_join" in mask_names
    assert "comma_guard_pattern_phase_class" in mask_names
    assert "comma_guard_shifted_pattern" in mask_names
    assert "comma_guard_pattern" not in response_names
    assert "comma_guard_join" not in response_names


def test_residual_summary_recurrence_uses_canonical_control() -> None:
    core_path = (
        isabelle_root(repository_root())
        / "families/comma/comma_decade_residual_core"
        / "Comma_Decade_Residual_Core.thy"
    )
    core = {
        item.name: item
        for item in extract_isabelle_declarations(
            core_path.read_text(encoding="utf-8"), core_path
        )
    }
    classifier = core["comma_decade_residual_classifier_ok"].body
    assert "comma_decade_summary_step" in classifier
    canonical = core["comma_decade_summary_recurrence_sound"].body
    assert "comma_decade_control s" in canonical
    assert "comma_decade_summary_step_for" in core["comma_decade_summary_step"].body


def test_concrete_summary_decodes_the_checked_m204_weight() -> None:
    root = isabelle_root(repository_root())
    path = (
        root
        / "families/comma/comma_semantic_b1_instance"
        / "Comma_Semantic_Summary_Instance.thy"
    )
    text = path.read_text(encoding="utf-8")
    source = executable_text(text)
    declarations = {
        item.name: item for item in extract_isabelle_declarations(text, path)
    }
    provider = declarations["comma_semantic_decade_summary_code"].body
    assert "comma_frontier_m204_weight r (comma_offset_orbit x)" in provider
    assert "comma_terminal_weight_decode" in provider
    assert "comma_frontier_m204_exact_weight_from_checked_bellman" in provider
    assert "comma_frontier_m204_bellman_native" in provider
    assert "Comma_Semantic_B1_Stop" in provider
    exact = declarations["comma_semantic_decade_summary_total_exact"].body
    assert "comma_semantic_b1_action_power_b32_stop242" in exact
    bound = declarations["comma_semantic_b1_action_power_b32_stop242"].body
    assert "comma_semantic_b1_action_b32_stop242_checked" in bound
    assert "D\\<le>242" in bound
    assert "comma_semantic_decade_summary_total_exact_for_bound" in source
    assert "comma_semantic_concrete_boundary_occurrence_bridge" in source
    assert "[OF comma_semantic_decade_summary_provider_exact]" in source

    sessions = discover_sessions(root)
    closure = session_dependency_closure(sessions, ("Comma_Semantic_B1_Instance",))
    assert "Comma_Semantic_Future" in closure
    assert not {
        "Comma_Sparse_Core",
        "Comma_Sparse_Base_Instance",
        "Comma_Sparse_Power_Instance",
        "Comma_Future_Rank_Data",
    }.intersection(closure)


def test_generic_source_binding_retains_pointwise_port_and_guard() -> None:
    comma = isabelle_root(repository_root()) / "families/comma"
    path = comma / "comma_semantic_b1/Comma_Semantic_Graph_Pointwise_Binding_Row.thy"
    bridge = {
        item.name: item
        for item in extract_isabelle_declarations(path.read_text(), path)
    }["comma_semantic_b1_binding_row_valid_from_pointwise_port"].body
    assert "comma_round_admitted source" in bridge
    assert "source_to_port:" in bridge
    assert "port_row:" in bridge
    assert "comma_semantic_b1_edge_of_continuation bindings" in bridge
    assert "comma_semantic_b1_graph_valid" not in bridge

    transport_path = comma / "comma_semantic_b1/Comma_Guarded_Source_Row_Transport.thy"
    transport = {
        item.name: item.body
        for item in extract_isabelle_declarations(
            transport_path.read_text(), transport_path
        )
    }["comma_semantic_b1_binding_row_valid_pair_guarded_rebase"]
    assumptions = transport.split("shows", 1)[0]
    assert "comma_guarded_source_class_rel source representative" in assumptions
    assert "comma_source_continuation_id" not in assumptions
    assert "comma_semantic_b1_graph_valid" not in assumptions


def test_generic_completed_binding_preserves_source_guards() -> None:
    comma = isabelle_root(repository_root()) / "families/comma"
    graph_path = comma / "comma_semantic_b1/Comma_Semantic_Graph_Core.thy"
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(graph_path.read_text(), graph_path)
    }
    contract = declarations["comma_semantic_b1_completed_binding_row_valid"].body
    assert "representative\\<in>set bindings" in contract
    assert (
        "comma_semantic_b1_binding_row_valid bindings nodes representative" in contract
    )
    assert "\\<forall>clock." in contract
    assert "comma_round_admitted" in contract
    assert "Comma_Continuation_Goto" in contract
    assert "comma_semantic_b1_graph_valid" not in contract
