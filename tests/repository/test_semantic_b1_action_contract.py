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


def test_b32_release_uses_authenticated_graph_power() -> None:
    root = isabelle_root(repository_root())
    comma = root / "families/comma"
    instance_path = (
        comma / "comma_semantic_b1_instance" / "Comma_Semantic_B1_Instance.thy"
    )
    graph_path = (
        comma / "comma_semantic_graph_instance" / "Comma_Semantic_Graph_Instance.thy"
    )
    graph_power_path = (
        comma / "comma_semantic_b1_instance" / "Comma_Semantic_Graph_Action_Power.thy"
    )
    instance_text = instance_path.read_text(encoding="utf-8")
    instance = executable_text(instance_text)
    declarations = {
        item.name
        for item in extract_isabelle_declarations(instance_text, instance_path)
    }
    graph = executable_text(graph_path.read_text(encoding="utf-8"))
    graph_power = executable_text(graph_power_path.read_text(encoding="utf-8"))

    assert "comma_semantic_graph_valid_checked" in graph
    assert "comma_semantic_graph_root_binding_exact" in graph
    assert "comma_semantic_graph_root_binding_exists" in graph_power
    assert "comma_semantic_graph_root_action_exact" in graph_power
    assert "comma_semantic_graph_action_power_refines" in graph_power
    assert "comma_semantic_b1_action_power_refines_orbit" in graph_power
    assert "comma_semantic_graph_b32_stop242_checked" in declarations

    # Demanded output and the universal Stop bound consume the same checked
    # five-square action; neither restarts scalar predecessor discovery.
    assert 'ML_file "semantic_graph_action_certificate.ML"' in instance
    assert "Comma_Semantic_Graph_Action_Certificate.make" in instance
    assert "comma_semantic_graph_action_power_refines" in instance
    assert "comma_semantic_graph_stop242_from_weighted_crt_power_all" in instance

    sessions = discover_sessions(root)
    closure = session_dependency_closure(sessions, ("Comma_Semantic_B1_Instance",))
    assert "Comma_Semantic_Graph_Instance" in closure


def test_concrete_bound_requires_checked_quotient_transfers() -> None:
    owner = (
        isabelle_root(repository_root()) / "families/comma/comma_semantic_b1_instance"
    )
    transport_path = owner / "Comma_Semantic_Predecessor_Certificate.thy"
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(
            transport_path.read_text(), transport_path
        )
    }
    checked = declarations[
        "comma_semantic_graph_stop242_from_weighted_crt_power_all"
    ].body
    assert "roots_wf:" in checked
    assert "base_exact:" in checked
    assert "base_admitted:" in checked
    assert "final_exact:" in checked
    assert "final_bounded:" in checked
    assert "comma_semantic_b1_crt_power 5 roots!root" in checked
    assert "Some (Comma_Semantic_B1_CRT_Stop J,H)" in checked
    assert "J<9" in checked
    assert "H\\<le>26" in checked
    assert "Comma_Semantic_B1_Stop D" in checked
    assert "D\\<le>242" in checked
    publisher = executable_text(
        (owner / "semantic_predecessor_certificate.ML").read_text()
    )
    assert "parse_initial_source_ids" in publisher
    assert "comma_semantic_graph_initial_source_binding_exact" in publisher
    assert "Inttab.lookup node_refinements_by_cid cid" in publisher
    assert (
        "comma_semantic_b1_crt_compile_node_from_children_refines_graph_eval"
        in publisher
    )
    assert "Thm_Deps.all_oracles" in publisher
    assert "require_native_clean" in publisher


def test_postorder_compiler_refines_children_before_publishing_parents() -> None:
    owner = (
        isabelle_root(repository_root()) / "families/comma/comma_semantic_b1_instance"
    )
    source = executable_text((owner / "semantic_weighted_crt_dag.ML").read_text())
    node = source.split("and build_node cid", 1)[1].split("val base_raw", 1)[0]
    assert node.index("Inttab.lookup (!compiled) cid") < node.index("build_selector")
    assert node.index("certify_node raw") < node.index("Inttab.update (cid, result)")
    assert "#normalized (build_node child)" in source
    compiler = source.split("fun compile ctxt", 1)[1].split("fun make_serializer", 1)[0]
    assert compiler.index("length source_cids = 16") < compiler.index("val base_raw")
    assert compiler.index(
        "List.app (fn cid => ignore (build_node cid)) source_cids"
    ) < (compiler.index("val final_roots = square 0 base_roots"))
    path = owner / "Comma_Semantic_Graph_CRT_Local_Node_Compilation.thy"
    contract = {
        item.name: item.body
        for item in extract_isabelle_declarations(path.read_text(), path)
    }["comma_semantic_b1_crt_compile_node_from_children_refines_graph_eval"]
    assert "comma_semantic_b1_graph_completed_valid bindings nodes" in contract
    assert "comma_semantic_b1_node_of nodes cid = Some node" in contract
    assert "child_exact:" in contract
    assert (
        "\\<forall>phase. comma_weighted_crt_apply (child_action child) phase"
        in contract
    )
    assert "map_option comma_semantic_b1_crt_graph_result" in contract


def test_predecessor_publisher_does_not_materialize_scalar_phase_tables() -> None:
    owner = (
        isabelle_root(repository_root()) / "families/comma/comma_semantic_b1_instance"
    )
    path = owner / "semantic_predecessor_certificate.ML"
    declarations = {
        item.name: item
        for item in extract_isabelle_declarations(path.read_text(), path)
    }
    publisher = declarations["publish"].body
    assert "Array.array" not in publisher
    assert re.search(r"0\s+upto\s+923", publisher) is None
    assert "Comma_Semantic_Weighted_CRT_DAG.compile_checked" in publisher
    assert "comma_semantic_graph_stop242_from_weighted_crt_power_all" in publisher
    assert "comma_semantic_b1_stop_mask_iteration" not in publisher
    assert "#evaluate evaluator" not in publisher
    assert "0 upto 26" not in publisher
    assert "46 * 5" in publisher
    assert "#power_equation weighted_checked" in publisher
    assert "#bounded_stops weighted_checked" in publisher

    evaluator = executable_text(
        (owner / "semantic_graph_action_certificate.ML").read_text()
    )
    query = evaluator.split("fun query phase root", 1)[1].split("fun parse", 1)[0]
    assert query.index("case Inttab.lookup (!cache) key") < query.index(
        "val value = specialize phase root"
    )
    assert "Comma_Semantic_Graph_Power_Evaluator" not in evaluator
    assert "comma_semantic_graph_b32_weighted_actions_refine" in evaluator
    assert "Context.subthy" in evaluator
    assert "exact (request phase root)" in query
    assert "Exn.release attempted" in query


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
    assert "Conv.arg_conv (lookup index_context)" in lookup
    assert "nth index_context (Thm.rhs_of prepared) index_conversion" in lookup
    assert "extent_at extents depth" in source
    assert "fun make_nested" in source
    assert "literal_nested_extents depth" in source
    assert "index < extent" in source
    assert "fun make_named_children" in source


def _weighted_data_sources() -> tuple[Path, str, str, str]:
    owner = (
        isabelle_root(repository_root()) / "families/comma/comma_semantic_b1_instance"
    )
    theory = owner / "Comma_Semantic_Graph_CRT_Compilation.thy"
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
    owner, interface, implementation, builder = _weighted_data_sources()
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

    fixture_path = owner / "semantic_weighted_crt_data_cache_hit_fixture.ML"
    fixture = executable_text(fixture_path.read_text())
    compilation = executable_text(
        (owner / "Comma_Semantic_Graph_CRT_Compilation.thy").read_text()
    )
    assert f'ML_file "{fixture_path.name}"' in compilation
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
    fixture = executable_text(
        (owner / "semantic_weighted_crt_data_cache_hit_fixture.ML").read_text()
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
    path = comma / "comma_semantic_b1/Comma_CRT_Selector_Projection.thy"
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


def test_predecessor_closure_transports_actual_graph_control() -> None:
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
    transport_path = (
        root
        / "families/comma/comma_semantic_b1_instance"
        / "Comma_Semantic_Graph_Stop_Transport.thy"
    )
    transport = {
        item.name: item
        for item in extract_isabelle_declarations(
            transport_path.read_text(encoding="utf-8"), transport_path
        )
    }
    control = transport["comma_semantic_graph_root_control_transport"].body
    assert "comma_decade_control" in control
    assert "next_phase=(phase+1) mod 924" in control
    assert "Comma_Semantic_B1_Live (comma_offset_orbit next_offset)" in control
    assert "Comma_Semantic_B1_Stop" in control
    stop_transport = transport["comma_semantic_graph_stop242_from_stop_within"].body
    assert "comma_semantic_b1_stop_within" in stop_transport
    assert "comma_semantic_graph_stop_within_summary" in stop_transport
    assert "comma_semantic_graph_stop_from_exact_summary" in stop_transport

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


def test_concrete_summary_decodes_the_graph_power_result() -> None:
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
    assert "comma_semantic_graph_action_power 5 r (comma_offset_orbit x)" in provider
    assert "Comma_Semantic_B1_Stop D" in provider
    assert "comma_terminal_weight_decode D" in provider
    exact = declarations["comma_semantic_decade_summary_total_exact"].body
    assert "comma_semantic_b1_action_power_b32_stop242" in exact
    assert "comma_semantic_graph_b32_stop242_checked" in text
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


def test_graph_action_projection_is_demand_driven_and_request_bound() -> None:
    root = isabelle_root(repository_root())
    b1 = root / "families/comma/comma_semantic_b1_instance"
    future = root / "families/comma/comma_semantic_future_instance"
    instance = executable_text(
        (b1 / "Comma_Semantic_B1_Instance.thy").read_text(encoding="utf-8")
    )
    power_fixtures = executable_text(
        (b1 / "Comma_Semantic_Graph_Action_Power.thy").read_text(encoding="utf-8")
    )
    certificate = executable_text(
        (b1 / "semantic_graph_action_certificate.ML").read_text(encoding="utf-8")
    )
    entry = executable_text(
        (future / "Comma_Semantic_Entry_Open.thy").read_text(encoding="utf-8")
    )
    assert "Comma_Semantic_Graph_Action_Certificate.make" in entry
    assert "Comma_Selected_List_Conversion.schematize" in entry
    assert "comma_semantic_b1_action_power 5 phase root" in entry

    # The global provider consumes one all-phase family refinement. It must
    # not turn every candidate source/phase into a fresh B32 point request.
    future_instance = executable_text(
        (future / "Comma_Semantic_Future_Instance.thy").read_text(encoding="utf-8")
    )
    closure = executable_text(
        (future / "Comma_Semantic_Future_Candidate_Provider_Closure.thy").read_text()
    )
    assert "Comma_Semantic_Graph_Action_Certificate.make" not in future_instance
    assert "construct_provider_check" not in future_instance
    assert "provider_check_tac" not in future_instance
    assert "prove_indexed_list_all" not in closure
    assert "comma_semantic_future_candidate_provider_row_of_source_key" in closure
    assert "comma_semantic_future_candidate_parent_source_key_nf" in closure

    assert "type certificate" in certificate
    assert "query: int -> int -> result" in certificate
    assert "convert: cterm -> thm option" in certificate
    assert "fun query phase root" in certificate
    assert re.search(r"\bfun convert\s+\w+\s*=", certificate)
    assert "Context.subthy (theory, Thm.theory_of_cterm requested)" in certificate
    assert "r < 924" in certificate
    assert "i < 46" in certificate
    assert "SOME (pT, 5)" in certificate
    assert "0 <= r" in certificate
    assert "0 <= i" in certificate
    assert "case Inttab.lookup (!cache) key" in certificate
    assert "Inttab.update (key, value)" in certificate
    assert "aconv HOLogic.mk_Trueprop (HOLogic.mk_eq (request, value))" in certificate
    assert "null (Thm.hyps_of theorem)" in certificate
    assert "null (Thm.tpairs_of theorem)" in certificate
    assert "closed (Thm.prop_of theorem)" in certificate
    assert "query phase root" in instance
    assert "comma_semantic_graph_b32_stop242_checked" in instance
    assert '"Comma_Semantic_B1_Live 12"' in power_fixtures
    assert '"Comma_Semantic_B1_Live 23"' in power_fixtures
    assert "Distinct receiving phases lost their exact B1 results" in power_fixtures
    assert "Graph power failed to absorb an actual Stop endpoint" in power_fixtures
    assert "Live-to-Stop power lost the chronological weight" in power_fixtures
    assert "Named generic Invalid absorption" in power_fixtures
    assert '"Graph power phase is outside 0..923"' in power_fixtures
    assert '"Graph power root is outside 0..45"' in power_fixtures


def test_source_binding_publication_consumes_the_pointwise_port_bridge() -> None:
    comma = isabelle_root(repository_root()) / "families/comma"
    instance = comma / "comma_semantic_graph_instance"
    _, imports = parse_theory_header(
        (instance / "Comma_Semantic_Graph_Instance.thy").read_text(),
        instance / "Comma_Semantic_Graph_Instance.thy",
    )
    assert "Comma_Semantic_B1.Comma_Semantic_Graph_Pointwise_Binding_Row" in imports
    publication = executable_text(
        (instance / "semantic_graph_publication.ML").read_text()
    )
    assert "comma_semantic_b1_binding_row_valid_from_pointwise_port" in publication
    assert "comma_semantic_b1_source_action_at_port" in publication
    assert "comma_semantic_b1_source_port_action" in publication
    assert "comma_semantic_b1_binding_row_valid_pair_guarded_rebase" in publication
    declarations = {
        item.name: item.body
        for item in extract_isabelle_declarations(
            publication, instance / "semantic_graph_publication.ML"
        )
    }
    binding_rows = declarations["certify_binding_rows"]
    certificate = binding_rows.split("fun certified_class", 1)[1].split(
        "fun certify_row", 1
    )[0]
    assert certificate.index(
        "Termtab.lookup (!class_certificates)"
    ) < certificate.index("prove_class_row")
    receiving_row = binding_rows.split("fun certify_row", 1)[1].split(
        "fun completed_row", 1
    )[0]
    assert "#row_valid certificate" in receiving_row
    assert "NearClass" in receiving_row
    assert "#action_key source_info aconv #action_key row" in receiving_row
    assert "checked_near_selection_id source_info" in receiving_row
    assert "checked_near_selection_id row_source_info" in receiving_row
    assert "admitted_fact source_info" in receiving_row
    assert "normalized_fact source_info" in receiving_row
    assert "comma_semantic_b1_binding_row_valid_pair_id_rebase" in receiving_row
    assert "comma_semantic_b1_binding_row_valid_pair_guarded_rebase" in receiving_row
    assert "Goal.prove" not in receiving_row
    assert (
        "comma_semantic_b1_binding_row_valid_from_pointwise_port" not in receiving_row
    )

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

    source_path = instance / "semantic_source_ports.ML"
    source_owner = executable_text(source_path.read_text())
    membership = source_owner.split("fun membership", 1)[1].split("fun same_shape", 1)[
        0
    ]
    assert "comma_guarded_source_class_rel" in membership
    assert "comma_source_continuation_id" not in membership

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


def test_initial_source_publication_reuses_the_checked_literal_catalogue() -> None:
    owner = (
        isabelle_root(repository_root())
        / "families/comma/comma_semantic_graph_instance"
    )
    path = owner / "semantic_graph_publication.ML"
    publication = {
        item.name: item.body
        for item in extract_isabelle_declarations(path.read_text(), path)
    }["publish_initial_source_ids"]
    # Range arithmetic is already certified by discovery. Reopening it in a
    # sterile list-proof context can expand an undecided range indefinitely.
    assert "upt_rec" not in publication
    assert "list.map" not in publication
    assert "append.simps" not in publication
    assert "list_all2_Cons" in publication
    assert "list_all2_Nil" in publication
    assert "lookup_facts" in publication
    assert "checked exact_proposition" in publication

    constructor = executable_text((owner / "semantic_graph_constructor.ML").read_text())
    assert "initial_sources_equation" in constructor
    assert re.search(
        r"source_list_equation\s*=\s*initial_sources_equation", constructor
    )


def test_completed_alias_publication_uses_a_local_representative() -> None:
    comma = isabelle_root(repository_root()) / "families/comma"
    instance = comma / "comma_semantic_graph_instance"
    source = executable_text((instance / "semantic_source_ports.ML").read_text())
    publication = executable_text(
        (instance / "semantic_graph_publication.ML").read_text()
    )
    constructor = executable_text(
        (instance / "semantic_graph_constructor.ML").read_text()
    )
    theory = executable_text(
        (instance / "Comma_Semantic_Graph_Instance.thy").read_text()
    )

    # The native fixture measures actual transition-row discovery when an
    # admitted alias consumes its completed representative.
    assert "transition_evaluations= !transition_attempts" in source
    assert "comma_semantic_b1_entry_period_one_direct_goto_completed" in source
    assert "comma_semantic_b1_entry_period_one_direct_goto_action" in source
    assert "fun build ()" in constructor
    assert "val forward = #forward source_ports source" in constructor
    assert "val cid = compile child" in constructor
    assert "comma_semantic_b1_graph_completed_valid" in constructor
    assert "val representatives = filter" in publication
    assert "comma_semantic_graph_completed_binding_from_lookup" in publication
    completed_row = publication.split("fun completed_row", 1)[1].split(
        "val row_theorems =", 1
    )[0]
    assert "resolve_tac goal_context [found]" in completed_row
    assert "resolve_tac goal_context [local_row]" in completed_row
    assert "binding_row_valid_def" not in completed_row
    assert "base_simp @" not in completed_row
    assert "Completed source alias rediscovered a transition row" in theory
    assert "#transition_evaluations before_alias" in theory
    assert "#transition_evaluations after_alias" in theory

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
