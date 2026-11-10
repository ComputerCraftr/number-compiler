signature COMMA_SEMANTIC_FUTURE_CANDIDATE_PROVIDER_NF =
sig
  val publish: local_theory -> local_theory
end

structure Comma_Semantic_Future_Candidate_Provider_NF:
  COMMA_SEMANTIC_FUTURE_CANDIDATE_PROVIDER_NF =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data

  val natT = @{typ nat}
  val controlT = @{typ comma_future_control}
  val b1_controlT = @{typ comma_semantic_b1_crt_control}
  val control_optionT = Type (@{type_name option}, [controlT])
  val keyT = HOLogic.mk_prodT
    (control_optionT, HOLogic.listT natT)
  val b1_dagT = @{typ comma_semantic_b1_crt_dag}
  val id_dagT = Type (@{type_name comma_semantic_weighted_crt_dag}, [natT])
  val control_dagT = Type (@{type_name comma_semantic_weighted_crt_dag},
    [control_optionT])
  val child_dagT = id_dagT
  val b1_actionT = HOLogic.mk_prodT (natT, b1_dagT)
  val id_actionT = HOLogic.mk_prodT (natT, id_dagT)
  val control_actionT = HOLogic.mk_prodT (natT, control_dagT)
  val child_actionT = HOLogic.mk_prodT (natT, child_dagT)
  val projected_actionT = HOLogic.mk_prodT (control_actionT,
    HOLogic.mk_prodT (child_actionT, child_actionT))
  val key_actionT = projected_actionT
  val key_resultT = Type (@{type_name option}, [keyT])
  val key_apply = Const (@{const_name comma_semantic_future_projected_key_apply},
    projected_actionT --> natT --> key_resultT)
  type components = {control: Data.diagram, north: Data.diagram, south: Data.diagram}
  type certificate = {normalized: Data.diagram, equation: thm, certified_nodes: int}
  type certificates = {control: certificate, north: certificate, south: certificate}

  fun nat n = HOLogic.mk_number natT n

  datatype provider_control = Provider_Fork of int | Provider_Landmine

  fun parse_nat ctxt term =
    (case try HOLogic.dest_number term of
      SOME (typ, value) =>
        if typ = natT andalso value >= 0 then IntInf.toInt value
        else error "Future provider NF data contains a non-natural numeral"
    | NONE => error ("Future provider NF data contains a non-numeral: " ^
        Syntax.string_of_term ctxt term))

  fun parse_control ctxt value =
    (case strip_comb value of
      (Const (name, _), [control]) =>
        if name = @{const_name Some} then
          (case strip_comb control of
            (Const (control_name, _), [target_term]) =>
              if control_name = @{const_name Comma_Future_Fork} then
                let
                  val target = parse_nat ctxt target_term
                  val _ = if 2 <= target andalso target <= 9 then ()
                    else error "Future provider Fork control is outside 2..9"
                in Provider_Fork target end
              else error "Future provider output has an unknown control"
          | (Const (control_name, _), []) =>
              if control_name = @{const_name Comma_Future_Landmine} then
                Provider_Landmine
              else error "Future provider output has an unknown control"
          | _ => error "Future provider control option is malformed")
        else error "Future provider control option is malformed"
    | _ => error "Future provider control option is malformed")

  fun closed ctxt term =
    not (Term.is_open term) andalso
      null (Term.add_frees term []) andalso null (Term.add_vars term [])

  fun exact_closed ctxt theorem label =
    if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem) andalso
        closed ctxt (Thm.prop_of theorem) andalso
        null (Thm_Deps.all_oracles [theorem]) then theorem
    else error (label ^ " is not a closed native theorem")

  fun rewrite_rhs ctxt definition constant label =
    let
      val theorem = Simplifier.rewrite
        (Simplifier.add_simps ([definition]) (ctxt)) (Thm.cterm_of ctxt constant)
      val _ = if Thm.term_of (Thm.lhs_of theorem) aconv constant then ()
        else error (label ^ " rewrite changed its input")
    in Thm.term_of (Thm.rhs_of theorem) end

  fun list_extent ctxt definition label =
    length (HOLogic.dest_list
      (Thm.term_of (Thm.rhs_of definition)))

  fun make_selector ctxt name definition pattern =
    let val extent = list_extent ctxt definition name
    in Comma_Selected_List_Conversion.make
      {ctxt=ctxt, name=name, root_definition=definition,
       table_pattern=pattern, extents=[extent]} end

  fun payload ctxt class_count term: Data.payload =
    let
      fun control_key value =
        (case parse_control ctxt value of
          Provider_Fork target => "fork:" ^ Int.toString target
        | Provider_Landmine => "landmine")
      val value_type = fastype_of term
      val key =
        if value_type = natT then
          let
            val id = parse_nat ctxt term
            val _ = if id < class_count then ()
              else error "Future provider candidate ID is outside the checked table"
          in "future-provider:nat:" ^ Int.toString id end
        else if value_type = control_optionT then
          "future-provider:control:" ^ control_key term
        else if value_type = b1_controlT then
          (case strip_comb term of
            (Const (name, _), [terminal_term]) =>
              if name = @{const_name Comma_Semantic_B1_CRT_Stop} then
                let
                  val terminal = parse_nat ctxt terminal_term
                  val _ = if terminal < 9 then ()
                    else error "Future provider source Stop is outside 0..8"
                in "future-provider:source-stop:" ^ Int.toString terminal end
              else error "Future provider source has a non-Stop control"
          | _ => error "Future provider source control is malformed")
        else error "Future provider payload has an unsupported type"
      val _ = if not (Term.is_open term) andalso
          null (Term.add_frees term []) andalso null (Term.add_vars term []) then ()
        else error "Future provider payload is not a closed typed value"
    in {key=key, value=term} end

  fun parse_tree payload_of ctxt arena expectedT term =
    (case strip_comb term of
      (Const (name, _), [value]) =>
        if name = @{const_name Comma_Weighted_CRT_Leaf} then
          if fastype_of value = expectedT then Data.leaf arena (payload_of value)
          else error "Future provider NF leaf has an unexpected payload type"
        else error "Future provider NF action has a malformed CRT leaf"
    | (Const (name, _), [axis_term, rows_term]) =>
        if name = @{const_name Comma_Weighted_CRT_Branch} then
          let
            val axis = parse_nat ctxt axis_term
            val rows = HOLogic.dest_list rows_term
            val children = map (fn row =>
              let
                val (weight_term, child_term) = HOLogic.dest_prod row
                val child = parse_tree payload_of ctxt arena expectedT child_term
              in Data.with_offset arena (parse_nat ctxt weight_term) child end)
              rows
          in Data.raw_branch_diagrams arena axis children end
        else error "Future provider NF action has a malformed CRT branch"
    | _ => error ("Future provider NF action has a malformed CRT node: " ^
        Syntax.string_of_term ctxt term))

  fun parse_action payload_of ctxt arena expectedT expectedActionT term =
    let
      val (offset_term, tree_term) = HOLogic.dest_prod term
      val _ = if fastype_of term = expectedActionT then ()
        else error "Future provider NF action has an unexpected action type"
      val tree = parse_tree payload_of ctxt arena expectedT tree_term
    in Data.with_offset arena (parse_nat ctxt offset_term) tree end

  fun future_control terminal =
    if terminal = 8 then Const (@{const_name Comma_Future_Landmine}, controlT)
    else Const (@{const_name Comma_Future_Fork}, natT --> controlT) $
      nat (terminal + 2)

  fun some_control control =
    Const (@{const_name Some}, controlT --> control_optionT) $ control

  fun candidate_output ctxt context class_count output expectedT class_id =
    let
      val _ = if 0 <= class_id andalso class_id < class_count then ()
        else error "Candidate output lookup ID is outside the validated class table"
      val query = output $ nat class_id
      val theorem = Simplifier.rewrite context (Thm.cterm_of ctxt query)
      val result = Thm.term_of (Thm.rhs_of theorem)
      val _ = if fastype_of result = expectedT andalso closed ctxt result then ()
        else error "Candidate class projection did not reduce to a closed value"
      val _ = if Thm.term_of (Thm.lhs_of theorem) aconv query then ()
        else error "Candidate class projection rewrote a different query"
      val _ = exact_closed ctxt theorem "candidate class projection lookup"
      val theorem_theory = Thm.theory_of_thm theorem
      val _ = if Context.subthy (theorem_theory, Proof_Context.theory_of context) andalso
          Context.subthy (theorem_theory, Proof_Context.theory_of ctxt) then ()
        else error "Candidate class output lookup belongs to another theory"
    in (result, theorem) end

  type candidate_output_components =
    {control: Data.payload, north: Data.payload, south: Data.payload}

  fun parse_candidate_output_components ctxt class_count result:
      candidate_output_components =
    let
      val (control_term, children_term) = HOLogic.dest_prod result
      val children = HOLogic.dest_list children_term |> map (parse_nat ctxt)
      val control = parse_control ctxt control_term
      val (north_id, south_id) =
        (case control of
          Provider_Fork _ =>
            (case children of
              [north, south] => (north, south)
            | _ => error "Checked Fork candidate output must have two ordered children")
        | Provider_Landmine =>
            if null children then (0, 0)
            else error "Checked Landmine candidate output must have no children")
      val control_payload = payload ctxt class_count control_term
      val north_payload = payload ctxt class_count (nat north_id)
      val south_payload = payload ctxt class_count (nat south_id)
    in
      {control = control_payload, north = north_payload, south = south_payload}
    end

  fun terminal_of_payload ctxt ({value, ...}: Data.payload) =
    (case strip_comb value of
      (Const (name, _), [terminal_term]) =>
        if name = @{const_name Comma_Semantic_B1_CRT_Stop} then
          let val terminal = parse_nat ctxt terminal_term
          in if terminal < 9 then terminal
            else error "Source NF Stop terminal is outside 0..8" end
        else error "Source NF contains a nonterminal or invalid leaf"
    | _ => error "Source NF contains a nonterminal or invalid leaf")

  fun check_stopped_source ctxt arena action =
    let
      fun check leaf height () =
        let val _ = terminal_of_payload ctxt leaf
        in if height <= 27 then ()
          else error "Source NF total displacement exceeds the 27-round bound" end
    in Data.fold_leaves arena check () action end

  fun make_source_child_action payload_of ctxt arena id_actions family_offset source_action =
    let
      fun receiver terminal total_delta =
        if terminal = 8 then Data.leaf arena (payload_of (nat 0))
        else
          let
            val selected = List.nth (id_actions, family_offset terminal)
          in Data.shift arena total_delta selected end
      fun bind_stop leaf total_delta =
        receiver (terminal_of_payload ctxt leaf) total_delta
      val bound = Data.bind arena bind_stop source_action
    in Data.erase_weights arena bound end

  fun make_source_control_action payload_of ctxt arena source_action =
    let
      fun output leaf =
        let
          val terminal = terminal_of_payload ctxt leaf
          val value = some_control (future_control terminal)
        in payload_of value end
    in Data.erase_weights arena (Data.map_leaves arena output source_action) end

  fun define_constant name value lthy =
    let
      val ((constant, (_, definition)), lthy') = Local_Theory.define
        ((Binding.name name, NoSyn),
          ((Binding.name (name ^ "_def"), []), value)) lthy
      val morphism = Local_Theory.target_morphism lthy'
    in (Morphism.term morphism constant, Morphism.thm morphism definition, lthy') end

  fun note name theorem lthy =
    snd (Local_Theory.note ((Binding.name name, []), [theorem]) lthy)

  fun prove ctxt proposition rules label =
    let
      val theorem = Goal.prove ctxt [] [] proposition
        (fn {context, ...} => asm_full_simp_tac (Simplifier.add_simps (rules) (context)) 1)
    in exact_closed ctxt theorem label end

  fun publish lthy =
    let
      val ctxt = Local_Theory.target_of lthy
      val id_definition = @{thm comma_semantic_future_candidate_class_ids_def}
      val control_definition = @{thm comma_semantic_future_candidate_controls_def}
      val child_definition = @{thm comma_semantic_future_candidate_children_def}
      val ids_term = rewrite_rhs ctxt id_definition
        @{term comma_semantic_future_candidate_class_ids} "Candidate class-ID vector"
      val ids = HOLogic.dest_list ids_term |> map (parse_nat ctxt)
      val control_terms = HOLogic.dest_list
        (Thm.term_of (Thm.rhs_of control_definition))
      val class_count = length control_terms
      val _ = if length ids = 16*924 then ()
        else error "Provider NF requires sixteen 924-phase candidate slices"
      val _ = if class_count > 0 andalso
          List.all (fn id => 0 <= id andalso id < class_count) ids then ()
        else error "Provider NF candidate ID vector is out of class range"
      val controls_selector = make_selector ctxt "future_provider_controls"
        control_definition
        @{term "comma_semantic_future_candidate_controls ! index"}
      val children_selector = make_selector ctxt "future_provider_children"
        child_definition
        @{term "comma_semantic_future_candidate_children ! index"}
      val output_rules =
        [@{thm comma_semantic_future_candidate_output_control_def},
           @{thm comma_semantic_future_candidate_output_north_id_def},
           @{thm comma_semantic_future_candidate_output_south_id_def},
           @{thm comma_semantic_future_candidate_output_north_def},
           @{thm comma_semantic_future_candidate_output_south_def},
           @{thm comma_semantic_future_candidate_class_step_def},
           @{thm comma_semantic_future_candidate_class_valid_def},
           @{thm comma_semantic_future_candidate_class_ids_def},
           @{thm comma_semantic_future_candidate_controls_def},
           @{thm comma_semantic_future_candidate_children_def}] @
        @{thms list.map nth_Cons_0 nth_Cons_Suc nth_Cons' map_filter.simps
          list.size prod.case_eq_if if_True if_False}
      val output_key_context = ctxt
        |> Simplifier.add_proc (#procedure controls_selector)
        |> Simplifier.add_proc (#procedure children_selector)
        |> Simplifier.add_simps
          ([ @{thm comma_semantic_future_candidate_class_output_key_def},
             @{thm comma_semantic_future_candidate_controls_def},
             @{thm comma_semantic_future_candidate_children_def} ] @
            @{thms list.map nth_Cons_0 nth_Cons_Suc nth_Cons' map_filter.simps
              list.size prod.case_eq_if if_True if_False})
      val distinct_ids = sort_distinct int_ord ids
      val _ = if length distinct_ids <= class_count then ()
        else error "Candidate output lookup memo exceeds the validated class table"
      val output_values = Symtab.make (map (fn id =>
        let
          val (result, _lookup_theorem) = candidate_output ctxt output_key_context
            class_count @{term comma_semantic_future_candidate_class_output_key}
            keyT id
        in (Int.toString id,
          parse_candidate_output_components ctxt class_count result) end)
        distinct_ids)
      fun output_at_id id =
        (case Symtab.lookup output_values (Int.toString id) of
          SOME components => components
        | NONE => error "Candidate output projection was not admitted")
      val arena = Data.make_arena 8192
      val control_serializer = Data.make_serializer arena control_optionT
      val child_serializer = Data.make_serializer arena natT
      val control_normalization_cache =
        Data.make_normalization_proof_cache ctxt arena control_optionT
      val child_normalization_cache =
        Data.make_normalization_proof_cache ctxt arena natT
      val payload_of = payload ctxt class_count

      val candidate_id_action_terms = HOLogic.dest_list
        (rewrite_rhs ctxt
          @{thm comma_semantic_future_candidate_id_selector_actions_def}
          @{term comma_semantic_future_candidate_id_selector_actions}
          "Candidate ID selectors")
      val source_nf_terms = HOLogic.dest_list
        (rewrite_rhs ctxt @{thm comma_semantic_graph_initial_nf_actions_def}
          @{term comma_semantic_graph_initial_nf_actions}
          "Authenticated initial source NF vector")
      val _ = if length candidate_id_action_terms = 16 andalso
          length source_nf_terms = 16 then ()
        else error "Provider NF action vectors have an unexpected family extent"

      val id_actions = map (parse_action payload_of ctxt arena natT id_actionT)
        candidate_id_action_terms
      val source_actions = map (parse_action payload_of ctxt arena b1_controlT b1_actionT)
        source_nf_terms
      val _ = List.app (check_stopped_source ctxt arena) source_actions

      fun candidate_projection id_action =
        Data.map_leaves arena
          (fn id_payload =>
            let
              val id = parse_nat ctxt (#value id_payload)
              val {control, ...} = output_at_id id
            in control end)
          id_action
      fun candidate_child_projection choose_north id_action =
        Data.map_leaves arena
          (fn id_payload =>
            let
              val id = parse_nat ctxt (#value id_payload)
              val {north, south, ...} = output_at_id id
            in if choose_north then north else south end)
          id_action
      fun candidate_components id_action =
        {control = Data.erase_weights arena
            (candidate_projection id_action),
         north = Data.erase_weights arena
            (candidate_child_projection true id_action),
         south = Data.erase_weights arena
            (candidate_child_projection false id_action)}
      fun source_components source_action =
        {control = make_source_control_action payload_of ctxt arena source_action,
         north = make_source_child_action payload_of ctxt arena id_actions
            (fn terminal => terminal) source_action,
         south = make_source_child_action payload_of ctxt arena id_actions
            (fn terminal => 8 + terminal) source_action}
      val raw_candidate_rows = map candidate_components id_actions
      val raw_source_rows = map source_components source_actions
      fun certify_control action = Data.certify_normalization ctxt arena
        control_optionT control_serializer control_normalization_cache action
      fun certify_child action = Data.certify_normalization ctxt arena
        natT child_serializer child_normalization_cache action
      fun certify_components ({control, north, south}: components): certificates =
        {control = certify_control control,
         north = certify_child north,
         south = certify_child south}
      val candidate_certificates = map certify_components raw_candidate_rows
      val source_certificates = map certify_components raw_source_rows
      fun normalized_components ({control,north,south}: certificates): components =
        {control = #normalized control, north = #normalized north,
         south = #normalized south}
      val candidate_diagrams = map normalized_components candidate_certificates
      val source_diagrams = map normalized_components source_certificates
      (* Controls are compared first.  Candidate child-table outputs are read
         only for Fork IDs; Landmine maps directly to the canonical Nat 0
         payload, matching the source mask without consulting child columns. *)
      val _ = List.app (fn (family, (candidate, source)) =>
        if Data.same_action arena (#control candidate) (#control source) andalso
            Data.same_action arena (#north candidate) (#north source) andalso
            Data.same_action arena (#south candidate) (#south source) then ()
        else
          let val s = Data.stats arena
          in error ("Candidate/source projected NF action mismatch in family " ^
            Int.toString family ^ "; nodes=" ^ Int.toString (#nodes s) ^
            " proofs=" ^ Int.toString (#proof_entries s) ^
            " peak=" ^ Int.toString (#peak_entries s)) end)
        (map_index (fn (family, candidate) =>
          (family, (candidate, List.nth (source_diagrams, family))))
          candidate_diagrams)

      fun component_action
          ({control, child}: {control: Data.serializer, child: Data.serializer})
          ({control=control_diagram, north, south}: components) =
        HOLogic.mk_prod (Data.action control control_diagram,
          HOLogic.mk_prod (Data.action child north,
            Data.action child south))
      val serializers = {control=control_serializer, child=child_serializer}
      val candidate_actions_term = HOLogic.mk_list key_actionT
        (map (component_action serializers) candidate_diagrams)
      val source_actions_term = HOLogic.mk_list key_actionT
        (map (component_action serializers) source_diagrams)
      val (candidate_actions, candidate_definition, lthy1) = define_constant
        "comma_semantic_future_candidate_provider_nf_candidate_actions"
        candidate_actions_term lthy
      val (source_actions, source_definition, lthy2) = define_constant
        "comma_semantic_future_candidate_provider_nf_source_actions"
        source_actions_term lthy1

      fun certificate_equations ({control,north,south}: certificates) =
        [#equation control,#equation north,#equation south]

      val candidate_refinements = map_index (fn (family, (raw_action, certificate)) =>
        let
          val family_term = nat family
          val candidate_logic = @{term comma_semantic_future_candidate_parent_key_action} $
            family_term
          val raw_term = component_action serializers raw_action
          val raw_proposition = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (raw_term, candidate_logic))
          val rules = [@{thm comma_semantic_future_candidate_parent_key_action_def},
            @{thm comma_semantic_future_crt_map_action_control_def},
            @{thm comma_semantic_future_crt_map_control.simps},
            @{thm comma_semantic_future_candidate_output_control_def},
            @{thm comma_semantic_future_candidate_output_north_id_def},
            @{thm comma_semantic_future_candidate_output_south_id_def},
            @{thm comma_semantic_future_candidate_output_north_def},
            @{thm comma_semantic_future_candidate_output_south_def},
            @{thm comma_semantic_future_candidate_class_output_key_def},
            @{thm comma_semantic_future_candidate_id_selector_actions_def},
            @{thm comma_semantic_future_candidate_id_selector_actions_length},
            @{thm comma_semantic_future_candidate_id_selector_actions_shape}] @
            @{thms comma_weighted_crt_shape.simps comma_crt_axis_radix_def
              comma_semantic_future_crt_map_control_shape list_all_iff
              list.map nth_Cons_0 nth_Cons_Suc nth_Cons' map_filter.simps
              list.size prod.case if_True if_False}
          val proof_context = Local_Theory.target_of lthy2
            |> Simplifier.add_proc (#procedure controls_selector)
            |> Simplifier.add_proc (#procedure children_selector)
            |> Simplifier.add_simps output_rules
          val raw_theorem = Goal.prove proof_context [] [] raw_proposition
            (fn {context, ...} => asm_full_simp_tac (Simplifier.add_simps (rules) (context)) 1)
            |> exact_closed proof_context
              ("raw candidate parent-key action family " ^ Int.toString family)
          val normalized_term = component_action serializers
            (normalized_components certificate)
          val phase = Free ("phase", natT)
          val normalized_proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
            ("phase", natT,
              HOLogic.mk_eq
                (key_apply $
                  normalized_term $ phase,
                 key_apply $
                  candidate_logic $ phase)))
          val theorem = Goal.prove proof_context [] [] normalized_proposition
            (fn {context, ...} => asm_full_simp_tac (Simplifier.add_simps ((rules @ certificate_equations certificate @ [raw_theorem,
                @{thm comma_semantic_future_projected_key_apply_def},
                @{thm comma_weighted_crt_apply_def}])) (context)) 1)
        in exact_closed proof_context theorem
            ("normalized candidate parent-key action family " ^ Int.toString family) end)
        (map_index (fn (family, raw_action) =>
          (raw_action, List.nth (candidate_certificates, family)))
          raw_candidate_rows)

      val source_refinements = map_index (fn (family, (raw_action, certificate)) =>
        let
          val source_logic =
            @{term comma_semantic_future_initial_nf_source_key_action} $ nat family
          val raw_term = component_action serializers raw_action
          val raw_proposition = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (raw_term, source_logic))
          val rules = [
            @{thm comma_semantic_future_initial_nf_source_key_action_def},
            @{thm comma_semantic_future_nf_key_action_def},
            @{thm comma_semantic_future_selected_phase_bind_def},
            @{thm comma_semantic_future_control_projection_action_def},
            @{thm comma_semantic_future_child_projection_action_def},
            @{thm comma_semantic_future_crt_forget_action_weights_def},
            @{thm comma_semantic_future_crt_phase_bind_def},
            @{thm comma_semantic_graph_initial_nf_actions_def}] @
            @{thms comma_semantic_future_crt_phase_bind_aux.simps
              comma_semantic_future_crt_forget_weights.simps
              comma_semantic_future_crt_map_control.simps
              comma_semantic_future_nf_control_of_crt.simps
              comma_weighted_crt_shift.simps
              comma_semantic_future_candidate_child_receiver_north_def
              comma_semantic_future_candidate_child_receiver_south_def
              comma_semantic_future_candidate_id_selector_actions_def
              comma_weighted_crt_shape.simps comma_crt_axis_radix_def
              list.map nth_Cons_0 nth_Cons_Suc nth_Cons'
              list.size list_all_iff map_option.simps
              map_filter.simps prod.case if_True if_False}
          val proof_context = Local_Theory.target_of lthy2
            |> Simplifier.add_proc (#procedure controls_selector)
            |> Simplifier.add_proc (#procedure children_selector)
            |> Simplifier.add_simps output_rules
          val raw_theorem = Goal.prove proof_context [] [] raw_proposition
            (fn {context, ...} => asm_full_simp_tac (Simplifier.add_simps (rules) (context)) 1)
            |> exact_closed proof_context
              ("raw source NF key action family " ^ Int.toString family)
          val normalized_term = component_action serializers
            (normalized_components certificate)
          val phase = Free ("phase", natT)
          val normalized_proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
            ("phase", natT,
              HOLogic.mk_eq
                (key_apply $
                  normalized_term $ phase,
                 key_apply $
                  source_logic $ phase)))
          val normalized_theorem = Goal.prove proof_context [] []
            normalized_proposition
            (fn {context, ...} => asm_full_simp_tac
              (Simplifier.add_simps ((rules @ certificate_equations certificate @ [raw_theorem,
                @{thm comma_semantic_future_projected_key_apply_def},
                @{thm comma_weighted_crt_apply_def}])) (context)) 1)
            |> exact_closed proof_context
              ("normalized source NF key action family " ^ Int.toString family)
        in normalized_theorem end)
        (map_index (fn (family, raw_action) =>
          (raw_action, List.nth (source_certificates, family))) raw_source_rows)

      val candidate_definition' = candidate_definition
      val source_definition' = source_definition
      val candidate_source_equal = prove (Local_Theory.target_of lthy2)
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (candidate_actions,source_actions)))
        [candidate_definition',source_definition']
        "candidate/source NF action-vector equality"
      val candidate_refinement_rows = map_index (fn (family, theorem) =>
        let
          val phase = Free ("phase",natT)
          val slot = nat family
          val action = Const (@{const_name nth},
            HOLogic.listT key_actionT --> natT --> key_actionT) $
              candidate_actions $ slot
          val source_result = @{term comma_semantic_future_initial_nf_source_key_action} $
            slot
          val lhs = key_apply $ action $ phase
          val rhs = key_apply $ source_result $ phase
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all ("phase",natT,
            HOLogic.mk_eq (lhs,rhs)))
        in Goal.prove (Local_Theory.target_of lthy2) [] [] proposition
          (fn {context, ...} => asm_full_simp_tac (Simplifier.add_simps ([List.nth (candidate_refinements,family),
             List.nth (source_refinements,family),
             candidate_source_equal, candidate_definition', source_definition',
             @{thm comma_semantic_future_projected_key_apply_def}]) (context)) 1)
          |> exact_closed (Local_Theory.target_of lthy2)
            ("all-phase provider NF family " ^ Int.toString family)
        end) (0 upto 15)

      val candidate_parent_refinement_rows = map_index (fn (family, theorem) =>
        let
          val phase = Free ("phase",natT)
          val slot = nat family
          val action = Const (@{const_name nth},
            HOLogic.listT key_actionT --> natT --> key_actionT) $
              candidate_actions $ slot
          val parent_key = @{term comma_semantic_future_candidate_parent_key_action} $
            slot
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all ("phase",natT,
            HOLogic.mk_eq
              (key_apply $ action $ phase,
               key_apply $ parent_key $ phase)))
        in Goal.prove (Local_Theory.target_of lthy2) [] [] proposition
          (fn {context, ...} => asm_full_simp_tac (Simplifier.add_simps ([List.nth (candidate_refinements,family), candidate_definition',
             @{thm comma_semantic_future_projected_key_apply_def}]) (context)) 1)
          |> exact_closed (Local_Theory.target_of lthy2)
            ("candidate provider NF row to parent-key action " ^
              Int.toString family)
        end) (0 upto 15)

      val parent_family_term = Free ("family_slot",natT)
      val parent_phase_term = Free ("phase",natT)
      val parent_action_at = Const (@{const_name nth},
        HOLogic.listT key_actionT --> natT --> key_actionT) $ candidate_actions $
          parent_family_term
      val parent_key_at = @{term comma_semantic_future_candidate_parent_key_action} $
        parent_family_term
      val parent_family_predicate = Term.lambda parent_family_term
        (HOLogic.mk_all ("phase",natT,
          HOLogic.mk_eq
            (key_apply $
              parent_action_at $ parent_phase_term,
             key_apply $
              parent_key_at $ parent_phase_term)))
      val parent_family_prop = HOLogic.mk_Trueprop
        (Const (@{const_name list_all},(natT --> HOLogic.boolT) -->
          HOLogic.listT natT --> HOLogic.boolT) $ parent_family_predicate $
            @{term "[0..<16] :: nat list"})
      val parent_family_all = Goal.prove (Local_Theory.target_of lthy2) [] []
        parent_family_prop
        (fn {context, ...} => asm_full_simp_tac (Simplifier.add_simps ((candidate_parent_refinement_rows @
            @{thms list_all_iff set_upt atLeastLessThan_iff nth_Cons_0
              nth_Cons_Suc nth_Cons' list.map})) (context)) 1)
        |> exact_closed (Local_Theory.target_of lthy2)
          "all-family candidate NF to parent-key action transport"

      val family_term = Free ("family_slot",natT)
      val phase_term = Free ("phase",natT)
      val action_at = Const (@{const_name nth},
        HOLogic.listT key_actionT --> natT --> key_actionT) $ candidate_actions $
          family_term
      val source_key = @{term comma_semantic_future_initial_nf_source_key_action} $
        family_term
      val all_family_predicate = Term.lambda family_term
        (HOLogic.mk_all ("phase",natT,
          HOLogic.mk_imp
            (HOLogic.mk_binrel @{const_name less} (phase_term,nat 924),
             HOLogic.mk_eq
               (key_apply $ action_at $ phase_term,
                key_apply $ source_key $ phase_term))))
      val all_family_prop = HOLogic.mk_Trueprop
        (Const (@{const_name list_all},(natT --> HOLogic.boolT) -->
          HOLogic.listT natT --> HOLogic.boolT) $ all_family_predicate $
          @{term "[0..<16] :: nat list"})
      val all_family = Goal.prove (Local_Theory.target_of lthy2) [] [] all_family_prop
        (fn {context, ...} => asm_full_simp_tac (Simplifier.add_simps ((candidate_refinement_rows @
            @{thms list_all_iff set_upt atLeastLessThan_iff nth_Cons_0
              nth_Cons_Suc nth_Cons' list.map})) (context)) 1)
        |> exact_closed (Local_Theory.target_of lthy2)
          "all-family source-to-candidate provider NF transport"

      val action_list_length = prove (Local_Theory.target_of lthy2)
        (HOLogic.mk_Trueprop (HOLogic.mk_eq
          (Const (@{const_name length}, HOLogic.listT key_actionT --> natT) $
            candidate_actions, nat 16)))
        [candidate_definition'] "candidate provider NF vector length"
      val source_action_list_length = prove (Local_Theory.target_of lthy2)
        (HOLogic.mk_Trueprop (HOLogic.mk_eq
          (Const (@{const_name length}, HOLogic.listT key_actionT --> natT) $
            source_actions, nat 16)))
        [source_definition'] "source provider NF vector length"
      fun projected_action_shape actions definition label =
        let
          val action = Free ("action", key_actionT)
          val control_action = HOLogic.mk_fst action
          val child_actions = HOLogic.mk_snd action
          val north_action = HOLogic.mk_fst child_actions
          val south_action = HOLogic.mk_snd child_actions
          fun shape action_term dagT =
            Const (@{const_name comma_weighted_crt_shape},
              natT --> Type (@{type_name comma_semantic_weighted_crt_dag},[dagT]) -->
                HOLogic.boolT) $ nat 0 $ HOLogic.mk_snd action_term
          val row_shape = HOLogic.mk_conj
            (shape control_action control_optionT,
              HOLogic.mk_conj (shape north_action natT, shape south_action natT))
          val proposition = HOLogic.mk_Trueprop
            (Const (@{const_name list_all},(key_actionT --> HOLogic.boolT) -->
              HOLogic.listT key_actionT --> HOLogic.boolT) $
              (Term.lambda action row_shape) $ actions)
        in prove (Local_Theory.target_of lthy2) proposition
          ([definition] @ @{thms comma_weighted_crt_shape.simps
            comma_crt_axis_radix_def list_all_iff list.map}) label end
      val candidate_action_shape = projected_action_shape candidate_actions
        candidate_definition' "candidate provider NF component shapes"
      val source_action_shape = projected_action_shape source_actions
        source_definition' "source provider NF component shapes"

      val _ = Comma_Proof_Dependency_Audit.require_native_clean
        (Local_Theory.target_of lthy2)
        "Future candidate/source action NF comparison"
        ([candidate_source_equal,all_family,parent_family_all,action_list_length,
          source_action_list_length,candidate_action_shape,source_action_shape] @
          candidate_parent_refinement_rows)
      val (_, lthy3) = note
        "comma_semantic_future_candidate_provider_nf_actions_equal"
        candidate_source_equal lthy2
      val (_, lthy4) = note
        "comma_semantic_future_candidate_source_key_nf_all_phases"
        all_family lthy3
      val (_, lthy5) = note
        "comma_semantic_future_candidate_parent_key_nf_all_phases"
        parent_family_all lthy4
      val (_, lthy6) = note
        "comma_semantic_future_candidate_provider_nf_candidate_actions_length"
        action_list_length lthy5
      val (_, lthy7) = note
        "comma_semantic_future_candidate_provider_nf_source_actions_length"
        source_action_list_length lthy6
      val (_, lthy8) = note
        "comma_semantic_future_candidate_provider_nf_candidate_actions_shape"
        candidate_action_shape lthy7
      val (_, lthy9) = note
        "comma_semantic_future_candidate_provider_nf_source_actions_shape"
        source_action_shape lthy8
      val stats = Data.stats arena
      val _ = if #scratch_entries stats = 0 andalso #peak_entries stats <= 8192 then ()
        else error "Future provider NF exceeded its shared node/proof/scratch envelope"
      val _ = Output.information ("future_provider_nf_nodes=" ^
        Int.toString (#nodes stats) ^ " proofs=" ^
        Int.toString (#proof_entries stats) ^ " peak=" ^
        Int.toString (#peak_entries stats))
    in lthy9 end
end
