structure Comma_Semantic_Future_Candidate_Selector_Publisher =
struct
  val natT = @{typ nat}

  fun numeral n = HOLogic.mk_number natT n

  fun length_term list =
    Const (@{const_name length}, fastype_of list --> natT) $ list

      fun make_list elementT values = HOLogic.mk_list elementT values

  fun checked_closed ctxt theorem label =
    if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem) andalso
        not (Term.is_open (Thm.prop_of theorem)) andalso
        null (Term.add_frees (Thm.prop_of theorem) []) andalso
        null (Term.add_vars (Thm.prop_of theorem) []) andalso
        null (Thm_Deps.all_oracles [theorem]) then theorem
    else error (label ^ " is not a closed native theorem")

  fun prove ctxt proposition rules =
    let
      val theorem = Goal.prove ctxt [] [] proposition
        (fn {context, ...} =>
          asm_full_simp_tac (context addsimps rules) 1)
    in checked_closed ctxt theorem "Future candidate selector proof" end

  fun parse_nat term =
    (case try HOLogic.dest_number term of
      SOME (typ, value) =>
        if typ = natT andalso value >= 0 then IntInf.toInt value
        else error "Candidate selector input contains a non-natural label"
    | NONE => error "Candidate selector input contains a non-numeral")

  fun note name theorem lthy =
    snd (Local_Theory.note ((Binding.name name, []), [theorem]) lthy)

  fun define_constant name value lthy =
    let
      val ((constant, (_, definition)), lthy') = Local_Theory.define
        ((Binding.name name, NoSyn),
          ((Binding.name (name ^ "_def"), []), value)) lthy
      val morphism = Local_Theory.target_morphism lthy'
    in (Morphism.term morphism constant,
      Morphism.thm morphism definition, lthy') end

  fun publish lthy =
    let
      val ctxt = Local_Theory.target_of lthy
      val ids = @{term comma_semantic_future_candidate_class_ids}
      val ids_definition = checked_closed ctxt
        @{thm comma_semantic_future_candidate_class_ids_def}
        "Candidate source-ID definition"
      val controls_definition = checked_closed ctxt
        @{thm comma_semantic_future_candidate_controls_def}
        "Candidate class-control definition"
      val ids_values = HOLogic.dest_list (Thm.term_of (Thm.rhs_of ids_definition))
        |> map parse_nat
      val control_values = HOLogic.dest_list
        (Thm.term_of (Thm.rhs_of controls_definition))
      val class_count = length control_values
      val _ = if length ids_values = 16*924 then ()
        else error "Candidate source-ID vector must contain exactly 16 by 924 labels"
      val _ = if class_count > 0 andalso class_count <= 65536 andalso
          List.all (fn id => 0 <= id andalso id < class_count) ids_values then ()
        else error "Candidate source-ID vector contains an out-of-range class label"
      val slices = map (fn family =>
        let val values = take 924 (drop (family*924) ids_values)
        in if length values = 924 then values
          else error "Candidate family slice has the wrong phase extent" end)
        (0 upto 15)
      val arena = Comma_Semantic_Weighted_CRT_Data.make_arena 8192
      fun payload value:
          Comma_Semantic_Weighted_CRT_Data.payload =
        {key="future-class-id:" ^ Int.toString value,
         value=numeral value}
      val raw_diagrams = map (Comma_Semantic_Weighted_CRT_Data.compile_selector arena 924 o
        (fn values => map payload values)) slices
      val serializer = Comma_Semantic_Weighted_CRT_Data.make_serializer arena natT
      val normalization_cache =
        Comma_Semantic_Weighted_CRT_Data.make_normalization_proof_cache
          ctxt arena natT
      val certified = map (Comma_Semantic_Weighted_CRT_Data.certify_normalization
        ctxt arena natT serializer normalization_cache) raw_diagrams
      val normalized = map #normalized certified
      val actions = map (Comma_Semantic_Weighted_CRT_Data.action serializer) normalized
      val raw_trees = map (Comma_Semantic_Weighted_CRT_Data.tree serializer) raw_diagrams
      val axes = make_list natT (map numeral [0,1,2,3])
      val selector_auxT = @{typ "nat list => nat => nat => nat list =>
        nat comma_semantic_weighted_crt_dag"}
      val selector_aux = Const (@{const_name comma_weighted_crt_selector_aux},
        selector_auxT)
      val slice_fun = Const (@{const_name comma_semantic_future_candidate_id_family_slice},
        @{typ "nat list => nat => nat list"})
      val selector_specs = @{term comma_semantic_future_candidate_id_selector_specs}
      val family_slice_tree = fn family => selector_aux $ axes $ numeral 924 $ numeral 0 $
        (slice_fun $ ids $ numeral family)
      val simp_rules = ids_definition :: controls_definition ::
        @{thms comma_semantic_future_candidate_id_family_slice_def
          comma_semantic_future_candidate_id_selector_specs_def
          comma_weighted_crt_selector_aux.simps comma_crt_axis_weight_def
          comma_crt_axis_radix_def list.map upt_rec nth_Cons_0 nth_Cons_Suc
          nth_Cons' list.size}
      fun raw_selector_equation family raw_tree =
        prove ctxt (HOLogic.mk_Trueprop
          (HOLogic.mk_eq (raw_tree, family_slice_tree family))) simp_rules
      val selector_equations = map raw_selector_equation (0 upto 15) raw_trees
      val ids_length = prove ctxt (HOLogic.mk_Trueprop
        (HOLogic.mk_eq (length_term ids, numeral (16*924))) [ids_definition])
      val actionT = HOLogic.mk_prodT (natT,
        Type (@{type_name comma_semantic_weighted_crt_dag}, [natT]))
      fun shape_const payloadT =
        Const (@{const_name comma_weighted_crt_shape},
          natT --> Type (@{type_name comma_semantic_weighted_crt_dag}, [payloadT]) -->
            HOLogic.boolT)
      fun wellformed_const payloadT =
        Const (@{const_name comma_weighted_crt_wellformed},
          Type (@{type_name comma_semantic_weighted_crt_dag}, [payloadT]) -->
            HOLogic.boolT)
      val actions_term = make_list actionT actions
      val (actions_constant, actions_definition, lthy1) = define_constant
        "comma_semantic_future_candidate_id_selector_actions" actions_term lthy
      val actions_length = prove (Local_Theory.target_of lthy1)
        (HOLogic.mk_Trueprop (HOLogic.mk_eq
          (length_term actions_constant, numeral 16))) [actions_definition]
      val apply_const = Const (@{const_name comma_weighted_crt_apply},
        actionT --> natT --> Type (@{type_name option},
          [HOLogic.mk_prodT (natT,natT)]))
      val vector_nth = Const (@{const_name nth}, HOLogic.listT natT --> natT --> natT) $ ids
      val phase = Free ("phase", natT)
      fun action_at_family family =
        Const (@{const_name nth}, HOLogic.listT actionT --> natT --> actionT) $
          actions_constant $ numeral family
      fun normalization_at family =
        let
          val theorem = #equation (List.nth (certified, family))
          val root = Thm.forall_elim (Thm.cterm_of ctxt (numeral 0)) theorem
        in Thm.forall_elim (Thm.cterm_of ctxt phase) root end
      fun family_refinement family =
        let
          val action = action_at_family family
          val selected_index =
            HOLogic.mk_binop @{const_name plus} (numeral (924*family), phase)
          val selected_id = vector_nth $ selected_index
          val result = HOLogic.mk_eq
            (apply_const $ action $ phase,
              Const (@{const_name Some}, HOLogic.mk_prodT (natT,natT) -->
                Type (@{type_name option}, [HOLogic.mk_prodT (natT,natT)])) $
                HOLogic.mk_prod (selected_id, numeral 0))
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all ("phase",natT,
            HOLogic.mk_imp
              (HOLogic.mk_binrel @{const_name less} (phase,numeral 924), result)))
          val norm_eq = normalization_at family
          val generated_tree = List.nth (raw_trees,family)
          val tree_equation = List.nth (selector_equations,family)
          val generated_selector = family_slice_tree family
          val selector_spec_action = @{thm
            comma_semantic_future_candidate_id_selector_spec_action_apply}
          val family_bound = prove ctxt
            (HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less}
              (numeral family,numeral 16))) []
          val facts = [norm_eq, tree_equation, ids_length, family_bound,
              selector_spec_action, actions_definition] @
            @{thms comma_weighted_crt_apply_def
              comma_semantic_future_candidate_id_selector_specs_def
              comma_semantic_future_candidate_id_family_slice_def
              comma_semantic_future_candidate_id_selector_spec_action_apply
              comma_semantic_future_candidate_id_family_slice_nth
              comma_weighted_crt_selector_aux_exact}
        in
          prove (Local_Theory.target_of lthy1) proposition facts
        end
      val family_refinements = map family_refinement (0 upto 15)
      fun all_phase_rows actions_value =
        let
          val family = Free ("family",natT)
          val selected_action = Const (@{const_name nth},
            HOLogic.listT actionT --> natT --> actionT) $ actions_value $ family
          val selected_index = HOLogic.mk_binop @{const_name plus}
            (HOLogic.mk_binop @{const_name times} (numeral 924,family), phase)
          val result = HOLogic.mk_eq
            (apply_const $ selected_action $ phase,
              Const (@{const_name Some}, HOLogic.mk_prodT (natT,natT) -->
                Type (@{type_name option}, [HOLogic.mk_prodT (natT,natT)])) $
                HOLogic.mk_prod (vector_nth $ selected_index,numeral 0))
          val predicate = Term.lambda family (HOLogic.mk_all ("phase", natT,
            HOLogic.mk_imp
              (HOLogic.mk_binrel @{const_name less} (phase,numeral 924), result)))
        in Const (@{const_name list_all}, (natT --> HOLogic.boolT) -->
          HOLogic.listT natT --> HOLogic.boolT) $ predicate $
          @{term "[0..<16] :: nat list"} end
      val rows_prop = HOLogic.mk_Trueprop (all_phase_rows actions_constant)
      val rows_theorem = Goal.prove (Local_Theory.target_of lthy1) [] [] rows_prop
        (fn {context, ...} =>
          asm_full_simp_tac (context addsimps
            (actions_definition :: family_refinements @
              @{thms list_all_iff set_upt atLeastLessThan_iff
                nth_Cons_0 nth_Cons_Suc nth_Cons' list.map})) 1)
      val rows_theorem = checked_closed (Local_Theory.target_of lthy1)
        rows_theorem "Candidate selector 16-family vector refinement"
      val shape_terms = map (fn action =>
        HOLogic.mk_Trueprop (shape_const natT $
          numeral 0 $ (HOLogic.mk_snd action))) actions
      val shape_facts = map (fn proposition =>
        prove (Local_Theory.target_of lthy1) proposition
          (@{thms comma_weighted_crt_shape.simps comma_crt_axis_radix_def
            list_all_iff list.map})) shape_terms
      val shape_prop = HOLogic.mk_Trueprop
        (Const (@{const_name list_all}, (actionT --> HOLogic.boolT) -->
            HOLogic.listT actionT --> HOLogic.boolT) $
          Term.lambda (Free ("action",actionT))
            (shape_const natT $ numeral 0 $
              (HOLogic.mk_snd (Free ("action",actionT)))) $ actions_constant)
      val shape_theorem = Goal.prove (Local_Theory.target_of lthy1) [] [] shape_prop
        (fn {context, ...} => asm_full_simp_tac (context addsimps
          (actions_definition :: shape_facts @
            @{thms list_all_iff list.map nth_Cons_0 nth_Cons_Suc nth_Cons'})) 1)
        |> checked_closed (Local_Theory.target_of lthy1)
          "Candidate selector shape vector"
      val wellformed_facts = map2 (fn action => fn shape_fact =>
        Goal.prove (Local_Theory.target_of lthy1) [] []
          (HOLogic.mk_Trueprop (wellformed_const natT $
            (HOLogic.mk_snd action)))
          (fn {context, ...} =>
            resolve_tac context [@{thm comma_weighted_crt_shape_wellformed}] 1 THEN
            resolve_tac context [shape_fact] 1)
          |> checked_closed (Local_Theory.target_of lthy1)
            "Candidate selector wellformed action") actions shape_facts
      val wellformed_prop = HOLogic.mk_Trueprop
        (Const (@{const_name list_all}, (actionT --> HOLogic.boolT) -->
            HOLogic.listT actionT --> HOLogic.boolT) $
          Term.lambda (Free ("action",actionT))
            (wellformed_const natT $ HOLogic.mk_snd
              (Free ("action",actionT))) $ actions_constant)
      val wellformed_theorem = Goal.prove (Local_Theory.target_of lthy1) [] []
        wellformed_prop (fn {context, ...} =>
          asm_full_simp_tac (context addsimps
            (actions_definition :: wellformed_facts @
              @{thms list_all_iff list.map nth_Cons_0 nth_Cons_Suc nth_Cons'})) 1)
        |> checked_closed (Local_Theory.target_of lthy1)
          "Candidate selector wellformed vector"
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Future candidate selector DAG and 16-family phase transport"
        (ids_definition :: controls_definition :: ids_length ::
          map #equation certified @ selector_equations @ family_refinements @
          [rows_theorem,actions_length,shape_theorem,wellformed_theorem])
      val (_, lthy2) = note
        "comma_semantic_future_candidate_id_selector_actions_refine"
        rows_theorem lthy1
      val (_, lthy3) = note
        "comma_semantic_future_candidate_id_selector_actions_shape"
        shape_theorem lthy2
      val (_, lthy4) = note
        "comma_semantic_future_candidate_id_selector_actions_wellformed"
        wellformed_theorem lthy3
      val (_, lthy5) = note
        "comma_semantic_future_candidate_id_selector_actions_length"
        actions_length lthy4
      val (_, lthy9) = note
        "comma_semantic_future_candidate_class_ids_length"
        ids_length lthy5
      val final_stats = Comma_Semantic_Weighted_CRT_Data.stats arena
      val _ = if #nodes final_stats + #proof_entries final_stats +
          #scratch_entries final_stats <= 8192 andalso
          #scratch_entries final_stats = 0 andalso
          #peak_entries final_stats <= 8192 then ()
        else error "Future candidate selector exceeded the shared CRT arena envelope"
      val _ = Output.information
        ("candidate_selector_families=16 phases=924 interned_nodes=" ^
          Int.toString (#nodes final_stats) ^ " proof_entries=" ^
          Int.toString (#proof_entries final_stats) ^ " scratch_entries=" ^
          Int.toString (#scratch_entries final_stats) ^ " peak_entries=" ^
          Int.toString (#peak_entries final_stats))
    in lthy9 end
end
