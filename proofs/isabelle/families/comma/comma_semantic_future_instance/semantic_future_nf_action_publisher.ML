(* Import the authenticated 16 source actions and the rank-owned 46-action
   B32 vector into one weighted CRT arena.  Only the 16 source/B32 products
   are built and normalized here; this owner does not compile a second B32. *)
signature COMMA_SEMANTIC_FUTURE_NF_ACTION_PUBLISHER =
sig
  val publish: local_theory -> local_theory
end

structure Comma_Semantic_Future_NF_Action_Publisher:
  COMMA_SEMANTIC_FUTURE_NF_ACTION_PUBLISHER =
struct
  structure DAG = Comma_Semantic_Weighted_CRT_DAG
  structure Transport = Comma_Semantic_Weighted_CRT_Data_Transport

  val natT = @{typ nat}
  val actionT = @{typ nat \<times> comma_semantic_b1_crt_dag}
  val dagT = @{typ comma_semantic_b1_crt_dag}

  fun nat n = HOLogic.mk_number natT n

  fun closed proposition = not (Term.is_open proposition) andalso
    null (Term.add_frees proposition []) andalso
    null (Term.add_vars proposition [])

  fun define name value lthy =
    let
      val ((constant, (_, definition)), lthy') = Local_Theory.define
        ((Binding.name name, NoSyn),
          ((Binding.name (name ^ "_def"), []), value)) lthy
      val morphism = Local_Theory.target_morphism lthy'
    in (Morphism.term morphism constant, Morphism.thm morphism definition, lthy') end

  fun note name theorem lthy =
    snd (Local_Theory.note ((Binding.name name, []), [theorem]) lthy)

  fun rewrite_rhs ctxt theorem constant label =
    let
      val rewritten = Simplifier.rewrite
        (Simplifier.add_simps [theorem] ctxt) (Thm.cterm_of ctxt constant)
      val rhs = Thm.term_of (Thm.rhs_of rewritten)
      val _ = if Thm.term_of (Thm.lhs_of rewritten) aconv constant andalso
          Thm.nprems_of rewritten = 0 andalso null (Thm.hyps_of rewritten) andalso
          null (Thm.tpairs_of rewritten) andalso closed rhs then ()
        else error (label ^ " did not rewrite to a closed literal")
    in (rhs, rewritten) end

  fun expand ctxt constant rules label =
    let
      val rewritten = Simplifier.rewrite
        (Simplifier.add_simps rules ctxt) (Thm.cterm_of ctxt constant)
      val rhs = Thm.term_of (Thm.rhs_of rewritten)
      val _ = if Thm.term_of (Thm.lhs_of rewritten) aconv constant andalso
          Thm.nprems_of rewritten = 0 andalso null (Thm.hyps_of rewritten) andalso
          null (Thm.tpairs_of rewritten) andalso closed rhs then ()
        else error (label ^ " expansion is open or has unresolved premises")
    in (rhs, rewritten) end

  fun exact_object ctxt proposition theorem =
    if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem) andalso closed (Thm.prop_of theorem) andalso
        Thm.prop_of theorem aconv proposition andalso
        Context.subthy (Thm.theory_of_thm theorem, Proof_Context.theory_of ctxt)
      then theorem
    else error "Future NF object proof has the wrong proposition or open hypotheses"

  fun list_all elementT predicate values =
    Const (@{const_name list_all},
      (elementT --> HOLogic.boolT) --> HOLogic.listT elementT --> HOLogic.boolT) $
      predicate $ values

  fun define_action_vector lthy action_terms =
    let
      val _ = if length action_terms = 16 andalso
          List.all (fn term => fastype_of term = actionT andalso closed term)
            action_terms then ()
        else error "Future NF compiler did not return sixteen closed actions"
      val action_list = HOLogic.mk_list actionT action_terms
    in define "comma_semantic_graph_initial_nf_actions" action_list lthy end

  fun apply_action_equation ctxt action_equality phase =
    let
      val apply_const = Const (@{const_name comma_weighted_crt_apply},
        actionT --> natT --> Type (@{type_name option},
          [HOLogic.mk_prodT (@{typ comma_semantic_b1_crt_control}, natT)]))
      val applied_meta = Thm.combination
        (Thm.combination (Thm.reflexive (Thm.cterm_of ctxt apply_const))
          action_equality)
        (Thm.reflexive (Thm.cterm_of ctxt phase))
    in applied_meta RS @{thm meta_eq_to_obj_eq} end

  fun universally ctxt phase theorem =
    Thm.forall_intr (Thm.cterm_of ctxt phase) theorem COMP @{thm allI}

  fun publish lthy =
    let
      val ctxt = Local_Theory.target_of lthy
      val source_const = @{term comma_semantic_graph_initial_source_actions}
      val (source_list, source_definition) = rewrite_rhs ctxt
        @{thm comma_semantic_graph_initial_source_actions_def}
        source_const "Authenticated source action vector"
      val source_terms = HOLogic.dest_list source_list
      val _ = if length source_terms = 16 andalso
          List.all (fn action => fastype_of action = actionT) source_terms then ()
        else error "Authenticated source action vector is not length 16"

      val rank_const = @{term comma_semantic_future_rank_b32_weighted_actions}
      val rank_rules = @{thms
        comma_semantic_future_rank_b32_weighted_actions_def
        comma_semantic_b1_crt_power.simps comma_semantic_b1_crt_compose_def
        comma_semantic_b1_crt_add_stop_def comma_semantic_b1_crt_leaf_def
        comma_semantic_b1_crt_invalid_action_def comma_weighted_crt_bind.simps
        comma_weighted_crt_shift.simps comma_semantic_future_rank_action_roots_def
        comma_semantic_future_b1_control_of_rank_action.simps
        comma_semantic_phase_class_rank_action_roots_def
        list.map fst_conv snd_conv nth_Cons_0 nth_Cons_Suc nth_Cons'}
      val (rank_list, rank_definition) = expand ctxt rank_const rank_rules
        "Rank-owned B32 action vector"
      val rank_terms = HOLogic.dest_list rank_list
      val _ = if length rank_terms = 46 andalso
          List.all (fn action => fastype_of action = actionT) rank_terms then ()
        else error "Rank-owned B32 action vector is not length 46"

      val arena = DAG.make_arena 131072
      val serializer = DAG.make_serializer arena
      val cache = DAG.make_normalization_proof_cache ctxt arena
      val source_diagrams = Vector.fromList
        (map (DAG.import_action_term arena) source_terms)
      val rank_diagrams = Vector.fromList
        (map (DAG.import_action_term arena) rank_terms)
      val compose_const = Const (@{const_name comma_semantic_b1_crt_compose},
        natT --> actionT --> HOLogic.listT actionT --> actionT)
      val apply_const = Const (@{const_name comma_weighted_crt_apply},
        actionT --> natT --> Type (@{type_name option},
          [HOLogic.mk_prodT (@{typ comma_semantic_b1_crt_control}, natT)]))
      val compiler_rules = @{thms comma_semantic_b1_crt_compose_def
        comma_semantic_b1_crt_add_stop_def comma_semantic_b1_crt_leaf_def
        comma_semantic_b1_crt_invalid_action_def comma_weighted_crt_bind.simps
        comma_weighted_crt_shift.simps comma_semantic_b1_crt_control.case
        fst_conv snd_conv list.map nth_Cons_0 nth_Cons_Suc nth_Cons'}
      val normalization_equations = Unsynchronized.ref ([]: thm list)
      val composer_equations = Unsynchronized.ref ([]: thm list)
      val row_equations = Unsynchronized.ref ([]: thm list)
      val normalized_terms =
        Vector.tabulate (16, fn index =>
          let
            val source = Vector.sub (source_diagrams, index)
            val (raw, normalized) = DAG.apply arena 1 source rank_diagrams
            val raw_term = DAG.serialize_action serializer raw
            val normalized_term = DAG.serialize_action serializer normalized
            val (raw_offset, _) = HOLogic.dest_prod raw_term
            val normalizer = DAG.certify_normalization ctxt arena serializer cache raw
            val normalized_to_raw =
              Transport.specialize_hol_all ctxt raw_offset (#equation normalizer)
              |> Transport.object_symmetric ctxt
              |> Simplifier.rewrite_rule
                (Comma_Entry_Arithmetic.numeral_context ctxt) []
            val expected_compose = compose_const $ nat 1 $
              List.nth (source_terms, index) $ rank_const
            val composer = DAG.compiler_expression_reflexive ctxt serializer raw
              expected_compose (rank_definition :: compiler_rules)
            val phase = Free ("future_nf_phase", natT)
            val norm_eq_phase =
              Transport.specialize_hol_all ctxt phase normalized_to_raw
            val compose_eq_phase = apply_action_equation ctxt composer phase
            val row_equation =
              (Thm.transitive
                (norm_eq_phase RS @{thm eq_reflection})
                (compose_eq_phase RS @{thm eq_reflection}))
              RS @{thm meta_eq_to_obj_eq}
            val row_proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
              ("future_nf_phase", natT,
                HOLogic.mk_eq (apply_const $ normalized_term $ phase,
                  apply_const $ expected_compose $ phase)))
            val row_theorem = universally ctxt phase row_equation
              |> exact_object ctxt row_proposition
            val _ = normalization_equations := #equation normalizer ::
              !normalization_equations
            val _ = composer_equations := composer :: !composer_equations
            val _ = row_equations := row_theorem :: !row_equations
          in normalized_term end)
      val actions_terms = Vector.foldr op:: [] normalized_terms
      val (nf_constant, nf_definition, lthy1) =
        define_action_vector lthy actions_terms
      val slot = Free ("future_nf_slot", natT)
      val phase = Free ("future_nf_phase", natT)
      val nth_action = Const (@{const_name nth},
        HOLogic.listT actionT --> natT --> actionT)
      val source_action = Const (@{const_name nth},
        HOLogic.listT actionT --> natT --> actionT) $ source_const $ slot
      val nf_action = nth_action $ nf_constant $ slot
      val compose = compose_const $ nat 1 $ source_action $ rank_const
      val row = HOLogic.mk_all ("future_nf_phase", natT,
        HOLogic.mk_imp (HOLogic.mk_binrel @{const_name less} (slot, nat 16),
          HOLogic.mk_eq (apply_const $ nf_action $ phase,
            apply_const $ compose $ phase)))
      val refinement_predicate = Term.lambda slot row
      val refinement_prop = HOLogic.mk_Trueprop
        (list_all natT refinement_predicate @{term "[0..<16]::nat list"})
      val refinement = Goal.prove (Local_Theory.target_of lthy1) [] [] refinement_prop
        (fn {context, ...} => asm_full_simp_tac
          (Simplifier.add_simps
            ([nf_definition, source_definition] @
             Vector.foldr op:: [] row_equations @
             @{thms list_all_iff set_upt atLeastLessThan_iff upt_rec
               nth_Cons_0 nth_Cons_Suc nth_Cons' list.map}) context) 1)
        |> exact_object (Local_Theory.target_of lthy1) refinement_prop

      val length_prop = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (Const (@{const_name size}, HOLogic.listT actionT --> natT) $
          nf_constant, nat 16))
      val length_thm = Goal.prove (Local_Theory.target_of lthy1) [] [] length_prop
        (fn {context, ...} => asm_full_simp_tac
          (Simplifier.add_simps [nf_definition] context) 1)
        |> exact_object (Local_Theory.target_of lthy1) length_prop

      val action = Free ("future_nf_action", actionT)
      val wellformed_prop = HOLogic.mk_Trueprop (list_all actionT
        (Term.lambda action (@{term comma_weighted_crt_wellformed} $
          (Const (@{const_name snd}, actionT --> dagT) $ action))) nf_constant)
      val wellformed = Goal.prove (Local_Theory.target_of lthy1) [] [] wellformed_prop
        (fn {context, ...} => asm_full_simp_tac
          (Simplifier.add_simps ([nf_definition] @
            @{thms comma_weighted_crt_wellformed.simps comma_crt_axis_radix_def
              list_all_iff}) context) 1)
        |> exact_object (Local_Theory.target_of lthy1) wellformed_prop

      val shape_prop = HOLogic.mk_Trueprop (list_all actionT
        (Term.lambda action (@{term comma_weighted_crt_shape} $ nat 0 $
          (Const (@{const_name snd}, actionT --> dagT) $ action))) nf_constant)
      val shape = Goal.prove (Local_Theory.target_of lthy1) [] [] shape_prop
        (fn {context, ...} => asm_full_simp_tac
          (Simplifier.add_simps ([nf_definition] @
            @{thms comma_weighted_crt_shape.simps comma_crt_axis_radix_def
              list_all_iff}) context) 1)
        |> exact_object (Local_Theory.target_of lthy1) shape_prop

      val exported = Vector.foldr op:: [] row_equations @
        Vector.foldr op:: [] normalization_equations @
        Vector.foldr op:: [] composer_equations @
        [source_definition, rank_definition, nf_definition, refinement,
          length_thm, wellformed, shape]
      val _ = Thm.consolidate exported
      val _ = Comma_Proof_Dependency_Audit.require_native_clean
        (Local_Theory.target_of lthy1)
        "Sixteen source actions composed with rank-owned B32 and normalized"
        exported
      val lthy2 = note "comma_semantic_graph_initial_nf_actions_refine"
        refinement lthy1
      val lthy3 = note "comma_semantic_graph_initial_nf_actions_length"
        length_thm lthy2
      val lthy4 = note "comma_semantic_graph_initial_nf_actions_wellformed"
        wellformed lthy3
      val lthy5 = note "comma_semantic_graph_initial_nf_actions_shape"
        shape lthy4
    in lthy5 end
end
