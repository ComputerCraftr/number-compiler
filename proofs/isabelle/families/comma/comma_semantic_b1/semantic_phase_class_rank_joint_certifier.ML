(* Kernel-checked local constructors for a shared-reference rank certificate.
   These constructors accept shallow node equations and already checked child
   relations.  They never enumerate phases or accept an ML boolean as proof. *)
structure Comma_Semantic_Phase_Class_Rank_Joint_Certifier =
struct
  structure Transport = Comma_Semantic_Weighted_CRT_Data_Transport

  val natT = @{typ nat}
  val actionT = @{typ "comma_phase_rank_mask_action comma_semantic_weighted_crt_dag"}
  val rankT = @{typ "nat comma_semantic_weighted_crt_dag"}
  val successorsT = natT --> Type (@{type_name option}, [rankT])

  fun relation action current successors phase =
    Const (@{const_name comma_crt_rank_relation},
      actionT --> rankT --> successorsT --> natT --> HOLogic.boolT) $
      action $ current $ successors $ phase

  fun all_phase_proposition action current successors =
    let
      val _ = if fastype_of action = actionT andalso
          fastype_of current = rankT andalso
          fastype_of successors = successorsT then ()
        else error "Joint rank proof has a mistyped action, rank, or successor"
      val phase = Free ("phase",natT)
    in HOLogic.mk_Trueprop
      (HOLogic.mk_all ("phase",natT,relation action current successors phase))
    end

  fun terminal_template check ctxt {action,current,definitions} =
    let
      val successors = Free ("successors",successorsT)
      val phase = Free ("phase",natT)
      val proposition = HOLogic.mk_Trueprop
        (HOLogic.mk_all ("successors",successorsT,
          HOLogic.mk_all ("phase",natT,
            relation action current successors phase)))
      val rules = @{thms comma_crt_rank_relation_fork_leaf
        comma_crt_rank_relation_landmine_leaf
        comma_crt_rank_relation_def comma_crt_payload_def
        comma_weighted_crt_eval.simps option.simps map_option_case
        fst_conv comma_phase_rank_mask_action.case
        comma_phase_rank_mask_action.distinct} @ definitions
      val theorem = Goal.prove ctxt [] [] proposition
        (fn {context,...} =>
          HEADGOAL (asm_full_simp_tac (Simplifier.add_simps
            (Comma_Proof_Rewrite_Rules.nonreflexive_rules rules)
            (Transport.arithmetic_context context))))
    in check "Phase-class terminal leaf template" proposition theorem end

  fun instantiate_terminal check ctxt template action current successors =
    let
      val proposition = all_phase_proposition action current successors
      val instance = template RS @{thm spec}
      val theorem = Goal.prove ctxt [] [] proposition
        (fn {context,...} => HEADGOAL (resolve_tac context [instance]))
    in check "Phase-class terminal leaf instance" proposition theorem end

  fun continue_template check ctxt
      {action,current,target,child,later,definitions} =
    let
      val _ = if later >= 0 then ()
        else error "Continue target rank is negative"
      val successors = Free ("successors",successorsT)
      val phase = Free ("phase",natT)
      val selected = HOLogic.mk_eq
        (successors $ HOLogic.mk_number natT child,
         Const (@{const_name Some},rankT -->
           Type (@{type_name option},[rankT])) $ target)
      val proposition = HOLogic.mk_Trueprop
        (HOLogic.mk_all ("successors",successorsT,
          HOLogic.mk_all ("phase",natT,
            HOLogic.mk_imp (selected,
              relation action current successors phase))))
      val rules = @{thms comma_crt_payload_def
        comma_weighted_crt_eval.simps option.simps map_option_case
        fst_conv comma_phase_rank_mask_action.distinct} @ definitions
      val continue_rule = Drule.infer_instantiate ctxt
        [(("tree",0),Thm.cterm_of ctxt target),
         (("later",0),Thm.cterm_of ctxt
           (HOLogic.mk_number natT later))]
        @{thm comma_crt_rank_relation_continue_leaf}
      val theorem = Goal.prove ctxt [] [] proposition
        (fn {context,...} =>
          HEADGOAL (resolve_tac context [@{thm allI}]) THEN
          HEADGOAL (resolve_tac context [@{thm allI}]) THEN
          HEADGOAL (resolve_tac context [@{thm impI}]) THEN
          HEADGOAL (resolve_tac context [continue_rule]) THEN
          ALLGOALS (asm_full_simp_tac (Simplifier.add_simps
            (Comma_Proof_Rewrite_Rules.nonreflexive_rules rules)
            (Transport.arithmetic_context context))))
    in check "Phase-class Continue leaf template" proposition theorem end

  fun instantiate_continue check ctxt template action current successors equations =
    let
      val proposition = all_phase_proposition action current successors
      val context = Transport.arithmetic_context ctxt
        |> Simplifier.add_simps
          (Comma_Proof_Rewrite_Rules.nonreflexive_rules (template :: equations))
      val theorem = Goal.prove ctxt [] [] proposition
        (fn _ => HEADGOAL (simp_tac context))
    in check "Phase-class Continue leaf instance" proposition theorem end

  fun certify_leaf check ctxt {action,current,successors,definitions} =
    let
      val proposition = all_phase_proposition action current successors
      val rules = @{thms comma_crt_rank_relation_def comma_crt_payload_def
        comma_weighted_crt_eval.simps option.simps map_option_case
        fst_conv comma_phase_rank_mask_action.case
        comma_phase_rank_mask_action.distinct} @ definitions
      val theorem = Goal.prove ctxt [] [] proposition
        (fn {context,...} =>
          HEADGOAL (resolve_tac context [@{thm allI}]) THEN
          HEADGOAL (asm_full_simp_tac (Simplifier.add_simps
            (Comma_Proof_Rewrite_Rules.nonreflexive_rules rules)
            (Transport.arithmetic_context context))))
    in check "Phase-class leaf rank relation" proposition theorem end

  (* The slot equations must be exact cofactor equations of the named shallow
     nodes.  They are only rewrite facts; the all-cofactors theorem checks the
     actual relation and every finite slot. *)
  fun certify_from_cofactors check ctxt
      {axis,action,current,successors,action_shape,current_shape,
       successor_shape,cofactor_equations,children} =
    let
      val _ = if axis >= 0 andalso axis < 4 then ()
        else error "Joint rank proof has an invalid CRT axis"
      val proposition = all_phase_proposition action current successors
      val rule = Drule.infer_instantiate ctxt
        [( ("axis",0), Thm.cterm_of ctxt (HOLogic.mk_number natT axis)),
         ( ("lower",0), Thm.cterm_of ctxt (HOLogic.mk_number natT axis))]
        @{thm comma_crt_rank_relation_list_cofactors}
      val child_rules = map (fn theorem => theorem RS @{thm spec}) children
      val facts = [action_shape,current_shape,successor_shape] @
        cofactor_equations @
        @{thms comma_crt_axis_radix_def list_all_Cons_iff
          list_all_Nil_iff upt_rec map_option_case option.simps}
      val theorem = Goal.prove ctxt [] [] proposition
        (fn {context,...} =>
          let
            val base = Transport.arithmetic_context context
              |> Simplifier.add_simps
                (Comma_Proof_Rewrite_Rules.nonreflexive_rules facts)
            val selected = Simplifier.add_simps
              (Comma_Proof_Rewrite_Rules.nonreflexive_rules child_rules) base
          in
            HEADGOAL (resolve_tac context [@{thm allI}]) THEN
            HEADGOAL (resolve_tac context [rule]) THEN
            ALLGOALS (asm_full_simp_tac base) THEN
            REPEAT_DETERM (FIRSTGOAL
              (resolve_tac context [@{thm conjI},@{thm allI}])) THEN
            ALLGOALS (asm_full_simp_tac selected)
          end)
    in check "Phase-class joint cofactor relation" proposition theorem end
end
