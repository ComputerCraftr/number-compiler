(* Publish the compact classifier only after checked cross-Store transport. *)
structure Comma_Future_M204_Compact_Rank_Publication =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  val natT = @{typ nat}
  val stateT = @{typ comma_boundary_state}
  fun nat n = HOLogic.mk_number natT n
  fun tp t = HOLogic.mk_Trueprop t

  fun publish lthy source_store source_roots root_equalities
      work_map work_definition bellman work_join work_rank =
    let
      val _ = if length source_roots = 16 andalso length root_equalities = 16 then ()
        else error "Compact rank publication needs sixteen checked roots"
      val ids = map (Store.action_index source_store) source_roots
      val roots = HOLogic.mk_list natT (map nat ids)
      val rhs = @{term comma_future_m204_mdd_class} $ Store.table source_store $ roots
      val ((local_map,(_,local_definition)),lthy1) = Local_Theory.define
        ((Binding.name "comma_future_m204_compact_class_map",NoSyn),
         ((Binding.name "comma_future_m204_compact_class_map_def",[]),rhs)) lthy
      val morphism = Local_Theory.target_morphism lthy1
      val compact = Morphism.term morphism local_map
      val definition = Morphism.thm morphism local_definition
      val ctxt = Local_Theory.target_of lthy1
      val phase = Free ("compact_family_phase",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      fun family (index,equality) =
        let
          val kind = if index < 8 then @{term Comma_N} else @{term Comma_Z}
          val digit = nat (index mod 8 + 2)
          val q = HOLogic.mk_prod (kind,HOLogic.mk_prod (digit,phase))
          val goal = tp (HOLogic.mk_eq (work_map $ q,compact $ q))
          val fact = Thm.forall_elim phase_ct equality
          val scalar = Comma_Entry_Arithmetic.natural_context ctxt
            |> Simplifier.add_simps [work_definition,definition,fact]
            |> Simplifier.add_simps @{thms comma_future_m204_mdd_class_def
              comma_future_m204_family_slot_def comma_boundary_kind.case
              prod.case list.simps nth_Cons_0 nth_Cons_Suc nth_Cons_numeral nth_Cons'}
          val theorem = Goal.prove ctxt ["compact_family_phase"] [] goal
            (fn _ => simp_tac scalar 1)
        in theorem end
      val families = map_index family root_equalities
      val q = Free ("compact_boundary_state",stateT)
      val predicate = HOLogic.mk_eq (work_map $ q,compact $ q)
      val valid = tp (@{term comma_boundary_valid} $ q)
      val boundary = Drule.infer_instantiate ctxt
        [(("P",0),Thm.cterm_of ctxt (Term.lambda q predicate)),
         (("q",0),Thm.cterm_of ctxt q)] @{thm comma_future_m204_boundary_cases}
      val same = Goal.prove ctxt ["compact_boundary_state"] [valid] (tp predicate)
        (fn {context,prems} =>
          resolve_tac context [boundary] 1 THEN resolve_tac context prems 1 THEN
          EVERY (map (fn fact =>
            (resolve_tac context [fact] THEN_ALL_NEW assume_tac context) 1) families))
      val rank = @{thm comma_future_m204_rank_transport} OF [bellman,same,work_rank]
      val morphism = @{thm comma_future_m204_morphism_transport} OF
        [bellman,same,work_join]
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Compact class map morphism and rank transport" (same :: morphism :: rank :: families)
      val (_,lthy2) = Local_Theory.note
        ((Binding.name "comma_future_m204_compact_morphism_native",[]),[morphism]) lthy1
      val (_,lthy3) = Local_Theory.note
        ((Binding.name "comma_future_m204_compact_rank_native",[]),[rank]) lthy2
    in ({class_map=compact,definition=definition,equality=same,morphism=morphism,
      rank=rank},lthy3) end
end
