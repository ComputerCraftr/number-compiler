(* Publish the checked class map only after all sixteen physical-family
   bounds and ordered joins have been proved. *)
structure Comma_Future_M204_Final_Publication =
struct
  val natT = @{typ nat}
  val stateT = @{typ comma_boundary_state}
  fun nat n = HOLogic.mk_number natT n
  fun tp t = HOLogic.mk_Trueprop t
  fun app f xs = Envir.beta_norm (list_comb (f,xs))

  fun publish lthy D bellman rows rows_checked nodes roots (family_facts: (thm * thm) list)
      source20_north source20_south =
    let
      val ctxt = Local_Theory.target_of lthy
      val _ = if length family_facts=16 then ()
        else error "Future final publisher requires sixteen checked families"
      val class_rhs = @{term comma_future_m204_mdd_class} $ nodes $ roots
      val q = Free ("future_publication_state",stateT)
      val J = Free ("future_publication_digit",natT)
      val delta = Free ("future_publication_delta",natT)
      val valid = tp (@{term comma_boundary_valid} $ q)
      val bound = @{term "\<lambda>rows::comma_future_m204_row list.
        \<lambda>class_of::comma_boundary_state \<Rightarrow> nat. \<lambda>q::comma_boundary_state.
        class_of q < length rows"} $ rows $ class_rhs $ q |> Envir.beta_norm |> tp
      val join_template = @{term "\<lambda>D::nat \<Rightarrow> nat \<Rightarrow> nat.
        \<lambda>rows::comma_future_m204_row list.
        \<lambda>class_of::comma_boundary_state \<Rightarrow> nat. \<lambda>q::comma_boundary_state.
        \<lambda>J::nat. \<lambda>delta::nat.
        comma_future_m204_graph_control rows (class_of q) = Suc J \<and>
        comma_future_m204_graph_child rows (class_of q) 0 =
          (if J=8 then 0 else Suc (class_of (Comma_N,J+2,(snd (snd q)+delta) mod 924))) \<and>
        comma_future_m204_graph_child rows (class_of q) 1 =
          (if J=8 then 0 else Suc (class_of (Comma_Z,J+2,(snd (snd q)+delta) mod 924)))"}
      val output = tp (HOLogic.mk_eq
        (@{term comma_future_m204_source_output} $ D $ q,
         Const (@{const_name Some},@{typ "nat * nat => (nat * nat) option"}) $
           HOLogic.mk_prod (J,delta)))
      val join = tp (app join_template [D,rows,class_rhs,q,J,delta])
      fun boundary_rule predicate = Drule.infer_instantiate ctxt
        [(("P",0),Thm.cterm_of ctxt (Term.lambda q predicate)),
         (("q",0),Thm.cterm_of ctxt q)] @{thm comma_future_m204_boundary_cases}
      val bound_rule = boundary_rule (HOLogic.dest_Trueprop bound)
      fun split_tac context prems facts =
        resolve_tac context [bound_rule] 1 THEN
        resolve_tac context prems 1 THEN
        EVERY (map (fn fact =>
          (resolve_tac context [fact] THEN_ALL_NEW assume_tac context) 1) facts)
      val family_bounds = map #1 family_facts
      val family_joins = map #2 family_facts
      val bound_fact = Goal.prove ctxt ["future_publication_state"] [valid] bound
        (fn {context,prems} => split_tac context prems family_bounds)
      val implication = tp (HOLogic.mk_imp (HOLogic.dest_Trueprop output,
        HOLogic.dest_Trueprop join))
      val join_rule = boundary_rule (HOLogic.dest_Trueprop implication)
      val join_predicate = Goal.prove ctxt
        ["future_publication_state","future_publication_digit","future_publication_delta"]
        [valid] implication (fn {context,prems} =>
          resolve_tac context [join_rule] 1 THEN
          resolve_tac context prems 1 THEN
          EVERY (map (fn fact =>
            asm_full_simp_tac (put_simpset HOL_basic_ss context
              |> Simplifier.add_simps [fact]) 1) family_joins))
      val join_fact = Goal.prove ctxt
        ["future_publication_state","future_publication_digit","future_publication_delta"]
        [valid,output] join (fn {context,prems} =>
          let val [valid_fact,output_fact] = prems
          in resolve_tac context [@{thm mp}] 1 THEN
            resolve_tac context [join_predicate] 1 THEN
            resolve_tac context [valid_fact] 1 THEN
            resolve_tac context [output_fact] 1 end)
      val rank = @{thm comma_future_m204_source_rank_lift} OF
        [bellman,rows_checked,bound_fact,join_fact]
      val ((class_map,(_,class_definition)),lthy1) = Local_Theory.define
        ((Binding.name "comma_future_m204_class_map",NoSyn),
         ((Binding.name "comma_future_m204_class_map_def",[]),class_rhs)) lthy
      val morphism = Local_Theory.target_morphism lthy1
      val class_map = Morphism.term morphism class_map
      val class_definition = Morphism.thm morphism class_definition
      val target_ctxt = Local_Theory.target_of lthy1
      fun rename theorem = Simplifier.rewrite_rule (put_simpset HOL_basic_ss target_ctxt)
        [Thm.symmetric class_definition] theorem
      val rank = rename rank
      val join = rename join_fact
      val north = rename source20_north
      val south = rename source20_south
      val _ = Comma_Proof_Dependency_Audit.require_native_clean target_ctxt
        "M204 global morphism, rank and source20" [join,rank,north,south]
      val (_,lthy2) = Local_Theory.note
        ((Binding.name "comma_future_m204_rank_native",[]),[rank]) lthy1
      val (_,lthy3) = Local_Theory.note
        ((Binding.name "comma_future_m204_source20_north_native",[]),[north]) lthy2
      val (_,lthy4) = Local_Theory.note
        ((Binding.name "comma_future_m204_source20_south_native",[]),[south]) lthy3
    in ({class_map=class_map,definition=class_definition,join=join,
      rank=rank,north=north,south=south},lthy4) end
end
