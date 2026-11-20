(* Derive one source-class bound and one physical join theorem per family
   from its checked source/child outputs and four exact graph zips. *)
structure Comma_Future_M204_Graph_Family_Pointwise =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Graph = Comma_Future_M204_Graph_Proposal
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n
  fun prove store rows roots count bounds D bellman (graph:Graph.result)
      graph_evals equalities class_bounds source_facts child_facts =
    let
      val ctxt = Store.context store
      val nodes = Store.table store
      val phase = Free ("future_graph_family_phase",natT)
      val J = Free ("future_graph_family_digit",natT)
      val delta = Free ("future_graph_family_delta",natT)
      val bound_prop = @{term "\<lambda>nodes::nat comma_crt_mdd_node list. \<lambda>roots::nat list.
        \<lambda>rows::comma_future_m204_row list. \<lambda>q::comma_boundary_state.
        comma_future_m204_mdd_class nodes roots q < length rows"}
      val join_prop = @{term "\<lambda>nodes::nat comma_crt_mdd_node list. \<lambda>roots::nat list.
        \<lambda>rows::comma_future_m204_row list. \<lambda>q::comma_boundary_state. \<lambda>J::nat. \<lambda>delta::nat.
        comma_future_m204_graph_control rows (comma_future_m204_mdd_class nodes roots q) = Suc J \<and>
        comma_future_m204_graph_child rows (comma_future_m204_mdd_class nodes roots q) 0 =
          (if J=8 then 0 else Suc (comma_future_m204_mdd_class nodes roots
            (Comma_N,J+2,(snd (snd q)+delta) mod 924))) \<and>
        comma_future_m204_graph_child rows (comma_future_m204_mdd_class nodes roots q) 1 =
          (if J=8 then 0 else Suc (comma_future_m204_mdd_class nodes roots
            (Comma_Z,J+2,(snd (snd q)+delta) mod 924)))"}
      val _ = if length (#comparisons graph) = length graph_evals then ()
        else error "Future graph phase replay has a mismatched transcript"
      val pairs = #comparisons graph ~~ graph_evals
      fun selected predicate = filter (fn ((row:Graph.comparison),_) => predicate (#operation row)) pairs
      fun control Graph.Graph_Control = true | control _ = false
      fun north Graph.Graph_N = true | north _ = false
      fun south Graph.Graph_Z = true | south _ = false
      fun actual Graph.Actual_Control = true | actual _ = false
      val controls = selected control
      val norths = selected north
      val souths = selected south
      val actuals = selected actual
      val _ = if List.all (fn n => n=16) [length controls,length norths,length souths,
          length actuals,length class_bounds,length source_facts] andalso
          length equalities=48 andalso length child_facts=32 then ()
        else error "Future family assembly lacks its 16-family checked inputs"
      fun family i =
        let
          val kind = if i<8 then @{term Comma_N} else @{term Comma_Z}
          val q = HOLogic.mk_prod (kind,HOLogic.mk_prod (nat (i mod 8 + 2),phase))
          val phase_bound = HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less} (phase,nat 924))
          val source_output = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (@{term comma_future_m204_source_output} $ D $ q,
             Const (@{const_name Some},@{typ "nat * nat => (nat * nat) option"}) $
               HOLogic.mk_prod (J,delta)))
          fun decoder context phase_fact =
            let
              val valid_goal = HOLogic.mk_Trueprop (@{term comma_boundary_valid} $ q)
              val valid = Goal.prove context [] [] valid_goal (fn _ =>
                simp_tac (Comma_Entry_Arithmetic.natural_context context
                  |> Simplifier.add_simps [phase_fact,@{thm comma_boundary_valid_def}]) 1)
              val rule = Drule.infer_instantiate context
                [(("q",0),Thm.cterm_of context q),(("nodes",0),Thm.cterm_of context nodes),
                 (("roots",0),Thm.cterm_of context roots)]
                @{thm comma_future_m204_mdd_class_exact} OF
                  [valid,Store.wellformed store,count,bounds]
            in (valid,rule) end
          val bound_target = HOLogic.mk_Trueprop (Envir.beta_norm
            (list_comb (bound_prop,[nodes,roots,rows,q])))
          val bound_theorem = Goal.prove ctxt ["future_graph_family_phase"] [phase_bound]
            bound_target (fn {context,prems} =>
              let val (_,decoded) = decoder context (hd prems)
                  val scalar = Comma_Entry_Arithmetic.natural_context context
                    |> Simplifier.add_simps [decoded,List.nth (class_bounds,i)]
              in auto_tac scalar end)
          val join_target = HOLogic.mk_Trueprop (Envir.beta_norm
            (list_comb (join_prop,[nodes,roots,rows,q,J,delta])))
          fun component ((row:Graph.comparison),fact) =
            [fact,Store.phase_leaf store (#right row)]
          val local_facts = maps component [List.nth (controls,i),List.nth (norths,i),
            List.nth (souths,i),List.nth (actuals,i)] @
            [List.nth (equalities,i),List.nth (equalities,16+i),List.nth (equalities,32+i),
             List.nth (source_facts,i),List.nth (child_facts,i),List.nth (child_facts,16+i)]
          val join_theorem = Goal.prove ctxt
            ["future_graph_family_phase","future_graph_family_digit","future_graph_family_delta"]
            [phase_bound,source_output] join_target (fn {context,prems} =>
              let
                val [phase_fact,source_fact] = prems
                val (valid,decoded) = decoder context phase_fact
                val digit_bound = Drule.infer_instantiate context
                  [(("D",0),Thm.cterm_of context D),(("q",0),Thm.cterm_of context q),
                   (("J",0),Thm.cterm_of context J),(("delta",0),Thm.cterm_of context delta)]
                  @{thm comma_future_m204_source_output_digit_bound} OF [bellman,valid,source_fact]
                val inverse = map (fn theorem => theorem OF [digit_bound])
                  @{thms comma_future_m204_decode_join}
                val scalar = put_simpset HOL_basic_ss context
                  |> Simplifier.add_simps (@{thms option.simps fst_conv snd_conv Let_def
                    comma_future_m204_family_slot_def prod.case comma_boundary_kind.case
                    nth_Cons_0 nth_Cons_Suc} @
                    decoded :: inverse @ local_facts @ prems)
              in auto_tac scalar end)
        in (bound_theorem,join_theorem) end
      val results = map family (0 upto 15)
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 per-family physical graph morphism" (maps (fn (x,y) => [x,y]) results)
    in results end
end
