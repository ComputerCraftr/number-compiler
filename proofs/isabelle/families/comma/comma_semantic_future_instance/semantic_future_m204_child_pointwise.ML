(* Bind the checked source and child fold laws to the actual physical output. *)
structure Comma_Future_M204_Child_Pointwise =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Join = Comma_Future_M204_Join_Proposal
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n
  fun prove store (join:Join.result) D bellman source_pointwise child_transports class_roots =
    let
      val ctxt = Store.context store
      val phase = Free ("future_child_phase",natT)
      val J = Free ("future_child_digit",natT)
      val delta = Free ("future_child_delta",natT)
      val nodes = Store.table store
      val eval = @{term "comma_crt_mdd_eval_phase :: nat list => nat comma_crt_mdd_node list => nat => nat => nat option"} $ Store.radices store $ nodes $ phase
      val some = Const (@{const_name Some},natT --> @{typ "nat option"})
      val outputs = map (Store.action_index store) (#outputs join)
      val children_n = map (Store.action_index store) (#children_n join)
      val children_z = map (Store.action_index store) (#children_z join)
      val _ = if length outputs=16 andalso length children_n=16 andalso
          length children_z=16 andalso length source_pointwise=16 then ()
        else error "Child pointwise requires sixteen source families"
      val expected = @{term "\<lambda>nodes::nat comma_crt_mdd_node list. \<lambda>roots::nat list.
        \<lambda>kind::comma_boundary_kind. \<lambda>phase::nat. \<lambda>J::nat. \<lambda>delta::nat.
        if J=8 then 0 else Suc (comma_future_m204_mdd_class nodes roots
          (kind,J+2,(phase+delta) mod 924))"}
      fun family direction i =
        let
          val source_kind = if i<8 then @{term Comma_N} else @{term Comma_Z}
          val kind = if direction=1 then @{term Comma_N} else @{term Comma_Z}
          val q = HOLogic.mk_prod (source_kind,HOLogic.mk_prod (nat (i mod 8 + 2),phase))
          val source = List.nth (outputs,i)
          val child = List.nth (if direction=1 then children_n else children_z,i)
          val transport = (case AList.lookup (op =) child_transports (direction,source,child) of
              SOME theorem => theorem | NONE => error "Missing checked ordered-child fold")
          val bound = HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less} (phase,nat 924))
          val output = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (@{term comma_future_m204_source_output} $ D $ q,
             Const (@{const_name Some},@{typ "nat * nat => (nat * nat) option"}) $
               HOLogic.mk_prod (J,delta)))
          val value = Envir.beta_norm (list_comb (expected,[nodes,class_roots,kind,phase,J,delta]))
          val target = HOLogic.mk_Trueprop (HOLogic.mk_eq (eval $ nat child,some $ value))
          val source_fact = List.nth (source_pointwise,i)
          val theorem = Goal.prove ctxt ["future_child_phase","future_child_digit","future_child_delta"]
            [bound,output] target (fn {context,prems} =>
              let
                val [phase_bound,source_output] = prems
                val valid_goal = HOLogic.mk_Trueprop (@{term comma_boundary_valid} $ q)
                val valid = Goal.prove context [] [] valid_goal (fn _ =>
                  simp_tac (Comma_Entry_Arithmetic.natural_context context
                    |> Simplifier.add_simps [phase_bound,@{thm comma_boundary_valid_def}]) 1)
                val digit_bound = Drule.infer_instantiate context
                  [(("D",0),Thm.cterm_of context D),(("q",0),Thm.cterm_of context q),
                   (("J",0),Thm.cterm_of context J),(("delta",0),Thm.cterm_of context delta)]
                  @{thm comma_future_m204_source_output_digit_bound} OF [bellman,valid,source_output]
                val decode = map (fn theorem => theorem OF [digit_bound])
                  @{thms comma_future_m204_decode_join}
                val scalar = Comma_Entry_Arithmetic.natural_context context
                  |> Simplifier.add_simps ([source_fact,transport] @ decode)
              in auto_tac scalar end)
        in theorem end
      val theorems = map (family 1) (0 upto 15) @ map (family 2) (0 upto 15)
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 physical ordered-child transport" theorems
    in theorems end
end
