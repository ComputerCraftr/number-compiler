(* Per-family bridge from the issued physical source to the checked source fold. *)
structure Comma_Future_M204_Source_Pointwise =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Arena = Comma_CRT_MDD_Arena
  structure Join = Comma_Future_M204_Join_Proposal
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n
  fun prove store (join:Join.result) D source_facts import_evals source_transports =
    let
      val ctxt = Store.context store
      val phase = Free ("future_source_phase",natT)
      val J = Free ("future_source_digit",natT)
      val delta = Free ("future_source_delta",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      val eval = @{term "comma_crt_mdd_eval_phase :: nat list => nat comma_crt_mdd_node list => nat => nat => nat option"} $ Store.radices store $ Store.table store $ phase
      val some = Const (@{const_name Some},natT --> @{typ "nat option"})
      val code_of = @{term "\<lambda>q::comma_boundary_state. comma_parametric_typed_mask_code
        (comma_phase_program_full_action_output (snd (snd q))
          (comma_decisive_endpoint_round (snd (snd q)) (comma_finite_initial q)))"}
      val plus = Const (@{const_name plus},natT --> natT --> natT)
      val times = Const (@{const_name times},natT --> natT --> natT)
      val roots = map (Store.action_index store) (#sources join)
      val outputs = map (Store.action_index store) (#outputs join)
      val _ = if length roots=16 andalso length outputs=16 andalso
          length source_facts=16 andalso length import_evals=16 then ()
        else error "Source pointwise needs sixteen issued families"
      fun family i =
        let
          val kind = if i<8 then @{term Comma_N} else @{term Comma_Z}
          val a = i mod 8 + 2
          val q = HOLogic.mk_prod (kind,HOLogic.mk_prod (nat a,phase))
          val physical_code = Envir.beta_norm (code_of $ q)
          val bound = HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less} (phase,nat 924))
          val output = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (@{term comma_future_m204_source_output} $ D $ q,
             Const (@{const_name Some},@{typ "nat * nat => (nat * nat) option"}) $
               HOLogic.mk_prod (J,delta)))
          val target = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (eval $ nat (List.nth (outputs,i)),
             some $ (plus $ (plus $ nat 1 $ J) $ (times $ nat 9 $ delta))))
          val source = List.nth (roots,i)
          val result = List.nth (outputs,i)
          val transport = (case AList.lookup (op =) source_transports (source,result) of
              SOME theorem => theorem | NONE => error "Missing checked source fold")
          val fact = List.nth (source_facts,i)
          val imported = List.nth (import_evals,i)
          val theorem = Goal.prove ctxt ["future_source_phase","future_source_digit","future_source_delta"]
            [bound,output] target (fn {context,prems} =>
              let
                val [phase_bound,source_output] = prems
                val valid_goal = HOLogic.mk_Trueprop (@{term comma_boundary_valid} $ q)
                val valid = Goal.prove context [] [] valid_goal (fn _ =>
                  simp_tac (Comma_Entry_Arithmetic.natural_context context
                    |> Simplifier.add_simps [phase_bound,@{thm comma_boundary_valid_def}]) 1)
                val reflexive = Goal.prove context [] []
                  (HOLogic.mk_Trueprop (HOLogic.mk_eq (physical_code,physical_code)))
                  (fn _ => simp_tac (put_simpset HOL_basic_ss context) 1)
                val join_rule = Drule.infer_instantiate context
                  [(("D",0),Thm.cterm_of context D),(("q",0),Thm.cterm_of context q),
                   (("code",0),Thm.cterm_of context physical_code),
                   (("J",0),Thm.cterm_of context J),(("delta",0),Thm.cterm_of context delta)]
                  @{thm comma_future_m204_source_join_encoded} OF
                    [valid,reflexive,source_output]
                val fact_at = Thm.forall_elim phase_ct fact
                val imported_at = Thm.forall_elim phase_ct imported
                val source_work = @{thm trans} OF [@{thm sym} OF [imported_at],fact_at]
                val scalar = Comma_Entry_Arithmetic.natural_context context
                  |> Simplifier.add_simps [source_work,transport,join_rule]
              in auto_tac scalar end)
        in theorem end
      val theorems = map family (0 upto 15)
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 physical source output transport" theorems
    in theorems end
end
