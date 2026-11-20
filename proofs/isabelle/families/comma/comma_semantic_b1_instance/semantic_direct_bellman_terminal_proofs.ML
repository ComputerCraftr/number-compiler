(* Checked Bellman terminal projections over one frozen candidate Store. *)
structure Comma_Direct_Bellman_Terminal_Proofs =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Arena = Comma_CRT_MDD_Arena
  structure Operation = Comma_CRT_MDD_Operation_Replay
  structure Proposal = Comma_Direct_Bellman_Terminal_Proposal
  structure Utils = Comma_CRT_MDD_Proof_Utils
  val natT = @{typ nat}
  val optionT = @{typ "nat option"}
  fun nat n = HOLogic.mk_number natT n
  fun tp term = HOLogic.mk_Trueprop term
  fun indexed_shift ctxt store roots_term roots_definition target source output shift_cert =
    let
      val small = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps [roots_definition]
        |> Simplifier.add_simps @{thms list.simps list.size nth_Cons_0 nth_Cons_Suc nth_Cons_numeral nth_Cons'}
      val root_term = Const (@{const_name nth},@{typ "nat list => nat => nat"}) $
        roots_term $ nat target
      val root_lookup = Simplifier.rewrite small (Thm.cterm_of ctxt root_term)
        |> Utils.exact_prop ctxt "Bellman selected Continue root"
          (Logic.mk_equals (root_term,nat source))
      val source_conversion = Conv.arg_conv
        (Conv.fun_conv (Conv.arg_conv (Conv.rewr_conv (Thm.symmetric root_lookup))))
        (Thm.cprop_of shift_cert)
      val shifted_certificate = Thm.equal_elim source_conversion shift_cert
      val expected_shift = tp
        (@{term "comma_crt_mdd_root_shift_map_certificate :: nat list => nat comma_crt_mdd_node list => (nat => nat) => nat => nat => nat => bool"} $
          Store.radices store $ Store.table store $ @{term "\<lambda>x::nat. x+9"} $ nat 1 $ root_term $ nat output)
    in Utils.exact_prop ctxt "Bellman indexed Continue shift" expected_shift shifted_certificate end

  fun make ctxt store arena roots roots_term roots_definition D D_definition definition continuations =
    let
      val _ = Utils.ensure_closed_context ctxt "Bellman terminal Store" (Store.wellformed store)
      val wf = Store.wellformed store
      val phase = Free ("direct_bellman_terminal_phase",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      val plus9 = @{term "\<lambda>x::nat. x+9"}
      val store_ctxt = Store.context store
      fun leaf input output = Utils.prove_exact store_ctxt "Bellman mapped-shift leaf"
        (tp (HOLogic.mk_eq (Envir.beta_norm (plus9 $ nat input),nat output)))
        (fn _ => simp_tac (Comma_Entry_Arithmetic.natural_context store_ctxt) 1)
      val operations = Operation.make_mapped store plus9 leaf
      val continue_index = fold (fn (item:Proposal.continued) => fn table =>
        if Inttab.defined table (#target item) then error "Duplicate Bellman Continue proposal"
        else Inttab.update (#target item,item) table) continuations Inttab.empty
      val continue_cache = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      fun index root = Store.action_index store root
      fun eval root = @{term "comma_crt_mdd_eval_phase :: nat list => nat comma_crt_mdd_node list => nat => nat => nat option"} $
        Store.radices store $ Store.table store $ phase $ nat root
      fun some value = Const (@{const_name Some},natT --> optionT) $ value
      val small = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps [roots_definition]
        |> Simplifier.add_simps @{thms list.simps list.size nth_Cons_0 nth_Cons_Suc nth_Cons_numeral nth_Cons'}
      fun continued target =
        (case Inttab.lookup (!continue_cache) target of
          SOME theorem => theorem
        | NONE =>
            let
              val started = Time.now ()
              fun checkpoint stage = Comma_Proof_Profile.report
                ("Bellman Continue target=" ^ Int.toString target ^ " stage=" ^ stage ^
                  " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started)
              val _ = checkpoint "start"
              val item = (case Inttab.lookup continue_index target of
                  SOME value => value | NONE => error "Missing Bellman Continue transcript")
              val source = index (#source item)
              val output = index (#output item)
              val _ = if index (List.nth (roots,target)) = source then ()
                else error "Bellman Continue source root differs from candidate D root"
              val _ = checkpoint "shift-start"
              val shift_cert = Operation.certify_mapped_shift operations 1 source output
              val _ = checkpoint "shift-complete"
              val shifted_certificate = indexed_shift ctxt store roots_term roots_definition
                target source output shift_cert
              val cid_bound = Utils.prove_exact ctxt "Bellman target index bound"
                (tp (HOLogic.mk_binrel @{const_name less} (nat target,
                  Const (@{const_name size},@{typ "nat list => nat"}) $ roots_term)))
                (fn _ => simp_tac small 1)
              val root_bound = Utils.prove_exact ctxt "Bellman target root bound"
                (tp (HOLogic.mk_binrel @{const_name less}
                  (Const (@{const_name nth},@{typ "nat list => nat => nat"}) $ roots_term $ nat target,
                   Const (@{const_name size},@{typ "nat comma_crt_mdd_node list => nat"}) $ Store.table store)))
                (fn context => Method.insert_tac context [Store.bound store source] 1 THEN auto_tac small)
              val _ = checkpoint "index-complete"
              val shifted_rule = Drule.infer_instantiate ctxt
                [( ("phase",0),phase_ct),( ("cid",0),Thm.cterm_of ctxt (nat target)),
                 ( ("shifted",0),Thm.cterm_of ctxt (nat output)),
                 ( ("roots",0),Thm.cterm_of ctxt roots_term)]
                @{thm comma_frontier_m204_mapped_shifted_value}
              val shifted_eval = shifted_rule OF
                [wf,@{thm comma_frontier_radices_divide},cid_bound,root_bound,shifted_certificate]
              val shifted_eval = Simplifier.rewrite_rule (put_simpset HOL_basic_ss ctxt)
                [Thm.symmetric D_definition] shifted_eval
              val _ = checkpoint "value-complete"
              val expected_value = HOLogic.mk_binop @{const_name Groups.plus}
                (nat 9,D $ (HOLogic.mk_binop @{const_name modulo}
                  (HOLogic.mk_binop @{const_name Groups.plus} (phase,nat 1),nat 924)) $ nat target)
              val goal = tp (HOLogic.mk_eq (eval output,some expected_value))
              val scalar = Comma_Entry_Arithmetic.natural_context ctxt
                |> Simplifier.add_simps [shifted_eval]
              val _ = checkpoint "assembly-start"
              val point = Goal.prove ctxt [] [] goal (fn _ => simp_tac scalar 1)
              val _ = checkpoint "assembly-complete"
              val theorem = Thm.forall_intr phase_ct point
              val _ = Utils.exact_prop ctxt "Bellman Continue projection"
                (Logic.all phase goal) theorem
              val _ = continue_cache := Inttab.update (target,theorem) (!continue_cache)
            in theorem end)
      fun terminal expression shift root =
        let
          val body = Thm.term_of (Thm.rhs_of (definition expression))
          val (head,args) = strip_comb body
          val extra = (case (head,args) of
              (Const (name,_),[target,delta]) =>
                if name = @{const_name Comma_Direct_Continue} then
                  let val t = Utils.dest_nat "Continue target" natT target
                      val d = Utils.dest_nat "Continue delta" natT delta
                  in if t<46 andalso (d+shift) mod 924=1
                    then [Thm.forall_elim phase_ct (continued t)]
                    else [Thm.forall_elim phase_ct (Store.phase_leaf store root)] end
                else [Thm.forall_elim phase_ct (Store.phase_leaf store root)]
            | _ => [Thm.forall_elim phase_ct (Store.phase_leaf store root)])
          val projected = @{term comma_direct_bellman_mask_projection} $ D $ phase $
            (@{term comma_direct_action_interpret} $ expression $ phase $ nat shift)
          val goal = tp (HOLogic.mk_eq (eval root,some projected))
          val scalar = Comma_Entry_Arithmetic.natural_context ctxt
            |> Simplifier.add_simps (definition expression :: extra)
            |> Simplifier.add_simps @{thms comma_direct_bellman_terminal_projection}
          val point = Goal.prove ctxt [] [] goal (fn _ => simp_tac scalar 1)
        in Thm.forall_intr phase_ct point end
      fun fallback root =
        let
          val _ = (case Store.node store root of Store.Leaf 243 => ()
            | _ => error "Bellman fallback is not checked invalid sentinel")
          val leaf = Thm.forall_elim phase_ct (Store.phase_leaf store root)
          val value = @{term comma_direct_bellman_mask_projection} $ D $ phase $
            @{term Comma_Phase_Rank_Mask_Invalid}
          val goal = tp (HOLogic.mk_eq (eval root,some value))
          val point = Goal.prove ctxt [] [] goal (fn _ => simp_tac
            (put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps
              [leaf,@{thm comma_direct_bellman_mask_projection.simps(1)}]) 1)
        in Thm.forall_intr phase_ct point end
    in {terminal=terminal,fallback=fallback,
      statistics=fn () => "bellman_continue_proofs=" ^ Int.toString (Inttab.size (!continue_cache)) ^
        " " ^ Operation.mapped_statistics operations} end
end
