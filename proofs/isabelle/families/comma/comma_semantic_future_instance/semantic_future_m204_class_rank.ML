(* Prove the proposed class graph locally; source-to-class authority is separate. *)
structure Comma_Future_M204_Class_Rank =
struct
  structure Utils = Comma_CRT_MDD_Proof_Utils
  val natT = @{typ nat}
  val optionT = @{typ "nat option"}
  val rowT = @{typ comma_future_m204_row}
  fun nat n = if n < 0 then error "Negative class graph label"
    else HOLogic.mk_number natT n
  fun optional NONE = Const (@{const_name None}, optionT)
    | optional (SOME n) = Const (@{const_name Some}, natT --> optionT) $ nat n
  fun row (control, children, rank) =
    HOLogic.mk_prod (optional (if control = ~1 then NONE else SOME control),
      HOLogic.mk_prod (HOLogic.mk_list natT (map nat children), optional rank))
  fun publish_rows name rows lthy =
    let
      val count = length rows
      val started = Time.now ()
      val _ = Comma_Proof_Profile.report
        ("M204 class rank start rows=" ^ Int.toString count)
      val _ = if count > 0 andalso count <= 65536 then ()
        else error "Invalid semantic class count"
      val (selector,lthy') = Comma_CRT_Balanced_Table.make
        name rowT (map row rows) lthy
      val table = #table selector
      val ctxt = Local_Theory.target_of lthy'
      val predicate = @{term comma_future_m204_row_checked} $ table
      val count_eq = Utils.exact_prop ctxt "M204 class row count"
        (HOLogic.mk_Trueprop (HOLogic.mk_eq
          (Const (@{const_name size}, fastype_of table --> natT) $ table,nat count)))
        (#size selector)
      val rules = @{thms comma_future_m204_row_checked_def comma_future_m204_rank_def
        comma_future_m204_children_def comma_future_m204_step_def
        comma_semantic_rank_row_checked_def comma_future_control.simps
        list_all_Nil_iff list_all_Cons_iff
        filter.simps list.size fst_conv snd_conv option.simps}
      val simps = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_proc (#procedure selector)
        |> Simplifier.add_simps (count_eq :: rules)
      (* Check bounded intervals in one simplifier invocation, then join their
         kernel-checked results. The selector still authenticates every lookup. *)
      val list_all = Const (@{const_name list_all},
        (natT --> HOLogic.boolT) --> HOLogic.listT natT --> HOLogic.boolT)
      val upto = Const (@{const_name upt}, natT --> natT --> HOLogic.listT natT)
      fun interval a b = HOLogic.mk_Trueprop
        (list_all $ predicate $ (upto $ nat a $ nat b))
      val chunk_context = simps |> Simplifier.add_simps
        @{thms upt_rec list_all_Cons_iff list_all_Nil_iff}
      fun check_chunk a b = Utils.prove_exact ctxt "M204 class rank interval"
        (interval a b) (fn _ => Simplifier.asm_full_simp_tac chunk_context 1)
      fun join a b c left right =
        let
          val rule = Drule.infer_instantiate ctxt
            [(("P",0),Thm.cterm_of ctxt predicate),
             (("a",0),Thm.cterm_of ctxt (nat a)),
             (("b",0),Thm.cterm_of ctxt (nat b)),
             (("c",0),Thm.cterm_of ctxt (nat c))]
            @{thm comma_future_m204_checked_interval_join}
          val order_context = Comma_Entry_Arithmetic.natural_context ctxt
          fun order x y = Utils.prove_exact ctxt "M204 interval order"
            (HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less_eq} (nat x,nat y)))
            (fn _ => Simplifier.asm_full_simp_tac order_context 1)
        in Utils.exact_prop ctxt "M204 joined class rank interval" (interval a c)
          (rule OF [order a b,order b c,left,right]) end
      fun check_intervals a b =
        if b-a <= 16 then check_chunk a b
        else let val middle = a + (b-a) div 2
          in join a middle b (check_intervals a middle) (check_intervals middle b) end
      val indexed = check_intervals 0 count
      val size = Const (@{const_name size}, fastype_of table --> natT) $ table
      val target = HOLogic.mk_Trueprop (list_all $ predicate $ (upto $ nat 0 $ size))
      val conversion = Conv.arg_conv (Conv.arg_conv
        (Conv.arg_conv (Conv.rewr_conv (count_eq RS @{thm eq_reflection}))))
        (Thm.cterm_of ctxt target)
      val rows_checked = Thm.equal_elim (Thm.symmetric conversion) indexed
      val rank = @{thm comma_future_m204_checked_rank} OF [rows_checked]
      val _ = Utils.ensure_closed_context ctxt "M204 class rank" rank
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 semantic class rank" [rows_checked,rank]
      val _ = Comma_Proof_Profile.report
        ("M204 class rank complete elapsed_ms=" ^ LargeInt.toString
          (Time.toMilliseconds (Time.- (Time.now (),started))))
    in ({rows=table, count=count, count_theorem=count_eq, selector=selector,
      rows_checked=rows_checked, rank=rank},lthy') end

  fun publish lthy = publish_rows "comma_future_m204_class_rows"
    Comma_Future_M204_Graph_Data.rows lthy
end
