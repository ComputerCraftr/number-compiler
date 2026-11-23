(* Prove the proposed class graph locally; source-to-class authority is separate. *)
structure Comma_Future_M204_Class_Rank =
struct
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Branch_Ranks = Table(type key = int option * (int option * int option)
    val ord = prod_ord (option_ord int_ord) (prod_ord (option_ord int_ord) (option_ord int_ord)))
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
      val scalar = Comma_Entry_Arithmetic.natural_context ctxt
      val bounded = Simplifier.add_simp count_eq scalar
      val sizes = Const (@{const_name size}, fastype_of table --> natT) $ table
      val proposed = Vector.fromList rows
      val bounds = Inttab.unsynchronized_cache (fn i =>
        let
          val proposition = HOLogic.mk_Trueprop
            (HOLogic.mk_binrel @{const_name less} (nat i,sizes))
        in Utils.prove_exact ctxt "M204 class index bound" proposition
          (fn _ => simp_tac bounded 1) end)
      val bound = #apply bounds
      fun selected i = #lookup selector i RS @{thm meta_eq_to_obj_eq}
      val rank_values = Inttab.unsynchronized_cache (fn i =>
        @{thm comma_future_m204_rank_at} OF [bound i,selected i])
      val rank_at = #apply rank_values
      val branches = Simplifier.add_simps
        @{thms comma_future_m204_branch_rank_def option.simps HOL.simp_thms} scalar
      val rank_arithmetic = Branch_Ranks.unsynchronized_cache (fn (rank,(north,south)) =>
        let
          val proposition = HOLogic.mk_Trueprop (@{term comma_future_m204_branch_rank} $
            optional rank $ optional north $ optional south)
        in Utils.prove_exact ctxt "M204 local rank arithmetic" proposition
          (fn _ => simp_tac branches 1) end)
      fun rank_of i = #3 (Vector.sub (proposed,i))
      fun fork_digits digit =
        let
          fun comparison a b = Utils.prove_exact ctxt "M204 Fork digit bound"
            (HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less_eq} (nat a,nat b)))
            (fn _ => simp_tac scalar 1)
        in (comparison 2 digit,comparison digit 9) end
      val digit_bounds = Vector.tabulate (8,fn i => fork_digits (i+2))
      fun check_row i =
        let
          val theorem = (case Vector.sub (proposed,i) of
            (~1,[],SOME _) => @{thm comma_future_m204_checked_landmine_row} OF [bound i,selected i]
          | (digit,[north,south],rank) =>
              if digit<2 orelse digit>9 then error "Malformed M204 Fork digit"
              else let val (lo,hi) = Vector.sub (digit_bounds,digit-2) in
                @{thm comma_future_m204_checked_fork_row} OF
                  [bound i,bound north,bound south,lo,hi,selected i,rank_at north,rank_at south,
                   #apply rank_arithmetic (rank,(rank_of north,rank_of south))]
              end
          | _ => error "Malformed M204 class row")
        in Utils.exact_prop ctxt "M204 checked class row"
          (HOLogic.mk_Trueprop (predicate $ nat i)) theorem end
      (* Structural lookups authenticate each row. Only closed local rank
         options select the reusable arithmetic theorem for that row. *)
      val list_all = Const (@{const_name list_all},
        (natT --> HOLogic.boolT) --> HOLogic.listT natT --> HOLogic.boolT)
      val upto_term = Const (@{const_name upt}, natT --> natT --> HOLogic.listT natT)
      fun interval a b = HOLogic.mk_Trueprop
        (list_all $ predicate $ (upto_term $ nat a $ nat b))
      val chunk_context = scalar |> Simplifier.add_simps
        @{thms upt_rec list_all_Cons_iff list_all_Nil_iff}
      fun check_chunk a b =
        let val local_context = Simplifier.add_simps
          (map check_row (a upto (b-1))) chunk_context in
          Utils.prove_exact ctxt "M204 class rank interval" (interval a b)
            (fn _ => simp_tac local_context 1)
        end
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
            (fn _ => simp_tac order_context 1)
        in Utils.exact_prop ctxt "M204 joined class rank interval" (interval a c)
          (rule OF [order a b,order b c,left,right]) end
      fun check_intervals a b =
        if b-a <= 16 then check_chunk a b
        else let val middle = a + (b-a) div 2
          in join a middle b (check_intervals a middle) (check_intervals middle b) end
      val indexed = check_intervals 0 count
      val target = HOLogic.mk_Trueprop (list_all $ predicate $ (upto_term $ nat 0 $ sizes))
      val conversion = Conv.arg_conv (Conv.arg_conv
        (Conv.arg_conv (Conv.rewr_conv (count_eq RS @{thm eq_reflection}))))
        (Thm.cterm_of ctxt target)
      val rows_checked = Thm.equal_elim (Thm.symmetric conversion) indexed
      val rank = @{thm comma_future_m204_checked_rank} OF [rows_checked]
      val _ = Utils.ensure_closed_context ctxt "M204 class rank" rank
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 semantic class rank" [rows_checked,rank]
      val _ = Comma_Proof_Profile.report
        ("M204 class rank complete arithmetic_proofs=" ^
          Int.toString (#size rank_arithmetic ()) ^ " elapsed_ms=" ^ LargeInt.toString
          (Time.toMilliseconds (Time.- (Time.now (),started))))
    in ({rows=table, count=count, count_theorem=count_eq, selector=selector,
      rows_checked=rows_checked, rank=rank},lthy') end

  fun publish rows lthy = publish_rows "comma_future_m204_class_rows" rows lthy
end
