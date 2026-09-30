(* Proof-producing selected lookup for the untrusted future rank table. *)
structure Comma_Future_Rank_Check =
struct
  fun closed term = null (Term.add_frees term []) andalso
    null (Term.add_vars term []) andalso not (Term.is_open term)

  fun timed elapsed failures f x =
    let
      val start = Time.now ()
      val result = Exn.capture f x
      val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), start))
      val _ = if Exn.is_exn result then failures := !failures + 1 else ()
    in Exn.release result end

  (* Keep the four-dimensional rank data opaque to the general simpset.  A
     lookup opens only the selected path, using the data definition and the
     kernel's list-nth equations. *)
  fun selected_table ctxt name codes_def =
    let
      val scalar = Comma_Entry_Arithmetic.natural_context ctxt
      val arithmetic = Simplifier.rewrite scalar
      val root = codes_def RS @{thm eq_reflection}
      val root_term = Thm.term_of (Thm.lhs_of root)
      val memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val lookups = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val internal_publications = Unsynchronized.ref 0
      val leaf_evaluations = Unsynchronized.ref 0
      val retained = Unsynchronized.ref 0
      val peak_retained = Unsynchronized.ref 0
      val evicted = Unsynchronized.ref 0
      val elapsed = Unsynchronized.ref Time.zeroTime
      val failures = Unsynchronized.ref 0

      fun nth ct =
        let
          val normalized = Conv.arg_conv arithmetic ct
          val equation = Conv.rewr_conv
            (@{thm nth_Cons'} RS @{thm eq_reflection}) (Thm.rhs_of normalized)
          val condition = Conv.fun_conv (Conv.fun_conv (Conv.arg_conv arithmetic))
            (Thm.rhs_of equation)
          val reduced =
            (Conv.rewr_conv (@{thm if_True} RS @{thm eq_reflection}) else_conv
             Conv.rewr_conv (@{thm if_False} RS @{thm eq_reflection}))
              (Thm.rhs_of condition)
          val first = Thm.transitive normalized
            (Thm.transitive equation (Thm.transitive condition reduced))
          val (head, _) = strip_comb (Thm.term_of (Thm.rhs_of first))
        in
          if (case head of Const (constant, _) => constant = @{const_name nth} | _ => false)
          then Thm.transitive first (nth (Thm.rhs_of first)) else first
        end

      fun lookup ct =
        let
          val key = Thm.term_of ct
          val _ = lookups := !lookups + 1
        in
          (case Termtab.lookup (!memo) key of
            SOME theorem => (hits := !hits + 1; theorem)
          | NONE =>
              let
                val theorem = if key aconv root_term then root else
                  let
                    val transported = Conv.fun_conv (Conv.arg_conv lookup) ct
                  in Thm.transitive transported (nth (Thm.rhs_of transported)) end
                val _ = if fastype_of key = @{typ nat} then
                    leaf_evaluations := !leaf_evaluations + 1
                  else
                    let
                      val _ = if !retained < 8192 then () else
                        (evicted := !evicted + !retained;
                         memo := Termtab.empty; retained := 0)
                      val _ = memo := Termtab.update (key, theorem) (!memo)
                      val _ = retained := !retained + 1
                      val _ = peak_retained := Int.max (!peak_retained, !retained)
                    in internal_publications := !internal_publications + 1 end
              in theorem end)
        end

      fun convert ct =
        let val term = Thm.term_of ct in
          if not (closed term) then NONE else
            SOME (timed elapsed failures lookup ct)
        end
      val pattern = (case name of
          "N" => @{term "comma_rank_codes_N ! i"}
        | "Z" => @{term "comma_rank_codes_Z ! i"}
        | _ => error "Unknown future rank table")
        |> Term.map_aterms
          (fn Free (variable, typ) => Var ((variable, 0), typ) | atom => atom)
      val procedure = Simplifier.make_simproc ctxt
        {name = "comma_future_selected_" ^ name, kind = Simplifier.Simproc,
         lhss = [pattern], proc = fn _ => fn _ => convert, identifier = []}
      fun stats () = name ^ "_lookups=" ^ Int.toString (!lookups) ^
        " " ^ name ^ "_hits=" ^ Int.toString (!hits) ^
        " " ^ name ^ "_leaf_evaluations=" ^ Int.toString (!leaf_evaluations) ^
        " " ^ name ^ "_internal_publications=" ^
          Int.toString (!internal_publications) ^
        " " ^ name ^ "_internal_retained=" ^ Int.toString (!retained) ^
        " " ^ name ^ "_internal_peak=" ^ Int.toString (!peak_retained) ^
        " " ^ name ^ "_evicted=" ^ Int.toString (!evicted) ^
        " " ^ name ^ "_failed=" ^ Int.toString (!failures) ^
        " " ^ name ^ "_lookup_ms=" ^
          LargeInt.toString (Time.toMilliseconds (!elapsed))
    in (procedure, stats) end

  fun make ctxt =
    let
      val core = Comma_Fast_Kernel.make ctxt
      val (n_procedure, n_stats) = selected_table ctxt "N" @{thm comma_rank_codes_N_def}
      val (z_procedure, z_stats) = selected_table ctxt "Z" @{thm comma_rank_codes_Z_def}
      val evaluation = (#context core
        |> Simplifier.add_proc n_procedure
        |> Simplifier.add_proc z_procedure) addsimps
        @{thms comma_boundary_states_def comma_boundary_valid_def
          comma_fast_boundary_children_def comma_fast_boundary_macro_def
          comma_fast_boundary_run_numeral comma_finite_initial_def
          comma_future_rank_row_def comma_future_rank_check_def
          comma_rank_candidate_def comma_rank_code_at_def
          comma_boundary_kind.simps comma_finite_outcome.case
          option.case option.map option.inject option.distinct
          list.distinct list.inject list.map concat.simps append.simps
          list_ex_Nil_iff list_ex_Cons_iff}
      fun stats () = #stats core () ^ " " ^ n_stats () ^ " " ^ z_stats ()
    in {context = evaluation, stats = stats} end

  fun exact_closed ctxt proposition theorem =
    if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
        Thm.prop_of theorem aconv proposition andalso
        null (Thm_Deps.all_oracles [theorem])
    then theorem
    else error "Future rank checker produced a non-closed or inexact theorem"

  fun prove ctxt proposition context label =
    let
      val started = Time.now ()
      val result = Exn.capture (fn () => Goal.prove ctxt [] [] proposition
        (fn _ => simp_tac context 1)) ()
      val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
      val _ = if Exn.is_exn result then
        Comma_Fast_Kernel.report
          (label ^ " status=failed evaluation_ms=" ^ LargeInt.toString elapsed)
        else ()
      val theorem = exact_closed ctxt proposition (Exn.release result)
      val _ = Comma_Fast_Kernel.report
        (label ^ " status=proved evaluation_ms=" ^ LargeInt.toString elapsed)
    in theorem end

  fun tactic ctxt =
    let
      val engine = make ctxt
      val context = #context engine
      val row = HOLogic.mk_Trueprop
        (@{term comma_future_rank_row} $ HOLogic.mk_number @{typ nat} 28 $
          @{term comma_rank_candidate} $
          HOLogic.mk_prod (@{term Comma_N},
            HOLogic.mk_prod (HOLogic.mk_number @{typ nat} 2,
              HOLogic.mk_number @{typ nat} 0)))
      val _ = Comma_Fast_Kernel.report
        "Future rank first-row status=started state=(N,2,0)"
      val _ = prove ctxt row context "Future rank first-row"
      val _ = Comma_Fast_Kernel.report
        "Future rank aggregate status=started rows=14784"
      fun aggregate_tactic state =
        let
          val started = Time.now ()
          val result = Exn.capture
            (fn () => Seq.pull (simp_tac context 1 state)) ()
          val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
        in
          (case result of
            Exn.Res NONE =>
              (Comma_Fast_Kernel.report
                ("Future rank aggregate status=failed evaluation_ms=" ^
                  LargeInt.toString elapsed ^ " " ^ #stats engine ());
               Seq.empty)
          | Exn.Res (SOME (proved, remaining)) =>
              let
                val solved = Thm.nprems_of proved = 0
                val status = if solved then "proved" else "incomplete"
                val _ = Comma_Fast_Kernel.report
                  ("Future rank aggregate status=" ^ status ^
                    " evaluation_ms=" ^ LargeInt.toString elapsed ^
                    " unresolved=" ^ Int.toString (Thm.nprems_of proved) ^
                    " " ^ #stats engine ())
              in Seq.cons proved remaining end
          | Exn.Exn failure =>
              (Comma_Fast_Kernel.report
                ("Future rank aggregate status=failed evaluation_ms=" ^
                  LargeInt.toString elapsed ^ " " ^ #stats engine ());
               Exn.reraise failure))
        end
    in aggregate_tactic end
end
