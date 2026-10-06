structure Comma_Run_Moore_Instance_Check =
struct
  fun theorem_ok theorem =
    Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)

  fun nat n = HOLogic.mk_number @{typ nat} n
  fun bool true = @{term True}
    | bool false = @{term False}

  fun number t = snd (HOLogic.dest_number t)

  fun dest_run term =
    let
      val (choice_term,k_term) = HOLogic.dest_prod term
      val choice = if choice_term aconv @{term True} then true
        else if choice_term aconv @{term False} then false
        else error "Run-Moore cycle contains a non-Boolean choice"
      val k = number k_term
      val _ = if k > 0 then () else error "Run-Moore cycle contains an empty run"
    in (choice,k) end

  fun cycle_terms () =
    let
      val proposition = HOLogic.dest_Trueprop (Thm.prop_of @{thm comma_nine_run_cycle_def})
      val (_,rhs) = HOLogic.dest_eq proposition
    in map dest_run (HOLogic.dest_list rhs) end

  fun make ctxt =
    let
      val base = Comma_Future_Structural_Instance_Check.make ctxt
      val context = (#context base) addsimps
        @{thms comma_summary_survivor_run.simps comma_summary_survivor_step_def
          Let_def prod.case option.case option.map}
      fun stats () = #stats base ()
    in {context=context, stats=stats, certify = #certify base} end

  fun check ctxt =
    let
      val started = Time.now ()
      val engine = make ctxt
      val context = #context engine
      val certify = #certify engine
      val runs = cycle_terms ()
      val _ = if length runs = 140 then ()
        else error "Run-Moore cycle does not contain exactly 140 states"
      val edges = fold (fn (_,k) => fn n => n+k) runs 0
      val selected_z = fold (fn (choice,k) => fn n => if choice then n+k else n) runs 0
      val selected_n = edges-selected_z
      val _ = if edges=314 andalso selected_z=171 andalso selected_n=143 then ()
        else error "Run-Moore cycle has the wrong edge/choice census"
      val _ = if null (Thm_Deps.all_oracles [@{thm comma_nine_run_cycle_cyclic_moore_minimal}])
        then () else error "Run-Moore minimality theorem depends on an oracle"

      val source_root = @{term "(Comma_N,2,10)::comma_boundary_state"}
      val root = @{term "(Comma_N,7,12)::comma_boundary_state"}
      val rank = @{term comma_rank_candidate_on_valid}
      val height = @{term comma_decade_rank_candidate_on_valid}
      val terminal = @{term comma_decade_terminal_candidate_on_valid}
      val run_constant = @{term comma_summary_survivor_run}
      val valid_constant = @{term comma_boundary_valid}

      fun prove proposition = certify (Goal.prove ctxt [] [] proposition
        (fn _ => simp_tac context 1))

      fun evaluate_run index (choice,k) q =
        let
          val expression = run_constant $ height $ terminal $ rank $
            bool choice $ nat k $ q
          val equation_meta = Simplifier.rewrite context (Thm.cterm_of ctxt expression)
          val rhs = Thm.term_of (Thm.rhs_of equation_meta)
          val (some,args) = Term.strip_comb rhs
          val is_some = (case some of
              Const (name,_) => name = @{const_name Some}
            | _ => false)
          val _ = if is_some andalso length args=1 then ()
            else error ("Run " ^ Int.toString index ^ " did not produce a survivor result")
          val (target,delta_term) = HOLogic.dest_prod (hd args)
          val delta = number delta_term
          val computed = certify (equation_meta RS @{thm meta_eq_to_obj_eq})
          val safe = certify (@{thm comma_summary_survivor_run_sound} OF
            [@{thm comma_decade_summary_candidate_checked},computed])
          val _ = if theorem_ok safe then ()
            else error ("Run " ^ Int.toString index ^ " produced an open proof")
          val _ = if getenv "COMMA_PROFILE_LOG" = "" orelse index mod 20 <> 0 then () else
            Comma_Fast_Kernel.report
              ("Run-Moore progress: run=" ^ Int.toString index ^
               " edges=" ^ Int.toString k ^ " " ^ #stats engine ())
        in {choice=choice,k=k,q=q,target=target,delta=delta,safe=safe} end

      fun walk [] _ _ acc = rev acc
        | walk (run::rest) q index acc =
            let val row = evaluate_run index run q
            in walk rest (#target row) (index+1) (row::acc) end
      val entry_row = evaluate_run ~1 (false,1) source_root
      val _ = if #target entry_row aconv root andalso #delta entry_row=2 then ()
        else error "The source boundary does not enter the run-Moore cycle at (N,7,12) with gain 2"
      val entry = certify (Simplifier.simplify
        (Comma_Entry_Arithmetic.natural_context ctxt) (#safe entry_row))
      val expected_entry = @{prop "comma_safe_choice_path comma_rank_candidate_on_valid [False] 1
        (Comma_N,2,10) (Comma_N,7,12) 2"}
      val _ = if theorem_ok entry andalso Thm.prop_of entry aconv expected_entry then ()
        else error "The source-to-run-cycle entry theorem has the wrong endpoint"

      val rows = walk runs root 0 []
      val last = #target (List.last rows)
      val exponent_gain = fold (fn row => fn n => #delta row+n) rows 0
      val _ = if last aconv root then ()
        else error "The 140-state run-Moore itinerary does not close"
      val _ = if exponent_gain=924 then ()
        else error "The 140-state run-Moore itinerary has the wrong exponent cocycle"

      val valid = prove (HOLogic.mk_Trueprop (valid_constant $ root))
      val live = prove (HOLogic.mk_Trueprop
        (@{term "(=) :: nat option => nat option => bool"} $ (rank $ root) $ @{term None}))
      val tail0 = certify (@{thm comma_safe_run_path.empty} OF [valid,live])

      fun positive k = prove (HOLogic.mk_Trueprop
        (@{term "(<) :: nat => nat => bool"} $ nat 0 $ nat k))

      fun prepend (row: {choice: bool, k: int, q: term, target: term,
          delta: int, safe: thm}) tail =
        certify (@{thm comma_safe_run_path.step} OF
          [positive (#k row),#safe row,tail])
      val raw = fold_rev prepend rows tail0
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
      val normalized = certify (Simplifier.simplify arithmetic raw)
      val expected_expanded = HOLogic.mk_Trueprop
        (@{term comma_safe_run_path} $ rank $
          HOLogic.mk_list @{typ comma_branch_run}
            (map (fn (choice,k) => HOLogic.mk_prod (bool choice,nat k)) runs) $
          nat 314 $ root $ root $ nat 924)
      val _ = if theorem_ok normalized andalso Thm.prop_of normalized aconv expected_expanded
        then () else error "Run-Moore proof has the wrong cycle/count/cocycle"
      val elapsed = Time.toMilliseconds (Time.- (Time.now (),started))
      val _ = Comma_Fast_Kernel.report
        ("Run-Moore check: states=140 edges=314 selected_N=143 selected_Z=171 " ^
         "cocycle=924 proof_ms=" ^ LargeInt.toString elapsed ^ " " ^ #stats engine ())
    in (entry,normalized) end
end
