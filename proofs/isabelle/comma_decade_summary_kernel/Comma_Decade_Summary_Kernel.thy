theory Comma_Decade_Summary_Kernel
  imports Comma_Decade_Orbit.Comma_Decade_Orbit_Quotient
    Comma_Decade_Summary_Transport.Comma_Decade_Summary_Transport
    Comma_Decade_Terminal_Data.Comma_Decade_Terminal_Data
begin

text \<open>The reusable quotient-aware evaluator owns no global certificate.
This focused check evaluates one phase, repeats it through the same engine,
and verifies the restored proposition. Full coverage remains a separate gate.\<close>

ML_file "fast_summary_check.ML"

local_setup \<open>fn lthy =>
  let
    fun make_lookup codes candidate = Comma_Decade_Rank_Lookup.make_lookup
      {numeral_context = Comma_Entry_Arithmetic.numeral_context,
       natural_context = Comma_Entry_Arithmetic.natural_context} lthy codes candidate
    val (rank_lookup, rank_stats) = make_lookup
      @{thm comma_decade_rank_codes_def} @{thm comma_decade_rank_candidate_on_valid_def}
    val (terminal_lookup, terminal_stats) = make_lookup
      @{thm comma_decade_terminal_codes_def}
      @{thm comma_decade_terminal_code_candidate_on_valid_def}
    val rank_edge = rank_lookup @{term "Comma_Decade 923 90"}
    val terminal_edge = terminal_lookup @{term "Comma_Decade 923 90"}
    fun expected_error message result =
      (case result of Exn.Exn (ERROR actual) => actual = message | _ => false)
    fun rejected_before_table lookup count_lookups state =
      let
        val prior = count_lookups ()
        val result = Exn.capture lookup state
        val after = count_lookups ()
      in expected_error "Candidate lookup outside admitted decade domain" result andalso
        prior = after end
    val invalid_rank_phase = rejected_before_table rank_lookup
      (fn () => #lookups (rank_stats ()))
      @{term "Comma_Decade 924 90"}
    val invalid_rank_offset = rejected_before_table rank_lookup
      (fn () => #lookups (rank_stats ()))
      @{term "Comma_Decade 923 91"}
    val invalid_terminal_phase = rejected_before_table terminal_lookup
      (fn () => #lookups (terminal_stats ()))
      @{term "Comma_Decade 924 90"}
    val invalid_terminal_offset = rejected_before_table terminal_lookup
      (fn () => #lookups (terminal_stats ()))
      @{term "Comma_Decade 923 91"}
    fun nat n = HOLogic.mk_number @{typ nat} n
    val constructor = Const (@{const_name Comma_Decade},
      @{typ nat} --> @{typ nat} --> @{typ comma_decade_state})
    fun check_samples lookup candidate rows =
      let
        val samples = [(0,0), (15,15), (16,16), (255,79),
          (256,80), (911,90), (912,80), (923,90)]
        fun check (r,x) =
          let
            val state = constructor $ nat r $ nat x
            val code = Char.ord (String.sub (List.nth (rows, r), x)) - Char.ord #"A"
            val wanted = HOLogic.mk_Trueprop (HOLogic.mk_eq
              (Const (candidate, @{typ comma_decade_state} --> @{typ nat}) $ state, nat code))
          in Thm.prop_of (lookup state) aconv wanted end
      in forall check samples end
    val rank_samples = check_samples rank_lookup
      @{const_name comma_decade_rank_candidate_on_valid} comma_decade_candidate_rows
    val terminal_samples = check_samples terminal_lookup
      @{const_name comma_decade_terminal_code_candidate_on_valid} comma_decade_terminal_candidate_rows
    val _ = if Thm.prop_of rank_edge aconv
          @{prop "comma_decade_rank_candidate_on_valid (Comma_Decade 923 90) = 6"} andalso
        Thm.prop_of terminal_edge aconv
          @{prop "comma_decade_terminal_code_candidate_on_valid (Comma_Decade 923 90) = 5"} andalso
        forall (fn th => null (Thm.hyps_of th) andalso Thm.nprems_of th = 0 andalso
          null (Thm_Deps.all_oracles [th])) [rank_edge, terminal_edge] andalso
        rank_samples andalso terminal_samples andalso
        invalid_rank_phase andalso invalid_rank_offset andalso
        invalid_terminal_phase andalso invalid_terminal_offset then ()
      else error "Ragged candidate table boundary/domain audit failed"
    val (_, lthy) = Local_Theory.note
      ((Binding.name "comma_decade_rank_final_cell_checked", []), [rank_edge]) lthy
    val (_, lthy) = Local_Theory.note
      ((Binding.name "comma_decade_terminal_final_cell_checked", []), [terminal_edge]) lthy
  in lthy end\<close>

local_setup \<open>fn lthy =>
  let
    val engine = Comma_Decade_Summary_Kernel.make lthy
    val empty = #lens_stats engine ()
    val _ = if #lookups empty = 0 andalso #hits empty = 0 andalso
        #misses empty = 0 andalso #publications empty = 0 andalso
        #failures empty = 0 andalso #retained empty = 0 then ()
      else error "Summary engine construction eagerly evaluated coordinate lenses"
    val representative = @{term
      "comma_fast_decade_control (Comma_Decade (0::nat) 0)"}
    fun demand request =
      (case #transport engine "decade" request of
        SOME theorem =>
          if Thm.term_of (Thm.lhs_of theorem) aconv request andalso
              Thm.term_of (Thm.rhs_of theorem) aconv representative andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm_Deps.all_oracles [theorem])
          then () else error "Demanded coordinate lens changed its exact source"
      | _ => error "Admitted coordinate offset did not produce a transport theorem")
    val offset1 = @{term "comma_fast_decade_control (Comma_Decade (0::nat) 1)"}
    val offset12 = @{term "comma_fast_decade_control (Comma_Decade (0::nat) 12)"}
    val _ = demand offset1
    val after_first = #lens_stats engine ()
    val _ = if #lookups after_first = 1 andalso #misses after_first = 1 andalso
        #publications after_first = 1 andalso #retained after_first = 1 andalso
        #hits after_first = 0 andalso #failures after_first = 0 then ()
      else error "One coordinate request did not construct exactly one lens"
    val _ = demand offset1
    val after_repeat = #lens_stats engine ()
    val _ = if #lookups after_repeat = 2 andalso #hits after_repeat = 1 andalso
        #misses after_repeat = 1 andalso #publications after_repeat = 1 andalso
        #retained after_repeat = 1 then ()
      else error "Repeated coordinate request did not reuse its exact lens"
    val _ = demand offset12
    val after_second = #lens_stats engine ()
    val _ = if #lookups after_second = 3 andalso #hits after_second = 1 andalso
        #misses after_second = 2 andalso #publications after_second = 2 andalso
        #retained after_second = 2 then ()
      else error "A second offset did not receive its own lens memo entry"
    val first = Comma_Decade_Summary_Kernel.range lthy engine (0,1)
    val repeated = Comma_Decade_Summary_Kernel.range lthy engine (0,1)
    val _ = if Thm.prop_of first aconv Thm.prop_of repeated then ()
      else error "Summary memo changed the receiving proposition"
    (* A closed theorem about a foreign occurrence cannot authorize a key. *)
    val foreign = Thm.reflexive @{cterm "0::nat"}
    val bad = Comma_Fast_Kernel.make_with_transport
      (fn name => fn _ => if name="decade" then SOME foreign else NONE) lthy
    val request = @{cterm "comma_fast_decade_control (Comma_Decade 0 0)"}
    val rejected = Exn.capture (Simplifier.rewrite (#context bad)) request
    val _ = case rejected of Exn.Exn (ERROR message) =>
          if String.isSubstring "Foreign or open fast-kernel transport" message then ()
          else error ("Unexpected transport rejection: " ^ message)
      | _ => error "Foreign transport was accepted"
  in #2 (Local_Theory.note
    ((Binding.name "comma_summary_orbit_phase_zero_checked", []), [first]) lthy) end\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_summary_orbit_phase_zero_checked}) then ()
    else error "Summary smoke depends on an oracle";
\<close>

end
