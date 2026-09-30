theory Comma_Fast_Kernel
  imports Comma_Sector_Alphabet
begin

text \<open>Shared closed one-round evaluator. The simpset contains no
termination search, candidate ranks, weighted germ or occurrence exporter.
Consumers add only their own Boolean checker and checked lookup equations.\<close>

lemma comma_fast_round_aux_eval:
  "comma_fast_round_aux fuel r source =
    (if fuel=0 then Comma_Round_Invalid else
      let t=comma_fast_sector_target r source in
        case comma_fast_step (r mod 924) t of
          Comma_Next target \<Rightarrow>
            if comma_round_crossing t target then Comma_Round_Cross target
            else comma_fast_round_aux (fuel-1) r target
        | Comma_Fork a d \<Rightarrow> Comma_Round_Fork a d
        | Comma_Landmine d \<Rightarrow> Comma_Round_Landmine d
        | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)"
  by (cases fuel)
    (simp_all add: comma_fast_sector_target_correct Let_def
      split: prod.splits cong: prod.case_cong comma_finite_move.case_cong if_cong)

lemma comma_near_residual_count_eval:
  "comma_near_residual_count k f d b =
    (if k=0 then (0,b) else
      let a=10*d+f in
        if a\<le>b then
          case comma_near_residual_count (k-1) f ((d+f) mod 10) (b-a) of
            (j,u) \<Rightarrow> (Suc j,u)
        else (0,b))"
  by (cases k) (simp_all cong: prod.case_cong if_cong)

lemma comma_near_residual_target_eval:
  "snd (comma_near_residual_count k f d b) =
    (if k=0 then b else
      let a=10*d+f in
        if a\<le>b then snd (comma_near_residual_count (k-1) f ((d+f) mod 10) (b-a))
        else b)"
  by (cases k) (simp_all add: Let_def split: prod.splits)

lemma comma_near_closed_target_eval:
  "snd (comma_near_closed_germ f h) =
    (let e=if f<9 then 1 else 0 in
      if f<1 \<or> 9<f \<or> h=0 \<or> 540<h \<or> h\<le>e then h
      else (let d=(10-h mod 10) mod 10;
        L=comma_cycle_length_fast f;
        P=comma_finite_period_fast f d;
        B=h-e-1;
        q=B div P;
        b=B mod P
      in h-q*P-(b-snd (comma_near_residual_count (L-1) f d b))))"
  by (simp add: comma_near_closed_germ_def Let_def split: prod.splits)

ML \<open>
structure Comma_Fast_Kernel =
struct
  fun context ctxt = (Comma_Entry_Arithmetic.natural_context ctxt
    |> fold Simplifier.add_cong
      @{thms let_weak_cong prod.case_cong_weak
        comma_decade_outcome.case_cong_weak comma_finite_move.case_cong_weak
        comma_finite_position.case_cong_weak comma_round_result.case_cong_weak
        conj_left_cong disj_left_cong}) addsimps
    @{thms comma_fast_round_aux_eval
      comma_near_residual_target_eval comma_fast_decade_control.simps
      comma_sector_entry_alphabet comma_sector_near_alphabet comma_entry_alphabet_phase_def
      comma_entry_alphabet_endpoint_def comma_fast_step.simps(1)
      comma_fast_near_event_alphabet comma_near_event_alphabet_eval
      comma_shift_move.simps comma_shift_position.simps comma_near_closed_target_eval
      comma_cycle_length_fast_def comma_finite_period_fast_def
      comma_finite_headroom_fast_def comma_power_residue_fast_def
      comma_power_table_def comma_short_period_def comma_round_crossing_def
      comma_decade_decode.simps comma_decade_outcome.case
      comma_finite_move.case comma_finite_position.case comma_round_result.case
      list_all_Nil_iff list_all_Cons_iff
      upt_rec nth_Cons' of_nat_numeral of_nat_0 of_nat_1
      zmod_zminus1_eq_if zmod_zminus2_eq_if Num.inc.simps};

  (* A cache belongs to one immutable, assumption-free evaluation context.
     Simprocs ignore the invoking goal context and publish only closed kernel
     equalities certified by the existing dependency audit. *)
  fun make ctxt =
    let
      val started = Time.now ()
      val (certify, certification) = Comma_Entry_Arithmetic.make_certifier ctxt
      val selected =
        [("cycle_length", @{term "comma_cycle_length_fast f"},
            @{thms comma_cycle_length_fast_def}),
         ("period", @{term "comma_finite_period_fast f d"},
            @{thms comma_finite_period_fast_def}),
         ("power", @{term "comma_power_residue_fast P r"},
            @{thms comma_power_residue_fast_def}),
         ("power_cell", @{term "comma_power_table P ! k"},
            @{thms comma_power_table_def}),
         ("headroom", @{term "comma_finite_headroom_fast f r d x"},
            @{thms comma_finite_headroom_fast_def}),
         ("near_target", @{term "snd (comma_near_closed_germ f h)"},
            @{thms comma_near_closed_target_eval}),
         ("near_event", @{term "comma_near_event f h"},
            @{thms comma_near_event_alphabet_eval}),
         ("entry_endpoint", @{term "comma_entry_alphabet_endpoint f x k"},
            @{thms comma_entry_alphabet_endpoint_def}),
         ("sector_target", @{term "comma_fast_sector_target r source"},
            @{thms comma_sector_entry_alphabet comma_sector_near_alphabet}),
         ("decade", @{term "comma_fast_decade_control s"},
            @{thms comma_fast_decade_control.simps})]
      val base = context ctxt delsimps (maps #3 selected)
      val evaluator = Unsynchronized.ref (NONE: Proof.context option)
      fun closed t = null (Term.add_frees t []) andalso
        null (Term.add_vars t []) andalso not (Term.is_open t)
      val constructors =
        @{const_name Pair} :: @{const_name Comma_Entry} :: @{const_name Comma_Near} ::
        @{const_name Comma_Decade} :: @{const_name Comma_Decade_Fork} ::
        @{const_name Comma_Decade_Landmine} :: @{const_name Comma_Decade_Continue} ::
        @{const_name Comma_Decade_Invalid} ::
        @{const_name Comma_Next} :: @{const_name Comma_Fork} ::
        @{const_name Comma_Landmine} :: @{const_name Comma_Invalid} :: []
      fun natural_value t =
        (case try HOLogic.dest_number t of
          SOME (typ, number) => typ = @{typ nat} andalso number >= 0
        | NONE => can HOLogic.dest_nat t)
      fun value t = natural_value t orelse
        (case strip_comb t of (Const (name, _), args) =>
          member (op =) constructors name andalso forall value args | _ => false)
      (* Only Near sector endpoints forget the decimal phase. Entry endpoints
         retain it in their arithmetic key. Occurrence delta is kept in both
         cases; the transport theorem changes exactly the Near phase. *)
      fun canonical_sector name key =
        if name <> "sector_target" then (key, NONE) else
        (case strip_comb key of
          (head as Const (target, _), [phase, source]) =>
            if target <> @{const_name comma_fast_sector_target} then (key, NONE) else
            (case strip_comb source of
              (Const (position, _), [f, delta, h]) =>
                if position <> @{const_name Comma_Near} then (key, NONE) else
                let
                  val zero = @{term "0::nat"}
                  val canonical = head $ zero $ source
                in
                  if canonical aconv key then (key, NONE) else
                  let
                    val transport = Drule.infer_instantiate ctxt
                      [(("r", 0), Thm.cterm_of ctxt phase), (("r'", 0), Thm.cterm_of ctxt zero),
                       (("f", 0), Thm.cterm_of ctxt f), (("delta", 0), Thm.cterm_of ctxt delta),
                       (("h", 0), Thm.cterm_of ctxt h)]
                      @{thm comma_near_alphabet_phase_independent}
                  in (canonical, SOME (transport RS @{thm eq_reflection})) end
                end
            | _ => (key, NONE))
        | _ => (key, NONE))
      fun boundary (name, pattern, equations) =
        let
          val memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
          val own_procedure = Unsynchronized.ref (NONE: Simplifier.simproc option)
          val boundary_context = Unsynchronized.ref (NONE: Proof.context option)
          val context_builds = Unsynchronized.ref 0
          val hits = Unsynchronized.ref 0
          val misses = Unsynchronized.ref 0
          val failures = Unsynchronized.ref 0
          val retained = Unsynchronized.ref 0
          val evicted = Unsynchronized.ref 0
          val elapsed = Unsynchronized.ref Time.zeroTime
          (* The evaluator and equations belong to this one immutable make
             invocation. Build the boundary simpset only on its first miss,
             after all dependency procedures have been installed. Rebuilding
             it for every concrete source repeated identical proof setup. *)
          fun evaluation_context () =
            (case !boundary_context of
              SOME evaluation => evaluation
            | NONE =>
                let
                  val evaluation = (the (!evaluator)
                    |> Simplifier.del_proc (the (!own_procedure))) addsimps equations
                  val _ = boundary_context := SOME evaluation
                  val _ = context_builds := !context_builds + 1
                in evaluation end)
          fun convert ct =
            let val original = Thm.term_of ct in
              if not (closed original) then NONE else
              let
                val (key, transport) = canonical_sector name original
                fun restore theorem =
                  (case transport of NONE => theorem
                  | SOME equation =>
                      let
                        val begin = Time.now ()
                        val result = Exn.capture (fn () =>
                          certify (Thm.transitive equation theorem)) ()
                        val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), begin))
                        val _ = if Exn.is_exn result then failures := !failures + 1 else ()
                      in Exn.release result end)
              in
              case Termtab.lookup (!memo) key of
                SOME theorem => (hits := !hits + 1; SOME (restore theorem))
              | NONE =>
                let
                  val _ = misses := !misses + 1
                  val begin = Time.now ()
                  val result = Exn.capture (fn () =>
                    let
                      (* Exclude this boundary's own procedure while unfolding it.
                         Dependency boundaries remain available for demand reuse. *)
                      val theorem = Simplifier.rewrite (evaluation_context ())
                        (Thm.cterm_of ctxt key)
                      val _ = if value (Thm.term_of (Thm.rhs_of theorem)) then ()
                        else error ("Incomplete fast kernel value: " ^ name ^ " RHS=" ^
                          Syntax.string_of_term ctxt (Thm.term_of (Thm.rhs_of theorem)))
                      val _ = if Thm.term_of (Thm.lhs_of theorem) aconv key then ()
                        else error "Fast kernel cache key mismatch"
                    in certify theorem end) ()
                  val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), begin))
                  val _ = if Exn.is_exn result then failures := !failures + 1 else ()
                  val theorem = Exn.release result
                  val _ = if !retained < 8192 then () else
                    (evicted := !evicted + !retained;
                     memo := Termtab.empty; retained := 0)
                  val _ = memo := Termtab.update (key, theorem) (!memo)
                  val _ = retained := !retained + 1
                in SOME (restore theorem) end
              end
            end
          val procedure = Simplifier.make_simproc ctxt
            {name = "comma_fast_demand_" ^ name, kind = Simplifier.Simproc,
             lhss = [Term.map_aterms
               (fn Free (variable, typ) => Var ((variable, 0), typ) | atom => atom) pattern],
             proc = fn _ => fn _ => convert, identifier = []}
          val _ = own_procedure := SOME procedure
          fun stats () = name ^ "_hits=" ^ Int.toString (!hits) ^
            " " ^ name ^ "_context_builds=" ^ Int.toString (!context_builds) ^
            " " ^ name ^ "_misses=" ^ Int.toString (!misses) ^
            " " ^ name ^ "_failed=" ^ Int.toString (!failures) ^
            " " ^ name ^ "_retained=" ^ Int.toString (!retained) ^
            " " ^ name ^ "_evicted=" ^ Int.toString (!evicted) ^
            " " ^ name ^ "_inclusive_ms=" ^
              LargeInt.toString (Time.toMilliseconds (!elapsed))
        in (procedure, stats) end
      val boundaries = map boundary selected
      val evaluation = fold (Simplifier.add_proc o #1) boundaries base
      val _ = evaluator := SOME evaluation
      val setup_ms = Time.toMilliseconds (Time.- (Time.now (), started))
      fun stats () =
        let val cert = certification () in
          "setup_ms=" ^ LargeInt.toString setup_ms ^ " " ^
          space_implode " " (map (fn (_, report) => report ()) boundaries) ^
          " cert_calls=" ^ Int.toString (#calls cert) ^
          " cert_nodes=" ^ Int.toString (#nodes cert) ^
          " cert_failed=" ^ Int.toString (#failed_calls cert) ^
          " cert_ms=" ^ LargeInt.toString (#milliseconds cert)
        end
    in {context = evaluation, stats = stats} end

  fun report line =
    let val _ = Output.physical_stderr (line ^ "\n")
        val destination = getenv "COMMA_PROFILE_LOG"
    in if destination = "" then () else File.append (Path.explode destination) (line ^ "\n") end

end
\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_fast_round_aux_eval comma_near_residual_count_eval
      comma_near_residual_target_eval comma_near_closed_target_eval
      comma_near_alphabet_phase_independent}) then ()
    else error "Fast rank dependency audit failed";
\<close>
end
