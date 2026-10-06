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

lemma comma_fast_entry_round_jump:
  "comma_fast_round_aux fuel r (Comma_Entry f 0 x) =
    (if fuel=0 \<or> f<1 \<or> 9<f \<or> 98<x then Comma_Round_Invalid
     else case comma_entry_jump f x (comma_entry_alphabet_phase f r 0 x) of
       Inl result \<Rightarrow> result
     | Inr target \<Rightarrow> comma_fast_round_aux (fuel-1) r target)"
proof (cases "fuel=0")
  case True
  then show ?thesis by (simp add: comma_fast_round_aux_eval)
next
  case nonzero: False
  show ?thesis
  proof (cases "f<1 \<or> 9<f \<or> 98<x")
    case True
    have target: "comma_fast_sector_target r (Comma_Entry f 0 x)=Comma_Entry f 0 x"
      using True by (simp only: comma_sector_entry_alphabet if_True)
    have invalid: "comma_fast_step (r mod 924) (Comma_Entry f 0 x)=Comma_Invalid"
      using True by (simp only: comma_fast_step.simps if_True)
    show ?thesis using comma_fast_round_aux_eval[of fuel r "Comma_Entry f 0 x"]
      nonzero True
      by (simp only: target invalid Let_def comma_finite_move.case if_False if_True simp_thms)
  next
    case valid: False
    let ?k = "comma_entry_alphabet_phase f r 0 x"
    let ?t = "Comma_Near f 0 (comma_entry_alphabet_endpoint f x ?k)"
    have target: "comma_fast_sector_target r (Comma_Entry f 0 x)=?t"
      using valid by (simp only: comma_sector_entry_alphabet if_False)
    have event: "comma_fast_step (r mod 924) ?t=comma_fast_step 0 ?t"
      by (simp only: comma_fast_step.simps)
    note equation = comma_fast_round_aux_eval[of fuel r "Comma_Entry f 0 x"]
    show ?thesis using equation nonzero valid
      by (simp only: target event comma_entry_jump_def Let_def if_False simp_thms;
        cases "comma_fast_step 0 ?t"; simp only: comma_finite_move.case;
        split if_splits; simp_all)
  qed
qed

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
        sum.case_cong_weak
        conj_left_cong disj_left_cong}) addsimps
    @{thms comma_fast_entry_round_jump comma_fast_round_aux_eval
      comma_near_residual_target_eval comma_fast_decade_control.simps
      comma_sector_entry_alphabet comma_sector_near_alphabet comma_entry_alphabet_phase_def
      comma_entry_alphabet_endpoint_def comma_fast_step.simps(1)
      comma_fast_near_event_alphabet comma_near_event_alphabet_eval
      comma_shift_move.simps comma_shift_position.simps comma_shift_round_result.simps
      comma_near_closed_target_eval
      comma_cycle_length_fast_def comma_finite_period_fast_def
      comma_finite_headroom_fast_def comma_power_residue_fast_def
      comma_power_table_def comma_short_period_def comma_round_crossing_def
      comma_decade_decode.simps comma_decade_root_admitted_entry
      comma_decade_outcome.case
      comma_finite_move.case comma_finite_position.case comma_round_result.case sum.case
      list_all_Nil_iff list_all_Cons_iff
      upt_rec nth_Cons' of_nat_numeral of_nat_0 of_nat_1
      zmod_zminus1_eq_if zmod_zminus2_eq_if Num.inc.simps};

  (* A cache belongs to one immutable, assumption-free evaluation context.
     Simprocs ignore the invoking goal context and publish only closed kernel
     equalities certified by the existing dependency audit. *)
  fun make_with_transport transport_key ctxt =
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
         ("entry_jump", @{term "comma_entry_jump f x k"},
            @{thms comma_entry_jump_def}),
         ("sector_target", @{term "comma_fast_sector_target r source"},
            @{thms comma_sector_entry_alphabet comma_sector_near_alphabet}),
         ("decade", @{term "comma_fast_decade_control s"},
            @{thms comma_fast_decade_control.simps})]
      val base = context ctxt delsimps (maps #3 selected @
        @{thms comma_fast_entry_round_jump comma_fast_round_aux_eval})
      val evaluator = Unsynchronized.ref (NONE: Proof.context option)
      fun closed t = null (Term.add_frees t []) andalso
        null (Term.add_vars t []) andalso not (Term.is_open t)
      val round_arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
      val round_guard_hits = Unsynchronized.ref 0
      val round_guard_misses = Unsynchronized.ref 0
      val round_guard_failures = Unsynchronized.ref 0
      val round_guards = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      fun round_guard premise =
        if not (closed premise) then error "Open proposition in round guard memo"
        else (case Termtab.lookup (!round_guards) premise of
          SOME theorem =>
            let
              val _ = if Thm.prop_of theorem aconv premise andalso
                Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
                then () else error "Round guard memo authority mismatch"
              val _ = round_guard_hits := !round_guard_hits + 1
            in theorem end
        | NONE =>
            let
              val _ = round_guard_misses := !round_guard_misses + 1
              val result = Exn.capture (fn () =>
                let
                  val theorem = Goal.prove ctxt [] [] premise
                    (fn _ => simp_tac round_arithmetic 1) |> certify
                  val _ = if Thm.prop_of theorem aconv premise andalso
                    Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
                    then () else error "Round guard proof changed its proposition"
                in theorem end) ()
              val _ = if Exn.is_exn result then
                round_guard_failures := !round_guard_failures + 1 else ()
              val theorem = Exn.release result
              val _ = round_guards := Termtab.update (premise,theorem) (!round_guards)
            in theorem end)
      val constructors =
        @{const_name Inl} :: @{const_name Inr} ::
        @{const_name Comma_Round_Cross} :: @{const_name Comma_Round_Fork} ::
        @{const_name Comma_Round_Landmine} :: @{const_name Comma_Round_Invalid} ::
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
      fun canonical_headroom name key =
        if name <> "headroom" then (key, NONE) else
        (case strip_comb key of
          (Const (head, _), [f, residue, delta, offset]) =>
            if head <> @{const_name comma_finite_headroom_fast} then (key, NONE)
            else
              (case map (try HOLogic.dest_number) [f, residue, delta, offset] of
                [SOME (f_type, sector), SOME (r_type, _),
                    SOME (d_type, _), SOME (x_type, _)] =>
                  if f_type <> @{typ nat} orelse r_type <> @{typ nat} orelse
                    d_type <> @{typ nat} orelse x_type <> @{typ nat} orelse
                    sector < 1 orelse sector > 9 then (key, NONE)
                  else
                    let
                      val rule = Drule.infer_instantiate ctxt
                        (map (fn (name, term) => ((name, 0), Thm.cterm_of ctxt term))
                          [("f", f), ("residue", residue),
                           ("delta", delta), ("offset", offset)])
                        @{thm comma_finite_headroom_fast_phase_normalized}
                      val admitted = rule OF (map round_guard (Thm.prems_of rule))
                      val admitted_meta = admitted RS @{thm eq_reflection}
                      val rhs = Thm.rhs_of admitted_meta
                      val normalize_phase = Simplifier.rewrite
                        (round_arithmetic addsimps
                          @{thms comma_finite_period_fast_def comma_short_period_def
                            nth_Cons'}) rhs
                      val equation = Thm.transitive admitted_meta normalize_phase
                      val canonical = Thm.term_of (Thm.rhs_of equation)
                      val _ = if Thm.term_of (Thm.lhs_of equation) aconv key andalso
                        closed canonical then ()
                        else error "Headroom phase transport changed its source"
                    in (canonical, SOME equation) end
              | _ => (key, NONE))
        | _ => (key, NONE))
      fun transport_record_valid original (key, transport) =
        if not (closed key) then false else
        (case transport of
          NONE => original aconv key
        | SOME theorem =>
            Thm.term_of (Thm.lhs_of theorem) aconv original andalso
            Thm.term_of (Thm.rhs_of theorem) aconv key andalso
            Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem))
      fun boundary (name, pattern, equations) =
        let
          val memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
          (* These two tables are occurrence-level accelerators, not action
             identities. The transport table avoids normalizing an identical
             closed request twice; the result table avoids rebuilding and
             re-certifying its exact transported theorem. Their keys may retain
             linear occurrence data because they never authorize substitution
             at a different source occurrence. *)
          val transport_memo = Unsynchronized.ref
            (Termtab.empty: (term * thm option) Termtab.table)
          val occurrence_memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
          val own_procedure = Unsynchronized.ref (NONE: Simplifier.simproc option)
          val boundary_context = Unsynchronized.ref (NONE: Proof.context option)
          val context_builds = Unsynchronized.ref 0
          val hits = Unsynchronized.ref 0
          val misses = Unsynchronized.ref 0
          val failures = Unsynchronized.ref 0
          val retained = Unsynchronized.ref 0
          val evicted = Unsynchronized.ref 0
          val transport_hits = Unsynchronized.ref 0
          val transport_misses = Unsynchronized.ref 0
          val transport_evicted = Unsynchronized.ref 0
          val occurrence_hits = Unsynchronized.ref 0
          val occurrence_misses = Unsynchronized.ref 0
          val occurrence_evicted = Unsynchronized.ref 0
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
          fun transport_for original =
            (case Termtab.lookup (!transport_memo) original of
              SOME prepared =>
                let
                  val _ = if transport_record_valid original prepared then ()
                    else error "Transport memo authority mismatch"
                  val _ = transport_hits := !transport_hits + 1
                in prepared end
            | NONE =>
                let
                  val _ = transport_misses := !transport_misses + 1
                  val (sector_key, sector_transport) =
                    canonical_sector name original
                  val (first_key, headroom_transport) =
                    canonical_headroom name sector_key
                  val first_transport = (case (sector_transport, headroom_transport) of
                      (NONE, NONE) => NONE
                    | (SOME equation, NONE) => SOME equation
                    | (NONE, SOME equation) => SOME equation
                    | (SOME prior, SOME equation) =>
                        SOME (Thm.transitive prior equation))
                  val extra = transport_key name first_key
                  val prepared = (case extra of
                      NONE => (first_key, first_transport)
                    | SOME raw =>
                        let
                          val equation = certify raw
                          val lhs = Thm.term_of (Thm.lhs_of equation)
                          val rhs = Thm.term_of (Thm.rhs_of equation)
                          val _ = if lhs aconv first_key andalso closed rhs then ()
                            else error "Foreign or open fast-kernel transport"
                          val composed = (case first_transport of NONE => equation
                            | SOME prior => Thm.transitive prior equation)
                        in (rhs, SOME composed) end)
                  val _ = if transport_record_valid original prepared then ()
                    else error "Transport construction changed its source"
                  val transformed = not (#1 prepared aconv original) orelse
                    is_some (#2 prepared)
                  val _ = if not transformed then () else
                    let
                      val _ = if Termtab.size (!transport_memo) < 8192 then () else
                        (transport_evicted := !transport_evicted +
                          Termtab.size (!transport_memo);
                         transport_memo := Termtab.empty)
                    in transport_memo := Termtab.update
                      (original, prepared) (!transport_memo) end
                in prepared end)
          fun remember_occurrence original theorem =
            let
              val _ = if Thm.term_of (Thm.lhs_of theorem) aconv original andalso
                Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
                then () else error "Invalid complete occurrence theorem"
              val _ = if Termtab.size (!occurrence_memo) < 8192 then () else
                (occurrence_evicted := !occurrence_evicted +
                  Termtab.size (!occurrence_memo);
                 occurrence_memo := Termtab.empty)
              val _ = occurrence_misses := !occurrence_misses + 1
            in occurrence_memo := Termtab.update
              (original, theorem) (!occurrence_memo) end
          fun convert ct =
            let val original = Thm.term_of ct in
              if not (closed original) then NONE else
              (case Termtab.lookup (!occurrence_memo) original of
                SOME theorem =>
                  let
                    val _ = if Thm.term_of (Thm.lhs_of theorem) aconv original andalso
                      Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
                      then () else error "Occurrence memo authority mismatch"
                    val _ = occurrence_hits := !occurrence_hits + 1
                  in SOME theorem end
              | NONE =>
              let
                val (key, transport) = transport_for original
                fun restore theorem = (case transport of NONE => theorem
                  | SOME equation => Thm.transitive equation theorem)
                fun publish_occurrence theorem =
                  let val restored = restore theorem
                      val _ = if Thm.term_of (Thm.lhs_of restored) aconv original andalso
                        Thm.nprems_of restored = 0 andalso null (Thm.hyps_of restored)
                        then () else error "Transported occurrence theorem mismatch"
                      val _ = if key aconv original andalso not (is_some transport)
                        then () else remember_occurrence original restored
                  in restored end
              in case Termtab.lookup (!memo) key of
                SOME theorem =>
                  let val restored = publish_occurrence theorem
                  in hits := !hits + 1; SOME restored end
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
                  val restored = publish_occurrence theorem
                  val _ = if !retained < 8192 then () else
                    (evicted := !evicted + !retained;
                     memo := Termtab.empty; retained := 0)
                  val _ = memo := Termtab.update (key, theorem) (!memo)
                  val _ = retained := !retained + 1
                in SOME restored end
              end
              )
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
            " " ^ name ^ "_transport_hits=" ^ Int.toString (!transport_hits) ^
            " " ^ name ^ "_transport_misses=" ^ Int.toString (!transport_misses) ^
            " " ^ name ^ "_transport_evicted=" ^ Int.toString (!transport_evicted) ^
            " " ^ name ^ "_occurrence_hits=" ^ Int.toString (!occurrence_hits) ^
            " " ^ name ^ "_occurrence_misses=" ^ Int.toString (!occurrence_misses) ^
            " " ^ name ^ "_occurrence_evicted=" ^ Int.toString (!occurrence_evicted) ^
            " " ^ name ^ "_inclusive_ms=" ^
              LargeInt.toString (Time.toMilliseconds (!elapsed))
        fun measurement () = (name, {hits= !hits, misses= !misses,
            failures= !failures, retained= !retained})
        in (procedure, stats, measurement) end
      (* Round continuation syntax is occurrence work, not a semantic action.
         Rewrite one root, then let the simplifier demand cached complete local
         jumps. Retaining all phase-specific suffix proofs had zero release-path
         hits and duplicated the complete decade memo. *)
      val round_expansions = Unsynchronized.ref 0
      val round_transports = Unsynchronized.ref 0
      fun round_transport ct =
        (case Term.strip_comb (Thm.term_of ct) of
          (_, [fuel,r,source]) =>
            (case Term.strip_comb source of
              (Const (head,_), [f,d,x]) =>
                if head <> @{const_name Comma_Entry} then NONE else
                (case map (try HOLogic.dest_number) [fuel,f,d,x] of
                  [SOME (_,9),SOME (_,sector),SOME (_,delta),SOME (_,offset)] =>
                    if delta <= 0 orelse sector < 1 orelse sector > 9 orelse offset > 98
                    then NONE else
                    let
                      val rule = Drule.infer_instantiate ctxt
                        (map (fn (name,t) => ((name,0),Thm.cterm_of ctxt t))
                          [("r",r),("f",f),("d",d),("x",x)])
                        @{thm comma_fast_entry_round_phase_normalized}
                      val admitted = Simplifier.simplify round_arithmetic
                        (rule OF map round_guard (Thm.prems_of rule))
                      val equation = Conv.rewr_conv (admitted RS @{thm eq_reflection}) ct
                      (* The source phase theorem is covered by the theory's
                         oracle audit and every dynamic premise comes from
                         round_guard's certified closed memo. Rewalking the
                         complete dependency DAG for each instantiated root
                         repeated the same proof audit without adding authority. *)
                      val _ = if Thm.term_of (Thm.lhs_of equation) aconv Thm.term_of ct andalso
                        Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation)
                        then () else error "Round transport changed its closed source"
                      val _ = round_transports := !round_transports+1
                    in SOME equation end
                | _ => NONE)
            | _ => NONE)
        | _ => NONE)
      fun round_convert ct =
        if not (closed (Thm.term_of ct)) then NONE else
        (case round_transport ct of
          SOME equation => SOME equation
        | NONE =>
          let
            val equation = Conv.rewrs_conv
              (map (fn th => th RS @{thm eq_reflection})
                @{thms comma_fast_entry_round_jump comma_fast_round_aux_eval}) ct
            val _ = round_expansions := !round_expansions + 1
          in SOME equation end)
      val round_procedure = Simplifier.make_simproc ctxt
        {name = "comma_fast_round_root", kind = Simplifier.Simproc,
         lhss = [@{term comma_fast_round_aux} $ Var (("fuel",0), @{typ nat}) $
           Var (("r",0), @{typ nat}) $ Var (("source",0), @{typ comma_finite_position})],
         proc = fn _ => fn _ => round_convert, identifier = []}
      val boundaries = map boundary selected
      val evaluation = fold (Simplifier.add_proc o #1) boundaries
        (base |> Simplifier.add_proc round_procedure)
      val _ = evaluator := SOME evaluation
      val setup_ms = Time.toMilliseconds (Time.- (Time.now (), started))
      fun stats () =
        let val cert = certification () in
          "setup_ms=" ^ LargeInt.toString setup_ms ^
          " round_expansions=" ^ Int.toString (!round_expansions) ^
          " round_transports=" ^ Int.toString (!round_transports) ^
          " round_guard_hits=" ^ Int.toString (!round_guard_hits) ^
          " round_guard_misses=" ^ Int.toString (!round_guard_misses) ^
          " round_guard_failed=" ^ Int.toString (!round_guard_failures) ^
          " round_guard_entries=" ^ Int.toString (Termtab.size (!round_guards)) ^ " " ^
          space_implode " " (map (fn (_, report, _) => report ()) boundaries) ^
          " cert_calls=" ^ Int.toString (#calls cert) ^
          " cert_nodes=" ^ Int.toString (#nodes cert) ^
          " cert_failed=" ^ Int.toString (#failed_calls cert) ^
          " cert_ms=" ^ LargeInt.toString (#milliseconds cert)
        end
    in {context = evaluation, stats = stats,
      measurements = fn () => map (fn (_, _, measure) => measure ()) boundaries} end

  fun make ctxt = make_with_transport (fn _ => fn _ => NONE) ctxt

  fun report line =
    let val _ = Output.physical_stderr (line ^ "\n")
        val destination = getenv "COMMA_PROFILE_LOG"
    in if destination = "" orelse destination = "1" then ()
       else File.append (Path.explode destination) (line ^ "\n") end

end
\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_fast_entry_round_jump comma_entry_jump_transport
      comma_fast_round_aux_eval comma_near_residual_count_eval
      comma_near_residual_target_eval comma_near_closed_target_eval
      comma_near_alphabet_phase_independent}) then ()
    else error "Fast rank dependency audit failed";
\<close>
end
