structure Comma_Decade_Layer_Check =
struct
  type layer = {value: term, correct: thm, length: thm}
  datatype task = Enter of int * int | Join of int * int

  fun make ctxt {max_layers} =
    let
      val _ = if 1 <= max_layers andalso max_layers <= 8192 then ()
        else error "Layer cache capacity must lie in 1..8192"
      val kernel = Comma_Fast_Kernel.make ctxt
      val (certify, certification) = Comma_Entry_Arithmetic.make_certifier ctxt
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
      val base_context = #context kernel |> Simplifier.add_simps
        @{thms comma_decade_base_layer_orbit comma_decade_block_atom_def
          comma_layer_offset_constants
          comma_decade_admitted.simps comma_decade_block_result.case
          list.map upt_rec}
      val square_context = (arithmetic |> fold Simplifier.add_cong
        @{thms comma_decade_layer_lookup_weak_cong comma_decade_layer_resume_weak_cong
          comma_decade_layer_nth_weak_cong comma_decade_layer_length_weak_cong
          comma_decade_layer_square_weak_cong}) |> Simplifier.add_simps
        @{thms comma_decade_layer_square_def comma_decade_layer_lookup_def
          comma_decade_layer_resume.simps comma_decade_block_then.simps
          comma_decade_block_result.case list.map list.size
          nth_Cons' power_numeral_even power_numeral_odd power_0 power_one_right power_Suc0_right}
      val complete_context = square_context |> Simplifier.add_simps
        @{thms comma_decade_layer_complete_def comma_decade_block_stopped_below.simps
          list_all_Nil_iff list_all_Cons_iff}
      val memo = Unsynchronized.ref (Inttab.empty: layer Inttab.table)
      val retained = Unsynchronized.ref 0
      val lookups = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val base_phases = Unsynchronized.ref 0
      val base_attempts = Unsynchronized.ref 0
      val square_attempts = Unsynchronized.ref 0
      val complete_attempts = Unsynchronized.ref 0
      val complete_failures = Unsynchronized.ref 0
      val complete_elapsed = Unsynchronized.ref Time.zeroTime
      val base_elapsed = Unsynchronized.ref Time.zeroTime
      val square_elapsed = Unsynchronized.ref Time.zeroTime
      val squares = Unsynchronized.ref 0
      val publications = Unsynchronized.ref 0
      val evictions = Unsynchronized.ref 0
      val tasks = Unsynchronized.ref 0
      val failures = Unsynchronized.ref 0
      val elapsed = Unsynchronized.ref Time.zeroTime
      fun nat n = HOLogic.mk_number @{typ nat} n
      fun index (level, phase) = level * 924 + phase
      fun right_phase (level, phase) = (phase + Integer.pow (level - 1) 2) mod 924
      fun admitted (level, phase) =
        if 0 <= level andalso level <= 30 andalso 0 <= phase andalso phase < 924 then ()
        else error "Layer request requires level 0..30 and phase 0..923"
      fun lookup key =
        let val _ = lookups := !lookups + 1
        in case Inttab.lookup (!memo) (index key) of
          NONE => NONE
        | SOME result => (hits := !hits + 1; SOME result)
        end
      fun require key = case lookup key of SOME result => result
        | NONE => error "Layer postorder dependency is absent"
      fun natural t = case try HOLogic.dest_number t of
          SOME (typ, n) => typ = @{typ nat} andalso n >= 0
        | NONE => can HOLogic.dest_nat t
      fun terminal t = case strip_comb t of
          (Const (name, _), []) => name = @{const_name Comma_Terminal_Landmine}
        | (Const (name, _), [a]) => name = @{const_name Comma_Terminal_Fork} andalso natural a
        | _ => false
      fun state t = case strip_comb t of
          (Const (name, _), [r, x]) => name = @{const_name Comma_Decade}
            andalso natural r andalso natural x
        | _ => false
      fun result t = case strip_comb t of
          (Const (name, _), []) => name = @{const_name Comma_Block_Invalid}
        | (Const (name, _), [s]) => name = @{const_name Comma_Block_Live} andalso state s
        | (Const (name, _), [h, label]) => name = @{const_name Comma_Block_Stop}
            andalso natural h andalso terminal label
        | _ => false
      fun checked_value equation =
        let
          val value = Thm.term_of (Thm.rhs_of equation)
          val cells = HOLogic.dest_list value
          val _ = if length cells = 91 then ()
            else error ("Layer evaluation produced " ^ Int.toString (length cells) ^ " cells, expected 91")
          val _ = case get_first (fn (index, cell) =>
              if result cell then NONE else SOME (index, cell)) (map_index I cells) of
            NONE => ()
          | SOME (index, cell) => error ("Unresolved layer cell " ^ Int.toString index ^
              " head=" ^ XML.content_of (YXML.parse_body
                (Syntax.string_of_term ctxt (Term.head_of cell))))
        in value end
      fun equation context expression = certify (Simplifier.rewrite context
        (Thm.cterm_of ctxt expression))
      fun object equation = equation RS @{thm meta_eq_to_obj_eq}
      fun boolean expression =
        let
          val normalized = Simplifier.rewrite square_context
            (Thm.cterm_of ctxt (HOLogic.mk_Trueprop expression))
          val _ = if Thm.term_of (Thm.rhs_of normalized) aconv @{prop True} then ()
            else error "Layer arithmetic guard is false"
        in certify (Thm.equal_elim (Thm.symmetric normalized) @{thm TrueI}) end
      fun instantiate bindings theorem = Drule.infer_instantiate ctxt
        (map (fn (name, term) => ((name, 0), Thm.cterm_of ctxt term)) bindings) theorem
      fun timed elapsed action arg =
        let
          val started = Time.now ()
          val result = Exn.capture action arg
          val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), started))
        in Exn.release result end
      fun base phase =
        let
          val _ = base_attempts := !base_attempts + 1
          val evaluated = equation base_context (@{term comma_decade_base_layer} $ nat phase)
          val value = checked_value evaluated
          val correct = certify (@{thm comma_decade_base_layer_valueI} OF [object evaluated])
          val _ = base_phases := !base_phases + 1
          val _ = if getenv "COMMA_PROFILE_LOG" = "" then () else
            Comma_Fast_Kernel.report ("Layer base phase=" ^ Int.toString phase ^
              " checked_base_phases=" ^ Int.toString (!base_phases) ^
              " checked_base_atoms=" ^ Int.toString (91 * !base_phases) ^
              " base_attempts=" ^ Int.toString (!base_attempts) ^
              " square_attempts=" ^ Int.toString (!square_attempts) ^
              " checked_squares=" ^ Int.toString (!squares))
          val length = certify (@{thm comma_decade_layer_correct_length} OF [correct])
        in {value = value, correct = correct, length = length}: layer end
      fun square (level, phase) =
        let
          val _ = square_attempts := !square_attempts + 1
          val prior = level - 1
          val shifted = right_phase (level, phase)
          val left = require (prior, phase)
          val right = require (prior, shifted)
          val expression = @{term comma_decade_layer_square} $ nat prior $ nat phase $
            #value left $ #value right
          val evaluated = equation
            (square_context |> Simplifier.add_simps [#length left, #length right]) expression
          val value = checked_value evaluated
          val rule = instantiate [("next", nat level), ("k", nat prior),
            ("phase", nat shifted), ("r", nat phase), ("lhs", #value left),
            ("rhs", #value right), ("result", value)] @{thm comma_decade_square_layer_valueI}
          val next = boolean (HOLogic.mk_eq (nat level, @{term Suc} $ nat prior))
          val shift = boolean (HOLogic.mk_eq (nat shifted,
            @{term "(r+2^k) mod 924 :: nat"} |> Term.subst_free [(Free ("r", @{typ nat}), nat phase),
              (Free ("k", @{typ nat}), nat prior)]))
          val valid = boolean (@{term "less :: nat => nat => bool"} $ nat phase $ nat 924)
          val correct = certify (rule OF [next, shift, valid, #correct left, #correct right,
            object evaluated])
          val _ = squares := !squares + 1
          val length = certify (@{thm comma_decade_layer_correct_length} OF [correct])
        in {value = value, correct = correct, length = length}: layer end
      fun clear () = (evictions := !evictions + !retained;
        memo := Inttab.empty; retained := 0)
      fun construct key =
        let
          val started = Time.now ()
          val created = Unsynchronized.ref ([]: int list)
          fun reserve () =
            if !retained >= max_layers then error "Layer cache construction budget exhausted" else ()
          fun publish key value =
            if !retained >= max_layers then error "Layer cache construction budget exhausted"
            else (memo := Inttab.update (index key, value) (!memo);
              created := index key :: !created; retained := !retained + 1;
              publications := !publications + 1)
          fun work [] = ()
            | work (task :: rest) =
              let val _ = tasks := !tasks + 1 in
                case task of
                  Enter (key as (level, phase)) =>
                    (case lookup key of SOME _ => work rest | NONE =>
                      (reserve ();
                       if level = 0 then (publish key (timed base_elapsed base phase); work rest)
                       else work (Enter (level - 1, phase) ::
                         Enter (level - 1, right_phase key) :: Join key :: rest)))
                | Join key => (reserve (); publish key (timed square_elapsed square key); work rest)
              end
          val attempt = Exn.capture (fn () =>
            (admitted key;
             if !retained = max_layers andalso is_none (Inttab.lookup (!memo) (index key))
               then clear () else ();
             work [Enter key]; require key)) ()
          val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), started))
        in case attempt of
          Exn.Res result => result
        | Exn.Exn failure =>
            (failures := !failures + 1;
             memo := fold Inttab.delete_safe (!created) (!memo);
             retained := !retained - length (!created);
             Exn.reraise failure)
        end
      fun complete level phase bound =
        let
          val started = Time.now ()
          val _ = complete_attempts := !complete_attempts + 1
          (* Construction counts its own failures. Count a complete request once,
             including an invalid bound or a rejected final completeness check. *)
          val failures_before = !failures
          val attempt = Exn.capture (fn () =>
            let
              val _ = if bound >= 0 then () else error "Negative layer stop bound"
              val layer = construct (level, phase)
              val expression = @{term comma_decade_layer_complete} $ nat bound $ #value layer
              val evaluated = equation complete_context expression
              val _ = if Thm.term_of (Thm.rhs_of evaluated) aconv @{term True} then ()
                else error "Layer contains a live, invalid, or over-bound result"
              val complete = certify (object evaluated RS @{thm eqTrueE})
            in {layer = layer, complete = complete} end) ()
          val _ = complete_elapsed := Time.+ (!complete_elapsed, Time.- (Time.now (), started))
        in case attempt of
          Exn.Res result => result
        | Exn.Exn failure =>
            (complete_failures := !complete_failures + 1;
             if !failures = failures_before then failures := !failures + 1 else ();
             Exn.reraise failure)
        end
      fun stats () = {lookups = !lookups, hits = !hits, base_phases = !base_phases,
        checked_base_atoms = 91 * !base_phases, base_attempts = !base_attempts,
        square_attempts = !square_attempts, squares = !squares, publications = !publications,
        retained_layers = !retained, evictions = !evictions, tasks = !tasks,
        failed_requests = !failures, construction_ms = Time.toMilliseconds (!elapsed),
        base_ms = Time.toMilliseconds (!base_elapsed), square_ms = Time.toMilliseconds (!square_elapsed),
        complete_attempts = !complete_attempts, complete_failures = !complete_failures,
        complete_inclusive_ms = Time.toMilliseconds (!complete_elapsed),
        kernel = #stats kernel (), certification = certification ()}
      fun report () =
        let
          val measured = stats ()
          fun count (name, value) = name ^ "=" ^ Int.toString value
          fun duration (name, value) = name ^ "=" ^ LargeInt.toString value
        in space_implode " "
          (map count [("lookups", #lookups measured), ("hits", #hits measured),
            ("base_phases", #base_phases measured), ("checked_base_atoms", #checked_base_atoms measured),
            ("base_attempts", #base_attempts measured), ("square_attempts", #square_attempts measured),
            ("squares", #squares measured), ("publications", #publications measured),
            ("retained_layers", #retained_layers measured), ("evictions", #evictions measured),
            ("tasks", #tasks measured), ("failed_requests", #failed_requests measured),
            ("complete_attempts", #complete_attempts measured), ("complete_failures", #complete_failures measured)] @
           map duration [("construction_ms", #construction_ms measured),
             ("base_ms", #base_ms measured), ("square_ms", #square_ms measured),
             ("complete_inclusive_ms", #complete_inclusive_ms measured)] @
           [#kernel measured])
        end
    in {construct = construct, complete = complete, clear = clear, stats = stats, report = report} end
end
