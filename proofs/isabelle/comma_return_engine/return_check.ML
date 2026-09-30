structure Comma_Return_Check =
struct
  (* Sole owner of the checked 314-choice witness. *)
  val nine_choices =
    "01110011101100001100101111110000110010010000110101000100001110010110001100111000111111110010111001111100101111110000011000000001011111011111010111011111110110100110011000101100100111100011111000110111011001001000110101101110010010110001100001111101110001000101110000111111101010100001110010001111010111011111010110"

  (* The shared engine turns one admitted boundary into a checked macro and
     its complete ordered child list.  Both the selected return and local
     losing-branch certificates use this same arithmetic owner. *)
  fun make_engine ctxt =
    let
      val core = Comma_Fast_Kernel.make ctxt
      val (certify, certification) = Comma_Entry_Arithmetic.make_certifier ctxt
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt addsimps
        @{thms comma_boundary_valid_def comma_finite_initial_def
          comma_total_children_def comma_boundary_kind.case comma_boundary_kind.distinct
          comma_finite_outcome.case list.set insert_iff empty_iff
          comma_round_admitted.simps comma_round_delta.simps
          comma_shift_position.simps comma_return_shift_outcome.simps}
      fun nat n = HOLogic.mk_number @{typ nat} n
      fun prove proposition facts = certify (Goal.prove ctxt [] [] proposition
        (fn _ => simp_tac (arithmetic addsimps facts) 1))
      fun eq term = Simplifier.rewrite (#context core) (Thm.cterm_of ctxt term)
      fun number t = snd (HOLogic.dest_number t)
      fun canonical_natural t =
        (case try HOLogic.dest_number t of
          SOME (typ,n) => typ = @{typ nat} andalso n >= 0 andalso t aconv nat n
        | NONE => false)
      fun phase_of q = @{term "snd :: nat * nat => nat"} $
        (@{term "snd :: comma_boundary_kind * (nat * nat) => nat * nat"} $ q)
      fun boundary_key theorem =
        let
          val proposition = Thm.prop_of theorem
          val _ = if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
              andalso null (Term.add_frees proposition [])
              andalso null (Term.add_vars proposition [])
            then () else error "Imported comma boundary trace is not a closed instance"
          val (head,args) = Term.strip_comb (HOLogic.dest_Trueprop proposition)
          val _ = if head = @{term comma_round_reaches} andalso length args = 3
            then () else error "Imported comma boundary trace has the wrong theorem head"
          val (initial,initial_args) = Term.strip_comb (nth args 1)
          val _ = if initial = @{term comma_finite_initial} andalso length initial_args = 1
            then () else error "Imported comma trace has no exact boundary source"
          val q = hd initial_args
          val (kind,coordinates) = HOLogic.dest_prod q
          val (digit,phase) = HOLogic.dest_prod coordinates
          val a = number digit
          val r = number phase
          val _ = if (kind = @{term Comma_N} orelse kind = @{term Comma_Z})
              andalso 2 <= a andalso a <= 9 andalso 0 <= r andalso r < 924
              andalso digit aconv nat a andalso phase aconv nat r
            then () else error "Imported comma boundary key is not canonical"
          val _ = if hd args aconv phase_of q then ()
            else error "Imported comma trace has a different source phase"
          val (terminal,terminal_args) = Term.strip_comb (nth args 2)
          val _ = if (terminal = @{term Comma_Fork_At} andalso length terminal_args=2)
              orelse (terminal = @{term Comma_Landmine_At} andalso length terminal_args=1)
            then () else error "Imported comma boundary trace has no complete outcome"
          val _ = if List.all canonical_natural terminal_args then ()
            else error "Imported comma boundary trace has a noncanonical outcome"
        in q end
      fun add_boundary theorem table =
        let val q = boundary_key theorem
        in case Termtab.lookup table q of
          NONE => Termtab.update (q,certify theorem) table
        | SOME old =>
            if Thm.prop_of old aconv Thm.prop_of theorem then table
            else error "Conflicting checked outcomes for one comma boundary source"
        end
      val boundaries = Unsynchronized.ref
        (fold add_boundary (Named_Theorems.get ctxt
          @{named_theorems comma_completed_boundary_traces}) Termtab.empty)
      val boundary_retained = Unsynchronized.ref (Termtab.size (!boundaries))
      val boundary_hits = Unsynchronized.ref 0
      val boundary_retrievals = Unsynchronized.ref 0
      val boundary_misses = Unsynchronized.ref 0
      val round_evaluations = Unsynchronized.ref 0

      (* Cold construction uses the kernel's checked local phase transport.
         Retain only the completed boundary, not every offset-restored suffix:
         those suffixes had no hits on the 314-edge return. *)
      fun reached phase initial =
        let
          fun seek source active stack =
            let
              val _ = if Termtab.defined active source then
                error "Nonterminating comma macro under exact source key" else ()
              val expression = @{term comma_fast_round_aux} $ nat 9 $
                nat phase $ source
              val _ = round_evaluations := !round_evaluations + 1
              val result = eq expression
              val fact = certify (result RS @{thm meta_eq_to_obj_eq})
              val equality = HOLogic.dest_eq
                (HOLogic.dest_Trueprop (Thm.prop_of fact))
              val _ = if #1 equality aconv expression andalso
                  Thm.nprems_of fact = 0 andalso null (Thm.hyps_of fact)
                then () else error "Comma round evaluation lost its source binding"
              val value = Thm.term_of (Thm.rhs_of result)
              val (constructor,args) = Term.strip_comb value
            in
              if constructor = @{term Comma_Round_Cross} then
                seek (hd args) (Termtab.update (source,()) active) (fact::stack)
              else
                let
                  val terminal = if constructor = @{term Comma_Round_Fork} then
                      fact RS @{thm comma_round_reaches.fork}
                    else if constructor = @{term Comma_Round_Landmine} then
                      fact RS @{thm comma_round_reaches.landmine}
                    else error "Invalid comma boundary macro"
                in fold (fn edge => fn child =>
                  @{thm comma_round_reaches.crossing} OF [edge,child])
                  stack terminal |> certify end
            end
        in seek initial Termtab.empty [] end

      fun as_round_outcome finite =
        let
          val (constructor,args) = Term.strip_comb finite
        in
          if constructor = @{term Comma_Fork_At} then
            @{term Comma_Round_Fork} $ hd args $ nth args 1
          else if constructor = @{term Comma_Landmine_At} then
            @{term Comma_Round_Landmine} $ hd args
          else error "A boundary tail must finish at a fork or landmine"
        end

      fun boundary q =
        let
          val phase_term = phase_of q
          val phase = number (Thm.term_of (Thm.rhs_of
            (Simplifier.rewrite arithmetic (Thm.cterm_of ctxt phase_term))))
          val initial_term = @{term comma_finite_initial} $ q
          (* This lookup precedes source expansion and every fast-round call.
             The theorem collection is scoped to the importing proof context. *)
          val cached = Termtab.lookup (!boundaries) q
          val trace = (case cached of
              SOME theorem =>
                (boundary_retrievals := !boundary_retrievals + 1; theorem)
            | NONE =>
                let
                  val _ = boundary_misses := !boundary_misses + 1
                  val initial = Thm.term_of (Thm.rhs_of
                    (Simplifier.rewrite arithmetic (Thm.cterm_of ctxt initial_term)))
                  val raw = reached phase initial
                  val (_,args) = Term.strip_comb
                    (HOLogic.dest_Trueprop (Thm.prop_of raw))
                  val theorem = prove (HOLogic.mk_Trueprop
                    (@{term comma_round_reaches} $ phase_term $ initial_term $
                      nth args 2)) [raw]
                  val _ = if !boundary_retained < 14784 then
                      (boundaries := add_boundary theorem (!boundaries);
                       boundary_retained := !boundary_retained + 1)
                    else ()
                in theorem end)
          val finite =
            let val (_,args) = Term.strip_comb (HOLogic.dest_Trueprop (Thm.prop_of trace))
            in nth args 2 end
          val outcome = as_round_outcome finite
          val valid = prove (HOLogic.mk_Trueprop (@{term comma_boundary_valid} $ q)) []
          val defined = @{thm comma_round_reaches_macro(1)} OF [valid,trace]
          val macro = @{thm comma_round_reaches_macro(2)} OF [valid,trace]
          val _ = if is_some cached then boundary_hits := !boundary_hits + 1 else ()
        in {valid=valid, trace=trace, defined=defined, macro=macro,
            outcome=outcome, finite_outcome=finite, phase=phase} end

      fun report () = #stats core () ^
        " return_cert_ms=" ^ LargeInt.toString (#milliseconds (certification ())) ^
        " completed_boundary_hits=" ^ Int.toString (!boundary_hits) ^
        " completed_boundary_retrievals=" ^ Int.toString (!boundary_retrievals) ^
        " completed_boundary_misses=" ^ Int.toString (!boundary_misses) ^
        " completed_boundary_retained=" ^ Int.toString (!boundary_retained) ^
        " boundary_round_evaluations=" ^ Int.toString (!round_evaluations)
    in
      {boundary=boundary, prove=prove, arithmetic=arithmetic, certify=certify,
       eq=eq, report=report,
       boundary_work=fn () => (!boundary_hits,!boundary_misses,!round_evaluations),
       boundary_traces=fn () => map #2 (Termtab.dest (!boundaries))}
    end

  fun check ctxt choices =
    let
      val _ = if size choices = 314 andalso
          List.all (fn c => c = #"0" orelse c = #"1") (String.explode choices)
        then () else error "Return witness must contain 314 binary choices"
      val engine = make_engine ctxt
      val boundary = #boundary engine
      val arithmetic = #arithmetic engine
      val certify = #certify engine
      fun nat n = HOLogic.mk_number @{typ nat} n
      fun number t = snd (HOLogic.dest_number t)
      val q0 = @{term "(Comma_N,2,10)::comma_boundary_state"}
      fun state kind a r = HOLogic.mk_prod (kind, HOLogic.mk_prod (nat a,nat r))
      fun edge choice q =
        let
          val {valid,trace,defined,macro,outcome,...} = boundary q
          val (constructor,args) = Term.strip_comb outcome
          val _ = if constructor = @{term Comma_Round_Fork} then ()
            else error "Candidate return chose a landmine"
          val a = number (hd args)
          val d = number (nth args 1)
          val r = number (Thm.term_of (Thm.rhs_of
            (Simplifier.rewrite arithmetic (Thm.cterm_of ctxt
              (@{term "snd :: nat * nat => nat"} $
                (@{term "snd :: comma_boundary_kind * (nat * nat) => nat * nat"} $ q))))))
          val kind = if choice = #"0" then @{term Comma_N}
            else if choice = #"1" then @{term Comma_Z}
            else error "Invalid return choice"
          val target = state kind a ((r+d) mod 924)
          val rule = Drule.infer_instantiate ctxt
            [(("kind",0),Thm.cterm_of ctxt kind)] @{thm comma_checked_return_edge}
          (* Membership and the empty suffix are proved once in the generic
             edge lemma; only the concrete target admission is simplified. *)
          val result = (rule OF [valid,defined,macro])
            |> Simplifier.full_simplify arithmetic |> certify
        in (target,result) end
      fun next choice (q,count,edges) =
        let
          val (target,proof) = edge choice q
          val _ = if count mod 32 = 31 then
            Comma_Fast_Kernel.report ("Return edges=" ^ Int.toString (count+1))
            else ()
        in (target,count+1,proof::edges) end
      val (last,_,backwards) = fold next (String.explode choices) (q0,0,[])
      val _ = if last aconv q0 then () else error "Candidate return does not close"
      fun join left right = (@{thm comma_return_path_append} OF [left,right])
        |> Simplifier.simplify arithmetic |> certify
      fun reduce [theorem] = theorem
        | reduce [] = error "Empty candidate return"
        | reduce theorems =
            let fun pairs (a::b::rest) = join a b :: pairs rest
                  | pairs rest = rest
            in reduce (pairs theorems) end
      val result = reduce (rev backwards)
      val expected = @{prop "comma_return_path 314 (Comma_N,2,10) (Comma_N,2,10) 924"}
      val _ = if Thm.prop_of result aconv expected andalso Thm.nprems_of result=0
          andalso null (Thm.hyps_of result) then ()
        else error "Candidate return has wrong exact displacement or edge count"
      val _ = Comma_Fast_Kernel.report ("Return check " ^ #report engine ())
    in (certify result,#boundary_traces engine ()) end
end
