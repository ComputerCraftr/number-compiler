structure Comma_Branch_Period_Check =
struct
  fun check ctxt =
    let
      val _ = Comma_Fast_Kernel.report "Concrete safe-return checker: entering local_setup"
      val choices = Comma_Return_Check.nine_choices
      val _ = if size choices = 314 andalso
          List.all (fn c => c = #"0" orelse c = #"1") (String.explode choices)
        then () else error "The canonical comma choice witness is malformed"
      val shared = Comma_Branch_Termination_Check.make ctxt
      val engine = #engine shared
      val children = #children shared
      val check_roots = #check_roots shared
      val boundary = #boundary engine
      val arithmetic = #arithmetic engine
      val certify = #certify engine
      val report = #report engine
      val root = @{term "(Comma_N,2,10)::comma_boundary_state"}
      val termination = @{term comma_boundary_terminates}
      fun nat n = HOLogic.mk_number @{typ nat} n
      fun state kind a phase = HOLogic.mk_prod (kind, HOLogic.mk_prod (nat a,nat phase))
      fun state_prop q = HOLogic.mk_Trueprop (termination $ q)
      fun number t = snd (HOLogic.dest_number t)
      fun theorem_ok theorem =
        Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
      fun lookup q visited = Termtab.lookup visited q

      val _ = Comma_Fast_Kernel.report ("Concrete safe-return checker: engine ready " ^ report ())
      val seed_theorem = @{thm comma_zero_child_terminates}
      val seed_state = @{term "(Comma_Z,2,10)::comma_boundary_state"}
      val _ = if theorem_ok seed_theorem andalso
          Thm.prop_of seed_theorem aconv state_prop seed_state
        then () else error "The checked zero-child theorem has the wrong root"
      val initial_memo = Termtab.update (seed_state,seed_theorem) Termtab.empty

      fun inspect choice (q,rows,roots,exponent_gain,completed) =
        let
          val edge_number = completed+1
          val checkpoint = edge_number <= 3 orelse edge_number mod 8 = 0
          val detail = edge_number <= 3
          val _ = if checkpoint then
              Comma_Fast_Kernel.report
                ("Safe-return edge start=" ^ Int.toString edge_number ^
                 " " ^ report ())
            else ()
          val row = boundary q
          val _ = if detail then
              Comma_Fast_Kernel.report
                ("Safe-return edge boundary=" ^ Int.toString edge_number ^
                 " " ^ report ())
            else ()
          val {valid,defined,macro,finite_outcome,phase,...} = row
          val (constructor,args) = Term.strip_comb finite_outcome
          val _ = if constructor = @{term Comma_Fork_At} then ()
            else error "Candidate path reaches a landmine before its return"
          val a = number (hd args)
          val d = number (nth args 1)
          val child_phase = (phase+d) mod 924
          val near = state @{term Comma_N} a child_phase
          val zero = state @{term Comma_Z} a child_phase
          val (actual,ordered_meta) = children q macro
          val ordered = ordered_meta RS @{thm meta_eq_to_obj_eq}
          val _ = if detail then
              Comma_Fast_Kernel.report
                ("Safe-return edge children=" ^ Int.toString edge_number ^
                 " " ^ report ())
            else ()
          val _ = if length actual = 2 andalso
              ListPair.allEq (op aconv) (actual,[near,zero])
            then () else error "Candidate fork does not retain both ordered children"
          val selected = if choice = #"0" then near
            else if choice = #"1" then zero
            else error "Candidate path contains a non-binary choice"
          val target_valid = #prove engine
            (HOLogic.mk_Trueprop (@{term comma_boundary_valid} $ selected)) []
          val next_roots = if choice = #"1" then near::roots else roots
          val next_exponent_gain = exponent_gain+d
          val edge = {q=q,target=selected,near=near,zero=zero,choice=choice,
            valid=valid,defined=defined,macro=macro,ordered=ordered,
            target_valid=target_valid,d=d,
            phase=phase,a=a}
          val completed' = completed+1
          val _ = if detail then
              Comma_Fast_Kernel.report
                ("Safe-return edge admission=" ^ Int.toString completed' ^
                 " rejected-N-roots=" ^ Int.toString (length next_roots) ^
                 " " ^ report ())
            else ()
          val _ = if completed' mod 8 = 0 then
              Comma_Fast_Kernel.report
                ("Selected-return progress: edges=" ^ Int.toString completed' ^
                 " rejected-N-roots=" ^ Int.toString (length next_roots) ^
                 " " ^ report ())
            else ()
        in (selected,edge::rows,next_roots,next_exponent_gain,completed') end

      val (last,edges,rejected_roots,exponent_gain,edge_count) =
        fold inspect (String.explode choices) (root,[],[],0,0)
      val (boundary_hits,boundary_misses,round_evaluations) = #boundary_work engine ()
      val _ = if boundary_hits = 314 andalso boundary_misses = 0
          andalso round_evaluations = 0 then ()
        else error "Selected return reconstructed an already checked boundary"
      val _ = Comma_Fast_Kernel.report
        ("Selected-return boundary reuse: " ^ report ())
      val _ = if edge_count = 314 then ()
        else error "The selected return did not inspect every choice edge"
      val _ = if last aconv root andalso length edges = 314 andalso exponent_gain = 924
        then () else error "The selected 314-edge witness has the wrong endpoint or exponent gain"
      val _ = if length rejected_roots = 171 then ()
        else error "The checked choice word does not contain all 171 larger-branch selections"

      val (memo,forks,terminals) = check_roots rejected_roots initial_memo
      val _ = if Termtab.defined memo seed_state then ()
        else error "Shared losing memo lost the initial zero-tail certificate"

      val builder = Comma_Selected_Block_Builder.make arithmetic certify
      fun leaf edge =
        let
          val {q=_,target=_,near=near,zero=_,choice=choice,valid=valid,
            defined=defined,macro=macro,ordered=ordered,target_valid=target_valid,
            d=_,phase=_,a=_} = edge
          val sibling = if choice = #"1" then
              (case lookup near memo of
                SOME theorem => theorem
              | NONE => error "A rejected smaller child lacks a checked theorem")
            else @{thm TrueI}
        in #leaf builder (choice = #"1") valid defined macro ordered
          target_valid sibling end
      val block = #reduce builder (map leaf (rev edges))
      (* Expanding the recorded word is a demand on a completed certificate;
         parent joins never simplify the descendant decision trees. *)
      val theorem = #observe builder block
      val expected_choices = HOLogic.mk_list @{typ bool}
        (map (fn c => if c = #"1" then @{term True} else @{term False})
          (String.explode choices))
      val expected = HOLogic.mk_Trueprop
        (@{term comma_earliest_return_path} $ expected_choices $ nat 314 $
          root $ root $ nat 924)
      val _ = if theorem_ok theorem andalso Thm.prop_of theorem aconv expected
        then () else error "Concrete safe return has the wrong path, count or displacement"
      val _ = Comma_Fast_Kernel.report
        ("Safe branch return: choices=" ^ Int.toString (size choices) ^
         " rejected-N-roots=" ^ Int.toString (length rejected_roots) ^
         " losing-nodes=" ^ Int.toString (Termtab.size memo-1) ^
         " forks=" ^ Int.toString forks ^ " landmines=" ^ Int.toString terminals)
    in (certify block,certify theorem) end
end
