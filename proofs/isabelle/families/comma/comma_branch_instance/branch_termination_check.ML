structure Comma_Branch_Termination_Check =
struct
  fun make ctxt =
    let
      val engine = Comma_Return_Check.make_engine ctxt
      val boundary = #boundary engine
      val arithmetic = #arithmetic engine
      val certify = #certify engine
      val report = #report engine
      val terminates = @{term comma_boundary_terminates}
      fun nat n = HOLogic.mk_number @{typ nat} n
      fun mk_state kind a phase = HOLogic.mk_prod (kind, HOLogic.mk_prod (nat a,nat phase))
      fun state_prop q = HOLogic.mk_Trueprop (terminates $ q)
      fun theorem_ok theorem =
        Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)

      fun children q macro =
        let
          val lhs = @{term comma_total_children} $ q
          val simp = arithmetic |> Simplifier.add_simps [macro]
          val result = Simplifier.rewrite simp
            (Thm.cterm_of ctxt lhs)
          val rhs = Thm.term_of (Thm.rhs_of result)
          val _ = if Thm.term_of (Thm.lhs_of result) aconv lhs andalso
              Thm.nprems_of result = 0 andalso null (Thm.hyps_of result)
            then () else error "Child rewrite is not a closed exact children equation"
          val cs = HOLogic.dest_list rhs
          val _ = if List.all (fn child => fastype_of child = @{typ comma_boundary_state}) cs
            then () else error "Child list contains a foreign state type"
        in (cs, certify result) end

      fun lookup q visited = Termtab.lookup visited q
      val completed_nodes = Unsynchronized.ref 0
      fun visit q (visited,active,forks,terminals) =
        (case lookup q visited of
          SOME theorem =>
            if theorem_ok theorem andalso Thm.prop_of theorem aconv state_prop q
            then (theorem,visited,active,forks,terminals)
            else error "Memoized termination theorem has the wrong state or open assumptions"
        | NONE =>
          if Termtab.defined active q then error "Cycle in finite losing boundary graph"
          else
            let
              val row = boundary q
              val {valid,defined,macro,outcome,phase,...} = row
              val active' = Termtab.update (q,()) active
              val (constructor,_) = Term.strip_comb outcome
              val (proof,seen_after,stack_after,forks',terminals') =
                if constructor = @{term Comma_Round_Landmine} then
                  let
                    val proof = (@{thm comma_boundary_terminates.terminal}
                      OF [valid,defined,macro]) |> certify
                  in (proof,visited,active',forks,terminals+1) end
                else if constructor = @{term Comma_Round_Fork} then
                  let
                    val (cs,_) = children q macro
                    val _ = if length cs = 2 then ()
                      else error "Fork outcome did not retain both ordered children"
                    val args = #2 (Term.strip_comb outcome)
                    val a = snd (HOLogic.dest_number (hd args))
                    val d = snd (HOLogic.dest_number (nth args 1))
                    val child_phase = (phase+d) mod 924
                    val expected_children =
                      [mk_state @{term Comma_N} a child_phase,
                       mk_state @{term Comma_Z} a child_phase]
                    val _ = if ListPair.allEq (op aconv) (cs,expected_children) then ()
                      else error "Macro children disagree with the checked ordered fork"
                    val (child_facts,visited',active'',forks'',terminals'') =
                      fold (fn child => fn (facts,seen,on_stack,fc,tc) =>
                        let val (fact,seen',on_stack',fc',tc') =
                          visit child (seen,on_stack,fc,tc)
                        in (fact::facts,seen',on_stack',fc',tc') end)
                        cs ([],visited,active',forks+1,terminals)
                    val [near,zero] = rev child_facts
                    val _ = if theorem_ok near andalso theorem_ok zero then ()
                      else error "A fork child is not backed by a closed termination theorem"
                    val fork_prefix =
                      (@{thm comma_boundary_terminates_fork}
                        OF [valid,defined,macro])
                      |> Simplifier.full_simplify arithmetic
                    val proof = (fork_prefix OF [near,zero]) |> certify
                    val _ = if theorem_ok proof then ()
                      else error "Branch termination proof has assumptions"
                  in (proof,visited',active'',forks'',terminals'') end
                else error "Boundary macro is neither a fork nor a landmine"
              val _ = if theorem_ok proof then ()
                else error "Termination node proof has assumptions"
              val seen' = Termtab.update (q,proof) seen_after
              val _ = completed_nodes := !completed_nodes + 1
              val completed = !completed_nodes
              val _ = if completed mod 128 = 0 then
                  Comma_Fast_Kernel.report
                    ("Losing-boundary progress: completed=" ^ Int.toString completed ^
                     " forks=" ^ Int.toString forks' ^
                     " landmines=" ^ Int.toString terminals' ^
                     " " ^ report ())
                else ()
            in (proof,seen',Termtab.delete q stack_after,forks',terminals') end)

      fun check_roots roots initial =
        let
          val _ = completed_nodes := Termtab.size initial
          val (visited,forks,terminals) =
            fold (fn q => fn (known,fc,tc) =>
              let
                val (_,known',_,fc',tc') =
                  visit q (known,Termtab.empty,fc,tc)
              in (known',fc',tc') end) roots (initial,0,0)
          val _ = if !completed_nodes = Termtab.size visited then ()
            else error "Completed branch accounting disagrees with the checked memo"
        in (visited,forks,terminals) end
    in {engine=engine, children=children, check_roots=check_roots} end

  fun check ctxt =
    let
      val checker = make ctxt
      val check_roots = #check_roots checker
      val root = @{term "(Comma_Z,2,10)::comma_boundary_state"}
      val terminates = @{term comma_boundary_terminates}
      fun state_prop q = HOLogic.mk_Trueprop (terminates $ q)
      fun theorem_ok theorem =
        Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
      val (visited,forks,terminals) = check_roots [root] Termtab.empty
      val proof =
        (case Termtab.lookup visited root of
          SOME theorem => theorem
        | NONE => error "Local losing root was not included in the visited memo")
      val node_count = Termtab.size visited
      val _ = if node_count = 17 andalso forks = 8 andalso terminals = 9 then ()
        else error ("Unexpected local losing graph size: nodes=" ^ Int.toString node_count ^
          " forks=" ^ Int.toString forks ^ " terminals=" ^ Int.toString terminals)
      val expected = @{prop "comma_boundary_terminates (Comma_Z,2,10)"}
      val _ = if Thm.prop_of proof aconv expected then ()
        else error "The checked local termination theorem has the wrong root"
      val _ = Comma_Fast_Kernel.report
        ("Losing boundary check: nodes=" ^ Int.toString node_count ^
          " forks=" ^ Int.toString forks ^ " landmines=" ^ Int.toString terminals)
    in
      if theorem_ok proof andalso Thm.prop_of proof aconv state_prop root
      then proof else error "The checked local theorem has an unexpected root or assumptions"
    end
end
