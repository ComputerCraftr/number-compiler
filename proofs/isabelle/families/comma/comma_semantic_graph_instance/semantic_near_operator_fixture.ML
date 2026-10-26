(* Bounded native fixture for the unbound Near operator/application split. *)
structure Comma_Semantic_Near_Operator_Fixture =
struct
  type make_arguments =
    {ctxt: Proof.context,
     equation: term -> thm,
     equation_with: thm list -> term -> thm,
     checked_object_proof: term -> thm list -> string -> thm,
     entry_chart_coordinates: term -> (int * int) option,
     number: term -> int,
     nat: int -> term}

  fun run ({ctxt, equation, equation_with, checked_object_proof,
      entry_chart_coordinates, number, nat}: make_arguments) =
    let
      fun is_near term =
        (case strip_comb term of
          (Const (name, _), [_, _, _]) =>
            name = @{const_name Comma_Near}
        | _ => false)
      fun is_literal_near_port expression =
        (case strip_comb expression of
          (Const (name, _), [source, _]) =>
            name = @{const_name comma_semantic_b1_source_port_action} andalso
              is_near source
        | _ => false)
      fun reject_legacy expression =
        if is_literal_near_port expression then
          error "Near operator fixture reached the poisoned literal source-port evaluator"
        else ()
      fun guarded_equation expression =
        (reject_legacy expression; equation expression)
      fun guarded_equation_with extra expression =
        (reject_legacy expression; equation_with extra expression)
      val ports = Comma_Semantic_Source_Ports.make
        {ctxt=ctxt, equation=guarded_equation,
         equation_with=guarded_equation_with,
         checked_object_proof=checked_object_proof,
         entry_chart_coordinates=entry_chart_coordinates,
         number=number, nat=nat}
      val near82 = @{term "Comma_Near 1 0 82"}
      val near92 = @{term "Comma_Near 1 0 92"}
      val near9 = @{term "Comma_Near 1 0 9"}
      val near10 = @{term "Comma_Near 1 0 10"}
      val class82 = #classify ports near82
      val class92 = #classify ports near92
      val class9 = #classify ports near9
      val class10 = #classify ports near10
      val shape82 = #shape class82
      val shape92 = #shape class92
      val _ = (#validate_selection ports class82;
        #validate_selection ports class92;
        #validate_selection ports class9;
        #validate_selection ports class10)
      val work_after_classify = #work ports ()
      val _ = if Term.aconv (#key shape82, #key shape92) andalso
          not (Term.aconv (#application_key class82, #application_key class92)) andalso
          not (Term.aconv (#action_key class82, #action_key class92)) andalso
          Term.aconv (#action_key class9, #action_key class10) andalso
          Option.map number (#selected_steps class9) = SOME 0 andalso
          Option.map number (#selected_steps class10) = SOME 1 andalso
          Option.map (fn action => action) (#selected_action class9) =
            #selected_action class10 andalso
          #near_operator_builds work_after_classify = 1 andalso
          #near_operator_reuses work_after_classify = 3 then ()
        else error "Near fixture conflated action selection, steps, or occurrence keys"

      val invalidated_selection =
        {shape= #shape class9, source=near9,
         application_key= #application_key class9,
         action_key= #action_key class9,
         selected_action= #selected_action class92,
         selected_steps= #selected_steps class9,
         selection_equation= #selection_equation class9,
         selection_id= #selection_id class9,
         membership= #membership class9,
         operator_refinement= #operator_refinement class9,
         header= #header class9}
      val _ = (case Exn.capture
          (fn () => #validate_selection ports invalidated_selection) () of
        Exn.Exn (ERROR "Near action-class key lacks its exact checked source selector") => ()
      | _ => error "Near action selector accepted a mismatched cached-key payload")

      val transition82 = #transition ports class82 0
      val transition92 = #transition ports class92 0
      fun physical_steps (transition:
          Comma_Semantic_Source_Ports.source_transition) =
        (case #physical_steps transition of
          SOME term =>
            (case HOLogic.dest_number term of
              (T, n) => if T = @{typ nat} andalso n >= 0 then n
                else error "Near fixture found a non-natural physical-step result")
        | NONE => error "Near fixture lost its completed physical-step payload")
      fun pair_application (transition:
          Comma_Semantic_Source_Ports.source_transition) source steps =
        (case #application_exact transition of
          SOME theorem =>
            let
              val proposition = Thm.prop_of theorem
              val (left, right) = HOLogic.dest_eq (HOLogic.dest_Trueprop proposition)
              val (source_action, _) = HOLogic.dest_prod left
              val (result_action, result_steps) = HOLogic.dest_prod right
              val exact_prop = Thm.prop_of (#exact transition)
              val (exact_left, exact_right) =
                HOLogic.dest_eq (HOLogic.dest_Trueprop exact_prop)
              val expected_port = @{term comma_semantic_b1_source_port_action} $
                source $ nat 0
              val expected_exact = HOLogic.mk_Trueprop (HOLogic.mk_eq
                (expected_port, #action transition))
              val (T, n) = HOLogic.dest_number result_steps
              val _ = if Thm.nprems_of theorem = 0 andalso
                  null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
                  not (Term.is_open proposition) andalso
                  null (Term.add_frees proposition []) andalso
                  null (Term.add_vars proposition []) andalso
                  null (Thm_Deps.all_oracles [theorem]) andalso
                  Term.aconv (source_action, expected_port) andalso
                  Term.aconv (result_action, #action transition) andalso
                  Thm.nprems_of (#exact transition) = 0 andalso
                  null (Thm.hyps_of (#exact transition)) andalso
                  null (Thm.tpairs_of (#exact transition)) andalso
                  Thm.prop_of (#exact transition) aconv expected_exact andalso
                  Term.aconv (exact_left, expected_port) andalso
                  Term.aconv (exact_right, #action transition) andalso
                  T = @{typ nat} andalso n = steps then ()
                else error "Near fixture application theorem lost exact action/step binding"
            in theorem end
        | NONE => error "Near fixture lacks its exact operator-pair application theorem")
      val steps82 = physical_steps transition82
      val steps92 = physical_steps transition92
      val pair82 = pair_application transition82 near82 steps82
      val pair92 = pair_application transition92 near92 steps92
      val work_after_transitions = #work ports ()
      val _ = if steps82 = 0 andalso steps92 = 1 andalso
          not (Term.aconv (#action transition82, #action transition92)) andalso
          #transition_evaluations work_after_transitions = 2 andalso
          #near_application_transports work_after_transitions = 2 then ()
        else error "Near H=82/H=92 actions or physical-step payloads were conflated"

      val repeated82 = #transition ports class82 0
      val repeated92 = #transition ports class92 0
      val work_after_repeat = #work ports ()
      fun application (theorem_transition:
          Comma_Semantic_Source_Ports.source_transition) =
        (case #application_exact theorem_transition of
          SOME theorem => theorem
        | NONE => error "Near repeated application lost its exact pair theorem")
      val _ = if #transition_evaluations work_after_repeat =
            #transition_evaluations work_after_transitions andalso
          #near_application_transports work_after_repeat =
            #near_application_transports work_after_transitions andalso
          Thm.prop_of (application repeated82) aconv Thm.prop_of pair82 andalso
          Thm.prop_of (application repeated92) aconv Thm.prop_of pair92 then ()
        else error "Near exact-application transition cache repeated its work"

      fun expect_rejection label expected_message thunk =
        (case Exn.capture thunk () of
          Exn.Res _ => error ("Near fixture accepted " ^ label)
        | Exn.Exn (ERROR actual) =>
            if actual = expected_message then ()
            else Exn.reraise (ERROR
              ("Near fixture expected error `" ^ expected_message ^
                "` but received `" ^ actual ^ "`"))
        | Exn.Exn exn => Exn.reraise exn)
      val work_before_bad_sector = #work ports ()
      val _ = expect_rejection "an out-of-alphabet sector"
        "Semantic source class producer received an unadmitted source"
        (fn () => ignore (#classify ports (@{term "Comma_Near 0 0 82"})))
      val work_after_bad_sector = #work ports ()
      val _ = if #near_operator_builds work_after_bad_sector =
            #near_operator_builds work_before_bad_sector then ()
        else error "Rejected Near sector allocated an operator-catalog entry"

      val forged: Comma_Semantic_Source_Ports.source_class =
        {shape=shape82, source=near92, application_key= #application_key class82,
         action_key= #action_key class82,
         selected_action= #selected_action class82,
         selected_steps= #selected_steps class82,
         selection_equation= #selection_equation class82,
         selection_id= #selection_id class82,
         membership= #membership class82,
         operator_refinement= #operator_refinement class82,
         header= #header class82}
      val work_before_bad_requests = #work ports ()
      val _ = expect_rejection "a source paired with another H application's selector"
        "Near action-class key lacks its exact checked source selector"
        (fn () => ignore (#transition ports forged 0))
      val _ = expect_rejection "a slot outside the unit Near period"
        "Semantic source transition phase is outside its class clock"
        (fn () => ignore (#transition ports class82 1))
      val work_after_bad_requests = #work ports ()
      val _ = if #transition_evaluations work_after_bad_requests =
            #transition_evaluations work_before_bad_requests then ()
        else error "Rejected Near application or slot allocated a transition"

      (* A closed, exact equation is not enough for the stored physical-step
         payload: require the production boundary to reject a result which is
         propositionally equal to the numeral but not yet in numeral form. *)
      val bad_operator_request =
        @{term comma_near_symbolic_port_operator} $ nat 1 $ nat 82 $ nat 0
      fun noncanonical_equation_with extra expression =
        let
          val delegated = equation_with extra expression
        in
          if not (Term.aconv (expression, bad_operator_request)) then delegated
          else
            let
              val (action, steps) = HOLogic.dest_prod
                (Thm.term_of (Thm.rhs_of delegated))
              val canonical_pair = HOLogic.mk_prod (action, steps)
              val noncanonical_steps =
                HOLogic.mk_binop @{const_name plus} (steps, nat 0)
              val noncanonical_pair = HOLogic.mk_prod (action, noncanonical_steps)
              val rewrite_context = put_simpset HOL_basic_ss ctxt
                addsimps [@{thm add_0_right}]
              val step_rewrite = Simplifier.rewrite rewrite_context
                (Thm.cterm_of ctxt noncanonical_pair)
              val _ = if Thm.term_of (Thm.lhs_of step_rewrite) aconv
                    noncanonical_pair andalso
                    Thm.term_of (Thm.rhs_of step_rewrite) aconv canonical_pair
                then () else error
                  "Near fixture could not build its noncanonical numeral equation"
            in Thm.transitive delegated (Thm.symmetric step_rewrite) end
        end
      val noncanonical_ports = Comma_Semantic_Source_Ports.make
        {ctxt=ctxt, equation=equation,
         equation_with=noncanonical_equation_with,
         checked_object_proof=checked_object_proof,
         entry_chart_coordinates=entry_chart_coordinates,
         number=number, nat=nat}
      val noncanonical_source = @{term "Comma_Near 1 0 82"}
      val before_noncanonical_transition = #work noncanonical_ports ()
      val _ = expect_rejection "a closed but non-numeral selected physical-step result"
        "Near action selector returned an incomplete physical-step count"
        (fn () => ignore (#classify noncanonical_ports noncanonical_source))
      val after_noncanonical_transition = #work noncanonical_ports ()
      val _ = if #transition_evaluations after_noncanonical_transition =
            #transition_evaluations before_noncanonical_transition andalso
          #near_application_transports after_noncanonical_transition =
            #near_application_transports before_noncanonical_transition
        then ()
        else error "Rejected Near selection mutated transition authority"

      (* The deliberately malformed owner's private cache must not poison a
         fresh owner using the canonical numeral-producing equation path. *)
      val retry_ports = Comma_Semantic_Source_Ports.make
        {ctxt=ctxt, equation=equation, equation_with=equation_with,
         checked_object_proof=checked_object_proof,
         entry_chart_coordinates=entry_chart_coordinates,
         number=number, nat=nat}
      val retry_class = #classify retry_ports noncanonical_source
      val retry_transition = #transition retry_ports retry_class 0
      val retry_work = #work retry_ports ()
      val _ = if physical_steps retry_transition = 0 andalso
          #transition_evaluations retry_work = 1 andalso
          #near_application_transports retry_work = 1 then ()
        else error "Near numeral validation rejected the independent canonical retry"
    in () end
end
