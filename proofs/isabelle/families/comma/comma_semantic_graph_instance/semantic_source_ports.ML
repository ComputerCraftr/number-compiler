(* Source classes and guarded scalar transitions. Entry classes use their
   proved finite-period/core coordinate. A Near shape identifies the reusable
   sector operator; a separate exact one-step action key identifies the
   selected ordered continuation, while the H-bearing source/application and
   physical steps remain occurrence data. These local action keys are not
   claims of Moore-minimal future equivalence. *)
structure Comma_Semantic_Source_Ports =
struct
  datatype source_kind = EntryClass | NearClass

  type source_header =
    {period: int, base: thm, period_equation: thm, admitted: thm}
  type source_class_shape =
    {key: term, representative: term, period: int, kind: source_kind}
  type source_class =
    {shape: source_class_shape, source: term, application_key: term,
     action_key: term, selected_action: term option, selected_steps: term option,
     selection_equation: thm option, selection_id: thm option,
     membership: thm option, operator_refinement: thm option,
     header: source_header}
  type source_transition =
    {action: term, exact: thm,
     application_exact: thm option, physical_steps: term option}
  type class_row =
    {class_source: source_class, transitions: source_transition list,
     application_key: term, action_key: term, actions: term list, cid: int}
  type source_forward =
    {child: term, completed: thm, action: thm, direct: thm,
     header: source_header}
  type api =
    {classify: term -> source_class,
     validate_selection: source_class -> unit,
     transition: source_class -> int -> source_transition,
     forward: term -> source_forward option,
     stats: unit -> string,
     work: unit -> {transition_evaluations: int,
       near_operator_builds: int, near_operator_reuses: int,
       near_residual_builds: int, near_residual_hits: int,
       near_application_transports: int}}

  fun make {ctxt, equation, equation_with, checked_object_proof,
      entry_chart_coordinates, number, nat} : api =
    let
      val headers = Unsynchronized.ref (Termtab.empty: source_header Termtab.table)
      val classes = Unsynchronized.ref
        (Termtab.empty: source_class_shape Termtab.table)
      val transitions = Unsynchronized.ref
        (Termtab.empty: source_transition Termtab.table)
      type near_operator = {source_rule: thm, sector: int}
      type near_selection =
        {key: term, action: term, steps: term, equation: thm}
      val near_operators = Unsynchronized.ref
        (Termtab.empty: near_operator Termtab.table)
      val near_residuals = Unsynchronized.ref
        (Termtab.empty: near_selection Termtab.table)
      val class_attempts = Unsynchronized.ref 0
      val class_hits = Unsynchronized.ref 0
      val class_failures = Unsynchronized.ref 0
      val transition_attempts = Unsynchronized.ref 0
      val transition_hits = Unsynchronized.ref 0
      val transition_failures = Unsynchronized.ref 0
      val near_operator_reuses = Unsynchronized.ref 0
      val near_operator_builds = Unsynchronized.ref 0
      val near_residual_builds = Unsynchronized.ref 0
      val near_residual_hits = Unsynchronized.ref 0
      val near_application_transports = Unsynchronized.ref 0
      val class_relation_rules = @{thms comma_guarded_source_class_rel_def
        comma_finite_position.inject comma_finite_position.distinct}

      fun header source =
        (case Termtab.lookup (!headers) source of
          SOME result => result
        | NONE =>
            let
              val base = @{term comma_source_continuation_base} $ source
              val base_theorem = equation base
              val base_value = Thm.term_of (Thm.rhs_of base_theorem)
              val period_request = @{term comma_decisive_sector_period} $ base_value
              val period_theorem = equation period_request
              val period = number (Thm.term_of (Thm.rhs_of period_theorem))
              val _ = if period > 0 andalso 924 mod period = 0 then ()
                else error "Semantic source period is not admitted"
              val admitted_request = @{term comma_round_admitted} $ source
              val admitted_theorem = equation admitted_request
              val admitted_value = Thm.term_of (Thm.rhs_of admitted_theorem)
              val _ = if admitted_value aconv @{term True} then ()
                else error "Semantic source class producer received an unadmitted source"
              val result : source_header =
                {period=period, base=base_theorem,
                 period_equation=period_theorem, admitted=admitted_theorem}
              val _ = headers := Termtab.update (source, result) (!headers)
            in result end)

      fun near_chart_coordinates source =
        (case strip_comb source of
          (Const (name, _), [f, delta, headroom]) =>
            if name = @{const_name Comma_Near} andalso number delta = 0
            then SOME (number f, headroom) else NONE
        | _ => NONE)

      fun key tag sector digit residue finite_period core core_period =
        HOLogic.mk_prod (nat tag,
          HOLogic.mk_prod (nat sector,
            HOLogic.mk_prod (nat digit,
              HOLogic.mk_prod (nat residue,
                HOLogic.mk_prod (nat finite_period,
                  HOLogic.mk_prod (nat core, nat core_period))))))

      fun near_operator_key sector =
        @{term comma_near_symbolic_port_operator} $ nat sector

      (* Select the checked symbolic Near control action before building the
         source-specific port theorem.  The action is the exact ordered
         continuation (including its exact Goto target); the physical step
         count remains occurrence payload.  This is a structural action key,
         not a Moore-minimal future equivalence. *)
      fun direct_near_action_selection sector headroom : near_selection =
        let
          val operator = near_operator_key sector
          val request = operator $ nat headroom $ nat 0
          val definitions = @{thms comma_near_symbolic_port_operator_eval
            comma_near_closed_germ_def comma_near_residual_count_eval
            comma_semantic_b1_near_control_port_action_def
            comma_near_control_formula Let_def}
          val theorem = equation_with definitions request
          val (action, steps) = HOLogic.dest_prod (Thm.term_of (Thm.rhs_of theorem))
          val _ = if is_some (try number steps) then ()
            else error "Near action selector returned an incomplete physical-step count"
          val action_type = @{typ comma_source_continuation_action}
          val key = HOLogic.mk_prod (nat 1,
            HOLogic.mk_list action_type [action])
        in {key=key, action=action, steps=steps, equation=theorem} end

      fun near_action_selection sector headroom : near_selection =
        if headroom <= (if sector < 9 then 1 else 0) then
          direct_near_action_selection sector headroom
        else
          let
            val packet = @{term comma_near_residual_binding} $
              nat sector $ nat headroom
            val packet_equation = equation_with
              @{thms comma_near_residual_binding_def Let_def} packet
            val _ = if Thm.term_of (Thm.lhs_of packet_equation) aconv packet then ()
              else error "Near residual packet was issued for another source"
            val (port,occurrence) =
              HOLogic.dest_prod (Thm.term_of (Thm.rhs_of packet_equation))
            val (elapsed,reduced) = HOLogic.dest_prod occurrence
            val residual_key = HOLogic.mk_prod (nat sector,port)
            val selected = (case Termtab.lookup (!near_residuals) residual_key of
                SOME existing =>
                  (near_residual_hits := !near_residual_hits + 1; existing)
              | NONE =>
                  let
                    val representative_source = @{term Comma_Near} $
                      nat sector $ nat 0 $ reduced
                    val _ = header representative_source
                    val representative =
                      direct_near_action_selection sector (number reduced)
                    val _ = near_residuals :=
                      Termtab.update (residual_key,representative) (!near_residuals)
                    val _ = near_residual_builds := !near_residual_builds + 1
                  in representative end)
          in if headroom = number reduced then selected else
            let
              val added = equation
                (@{term "(+) :: nat => nat => nat"} $ elapsed $ #steps selected)
              val steps = Thm.term_of (Thm.rhs_of added)
              val request = near_operator_key sector $ nat headroom $ nat 0
              val proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq
                (request,HOLogic.mk_prod (#action selected,steps)))
              val transport = Drule.infer_instantiate ctxt
                [(("f",0),Thm.cterm_of ctxt (nat sector)),
                 (("H",0),Thm.cterm_of ctxt (nat headroom)),
                 (("slot",0),Thm.cterm_of ctxt (nat 0))]
                @{thm comma_near_symbolic_port_operator_residual}
              val exact = Simplifier.full_simplify
                (Comma_Entry_Arithmetic.natural_context ctxt
                  |> Simplifier.add_simps
                    [packet_equation, #equation selected, added, @{thm Let_def}])
                transport
              val _ = if Thm.nprems_of exact = 0 andalso
                  null (Thm.hyps_of exact) andalso null (Thm.tpairs_of exact) andalso
                  Thm.prop_of exact aconv proposition andalso
                  null (Thm_Deps.all_oracles [exact]) then ()
                else error ("Near residual transport lost its exact action/physical cocycle: " ^
                  Thm.string_of_thm ctxt exact)
              val theorem = exact RS @{thm eq_reflection}
            in {key= #key selected, action= #action selected,
              steps=steps, equation=theorem}:near_selection end
          end

      fun near_operator sector =
        let
          val operator_key = near_operator_key sector
        in
          (case Termtab.lookup (!near_operators) operator_key of
            SOME issued =>
              if #sector issued = sector then
                (near_operator_reuses := !near_operator_reuses + 1; issued)
              else error "Near operator key was reused across sectors"
          | NONE =>
              let
                val result : near_operator =
                  {source_rule= @{thm comma_near_symbolic_port_operator_source},
                   sector=sector}
                val _ = near_operator_builds := !near_operator_builds + 1
                val _ = near_operators :=
                  Termtab.update (operator_key, result) (!near_operators)
              in result end)
        end

      fun canonical_offset sector digit period residue =
        (case find_first
            (fn candidate => candidate mod 10 = digit andalso
              candidate mod period = residue) (0 upto 98) of
          SOME candidate => candidate
        | NONE => error "Admitted Entry has no canonical finite-period representative")

      fun entry_shape source sector offset =
        let
          val digit = offset mod 10
          val period_request = @{term comma_finite_period_fast} $
            nat sector $ nat digit
          val finite_period_theorem = equation period_request
          val finite_period = number (Thm.term_of (Thm.rhs_of finite_period_theorem))
          val _ = if finite_period > 0 then ()
            else error "Admitted Entry has a zero finite carry period"
          val core_request = @{term comma_core_modulus} $ nat finite_period
          val core_theorem = equation core_request
          val core = number (Thm.term_of (Thm.rhs_of core_theorem))
          val clock_period_request = @{term comma_core_period} $ nat core
          val clock_period_theorem = equation clock_period_request
          val clock_period = number
            (Thm.term_of (Thm.rhs_of clock_period_theorem))
          val source_header as {period, ...} = header source
          val _ = if period = clock_period andalso 924 mod clock_period = 0 then ()
            else error "Entry core period does not match its admitted 924 selector"
          val residue = offset mod finite_period
          val representative_offset =
            canonical_offset sector digit finite_period residue
          val representative = @{term Comma_Entry} $
            nat sector $ nat 0 $ nat representative_offset
          val class_key = key 0 sector digit residue finite_period core clock_period
          val result : source_class_shape =
            {key=class_key, representative=representative,
             period=clock_period, kind=EntryClass}
          val _ = source_header
          val _ = finite_period_theorem
          val _ = core_theorem
          val _ = clock_period_theorem
        in result end

      fun near_shape sector headroom_value =
        let
          (* Reject malformed source parameters before they can allocate an
             operator-catalog entry.  Admission still validates the exact
             H-bearing source after this reusable f descriptor is issued. *)
          val _ = if 1 <= sector andalso sector <= 9 then ()
            else error "Near operator sector is outside the finite alphabet"
          (* Build a genuinely unbound family descriptor: no concrete H is
             evaluated or retained while the generic operator is interned. *)
          val operator_key = near_operator_key sector
          val operator = near_operator sector
          val free_headroom = Free ("near_application_headroom", @{typ nat})
          val near_source = @{term Comma_Near} $ nat sector $ nat 0 $ free_headroom
          val family = Term.lambda free_headroom near_source
          val result : source_class_shape =
            {key=operator_key, representative=family, period=1,
             kind=NearClass}
          val selected = near_action_selection sector (number headroom_value)
        in (result, #source_rule operator, selected) end

      (* Bind the preselected control action back to this exact Near source,
         then prove that its typed one-slot identifier is the complete
         source continuation identifier.  The step count is deliberately
         absent from the action key and remains occurrence data. *)
      fun selection_id (source: term) (source_header: source_header)
          (selection: near_selection) =
        let
          val (sector,headroom) =
            (case near_chart_coordinates source of
              SOME coordinates => coordinates
            | NONE => error "Near selector lost its exact source occurrence")
          val request = near_operator_key sector $ headroom $ nat 0
          val selected = #equation selection
          val _ = if Thm.term_of (Thm.lhs_of selected) aconv request andalso
              Thm.term_of (Thm.rhs_of selected) aconv
                HOLogic.mk_prod (#action selection,#steps selection) then ()
            else error "Near selector lost its exact source/action/step binding"
          val admitted = @{thm eqTrueE} OF
            [#admitted source_header RS @{thm meta_eq_to_obj_eq}]
          val source_id = Drule.infer_instantiate ctxt
            [(("f",0),Thm.cterm_of ctxt (nat sector)),
             (("H",0),Thm.cterm_of ctxt headroom)]
            @{thm comma_near_symbolic_port_source_id} OF [admitted]
          val result = Simplifier.full_simplify
            (put_simpset HOL_basic_ss ctxt
              |> Simplifier.add_simps [selected,@{thm fst_conv}]) source_id
          val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (@{term comma_source_continuation_id} $ source,#key selection))
          val _ = if Thm.nprems_of result = 0 andalso
              null (Thm.hyps_of result) andalso null (Thm.tpairs_of result) andalso
              Thm.prop_of result aconv expected andalso
              null (Thm_Deps.all_oracles [result]) then ()
            else error "Near selector did not transport its generic source-ID theorem"
        in result end

      fun membership source shape source_header =
        (case #kind shape of
          EntryClass =>
            let
              val representative = #representative shape
              val rep_header = header representative
              val proposition = HOLogic.mk_Trueprop
                (@{term comma_guarded_source_class_rel} $ source $ representative)
              val (sector, offset) = the (entry_chart_coordinates source)
              val (_, representative_offset) =
                the (entry_chart_coordinates representative)
              val digit_equal = equation (HOLogic.mk_eq
                (nat (offset mod 10), nat (representative_offset mod 10)))
              val period_value =
                let
                  val t = @{term comma_finite_period_fast} $
                    nat sector $ nat (offset mod 10)
                in number (Thm.term_of (Thm.rhs_of (equation t))) end
              val residue_equal = equation (HOLogic.mk_eq
                (nat (offset mod period_value),
                 nat (representative_offset mod period_value)))
              val period_equation = equation
                (@{term comma_finite_period_fast} $ nat sector $
                  nat (offset mod 10))
            in
              SOME (checked_object_proof proposition
                  (class_relation_rules @
                    [#admitted source_header, #admitted rep_header,
                     digit_equal, residue_equal, period_equation])
                  "Entry source failed the guarded finite-period class transport")
            end
        | NearClass => NONE)

      fun same_shape (left: source_class_shape, right: source_class_shape) =
        Term.aconv (#key left, #key right) andalso
          Term.aconv (#representative left, #representative right) andalso
          #period left = #period right andalso #kind left = #kind right

      fun classify source =
        let
          val _ = class_attempts := !class_attempts + 1
          fun build () =
            let
              val (proposed, operator_refinement, selected, source_header) =
                (case entry_chart_coordinates source of
                  SOME (sector, offset) =>
                    let val source_header = header source
                    in (entry_shape source sector offset, NONE, NONE, source_header) end
                | NONE => (case near_chart_coordinates source of
                    SOME (sector, headroom) =>
                      let
                        val source_header = header source
                        val _ = if #period source_header = 1 then ()
                          else error "Near source must have the checked unit selector period"
                        val (shape, operator_rule, selection) =
                          near_shape sector headroom
                      in (shape, SOME operator_rule, SOME selection, source_header) end
                  | NONE => error
                      "Semantic source class requires a normalized Entry or Near"))
              val found = Termtab.lookup (!classes) (#key proposed)
              val (shape, is_new) =
                (case found of
                  SOME existing =>
                    (class_hits := !class_hits + 1; (existing, false))
                | NONE => (proposed, true))
              val _ = if same_shape (shape, proposed) then ()
                else error "Semantic class key collision crossed state-space authority"
              val cert = membership source shape source_header
              val application_key =
                (case #kind shape of
                  EntryClass => #key shape
                | NearClass => HOLogic.mk_prod (#key shape, source))
              val action_key =
                (case selected of
                  SOME selection => #key selection
                | NONE => #key shape)
              val action_id = Option.map
                (selection_id source source_header) selected
              (* Entry representatives require the guarded membership proof.
                 A Near descriptor is only the already-issued generic f
                 operator; its H-bearing source remains outside this cache. *)
              val _ = if is_new then
                  classes := Termtab.update (#key proposed, proposed) (!classes)
                else ()
            in {shape=shape, source=source, application_key=application_key,
              action_key=action_key,
              selected_action=Option.map #action selected,
              selected_steps=Option.map #steps selected,
              selection_equation=Option.map #equation selected,
              selection_id=action_id,
              membership=cert, operator_refinement=operator_refinement,
              header=source_header} end
          val attempt = Exn.capture build ()
          val _ = if Exn.is_exn attempt then
              class_failures := !class_failures + 1 else ()
        in Exn.release attempt end

      fun validate_selection (source_class: source_class) =
        let
          val shape = #shape source_class
          val _ = (case #kind shape of
            EntryClass =>
              if #action_key source_class aconv #key shape andalso
                 is_none (#selected_action source_class) andalso
                 is_none (#selected_steps source_class) andalso
                 is_none (#selection_equation source_class) andalso
                 is_none (#selection_id source_class)
              then () else error "Entry class carried a forged Near selector payload"
          | NearClass =>
              let
                val source = #source source_class
                val (sector, headroom) =
                  (case near_chart_coordinates source of
                    SOME coordinates => coordinates
                  | NONE => error "Near selector authority lost its source binding")
                val action = the (#selected_action source_class)
                val steps = the (#selected_steps source_class)
                val equation = the (#selection_equation source_class)
                val id = the (#selection_id source_class)
                val request = near_operator_key sector $ headroom $ nat 0
                val expected_key = HOLogic.mk_prod (nat 1,
                  HOLogic.mk_list @{typ comma_source_continuation_action} [action])
                val equation_prop = Thm.prop_of equation
                val equation_lhs = Thm.term_of (Thm.lhs_of equation)
                val equation_rhs = Thm.term_of (Thm.rhs_of equation)
                val expected_id = HOLogic.mk_Trueprop (HOLogic.mk_eq
                  (@{term comma_source_continuation_id} $ source,
                   #action_key source_class))
                val _ = if equation_lhs aconv request andalso
                    equation_rhs aconv HOLogic.mk_prod (action, steps) andalso
                    #action_key source_class aconv expected_key andalso
                    is_some (try number steps) andalso
                    Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation) andalso
                    null (Thm.tpairs_of equation) andalso
                    not (Term.is_open equation_prop) andalso
                    null (Term.add_frees equation_prop []) andalso
                    null (Term.add_vars equation_prop []) andalso
                    null (Thm_Deps.all_oracles [equation]) andalso
                    Thm.nprems_of id = 0 andalso null (Thm.hyps_of id) andalso
                    null (Thm.tpairs_of id) andalso Thm.prop_of id aconv expected_id andalso
                    null (Thm_Deps.all_oracles [id]) then ()
                  else error "Near action-class key lacks its exact checked source selector"
              in () end)
        in () end

      fun transition (source_class: source_class) slot =
        let
          val _ = validate_selection source_class
          val shape = #shape source_class
          val source = #source source_class
          val _ = (case Termtab.lookup (!classes) (#key shape) of
              SOME issued => if same_shape (issued, shape) then ()
                else error "Source transition received a forged or stale operator shape"
            | NONE => error "Source transition received an unissued operator shape")
          val near_binding =
            (case #kind shape of
              EntryClass =>
                (if #application_key source_class aconv #key shape andalso
                    source aconv #representative shape then ()
                  else error "Entry transition was not requested from its canonical class representative";
                 NONE)
            | NearClass =>
                let
                  val (sector, headroom_term) =
                    (case near_chart_coordinates source of
                      SOME coordinates => coordinates
                    | NONE => error "Near transition lost its exact source binding")
                  val headroom = number headroom_term
                  val application_key = HOLogic.mk_prod (#key shape, source)
                  val _ = if application_key aconv #application_key source_class then ()
                    else error "Near transition application key lost its source headroom"
                  val source_header = header source
                  val _ = if #period source_header = 1 then ()
                    else error "Near application is outside its unit selector period"
                  val operator = near_operator_key sector
                  val _ = if operator aconv #key shape then ()
                    else error "Near application shape changed its operator family"
                  val operator_record =
                    (case Termtab.lookup (!near_operators) (#key shape) of
                      SOME value => value
                    | NONE => error "Near source operator was not issued")
                  val source_rule =
                    (case #operator_refinement source_class of
                      SOME theorem => theorem
                    | NONE => error "Near application lacks generic operator authority")
                  val _ = if #sector operator_record = sector andalso
                      Thm.eq_thm (#source_rule operator_record, source_rule)
                    then () else error "Near application uses a foreign operator authority"
                in SOME (sector, headroom, operator, source_header, source_rule) end)
          val transition_key = HOLogic.mk_prod
            ((case #kind shape of
                EntryClass => #key shape
              | NearClass => #application_key source_class), nat slot)
          fun build () =
            if slot < 0 orelse slot >= #period shape then
              error "Semantic source transition phase is outside its class clock"
            else
              (case Termtab.lookup (!transitions) transition_key of
                SOME result => (transition_hits := !transition_hits + 1; result)
              | NONE =>
                  let
                    val _ = transition_attempts := !transition_attempts + 1
                    val (action, exact, application_exact, physical_steps) =
                      (case #kind shape of
                        EntryClass =>
                          let
                            val (sector, offset) =
                              (case entry_chart_coordinates (#representative shape) of
                                SOME coordinates => coordinates
                              | NONE => error "Entry operator representative lost its chart")
                            val expression =
                              @{term comma_c1_b1_entry_core_port_action} $
                                nat sector $ nat offset $ nat slot
                            val equation_theorem = equation expression
                            val action = Thm.term_of (Thm.rhs_of equation_theorem)
                            val representative_header = header (#representative shape)
                            val exact_proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq
                              (@{term comma_semantic_b1_source_port_action} $
                                (#representative shape) $ nat slot, action))
                            val exact = checked_object_proof exact_proposition
                              [equation_theorem, #admitted representative_header,
                               #period_equation representative_header,
                               (@{thm comma_c1_b1_entry_core_port_action_source_exact}
                                 RS @{thm sym})]
                              "Entry transition did not refine its source port"
                          in (action, exact, NONE, NONE) end
                      | NearClass =>
                          let
                            val (sector, headroom, operator, source_header, source_rule) =
                              (case near_binding of
                                SOME data => data
                              | NONE => error "Near source lost its application binding")
                            val operator_request = operator $ nat headroom $ nat slot
                            val specialized_rule = Drule.infer_instantiate ctxt
                              [(("f", 0), Thm.cterm_of ctxt (nat sector)),
                               (("H", 0), Thm.cterm_of ctxt (nat headroom)),
                               (("slot", 0), Thm.cterm_of ctxt (nat slot))]
                              source_rule
                            val (rule_lhs, rule_rhs) = HOLogic.dest_eq
                              (HOLogic.dest_Trueprop (Thm.prop_of specialized_rule))
                            val (source_port_action, _) =
                              HOLogic.dest_prod rule_rhs
                            val expected_port_action =
                              @{term comma_semantic_b1_source_port_action} $
                                source $ nat slot
                            val _ = if rule_lhs aconv operator_request andalso
                                source_port_action aconv expected_port_action then ()
                              else error "Near operator theorem does not bind the exact source port"
                            (* The pre-cert selector has already reduced the
                               closed event/control result.  Reuse that exact
                               equation rather than normalizing the operator a
                               second time while constructing its source proof. *)
                            val operator_equation =
                              (case #selection_equation source_class of
                                SOME theorem => theorem
                              | NONE => error "Near application lost its selected action equation")
                            val _ = if Thm.term_of (Thm.lhs_of operator_equation)
                                aconv operator_request then ()
                              else error "Selected Near action belongs to another phase or source"
                            val (action, physical_steps) = HOLogic.dest_prod
                              (Thm.term_of (Thm.rhs_of operator_equation))
                            val _ = if is_some (try number physical_steps) then ()
                              else error "Near operator returned an incomplete physical-step count"
                            val exact_proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq
                              (expected_port_action, action))
                            val specialized_meta =
                              specialized_rule RS @{thm eq_reflection}
                            (* Simplifier.full_rewrite returns a meta equality. *)
                            val operator_meta = operator_equation
                            val pair_equality_meta =
                              Thm.transitive (Thm.symmetric specialized_meta) operator_meta
                            val pair_equality = pair_equality_meta
                              RS @{thm meta_eq_to_obj_eq}
                            val actionT = fastype_of source_port_action
                            val pairT = fastype_of rule_rhs
                            val first = Const (@{const_name fst}, pairT --> actionT)
                            val projection_rule = Drule.infer_instantiate ctxt
                              [(("f", 0), Thm.cterm_of ctxt first)]
                              @{thm arg_cong}
                            val projected_object = projection_rule OF [pair_equality]
                            val projected_meta = projected_object RS @{thm eq_reflection}
                            val basic_context = Simplifier.add_simps ([@{thm fst_conv}]) (put_simpset HOL_basic_ss ctxt)
                            val source_first = Simplifier.rewrite basic_context
                              (Thm.cterm_of ctxt (first $ rule_rhs))
                            val result_first = Simplifier.rewrite basic_context
                              (Thm.cterm_of ctxt
                                (first $ Thm.term_of (Thm.rhs_of operator_equation)))
                            val action_exact_meta = Thm.transitive
                              (Thm.symmetric source_first)
                              (Thm.transitive projected_meta result_first)
                            val action_exact = action_exact_meta
                              RS @{thm meta_eq_to_obj_eq}
                            val _ = if Thm.nprems_of action_exact = 0 andalso
                                null (Thm.hyps_of action_exact) andalso
                                null (Thm.tpairs_of action_exact) andalso
                                not (Term.is_open (Thm.prop_of action_exact)) andalso
                                null (Term.add_frees (Thm.prop_of action_exact) []) andalso
                                null (Term.add_vars (Thm.prop_of action_exact) []) andalso
                                Thm.prop_of action_exact aconv exact_proposition then ()
                              else error
                                "Near operator specialization lost its exact source row"
                            val _ = near_application_transports :=
                              !near_application_transports + 1
                          in (action, action_exact, SOME pair_equality,
                              SOME physical_steps) end
                      )
                    val result : source_transition =
                      {action=action, exact=exact,
                       application_exact=application_exact,
                       physical_steps=physical_steps}
                    val _ = transitions :=
                      Termtab.update (transition_key, result) (!transitions)
                  in result end)
          val attempt = Exn.capture build ()
          val _ = if Exn.is_exn attempt then
              transition_failures := !transition_failures + 1 else ()
        in Exn.release attempt end

      val forward_checks = Unsynchronized.ref 0
      val forward_port_evaluations = Unsynchronized.ref 0
      val forward_admissions = Unsynchronized.ref 0
      val forward_retrievals = Unsynchronized.ref 0
      val forward_failures = Unsynchronized.ref 0
      val forward_time = Unsynchronized.ref Time.zeroTime
      val forward_certificates = Unsynchronized.ref
        (Termtab.empty: source_forward option Termtab.table)
      fun forward source =
        (case Termtab.lookup (!forward_certificates) source of
          SOME result => (forward_retrievals := !forward_retrievals + 1; result)
        | NONE =>
            let
              val started = Time.now ()
              val _ = forward_checks := !forward_checks + 1
              val attempt = Exn.capture (fn () =>
                let
                  val header_value as {period, base, period_equation, admitted} =
                    header source
                  val result = (case (period, entry_chart_coordinates source) of
                    (1, SOME (sector, offset)) =>
                      let
                        val request = @{term comma_c1_b1_entry_core_port_action} $
                          nat sector $ nat offset $ nat 0
                        val _ = forward_port_evaluations :=
                          !forward_port_evaluations + 1
                        val direct_equation = equation request
                        val direct_value = Thm.term_of (Thm.rhs_of direct_equation)
                      in case strip_comb direct_value of
                        (Const (name, _), [child, shift]) =>
                          if name = @{const_name Comma_Continuation_Goto} andalso
                              number shift = 0 andalso #period (header child) > 1 then
                            let
                              val phase = Free ("completed_alias_phase", @{typ nat})
                              val output = @{term comma_semantic_b1_round_output}
                              val equality = HOLogic.mk_all ("completed_alias_phase", @{typ nat},
                                HOLogic.mk_eq (output $ phase $ source,
                                  output $ phase $ child))
                              val child_admitted = @{term comma_round_admitted} $ child
                              val rank = @{term "\<lambda>s. 9 - comma_sector_number s"}
                              val decreases = HOLogic.mk_binrel @{const_name less}
                                (Term.betapply (rank, child), Term.betapply (rank, source))
                              val proposition = HOLogic.mk_Trueprop
                                (HOLogic.mk_conj (equality,
                                  HOLogic.mk_conj (child_admitted, decreases)))
                              val completed_rule = Drule.infer_instantiate ctxt
                                [(("f", 0), Thm.cterm_of ctxt (nat sector)),
                                 (("x", 0), Thm.cterm_of ctxt (nat offset)),
                                 (("child", 0), Thm.cterm_of ctxt child)]
                                @{thm comma_semantic_b1_entry_period_one_direct_goto_completed}
                              val direct_port_proposition = HOLogic.mk_Trueprop
                                (HOLogic.mk_eq
                                  (@{term comma_semantic_b1_entry_near_port_action} $
                                    nat sector $ nat offset $ nat 0,
                                   direct_value))
                              val sector_lower = checked_object_proof
                                (HOLogic.mk_Trueprop
                                  (HOLogic.mk_binrel @{const_name less_eq}
                                    (nat 1, nat sector))) []
                                "Entry source has an invalid lower sector bound"
                              val sector_upper = checked_object_proof
                                (HOLogic.mk_Trueprop
                                  (HOLogic.mk_binrel @{const_name less_eq}
                                    (nat sector, nat 9))) []
                                "Entry source has an invalid upper sector bound"
                              val offset_bound = checked_object_proof
                                (HOLogic.mk_Trueprop
                                  (HOLogic.mk_binrel @{const_name less_eq}
                                    (nat offset, nat 98))) []
                                "Entry source has an invalid offset bound"
                              val direct_port = checked_object_proof
                                direct_port_proposition
                                [direct_equation, base, period_equation, admitted,
                                 sector_lower, sector_upper, offset_bound,
                                 (@{thm comma_c1_b1_entry_core_port_action_source_exact}
                                   RS @{thm sym}),
                                 (@{thm comma_semantic_b1_entry_slot_action_near}
                                   RS @{thm sym})]
                                "Core selector did not refine its guarded Entry/Near port"
                              val completed = checked_object_proof proposition
                                [completed_rule, admitted, base, period_equation,
                                 direct_port]
                                "Source preflight did not certify full-clock completed transport"
                              val action_proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq
                                (@{term comma_source_continuation_action_at} $ source $ nat 0,
                                  direct_value))
                              val action_rule = Drule.infer_instantiate ctxt
                                [(("f", 0), Thm.cterm_of ctxt (nat sector)),
                                 (("x", 0), Thm.cterm_of ctxt (nat offset)),
                                 (("child", 0), Thm.cterm_of ctxt child),
                                 (("clock", 0), Thm.cterm_of ctxt (nat 0))]
                                @{thm comma_semantic_b1_entry_period_one_direct_goto_action}
                              val action = checked_object_proof action_proposition
                                [action_rule, admitted, base, period_equation,
                                 direct_port]
                                "Source preflight lost its exact zero-shift Goto authority"
                              val _ = Thm.consolidate [completed, action]
                              val _ = forward_admissions :=
                                !forward_admissions + 1
                            in SOME {child=child, completed=completed, action=action,
                              direct=direct_equation, header=header_value} end
                          else NONE
                      | _ => NONE end
                  | _ => NONE)
                in result end) ()
              val _ = forward_time := Time.+
                (!forward_time, Time.- (Time.now (), started))
              val _ = if Exn.is_exn attempt then
                forward_failures := !forward_failures + 1 else ()
              val result = Exn.release attempt
              val _ = forward_certificates := Termtab.update
                (source, result) (!forward_certificates)
            in result end)

      fun stats () =
        "semantic_source_classifications=" ^ Int.toString (!class_attempts) ^
        " semantic_source_class_hits=" ^ Int.toString (!class_hits) ^
        " semantic_source_class_failures=" ^ Int.toString (!class_failures) ^
        " semantic_near_operator_builds=" ^ Int.toString (!near_operator_builds) ^
        " semantic_near_operator_reuses=" ^ Int.toString (!near_operator_reuses) ^
        " semantic_near_residual_builds=" ^ Int.toString (!near_residual_builds) ^
        " semantic_near_residual_hits=" ^ Int.toString (!near_residual_hits) ^
        " semantic_near_application_transports=" ^
          Int.toString (!near_application_transports) ^
        " semantic_source_transition_evaluations=" ^
          Int.toString (!transition_attempts) ^
        " semantic_source_transition_cache_hits=" ^
          Int.toString (!transition_hits) ^
        " semantic_source_transition_failures=" ^
          Int.toString (!transition_failures) ^
        " semantic_forward_preflight_checks=" ^ Int.toString (!forward_checks) ^
        " semantic_forward_preflight_port_evaluations=" ^
          Int.toString (!forward_port_evaluations) ^
        " semantic_forward_preflight_admissions=" ^
          Int.toString (!forward_admissions) ^
        " semantic_forward_preflight_retrievals=" ^ Int.toString (!forward_retrievals) ^
        " semantic_forward_preflight_failures=" ^ Int.toString (!forward_failures) ^
        " semantic_forward_preflight_ms=" ^ LargeInt.toString
          (Time.toMilliseconds (!forward_time))
      fun work () =
        {transition_evaluations= !transition_attempts,
         near_operator_builds= !near_operator_builds,
         near_operator_reuses= !near_operator_reuses,
         near_residual_builds= !near_residual_builds,
         near_residual_hits= !near_residual_hits,
         near_application_transports= !near_application_transports}
    in {classify=classify, validate_selection=validate_selection,
      transition=transition, forward=forward,
      stats=stats, work=work} end
end
