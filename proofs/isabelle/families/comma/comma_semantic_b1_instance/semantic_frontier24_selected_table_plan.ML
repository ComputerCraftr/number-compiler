(* Request-local selected-list plans for exact projection and named-table roots. *)
structure Comma_Frontier24_Selected_Table_Plan =
struct
  structure Runtime = Comma_Frontier24_Parametric_Runtime
  structure Utils = Comma_CRT_MDD_Proof_Utils

  val natT = @{typ nat}

  fun const name resultT args =
    list_comb (Const (name,fold_rev (curry (op -->)) (map fastype_of args) resultT),args)

  fun list T xs = HOLogic.mk_list T xs

  fun projection_size ctxt label projection_eq (owner: Runtime.named_table) =
    let
      val projection = Thm.term_of (Thm.lhs_of projection_eq)
      val _ = Utils.exact_prop ctxt (label ^ " table projection")
        (Logic.mk_equals (projection,#table owner)) projection_eq
      val size_const = Const (@{const_name size},fastype_of projection --> natT)
      val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
        (size_const $ projection,HOLogic.mk_number natT (length (#rows owner))))
      val owner_expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
        (size_const $ #table owner,HOLogic.mk_number natT (length (#rows owner))))
      val owner_size = Utils.exact_prop ctxt (label ^ " owner extent") owner_expected (#size owner)
      val lifted = Thm.combination (Thm.reflexive (Thm.cterm_of ctxt size_const)) projection_eq
      val theorem = Thm.transitive lifted (owner_size RS @{thm eq_reflection}) RS @{thm meta_eq_to_obj_eq}
    in Utils.exact_prop ctxt (label ^ " projection extent") expected theorem end

  type plan =
    {procedure: Simplifier.simproc, post_procedure: Simplifier.simproc,
     code_procedure: Simplifier.simproc, code_post_procedure: Simplifier.simproc,
     stats: unit -> string, canonicalize: cterm -> thm option,
     child_fields: Simplifier.simproc option, transport_equation: thm option,
     lookup: int -> thm}

  fun make_with_root ctxt bundle field_projections label field elementT expected_length
      expected_items named_root : plan =
    let
      val tableT = HOLogic.listT elementT
      val projection = const field tableT [bundle]
      fun project_to_root () =
        (case AList.lookup (op =) field_projections field of
          SOME theorem =>
            if Thm.term_of (Thm.lhs_of theorem) aconv projection then theorem
            else error (label ^ " projection belongs to another bundle")
        | NONE => error (label ^ " lacks its checked bundle projection"))
      val (table,root_definition,transport_equation) =
        (case named_root of
          NONE => (projection,project_to_root (),NONE)
        | SOME (table,definition) =>
            let
              val projection_definition = project_to_root ()
              val _ = Utils.exact_prop ctxt (label ^ " named projection")
                (Logic.mk_equals (projection,table)) projection_definition
              val definition = (if can Logic.dest_equals (Thm.prop_of definition)
                then definition else definition RS @{thm eq_reflection})
            in (table,definition,SOME projection_definition) end)
      val _ = if Thm.term_of (Thm.lhs_of root_definition) aconv table then ()
        else error (label ^ " lookup root differs from its definition")
      val literal = Thm.term_of (Thm.rhs_of root_definition)
      val _ = Utils.exact_prop ctxt (label ^ " table definition")
        (Logic.mk_equals (table,literal)) root_definition
      val rows = (HOLogic.dest_list literal
        handle TERM _ => error (label ^ " table is not a literal list"))
      val _ = if fastype_of table = tableT andalso fastype_of literal = tableT andalso
          Utils.closed table andalso Utils.closed literal andalso
          forall Utils.closed rows andalso length rows = expected_length andalso
          expected_length > 0
        then () else error (label ^ " table has an invalid literal extent")
      val _ = (case expected_items of
          NONE => ()
        | SOME items => ignore (Utils.exact_prop ctxt (label ^ " candidate table alignment")
            (Logic.mk_equals (table,list elementT items)) root_definition))
      val index = Free (label ^ "_index",natT)
      val table_pattern = Const (@{const_name nth},tableT --> natT --> elementT) $
        table $ index
      val {procedure,post_procedure,code_procedure,code_post_procedure,
          stats,canonicalize=canonical_root,select} =
        Comma_Selected_List_Conversion.make
          {ctxt=ctxt,name="frontier24_" ^ label,
           root_definition=root_definition,table_pattern=table_pattern,
           extents=[expected_length]}
      val projection_alias = (case transport_equation of
          NONE => NONE
        | SOME equation =>
            SOME (Comma_Selected_List_Alias.make
              {ctxt=ctxt,root_definition=equation,
               validate_equation=Comma_Selected_List_Conversion.validate_equation}))
      fun canonicalize argument =
        (case projection_alias of
          SOME aliases =>
            let
              val theorem = #canonical_value aliases argument
              val request = Thm.term_of argument
            in
              if Utils.closed request andalso
                  Thm.term_of (Thm.lhs_of theorem) aconv request andalso
                  Thm.term_of (Thm.rhs_of theorem) aconv table
              then SOME (Utils.exact_prop ctxt (label ^ " canonical projection")
                (Logic.mk_equals (request,table)) theorem)
              else canonical_root argument
            end
        | NONE => canonical_root argument)
      val field_requests = Unsynchronized.ref 0
      val field_success = Unsynchronized.ref 0
      val field_rules = map (fn th => th RS @{thm eq_reflection})
        @{thms comma_frontier24_closure.select_convs}
      val fields = [@{const_name cf24_closure_program_ref},
        @{const_name cf24_closure_full_shift}, @{const_name cf24_closure_output_root}]
      fun field_convert _ _ request =
        let
          val original = Thm.term_of request
          val (head,arguments) = Term.strip_comb original
          fun admitted argument = (case Term.strip_comb argument of
              (Const (name,_),[root,index]) =>
                name = @{const_name nth} andalso root aconv table andalso
                (case try (Utils.dest_nat "closure field index" natT) index of
                   SOME i => i < expected_length | NONE => false)
            | _ => false)
          val allowed = (case (head,arguments) of
              (Const (name,_),[argument]) => member (op =) fields name andalso admitted argument
            | _ => false)
        in if not allowed then NONE else
          let
            val _ = field_requests := !field_requests+1
            val argument = Thm.dest_arg request
            val selected = (case select argument of SOME theorem => theorem
              | NONE => error (label ^ " failed to select an admitted closure row"))
            val _ = if Thm.term_of (Thm.lhs_of selected) aconv Thm.term_of argument andalso
              not (Thm.term_of (Thm.rhs_of selected) aconv Thm.term_of argument)
              then () else error (label ^ " failed to select an admitted closure row")
            val lifted = Thm.combination (Thm.reflexive (Thm.dest_fun request)) selected
            val field = Conv.rewrs_conv field_rules (Thm.rhs_of lifted)
            val theorem = Thm.transitive lifted field
            val theorem = Utils.exact_prop ctxt (label ^ " selected child field")
              (Logic.mk_equals (original,Thm.term_of (Thm.rhs_of theorem))) theorem
            val _ = field_success := !field_success+1
          in SOME theorem end
        end
      fun lookup index =
        let
          val request = Const (@{const_name nth},tableT --> natT --> elementT) $
            projection $ HOLogic.mk_number natT index
          val input = Thm.cterm_of ctxt request
        in case select input of SOME theorem => theorem
          | NONE => error (label ^ " cannot authenticate selected index") end
      val child_fields = if elementT = @{typ comma_frontier24_closure} then
        let
      val field_patterns = map (fn name =>
        Comma_Selected_List_Conversion.schematize
          (Const (name, @{typ comma_frontier24_closure} --> natT) $ table_pattern)) fields
        in SOME (Simplifier.make_simproc ctxt
          {name="frontier24_" ^ label ^ "_child_fields",kind=Simplifier.Congproc false,
           lhss=field_patterns,proc=field_convert,identifier=[]}) end else NONE
      fun combined_stats () = stats () ^ " " ^ label ^ "_child_field_requests=" ^
        Int.toString (!field_requests) ^ " " ^ label ^ "_child_field_success=" ^
        Int.toString (!field_success)
    in {procedure=procedure,post_procedure=post_procedure,stats=combined_stats,
        code_procedure=code_procedure,code_post_procedure=code_post_procedure,
        canonicalize=canonicalize,child_fields=child_fields,transport_equation=transport_equation,
        lookup=lookup} end

  fun make ctxt bundle field_projections label field elementT expected_length expected_items =
    make_with_root ctxt bundle field_projections label field elementT expected_length expected_items NONE

  fun make_balanced ctxt bundle field_projections label field elementT expected_length
      (owner: Runtime.named_table) : plan =
    let
      val tableT = HOLogic.listT elementT
      val projection = const field tableT [bundle]
      val table = #table owner
      val rows = Vector.fromList (#rows owner)
      val _ = if fastype_of table = tableT andalso length (#rows owner) = expected_length
        then () else error (label ^ " balanced table type or extent differs")
      val projection_eq = (case AList.lookup (op =) field_projections field of
          SOME theorem => Utils.exact_prop ctxt (label ^ " balanced projection")
            (Logic.mk_equals (projection,table)) theorem
        | NONE => error (label ^ " lacks its balanced projection"))
      val nth = Const (@{const_name nth},tableT --> natT --> elementT)
      val field_requests = Unsynchronized.ref 0
      val field_success = Unsynchronized.ref 0
      val field_elapsed = Unsynchronized.ref Time.zeroTime
      fun at root index = nth $ root $ HOLogic.mk_number natT index
      fun lookup index =
        let
          val selected = #lookup owner index
          val expected = Logic.mk_equals (at table index,Vector.sub (rows,index))
          val selected = Utils.exact_prop ctxt (label ^ " balanced selected row") expected selected
          val fn_eq = Thm.combination (Thm.reflexive (Thm.cterm_of ctxt nth)) projection_eq
          val lhs_eq = Thm.combination fn_eq (Thm.reflexive
            (Thm.cterm_of ctxt (HOLogic.mk_number natT index)))
        in Thm.transitive lhs_eq selected end
      fun selected index_context request =
        let val term = Thm.term_of request in if not (Utils.closed term) then NONE else
          case Term.strip_comb term of
            (Const (name,_),[root,_]) =>
              if name <> @{const_name nth} orelse not (root aconv projection orelse root aconv table)
              then NONE else
                let
                  val transport = if root aconv projection then
                    let val lifted = Thm.combination (Thm.reflexive (Thm.cterm_of ctxt nth)) projection_eq
                    in Thm.combination lifted (Thm.reflexive (Thm.dest_arg request)) end
                    else Thm.reflexive request
                in Option.map (Thm.transitive transport)
                  (#select owner index_context (Thm.rhs_of transport)) end
          | _ => NONE
        end
      val variable = Free ("balanced_index",natT)
      val patterns = map (fn root => Comma_Selected_List_Conversion.schematize
        (nth $ root $ variable)) [projection,table]
      val procedure = Simplifier.make_simproc ctxt
        {name="frontier24_" ^ label ^ "_balanced",kind=Simplifier.Congproc false,
         lhss=patterns,proc=fn _ => selected,identifier=[]}
      val field_rules = map (fn th => th RS @{thm eq_reflection})
        @{thms comma_frontier24_closure.select_convs}
      val fields = [@{const_name cf24_closure_program_ref},
        @{const_name cf24_closure_full_shift}, @{const_name cf24_closure_output_root}]
      fun field_convert _ index_context request =
        (case Term.strip_comb (Thm.term_of request) of
          (Const (name,_),[_]) => if not (member (op =) fields name) then NONE else
            let
              val started = Time.now ()
              val outcome = Exn.capture (selected index_context) (Thm.dest_arg request)
              fun finish result =
                (field_elapsed := Time.+ (!field_elapsed,Time.- (Time.now (),started)); result)
            in (case Exn.release outcome of
              NONE => NONE
            | SOME theorem =>
                let val _ = field_requests := !field_requests + 1
                    val lifted = Thm.combination (Thm.reflexive (Thm.dest_fun request)) theorem
                    val result = Thm.transitive lifted (Conv.rewrs_conv field_rules (Thm.rhs_of lifted))
                    val _ = field_success := !field_success + 1
                in SOME result end) |> finish end
        | _ => NONE)
      val child_fields = if elementT = @{typ comma_frontier24_closure} then
        SOME (Simplifier.make_simproc ctxt
          {name="frontier24_" ^ label ^ "_balanced_fields",kind=Simplifier.Congproc false,
           lhss=maps (fn name => map (fn root => Comma_Selected_List_Conversion.schematize
             (Const (name,elementT --> natT) $ (nth $ root $ variable))) [projection,table]) fields,
           proc=field_convert,identifier=[]}) else NONE
      fun canonicalize argument = if Thm.term_of argument aconv projection
        then SOME projection_eq else NONE
    in {procedure=procedure,post_procedure=procedure,code_procedure=procedure,
      code_post_procedure=procedure,stats=fn () => label ^ " " ^ #statistics owner () ^
        " child_field_requests=" ^ Int.toString (!field_requests) ^
        " child_field_success=" ^ Int.toString (!field_success) ^
        " child_field_ms=" ^ LargeInt.toString (Time.toMilliseconds (!field_elapsed)),
      canonicalize=canonicalize,
      child_fields=child_fields,transport_equation=SOME projection_eq,lookup=lookup} end

  fun make_named ctxt bundle field_projections label field elementT expected_length
      ({table,definition}: Runtime.named_actions) expected_items =
    make_with_root ctxt bundle field_projections label field elementT expected_length (SOME expected_items)
      (SOME (table,definition))

  fun procedures ({code_procedure,code_post_procedure,...}: plan) =
    [code_procedure,code_post_procedure]

  fun statistics ({stats,...}: plan) = stats ()
end
