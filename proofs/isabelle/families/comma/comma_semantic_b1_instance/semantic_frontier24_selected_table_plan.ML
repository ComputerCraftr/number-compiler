(* Request-local selected-list plans for exact projection and named-table roots. *)
structure Comma_Frontier24_Selected_Table_Plan =
struct
  structure Runtime = Comma_Frontier24_Parametric_Runtime
  structure Utils = Comma_CRT_MDD_Proof_Utils

  val natT = @{typ nat}

  fun const name resultT args =
    list_comb (Const (name,fold_rev (curry (op -->)) (map fastype_of args) resultT),args)

  fun list T xs = HOLogic.mk_list T xs

  type plan =
    {procedure: Simplifier.simproc, post_procedure: Simplifier.simproc,
     code_procedure: Simplifier.simproc, code_post_procedure: Simplifier.simproc,
     stats: unit -> string, canonicalize: cterm -> thm option,
     transport_equation: thm option}

  fun make_with_root ctxt bundle label field elementT expected_length
      expected_items named_root : plan =
    let
      val tableT = HOLogic.listT elementT
      val projection = const field tableT [bundle]
      fun project_to_root () = Conv.rewrs_conv
        (map (fn theorem => theorem RS @{thm eq_reflection})
          @{thms comma_frontier24_parametric_bundle.select_convs})
        (Thm.cterm_of ctxt projection)
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
          stats,canonicalize=canonical_root} =
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
    in {procedure=procedure,post_procedure=post_procedure,stats=stats,
        code_procedure=code_procedure,code_post_procedure=code_post_procedure,
        canonicalize=canonicalize,transport_equation=transport_equation} end

  fun make ctxt bundle label field elementT expected_length expected_items =
    make_with_root ctxt bundle label field elementT expected_length expected_items NONE

  fun make_named ctxt bundle label field elementT expected_length
      ({table,definition}: Runtime.named_actions) expected_items =
    make_with_root ctxt bundle label field elementT expected_length (SOME expected_items)
      (SOME (table,definition))

  fun procedures ({code_procedure,code_post_procedure,...}: plan) =
    [code_procedure,code_post_procedure]

  fun statistics ({stats,...}: plan) = stats ()
end
