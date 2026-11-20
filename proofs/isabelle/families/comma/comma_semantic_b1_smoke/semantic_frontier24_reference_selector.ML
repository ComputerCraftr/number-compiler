(* Differential reference only; not a release certificate owner. *)
structure Comma_Frontier24_Reference_Selector =
struct
  open Comma_Frontier24_Bundle_Publisher
  fun code_true ctxt label head facts procedures predicate =
    let
      val _ = if fastype_of predicate = boolT andalso Utils.closed predicate then ()
        else error (label ^ " is not a closed Boolean check")
      fun scalar_reflexivity T =
        Drule.infer_instantiate ctxt
          [(("x",0),Thm.cterm_of ctxt (Var (("scalar_value",0),T)))]
          @{thm equal_refl}
        |> Axclass.unoverload ctxt
      val literal_lists = Simplifier.make_simproc ctxt
        {name="frontier24_literal_list_constructor",kind=Simplifier.Congproc false,
         lhss=map Comma_Selected_List_Conversion.schematize
           [@{term "Cons (h::comma_semantic_port_program) t"},
            @{term "Cons (h::comma_frontier24_selector_recipe) t"},
            @{term "Cons (h::comma_frontier24_selector_case) t"},
            @{term "Cons (h::comma_frontier24_closure) t"}],
         proc=fn _ => fn context => fn ct => SOME
           (Conv.fun_conv (Conv.arg_conv (Simplifier.rewrite context)) ct),
         identifier=[]}
      val local_ctxt = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_proc literal_lists
        |> Simplifier.add_cong @{thm conj_left_cong}
        |> Simplifier.add_cong @{thm disj_left_cong}
        |> Simplifier.add_cong @{thm bind_option_cong_code}
        |> Simplifier.add_cong @{thm comma_frontier24_list_all2_weak_cong}
        |> Simplifier.add_cong @{thm comma_frontier24_list_all_weak_cong}
        |> Simplifier.add_cong @{thm comma_frontier24_selector_recipe_weak_cong}
        |> Simplifier.add_cong @{thm comma_frontier24_selector_case_action_weak_cong}
        |> Simplifier.add_simp @{thm equal_refl}
        |> Simplifier.add_simps (map scalar_reflexivity [natT,@{typ integer}])
        |> Simplifier.add_simps facts
        |> fold (fn procedure => Simplifier.add_proc procedure) procedures
      val core_parameters = Comma_Direct_Entry_Arithmetic.core_parameter_conversion_plan local_ctxt
      val local_ctxt = local_ctxt
        |> Simplifier.add_proc (#procedure core_parameters)
      val simpset = Simplifier.simpset_of local_ctxt
      val consts = Code_Thingol.read_const_exprs local_ctxt [head]
      val started = Time.now ()
      val evaluator = Code_Simp.static_conv
        {ctxt=local_ctxt,simpset=SOME simpset,
         consts=consts} local_ctxt
      val _ = if Comma_Proof_Profile.enabled () then
          Comma_Proof_Profile.report ("Frontier24 evaluator " ^ label ^
            " stage=prepared elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started)
        else ()
      val evaluated = evaluator (Thm.cterm_of local_ctxt predicate)
      val _ = if Comma_Proof_Profile.enabled () then
          Comma_Proof_Profile.report
            ("Frontier24 core_parameter_rewrites=" ^
              Int.toString (#hits core_parameters ())) else ()
      (* Like Code_Simp.static_tac, conclude after its code postprocessor
         restores ordinary HOL operators. This cannot evaluate family code. *)
      val conclusion = Simplifier.rewrite
        (put_simpset HOL_basic_ss local_ctxt
          |> Simplifier.add_simps @{thms simp_thms}) (Thm.rhs_of evaluated)
      val conversion = Thm.transitive evaluated conclusion
      val right = Thm.term_of (Thm.rhs_of conversion)
      fun first_conjunct term =
        (case term of
          Const (name,_) $ left $ right =>
            if name = @{const_name HOL.conj} then
              if left aconv @{term True} then first_conjunct right
              else first_conjunct left
            else term
        | _ => term)
      fun first_port term =
        let
          fun search current =
            (case strip_comb current of
              (Const (name,_),_) =>
                if name = @{const_name comma_port_low} andalso
                    Term.size_of_term current <= 256 then SOME current
                else descend current
            | _ => descend current)
          and descend (Abs (_,_,body)) = search body
            | descend (left $ right) =
                (case search left of SOME found => SOME found | NONE => search right)
            | descend _ = NONE
        in search term end
      val first = first_conjunct right
      val diagnostic = (case first_port first of
          SOME term => "\nFirst bounded port expression: " ^
            Syntax.string_of_term (Config.put show_types true local_ctxt) term
        | NONE => if Term.size_of_term first <= 2048 then
            "\nFirst unresolved conjunct: " ^
              Syntax.string_of_term (Config.put show_types true local_ctxt) first
          else "\nFirst unresolved conjunct head: " ^
            Syntax.string_of_term local_ctxt (Term.head_of first) ^
            ", nodes=" ^ Int.toString (Term.size_of_term first))
      val _ = if right aconv @{term True} then ()
        else error (label ^ " did not reduce to True: " ^
          (if Term.size_of_term right <= 512
           then Syntax.string_of_term (Config.put show_types true local_ctxt) right
           else "residual head " ^ Syntax.string_of_term local_ctxt (Term.head_of right) ^
             ", nodes=" ^ Int.toString (Term.size_of_term right)) ^
          "\nConstants: " ^ commas (take 24 (Term.add_const_names right [])) ^
          diagnostic)
      val proof = conversion RS @{thm meta_eq_to_obj_eq} RS @{thm eqTrueE}
    in Utils.exact_prop local_ctxt label (HOLogic.mk_Trueprop predicate) proof end

  fun certify_selector ctxt bundle procedures =
    let
      val ports = Comma_Direct_Entry_Arithmetic.fixed_entry_port_conversion_plan ctxt
      val predicate = bundle_pred @{const_name comma_frontier24_selector_rows_checked} bundle
      (* Remove unrelated bundle fields before Code_Preproc traverses the
         evaluator input.  The kernel equation retains the original contract. *)
      val definition = Drule.infer_instantiate ctxt
        [(("bundle",0),Thm.cterm_of ctxt bundle)]
        @{thm comma_frontier24_selector_rows_checked_code}
        RS @{thm eq_reflection}
      val projection = Conv.top_sweep_rewrs_conv
        (map (fn theorem => theorem RS @{thm eq_reflection})
          @{thms comma_frontier24_parametric_bundle.select_convs}) ctxt
        (Thm.rhs_of definition)
      val reduced = Thm.transitive definition projection
      val selected = Thm.term_of (Thm.rhs_of reduced)
      val outcome = Exn.capture (fn () => profiled_stage "selector_rows" (fn () =>
        code_true ctxt "Frontier24 selector rows"
          @{const_name comma_frontier24_selector_rows_checked} []
          (#procedure ports::procedures) selected)) ()
      val _ = Comma_Proof_Profile.report ("Frontier24 " ^ #statistics ports ())
      val theorem = @{thm iffD2} OF
        [reduced RS @{thm meta_eq_to_obj_eq},Exn.release outcome]
      val expected = HOLogic.mk_Trueprop predicate
    in Utils.exact_prop ctxt "Frontier24 checked selector table" expected theorem end

end
