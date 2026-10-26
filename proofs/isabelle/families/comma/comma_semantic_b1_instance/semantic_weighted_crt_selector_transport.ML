(* Pure pointwise proof transport for the conditional weighted-CRT selector.
   The data owner retains all traversal, scope, cache, and resource authority. *)
structure Comma_Semantic_Weighted_CRT_Selector_Transport =
struct
  open Comma_Semantic_Weighted_CRT_Data_Transport

  datatype selector_piece =
      Same_Axis_Port of {slot: int, selected: term}
    | Lower_Axis_Port of
        {slot: int, restricted_rows: term list, child_common: int,
         child_result: term, child_equation: thm}

  val radices = [4,3,7,11]
  val natT = @{typ nat}

  (* This transport uses only the canonical closed arithmetic simp rules.
     Prepare their immutable simplifier database once for this theory, then
     install it into each caller context so local theory data is preserved. *)
  val arithmetic_simpset = Simplifier.simpset_of
    (Comma_Entry_Arithmetic.natural_context @{context})
  fun arithmetic_context ctxt = put_simpset arithmetic_simpset ctxt

  fun numeral value = HOLogic.mk_number natT value

  fun dest_nat label term =
    (case try HOLogic.dest_number term of
      SOME (typ,value) =>
        if typ = natT andalso value >= 0 then IntInf.toInt value
        else error (label ^ " is not a natural numeral")
    | NONE => error (label ^ " is not a numeral"))

  fun action_type payloadT =
    HOLogic.mk_prodT
      (natT,Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT]))

  fun action_parts label action =
    let
      val (offset,tree) = HOLogic.dest_prod action
      val weight = dest_nat (label ^ " offset") offset
    in (weight,tree) end

  fun branch_const payloadT =
    let
      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
      val rowsT = HOLogic.listT (HOLogic.mk_prodT (natT,dagT))
    in Const (@{const_name Comma_Weighted_CRT_Branch},natT --> rowsT --> dagT) end

  fun apply_const payloadT =
    let
      val actionT = action_type payloadT
      val resultT = HOLogic.mk_prodT (payloadT,natT)
    in Const (@{const_name comma_weighted_crt_apply},
      actionT --> natT --> Type (@{type_name option},[resultT])) end

  fun mk_branch payloadT axis rows =
    let val rowT = action_type payloadT
    in branch_const payloadT $ numeral axis $ HOLogic.mk_list rowT rows end

  fun mk_apply payloadT action phase = apply_const payloadT $ action $ phase

  fun mk_action offset tree = HOLogic.mk_prod (numeral offset,tree)

  fun mk_add left right = HOLogic.mk_binop @{const_name plus} (left,right)

  fun mk_first_port_rows payloadT axis slot rows =
    let
      val actionT = action_type payloadT
      val rowsT = HOLogic.listT actionT
      val function = Const (@{const_name comma_weighted_crt_first_port_rows},
        natT --> natT --> rowsT --> rowsT)
    in function $ numeral axis $ numeral slot $ HOLogic.mk_list actionT rows end

  fun mk_nth actionT rows index =
    Const (@{const_name nth},HOLogic.listT actionT --> natT --> actionT) $
      rows $ index

  fun literal_size_conversion_cterm ctxt rows_ct =
    let
      val rows = Thm.term_of rows_ct
      val size_const = Const (@{const_name size},fastype_of rows --> natT)
      val size_ct = Thm.apply (Thm.cterm_of ctxt size_const) rows_ct
      val literal = Comma_Selected_List_Conversion.literal_length_conversion
        (fn () => ()) size_ct
      val scalar = Simplifier.rewrite
        (arithmetic_context ctxt) (Thm.rhs_of literal)
    in Thm.transitive literal scalar end

  fun literal_size_conversion ctxt rows =
    literal_size_conversion_cterm ctxt (Thm.cterm_of ctxt rows)

  fun scalar_conversion ctxt profile term =
    let
      val canonical_nat_literal =
        (case try HOLogic.dest_number term of
          SOME (typ,value) =>
            if typ <> natT orelse value < 0 then false
            else (case try IntInf.toInt value of
              SOME number => term aconv numeral number
            | NONE => false)
        | NONE => false)
    in
      if canonical_nat_literal then Thm.reflexive (Thm.cterm_of ctxt term)
      else with_profile profile "selector_port" (fn () =>
        Simplifier.rewrite (arithmetic_context ctxt)
          (Thm.cterm_of ctxt term))
    end

  fun action_meta_equation ctxt profile payloadT left_action right_action =
    if left_action aconv right_action then
      (* Most selector-port transports compare the same already-normalized
         action on both sides. Avoid simplifying each scalar offset again;
         reflexivity retains the exact checked endpoints and requires no
         arithmetic assumptions. *)
      Thm.reflexive (Thm.cterm_of ctxt left_action)
    else let
      val (left_offset,left_tree) = HOLogic.dest_prod left_action
      val (right_offset,right_tree) = HOLogic.dest_prod right_action
      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
      val actionT = HOLogic.mk_prodT (natT,dagT)
      val pair_const = Const (@{const_name Pair},natT --> dagT --> actionT)
      fun pair_equation offset_equation =
        let
          val pair_offset = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt pair_const)) offset_equation
          val pair_tree = Thm.combination pair_offset
            (Thm.reflexive (Thm.cterm_of ctxt left_tree))
          val _ = if Thm.term_of (Thm.lhs_of pair_tree) aconv left_action andalso
              Thm.term_of (Thm.rhs_of pair_tree) aconv right_action then ()
            else error "Weighted CRT pair transport changed its exact action endpoints"
        in pair_tree end
      val _ = if left_tree aconv right_tree then ()
        else error "Weighted CRT row action changed its exact child"
      val offset_equation =
        if left_offset aconv right_offset then
          Thm.reflexive (Thm.cterm_of ctxt left_offset)
        else
          let
            val left_conversion = scalar_conversion ctxt profile left_offset
            val right_conversion = scalar_conversion ctxt profile right_offset
            val common_left = Thm.term_of (Thm.rhs_of left_conversion)
            val common_right = Thm.term_of (Thm.rhs_of right_conversion)
            val _ = if common_left aconv common_right then ()
              else error "Weighted CRT row action changed its exact weight"
          in Thm.transitive left_conversion (Thm.symmetric right_conversion) end
      val equation = pair_equation offset_equation
    in equation end

  fun first_port_action_root_equation profile ctxt axis slot successor_equation child_ct =
    with_profile profile "selector_first_port_root" (fn () =>
    let
      val child = Thm.term_of child_ct
      val dagT = fastype_of child
      val actionT = HOLogic.mk_prodT (natT,dagT)
      val action_const = Const (@{const_name comma_weighted_crt_first_port_action},
        natT --> natT --> dagT --> actionT)
      val source_action = action_const $ numeral axis $ numeral slot $ child
      val result =
        (case strip_comb child of
          (Const (name,_),[_]) =>
            if name = @{const_name Comma_Weighted_CRT_Leaf} then
              let
                val (_,control_ct) = Thm.dest_comb child_ct
              in Drule.infer_instantiate ctxt
                [(("axis",0),Thm.cterm_of ctxt (numeral axis)),
                 (("slot",0),Thm.cterm_of ctxt (numeral slot)),
                 (("control",0),control_ct)]
                @{thm comma_weighted_crt_first_port_action_leaf} end
            else error "Weighted CRT first-port root is an unknown leaf constructor"
        | (Const (name,_),[_,_]) =>
            if name <> @{const_name Comma_Weighted_CRT_Branch} then
              error "Weighted CRT first-port root is an unknown branch constructor"
            else
              let
                val (branch_head_ct,rows_ct) = Thm.dest_comb child_ct
                val (_,branch_axis_ct) = Thm.dest_comb branch_head_ct
                val branch_axis_term = Thm.term_of branch_axis_ct
                val rows_term = Thm.term_of rows_ct
                val branch_axis = dest_nat "Weighted CRT first-port branch axis"
                  branch_axis_term
                val _ = ignore (check_axis branch_axis)
                val rows = HOLogic.dest_list rows_term
                val _ = check_term_type "Weighted CRT first-port child rows"
                  (HOLogic.listT actionT) rows_term
              in
                if branch_axis = axis then
                  let
                    val radix = check_axis axis
                    val _ = if length rows = radix andalso slot < length rows then ()
                      else error "Weighted CRT matching child branch has an incompatible radix"
                    val size_conversion = literal_size_conversion_cterm ctxt rows_ct
                    val size_lhs = Const (@{const_name size},fastype_of rows_term --> natT) $
                      rows_term
                    val _ = if Thm.term_of (Thm.lhs_of size_conversion) aconv size_lhs andalso
                        Thm.term_of (Thm.rhs_of size_conversion) aconv numeral radix then ()
                      else error "Weighted CRT matching child branch extent changed"
                    val slot_bound = Goal.prove ctxt [] []
                      (HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less}
                        (numeral slot,numeral radix)))
                      (fn {context,...} =>
                        simp_tac (arithmetic_context context) 1)
                    val vector = make_literal_vector_cterm ctxt rows_ct
                    val branch_rule = Drule.infer_instantiate ctxt
                      [(("axis",0),Thm.cterm_of ctxt (numeral axis)),
                       (("slot",0),Thm.cterm_of ctxt (numeral slot)),
                       (("bound",0),Thm.cterm_of ctxt (numeral radix)),
                       (("rows",0),rows_ct)]
                      @{thm comma_weighted_crt_first_port_action_same_branch}
                      OF [slot_bound, size_conversion RS @{thm meta_eq_to_obj_eq}]
                    val branch_meta = branch_rule RS @{thm eq_reflection}
                    val selected = literal_nth_conversion_cterm ctxt successor_equation
                      slot vector
                  in (Thm.transitive branch_meta selected) RS @{thm meta_eq_to_obj_eq} end
                else if branch_axis > axis then
                  let
                    val axes_neq = Goal.prove ctxt [] []
                      (HOLogic.mk_Trueprop (HOLogic.mk_not
                        (HOLogic.mk_eq (numeral branch_axis,numeral axis))))
                      (fn {context,...} =>
                        simp_tac (arithmetic_context context) 1)
                    val other_rule = Drule.infer_instantiate ctxt
                      [(("axis",0),Thm.cterm_of ctxt (numeral axis)),
                       (("slot",0),Thm.cterm_of ctxt (numeral slot)),
                       (("branch_axis",0),Thm.cterm_of ctxt (numeral branch_axis)),
                       (("rows",0),rows_ct)]
                      @{thm comma_weighted_crt_first_port_action_other_branch}
                  in other_rule OF [axes_neq] end
                else error "Weighted CRT first-port axis precedes the child branch"
              end
        | _ => error "Weighted CRT first-port child has no closed root constructor")
      val result_meta = result RS @{thm eq_reflection}
      val _ = if Thm.term_of (Thm.lhs_of result_meta) aconv source_action then ()
        else error "Weighted CRT first-port root equation has another source"
    in result_meta end)

  fun first_port_rows_nth_action_equation ctxt profile payloadT axis slot rows_term
      rows_vector size_conversion successor_equation index row_count index_bound =
    with_profile profile "selector_port" (fn () =>
    let
      val actionT = action_type payloadT
      val selected_input = literal_nth_conversion_cterm ctxt successor_equation index rows_vector
      val selected_input_rhs = Thm.rhs_of selected_input
      val (selected_row_function,child_ct) = Thm.dest_comb selected_input_rhs
      val (_,weight_ct) = Thm.dest_comb selected_row_function
      val selected_row = Thm.term_of selected_input_rhs
      val weight = Thm.term_of weight_ct
      val _ = check_term_type "Weighted CRT selected first-port source row" actionT selected_row
      val action_equation = first_port_action_root_equation profile ctxt axis slot
        successor_equation child_ct
      val action_rhs = Thm.rhs_of action_equation
      val (action_result_function,target_ct) = Thm.dest_comb action_rhs
      val (_,delta_ct) = Thm.dest_comb action_result_function
      val delta = Thm.term_of delta_ct
      val target = Thm.term_of target_ct
      val selected_rule = Drule.infer_instantiate ctxt
        [(("axis",0),Thm.cterm_of ctxt (numeral axis)),
         (("slot",0),Thm.cterm_of ctxt (numeral slot)),
         (("index",0),Thm.cterm_of ctxt (numeral index)),
         (("bound",0),Thm.cterm_of ctxt (numeral row_count))]
        @{thm comma_weighted_crt_first_port_rows_nth_action}
      val selected_object = selected_input RS @{thm meta_eq_to_obj_eq}
      val action_object = action_equation RS @{thm meta_eq_to_obj_eq}
      val size_object = size_conversion RS @{thm meta_eq_to_obj_eq}
      val row_result = selected_rule OF
        [index_bound,size_object,selected_object,action_object]
      val expected = mk_nth actionT (mk_first_port_rows payloadT axis slot
        (HOLogic.dest_list rows_term)) (numeral index)
      val _ = if Thm.prop_of row_result aconv
          HOLogic.mk_Trueprop (HOLogic.mk_eq (expected,
            HOLogic.mk_prod (mk_add weight delta,target))) then ()
        else error "Weighted CRT first-port selected-row theorem has different endpoints"
    in row_result RS @{thm eq_reflection} end)

  fun mk_admissible payloadT axis tree =
    let val dagT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
    in Const (@{const_name comma_weighted_crt_first_port_admissible},
      natT --> dagT --> HOLogic.boolT) $ numeral axis $ tree end

  fun mk_shape_proposition payloadT axis rows action =
    let
      val root_offset = Free ("root_offset",natT)
      val phase = Free ("phase",natT)
      val source_tree = mk_branch payloadT axis rows
      val (result_offset,result_tree) = HOLogic.dest_prod action
    in HOLogic.mk_Trueprop (HOLogic.mk_all ("root_offset",natT,
      HOLogic.mk_all ("phase",natT,HOLogic.mk_eq
        (mk_apply payloadT (HOLogic.mk_prod (root_offset,source_tree)) phase,
         mk_apply payloadT
           (HOLogic.mk_prod (mk_add root_offset result_offset,result_tree)) phase))))
    end

  fun closed_simp native_certify profile stage ctxt label proposition simps =
    prove_profiled profile stage ctxt [] [] proposition
      (fn {context,...} => simp_tac (context addsimps simps) 1)
      |> checked_closed_profile native_certify profile ctxt label proposition

  fun fact_nat_lt native_certify profile ctxt label left right =
    closed_simp native_certify profile "selector_port" ctxt label
      (HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less} (left,right))) []

  fun exact_equation native_certify profile ctxt label left right simp_facts =
    let
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq (left,right))
    in closed_simp native_certify profile "selector_port" ctxt label
      proposition simp_facts end

  fun specialize_two ctxt root_offset phase theorem =
    let
      val at_offset = specialize_hol_all ctxt root_offset theorem
    in specialize_hol_all ctxt phase at_offset end

  fun port_extent_fact native_certify profile ctxt label payloadT axis ports vector =
    let
      val actionT = action_type payloadT
      val radix = check_axis axis
      val rows = HOLogic.mk_list actionT ports
      val rows_ct = literal_vector_rows_ct vector
      val _ = if Thm.term_of rows_ct aconv rows then ()
        else error "Weighted CRT selector extent vector differs from its port list"
      val size_term = Const (@{const_name size},HOLogic.listT actionT --> natT) $ rows
      val conversion = literal_size_conversion_cterm ctxt rows_ct
      val _ = if Thm.term_of (Thm.lhs_of conversion) aconv size_term andalso
          Thm.term_of (Thm.rhs_of conversion) aconv numeral radix then ()
        else error "Weighted CRT selector literal extent changed its exact port list"
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq (size_term,numeral radix))
      val extent = conversion RS @{thm meta_eq_to_obj_eq}
    in checked_closed_profile native_certify profile ctxt label proposition extent end

  fun input_admissibility native_certify profile ctxt payloadT axis rows =
    with_profile profile "selector_admissibility" (fn () =>
    let
      val actionT = action_type payloadT
      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
      val weight = Free ("weight",natT)
      val child = Free ("child",dagT)
      val predicate_body = Term.lambda weight
        (Term.lambda child (mk_admissible payloadT axis child))
      val case_prod = Const (@{const_name case_prod},
        fastype_of predicate_body --> actionT --> HOLogic.boolT)
      val predicate = case_prod $ predicate_body
      val list_all = Const (@{const_name list_all},fastype_of predicate -->
        HOLogic.listT actionT --> HOLogic.boolT)
      val proposition = HOLogic.mk_Trueprop
        (list_all $ predicate $ HOLogic.mk_list actionT rows)
    in closed_simp native_certify profile "selector_port" ctxt
      "Weighted CRT shallow first-port admissibility"
      proposition (@{thms comma_weighted_crt_first_port_admissible.simps
        comma_crt_axis_radix_def}) end)

  fun selected_port_equation native_certify profile ctxt payloadT axis slot input_rows
      input_rows_term input_vector input_size_conversion successor_equation port =
    let
      val actionT = action_type payloadT
      val first_ports = mk_first_port_rows payloadT axis slot input_rows
      val expected = mk_nth actionT first_ports (numeral slot)
      val _ = check_term_type "Weighted CRT same-axis selected port" actionT port
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq (expected,port))
      val row_count = length input_rows
      val index_bound = Goal.prove ctxt [] []
        (HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less}
          (numeral slot,numeral row_count)))
        (fn {context,...} =>
          simp_tac (arithmetic_context context) 1)
      val first_port = first_port_rows_nth_action_equation ctxt profile payloadT axis slot
        input_rows_term input_vector input_size_conversion successor_equation
        slot row_count index_bound
      val computed = Thm.term_of (Thm.rhs_of first_port)
      val action_equation = action_meta_equation ctxt profile payloadT computed port
      val equation = Thm.transitive first_port action_equation
      val _ = if Thm.term_of (Thm.lhs_of equation) aconv expected andalso
          Thm.term_of (Thm.rhs_of equation) aconv port then ()
        else error "Weighted CRT selected port theorem has the wrong endpoint"
    in checked_closed_profile native_certify profile ctxt
      "Weighted CRT same-axis port matches its first port" proposition
      (equation RS @{thm meta_eq_to_obj_eq}) end

  fun common_rows_term payloadT common rows =
    let
      val actionT = action_type payloadT
      fun shift action =
        let val (weight,tree) = action_parts "Weighted CRT lower-port row" action
        in mk_action (common + weight) tree end
    in HOLogic.mk_list actionT (map shift rows) end

  fun lower_port_rows_equation native_certify profile ctxt payloadT axis slot input_rows
      input_rows_term input_vector successor_equation common relative_rows =
    with_profile profile "selector_port" (fn () =>
    let
      val actionT = action_type payloadT
      val expected = mk_first_port_rows payloadT axis slot input_rows
      val actual = common_rows_term payloadT common relative_rows
      val row_count = length input_rows
      val _ = if row_count > 0 andalso length relative_rows = row_count then ()
        else error "Weighted CRT lower-port row vectors have incompatible extents"
      val actual_vector = make_literal_vector ctxt actual
      val input_rows_ct = literal_vector_rows_ct input_vector
      val _ = if Thm.term_of input_rows_ct aconv input_rows_term then ()
        else error "Weighted CRT lower-port input cterm changed its exact list"
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq (expected,actual))
      val axis_ct = Thm.cterm_of ctxt (numeral axis)
      val slot_ct = Thm.cterm_of ctxt (numeral slot)
      val rows_listT = HOLogic.listT actionT
      val first_port_rows_const = Const (@{const_name comma_weighted_crt_first_port_rows},
        natT --> natT --> rows_listT --> rows_listT)
      fun dest_spine rows_ct =
        (case Thm.term_of rows_ct of
          Const (name,_) =>
            if name = @{const_name Nil} then NONE
            else error "Weighted CRT lower-port spine has an unknown nullary constructor"
        | Const (name,_) $ _ $ _ =>
            if name <> @{const_name Cons} then
              error "Weighted CRT lower-port spine has an unknown list constructor"
            else
              let
                val (cons_head_ct,tail_ct) = Thm.dest_comb rows_ct
                val (cons_const_ct,head_ct) = Thm.dest_comb cons_head_ct
                val _ = (case Thm.term_of cons_const_ct of
                  Const (cons_name,_) => if cons_name = @{const_name Cons} then ()
                    else error "Weighted CRT lower-port cterm spine is not Cons"
                | _ => error "Weighted CRT lower-port cterm spine lost Cons")
              in SOME (head_ct,tail_ct) end
        | _ => error "Weighted CRT lower-port cterm spine is malformed")
      fun pair_parts label row_ct =
        let
          val (pair_head_ct,child_ct) = Thm.dest_comb row_ct
          val (pair_const_ct,weight_ct) = Thm.dest_comb pair_head_ct
          val _ = (case Thm.term_of pair_const_ct of
            Const (pair_name,_) => if pair_name = @{const_name Pair} then ()
              else error (label ^ " is not a weighted pair")
          | _ => error (label ^ " lost its pair constructor"))
        in (weight_ct,child_ct) end
      fun spine input_ct actual_ct =
        with_profile profile "selector_spine" (fn () =>
        (case (dest_spine input_ct,dest_spine actual_ct) of
          (NONE,NONE) =>
            let
              val nil_theorem = @{thm comma_weighted_crt_first_port_rows_nil}
              val [payload_type_var] = Term.add_tvars (Thm.prop_of nil_theorem) []
              val typed_nil_theorem = Thm.instantiate
                (TVars.make [(payload_type_var,Thm.ctyp_of ctxt payloadT)],Vars.empty)
                nil_theorem
              val nil_rule = Drule.infer_instantiate ctxt
                [(("axis",0),axis_ct),(("slot",0),slot_ct)] typed_nil_theorem
              val nil_prop = HOLogic.mk_Trueprop (HOLogic.mk_eq
                (mk_first_port_rows payloadT axis slot [],HOLogic.mk_list actionT []))
              val _ = if Thm.prop_of nil_rule aconv nil_prop then ()
                else error "Weighted CRT lower-port empty spine theorem changed endpoints"
            in nil_rule end
        | (SOME (input_head_ct,input_tail_ct),SOME (actual_head_ct,actual_tail_ct)) =>
            let
              val (input_weight_ct,child_ct) = pair_parts
                "Weighted CRT lower-port source head" input_head_ct
              val (actual_weight_ct,actual_target_ct) = pair_parts
                "Weighted CRT lower-port actual head" actual_head_ct
              val action_equation = first_port_action_root_equation profile ctxt axis slot
                successor_equation child_ct
              val action_rhs_ct = Thm.rhs_of action_equation
              val (action_pair_head_ct,target_ct) = Thm.dest_comb action_rhs_ct
              val (_,delta_ct) = Thm.dest_comb action_pair_head_ct
              val _ = if Thm.term_of target_ct aconv Thm.term_of actual_target_ct then ()
                else error "Weighted CRT lower-port first-port action changed its child"
              val input_weight = Thm.term_of input_weight_ct
              val actual_weight = Thm.term_of actual_weight_ct
              val delta = Thm.term_of delta_ct
              val input_delta = mk_add input_weight delta
              val input_delta_conversion = scalar_conversion ctxt profile input_delta
              val actual_weight_conversion = scalar_conversion ctxt profile actual_weight
              val _ = if Thm.term_of (Thm.rhs_of input_delta_conversion) aconv
                  Thm.term_of (Thm.rhs_of actual_weight_conversion) then ()
                else error "Weighted CRT lower-port head changed its exact carry weight"
              val weight_equation = Thm.transitive input_delta_conversion
                (Thm.symmetric actual_weight_conversion) RS @{thm meta_eq_to_obj_eq}
              val tail_equation = spine input_tail_ct actual_tail_ct
              val cons_rule = Drule.infer_instantiate ctxt
                [(("axis",0),axis_ct),(("slot",0),slot_ct),
                 (("input_weight",0),input_weight_ct),(("delta",0),delta_ct),
                 (("actual_weight",0),actual_weight_ct),(("child",0),child_ct),
                 (("target",0),target_ct),(("input_rows",0),input_tail_ct),
                 (("actual_rows",0),actual_tail_ct)]
                @{thm comma_weighted_crt_first_port_rows_cons_transport}
              val row_equation = cons_rule OF
                [action_equation RS @{thm meta_eq_to_obj_eq},weight_equation,tail_equation]
              val expected_prefix = first_port_rows_const $ numeral axis $ numeral slot $
                Thm.term_of input_ct
              val actual_prefix = Thm.term_of actual_ct
              val _ = if Thm.prop_of row_equation aconv
                  HOLogic.mk_Trueprop (HOLogic.mk_eq (expected_prefix,actual_prefix)) then ()
                else error "Weighted CRT lower-port cons transport changed its ordered endpoints"
            in row_equation end
        | _ => error "Weighted CRT lower-port source and result spines have different lengths"))
      val rows_equation = spine input_rows_ct (literal_vector_rows_ct actual_vector)
      val _ = if Thm.prop_of rows_equation aconv proposition then ()
        else error "Weighted CRT lower-port spine has a different whole-list endpoint"
    in checked_closed_profile native_certify profile ctxt
      "Weighted CRT lower-axis port carries its common weight" proposition rows_equation end)

  fun child_selector_proposition ctxt payloadT axis rows result =
    mk_shape_proposition payloadT axis rows result

  fun certify_same_axis_port native_certify profile ctxt payloadT parent_axis split_axis slot input_rows
      input_extent admissibility port_action selected_equation =
    with_profile profile "selector_port" (fn () =>
    let
      val radix = check_axis split_axis
      val incoming = Free ("incoming",natT)
      val phase = Free ("phase",natT)
      val axis = numeral split_axis
      val guard_bool = HOLogic.mk_eq
        (HOLogic.mk_binop @{const_name modulo}
          (phase,Const (@{const_name comma_crt_axis_radix},natT --> natT) $ axis),
         numeral slot)
      val guard_term = HOLogic.mk_Trueprop guard_bool
      val guard_assumption = Thm.assume (Thm.cterm_of ctxt guard_term)
      val source_tree = mk_branch payloadT parent_axis input_rows
      val actionT = action_type payloadT
      val first_ports = mk_first_port_rows payloadT split_axis slot input_rows
      val first_port = Const (@{const_name nth},HOLogic.listT actionT --> natT --> actionT) $
        first_ports $ numeral slot
      val (port_offset,port_tree) = action_parts
        "Weighted CRT selected port" port_action
      val expected_selected = HOLogic.mk_eq (first_port,port_action)
      val _ = if Thm.prop_of selected_equation aconv HOLogic.mk_Trueprop expected_selected then ()
        else error "Weighted CRT same-axis selected action has another first-port endpoint"
      val axis_fact = fact_nat_lt native_certify profile ctxt
        "Weighted CRT parent selector axis bound" axis (numeral 4)
      val axis_radix = Const (@{const_name comma_crt_axis_radix},natT --> natT) $ axis
      val slot_proposition = HOLogic.mk_Trueprop
        (HOLogic.mk_binrel @{const_name less} (numeral slot,axis_radix))
      val slot_fact = closed_simp native_certify profile "selector_port" ctxt
        "Weighted CRT selector symbolic slot bound" slot_proposition
        [@{thm comma_crt_axis_radix_def}]
      val rows_term = HOLogic.mk_list actionT input_rows
      val selected_rule = Drule.infer_instantiate ctxt
        [(("axis",0),Thm.cterm_of ctxt axis),
         (("slot",0),Thm.cterm_of ctxt (numeral slot)),
         (("incoming",0),Thm.cterm_of ctxt incoming),
         (("phase",0),Thm.cterm_of ctxt phase),
         (("rows",0),Thm.cterm_of ctxt rows_term)]
        @{thm comma_weighted_crt_branch_selected_first_port_guarded}
      val source_selected = selected_rule OF
        [axis_fact,slot_fact,input_extent,admissibility,guard_assumption]
      val selected_meta = selected_equation RS @{thm eq_reflection}
      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
      val fst_const = Const (@{const_name fst},actionT --> natT)
      val snd_const = Const (@{const_name snd},actionT --> dagT)
      val first_weight = Thm.combination (Thm.reflexive (Thm.cterm_of ctxt fst_const))
        selected_meta
      val first_tree = Thm.combination (Thm.reflexive (Thm.cterm_of ctxt snd_const))
        selected_meta
      val first_weight = Thm.transitive first_weight
        (Conv.rewr_conv (@{thm fst_conv} RS @{thm eq_reflection})
          (Thm.rhs_of first_weight))
      val first_tree = Thm.transitive first_tree
        (Conv.rewr_conv (@{thm snd_conv} RS @{thm eq_reflection})
          (Thm.rhs_of first_tree))
      val plus_const = Const (@{const_name plus},natT --> natT --> natT)
      val plus_incoming = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt plus_const))
        (Thm.reflexive (Thm.cterm_of ctxt incoming))
      val offset_equation = Thm.combination plus_incoming first_weight
      val pair_const = Const (@{const_name Pair},natT --> dagT --> actionT)
      val pair_head = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt pair_const)) offset_equation
      val selected_action_equation = Thm.combination pair_head first_tree
      val apply_head = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt (apply_const payloadT)))
        selected_action_equation
      val apply_equation = Thm.combination apply_head
        (Thm.reflexive (Thm.cterm_of ctxt phase))
      val transport = apply_equation RS @{thm meta_eq_to_obj_eq}
      val final_object = @{thm trans} OF [source_selected,transport]
      val target = mk_apply payloadT
        (HOLogic.mk_prod (mk_add incoming (numeral port_offset),port_tree)) phase
      val output_equality = HOLogic.mk_eq
        (mk_apply payloadT (HOLogic.mk_prod (incoming,source_tree)) phase,target)
      val _ = if Thm.prop_of final_object aconv HOLogic.mk_Trueprop output_equality then ()
        else error "Weighted CRT direct same-axis transport changed its action endpoints"
      val guarded = Thm.implies_intr (Thm.cterm_of ctxt guard_term) final_object
      val implication_rule = Drule.infer_instantiate' ctxt
        [SOME (Thm.cterm_of ctxt guard_bool),
         SOME (Thm.cterm_of ctxt output_equality)] @{thm impI}
      val implication = Thm.implies_elim implication_rule guarded
      val phase_all = Thm.forall_intr (Thm.cterm_of ctxt phase) implication
        COMP @{thm allI}
      val incoming_all = Thm.forall_intr (Thm.cterm_of ctxt incoming) phase_all
        COMP @{thm allI}
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
        ("incoming",natT,HOLogic.mk_all ("phase",natT,
          HOLogic.mk_imp (guard_bool,output_equality))))
      val _ = if Thm.prop_of incoming_all aconv proposition then ()
        else error "Weighted CRT direct same-axis theorem has different endpoints"
    in checked_closed_profile native_certify profile ctxt
      "Weighted CRT guarded selector port" proposition incoming_all end)

  fun prove_guarded_port_family native_certify profile ctxt payloadT split_axis source_tree port_facts =
    with_profile profile "selector_family" (fn () =>
    let
      val actionT = action_type payloadT
      val radix = check_axis split_axis
      val slot = Free ("slot",natT)
      val incoming = Free ("incoming",natT)
      val phase = Free ("phase",natT)
      val port_terms = map #1 port_facts
      val port_list = HOLogic.mk_list actionT port_terms
      val rows_term = Const (@{const_name nth},HOLogic.listT actionT --> natT --> actionT) $
        port_list $ slot
      val port_offset = Const (@{const_name fst},actionT --> natT) $ rows_term
      val port_tree = Const (@{const_name snd},actionT -->
        Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])) $ rows_term
      val radix_term = numeral radix
      val phase_radix = Const (@{const_name comma_crt_axis_radix},natT --> natT) $
        numeral split_axis
      val guard = HOLogic.mk_eq
        (HOLogic.mk_binop @{const_name modulo} (phase,phase_radix),slot)
      val pointwise = HOLogic.mk_all ("incoming",natT,
        HOLogic.mk_all ("phase",natT,HOLogic.mk_imp (guard,
          HOLogic.mk_eq
            (mk_apply payloadT (HOLogic.mk_prod (incoming,source_tree)) phase,
             mk_apply payloadT
               (HOLogic.mk_prod (mk_add incoming port_offset,port_tree)) phase))))
      val predicate = Term.lambda slot (HOLogic.mk_imp
        (HOLogic.mk_binrel @{const_name less} (slot,radix_term),pointwise))
      val predicate_const = predicate
      val predicate_ct = Thm.cterm_of ctxt predicate_const
      val port_vector = make_literal_vector ctxt port_list
      val ports_ct = literal_vector_rows_ct port_vector
      val source_tree_ct = Thm.cterm_of ctxt source_tree
      val axis_ct = Thm.cterm_of ctxt (numeral split_axis)
      val successor_equation = Comma_Selected_List_Conversion.make_successor_equation ctxt
      val indexed_list = Comma_Selected_List_Conversion.prove_indexed_list_all
        {ctxt=ctxt,predicate=predicate_const,bound=radix,
         zero_fact = @{thm comma_indexed_all_zero},
         step_fact = @{thm comma_indexed_all_Suc},
         successor_equation=successor_equation,
         prove_item=fn index =>
           let
             val port_fact = #2 (List.nth (port_facts,index))
             val port_action = #1 (List.nth (port_facts,index))
             val row_index = numeral index
             val row_index_ct = Thm.cterm_of ctxt row_index
             val item_ct = Thm.apply predicate_ct row_index_ct
             val item_term = Thm.term_of item_ct
             val proposition = HOLogic.mk_Trueprop item_term
             val beta = Thm.beta_conversion false item_ct
             val beta_trueprop = Thm.combination
               (Thm.reflexive (Thm.cterm_of ctxt
                 (Const (@{const_name Trueprop},HOLogic.boolT --> @{typ prop})))) beta
             val normalized_proposition = HOLogic.mk_Trueprop
               (Thm.term_of (Thm.rhs_of beta))
             val selected_conversion = literal_nth_conversion_cterm ctxt successor_equation
               index port_vector
             val selected_object = selected_conversion RS @{thm meta_eq_to_obj_eq}
             val selected_expected = HOLogic.mk_eq
               (mk_nth actionT port_list row_index,port_action)
             val _ = if Thm.prop_of selected_object aconv
                 HOLogic.mk_Trueprop selected_expected then ()
               else error "Weighted CRT indexed port conversion changed its exact action"
             val slot_bound_term = HOLogic.mk_Trueprop
               (HOLogic.mk_binrel @{const_name less} (row_index,radix_term))
             val slot_bound_ct = Thm.cterm_of ctxt slot_bound_term
             val port_rule = Drule.infer_instantiate ctxt
               [(("axis",0),axis_ct),
                (("slot",0),row_index_ct),
                (("source",0),source_tree_ct),
                (("ports",0),ports_ct)]
               @{thm comma_weighted_crt_selected_port_rebase}
             val pointwise = port_rule OF [selected_object,port_fact]
             val indexed_implication = Thm.implies_intr
               slot_bound_ct pointwise
             val implication_rule = Drule.infer_instantiate' ctxt
               [SOME (Thm.dest_arg slot_bound_ct),
                SOME (Thm.dest_arg (Thm.cprop_of pointwise))] @{thm impI}
             val indexed_item = Thm.implies_elim implication_rule indexed_implication
             val _ = if Thm.prop_of indexed_item aconv normalized_proposition then ()
               else error "Weighted CRT indexed port theorem has another guarded endpoint"
             val checked = checked_closed_profile native_certify profile ctxt
               "Weighted CRT normalized indexed selector port"
               normalized_proposition indexed_item
             val item = Thm.equal_elim (Thm.symmetric beta_trueprop) checked
           in checked_closed_profile native_certify profile ctxt "Weighted CRT indexed selector port"
             proposition item end}
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
        ("slot",natT,HOLogic.mk_imp
          (HOLogic.mk_binrel @{const_name less} (slot,radix_term),pointwise)))
      val theorem = (@{thm comma_weighted_crt_list_all_upt_implies_forall}
        OF [indexed_list])
        |> checked_closed_profile native_certify profile ctxt
          "Weighted CRT guarded selector port family" proposition
    in (source_tree,port_list,port_offset,port_tree,theorem,port_vector) end)

  fun lift_selector_common native_certify profile ctxt payloadT parent_axis common relative_rows
      relative_result relative_equation =
    let
      val radix = check_axis parent_axis
      val actionT = action_type payloadT
      val _ = if common >= 0 andalso length relative_rows = radix then ()
        else error "Weighted CRT selector common or row extent is invalid"
      val _ = List.app (check_term_type "Weighted CRT relative selector row" actionT)
        relative_rows
      val _ = check_term_type "Weighted CRT relative selector result" actionT relative_result
      val (relative_offset,relative_tree) = action_parts
        "Weighted CRT relative selector result" relative_result
      val relative_proposition = mk_shape_proposition payloadT parent_axis
        relative_rows relative_result
      val _ = checked_closed_profile native_certify profile ctxt
        "Weighted CRT relative selector equation"
        relative_proposition relative_equation
      val actual_rows =
        let fun shift action =
          let val (weight,tree) = action_parts "Weighted CRT relative row" action
          in mk_action (common + weight) tree end
        in map shift relative_rows end
      val actual_tree = mk_branch payloadT parent_axis actual_rows
      val relative_tree_term = mk_branch payloadT parent_axis relative_rows
      val root_offset = Free ("root_offset",natT)
      val phase = Free ("phase",natT)
      val target_offset = common + relative_offset
      val expected = HOLogic.mk_Trueprop (HOLogic.mk_all
        ("root_offset",natT,HOLogic.mk_all ("phase",natT,
          HOLogic.mk_eq
            (mk_apply payloadT (HOLogic.mk_prod (root_offset,actual_tree)) phase,
             mk_apply payloadT (HOLogic.mk_prod (mk_add root_offset (numeral target_offset),
               relative_tree)) phase))))
      val recenter_prop = HOLogic.mk_Trueprop (HOLogic.mk_all
        ("root_offset",natT,HOLogic.mk_all ("phase",natT,
          HOLogic.mk_eq
            (mk_apply payloadT (HOLogic.mk_prod (root_offset,actual_tree)) phase,
             mk_apply payloadT
               (HOLogic.mk_prod (mk_add root_offset (numeral common),relative_tree_term))
               phase))))
      val recenter_rule = Drule.infer_instantiate ctxt
        [(("axis",0),Thm.cterm_of ctxt (numeral parent_axis)),
         (("common",0),Thm.cterm_of ctxt (numeral common)),
         (("rows",0),Thm.cterm_of ctxt (HOLogic.mk_list actionT relative_rows))]
        @{thm comma_weighted_crt_branch_add_common}
        |> Simplifier.full_simplify
          (arithmetic_context ctxt addsimps
            @{thms comma_crt_axis_radix_def list.map list.size case_prod_beta})
      val recenter = prove_profiled profile "selector_common" ctxt [] [] recenter_prop
        (fn {context,...} =>
          simp_tac (arithmetic_context context addsimps
            [recenter_rule]) 1)
        |> checked_closed_profile native_certify profile ctxt
          "Weighted CRT common selector recenter" recenter_prop
      val result = prove_profiled profile "selector_common" ctxt [] [] expected
        (fn {context,...} =>
          REPEAT_DETERM (resolve_tac context [@{thm allI}] 1)
          THEN Method.insert_tac context [recenter,relative_equation] 1
          THEN asm_full_simp_tac (arithmetic_context context addsimps
            [@{thm add.assoc},@{thm add.commute},@{thm add.left_commute}]) 1)
        |> checked_closed_profile native_certify profile ctxt "Weighted CRT selector common transport"
          expected
    in result end

  fun direct_lower_axis_port native_certify profile ctxt payloadT parent_axis split_axis slot
      input_rows parent_axis_fact split_axis_fact slot_fact input_extent admissibility
      restricted_eq child_lifted child_common child_offset child_tree =
    with_profile profile "selector_port" (fn () =>
    let
      val actionT = action_type payloadT
      val expected_resolved = mk_first_port_rows payloadT split_axis slot input_rows
      val resolved_meta = restricted_eq RS @{thm eq_reflection}
      val resolved_rows = Thm.term_of (Thm.rhs_of resolved_meta)
      val resolved_proposition = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (expected_resolved,resolved_rows))
      val _ = if Thm.prop_of restricted_eq aconv resolved_proposition then ()
        else error "Weighted CRT lower-port rows have another resolved endpoint"
      val _ = if fastype_of resolved_rows = HOLogic.listT actionT then ()
        else error "Weighted CRT lower-port resolved rows have the wrong type"
      val _ = HOLogic.dest_list resolved_rows
      val _ = if child_common >= 0 andalso child_offset >= 0 then ()
        else error "Weighted CRT lower-port result offset is negative"
      val child_common_offset = numeral (child_common + child_offset)
      val incoming = Free ("incoming",natT)
      val phase = Free ("phase",natT)
      val phase_radix = Const (@{const_name comma_crt_axis_radix},natT --> natT) $
        numeral split_axis
      val guard_bool = HOLogic.mk_eq
        (HOLogic.mk_binop @{const_name modulo} (phase,phase_radix),numeral slot)
      val guard_term = HOLogic.mk_Trueprop guard_bool
      val guard_assumption = Thm.assume (Thm.cterm_of ctxt guard_term)
      val source_tree = mk_branch payloadT parent_axis input_rows
      val output_equality = HOLogic.mk_eq
        (mk_apply payloadT (HOLogic.mk_prod (incoming,source_tree)) phase,
         mk_apply payloadT
           (HOLogic.mk_prod (mk_add incoming child_common_offset,child_tree)) phase)
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all ("incoming",natT,
        HOLogic.mk_all ("phase",natT,HOLogic.mk_imp (guard_bool,output_equality))))
      val theorem = Drule.infer_instantiate ctxt
        [(("incoming",0),Thm.cterm_of ctxt incoming),
         (("phase",0),Thm.cterm_of ctxt phase)]
        @{thm comma_weighted_crt_first_port_completed}
      val applied = theorem OF
        [parent_axis_fact,split_axis_fact,slot_fact,input_extent,admissibility,
         restricted_eq,child_lifted,guard_assumption]
      val guarded = Thm.implies_intr (Thm.cterm_of ctxt guard_term) applied
      val implication_rule = Drule.infer_instantiate' ctxt
        [SOME (Thm.cterm_of ctxt guard_bool),
         SOME (Thm.cterm_of ctxt output_equality)] @{thm impI}
      val implication = Thm.implies_elim implication_rule guarded
      val phase_all = Thm.forall_intr (Thm.cterm_of ctxt phase) implication
        COMP @{thm allI}
      val incoming_all = Thm.forall_intr (Thm.cterm_of ctxt incoming) phase_all
        COMP @{thm allI}
      val _ = if Thm.prop_of incoming_all aconv proposition then ()
        else error "Weighted CRT direct lower-port theorem has different endpoints"
    in checked_closed_profile native_certify profile ctxt
      "Weighted CRT lower-axis selector port" proposition incoming_all end)

  fun certify_completed_select native_certify profile ctxt payloadT parent_axis split_axis input_rows
      pieces result_action =
    let
      val parent_radix = check_axis parent_axis
      val split_radix = check_axis split_axis
      val actionT = action_type payloadT
      val _ = if split_axis <= parent_axis andalso length input_rows = parent_radix andalso
          length pieces = split_radix then ()
        else error "Weighted CRT selector axes or row extents are invalid"
      val _ = List.app (check_term_type "Weighted CRT selector input row" actionT) input_rows
      val _ = check_term_type "Weighted CRT selector result" actionT result_action
      val (result_offset,result_tree) = action_parts "Weighted CRT selector result" result_action
      val parent_axis_fact = fact_nat_lt native_certify profile ctxt
        "Weighted CRT selector parent-axis bound" (numeral parent_axis) (numeral 4)
      val split_axis_fact = fact_nat_lt native_certify profile ctxt
        "Weighted CRT selector split-axis bound" (numeral split_axis) (numeral 4)
      val input_rows_term = HOLogic.mk_list actionT input_rows
      val input_vector = make_literal_vector ctxt input_rows_term
      val input_size_conversion = literal_size_conversion ctxt input_rows_term
      val input_size_term = Const (@{const_name size},HOLogic.listT actionT --> natT) $
        input_rows_term
      val _ = if Thm.term_of (Thm.lhs_of input_size_conversion) aconv input_size_term andalso
          Thm.term_of (Thm.rhs_of input_size_conversion) aconv numeral parent_radix then ()
        else error "Weighted CRT selector literal vector has another parent extent"
      val input_extent_proposition = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (input_size_term,numeral parent_radix))
      val input_extent = checked_closed_profile native_certify profile ctxt
        "Weighted CRT selector literal extent" input_extent_proposition
        (input_size_conversion RS @{thm meta_eq_to_obj_eq})
      val input_radix_conversion = with_profile profile "selector_port" (fn () =>
        Simplifier.rewrite (arithmetic_context ctxt
          addsimps [@{thm comma_crt_axis_radix_def}])
          (Thm.cterm_of ctxt
            (Const (@{const_name comma_crt_axis_radix},natT --> natT) $ numeral parent_axis)))
      val _ = if Thm.term_of (Thm.lhs_of input_radix_conversion) aconv
          (Const (@{const_name comma_crt_axis_radix},natT --> natT) $ numeral parent_axis)
          andalso Thm.term_of (Thm.rhs_of input_radix_conversion) aconv numeral parent_radix then ()
        else error "Weighted CRT selector axis radix conversion changed its endpoint"
      val exact_input_extent = Thm.transitive input_size_conversion
        (Thm.symmetric input_radix_conversion) RS @{thm meta_eq_to_obj_eq}
      val admissibility = input_admissibility native_certify profile ctxt payloadT split_axis input_rows
      val successor_equation =
        Comma_Selected_List_Conversion.make_successor_equation ctxt
      val source_tree = mk_branch payloadT parent_axis input_rows
      val (port_terms,port_facts) =
        let
          fun one slot piece =
            (case piece of
              Same_Axis_Port {slot=recorded,selected} =>
                if split_axis <> parent_axis orelse recorded <> slot then
                  error "Weighted CRT same-axis selector piece has incompatible coordinates"
                else
                  let
                    val selected_eq = selected_port_equation native_certify profile ctxt payloadT
                      split_axis slot input_rows input_rows_term input_vector input_size_conversion
                      successor_equation selected
                    val (port_offset,port_tree) = action_parts
                      "Weighted CRT same-axis selector piece" selected
                    val port_action = mk_action port_offset port_tree
                    val equation = certify_same_axis_port native_certify profile ctxt payloadT parent_axis
                      split_axis slot input_rows exact_input_extent admissibility
                      port_action selected_eq
                  in (port_action,equation) end
            | Lower_Axis_Port {slot=recorded,restricted_rows,child_common,
                 child_result,child_equation} =>
                if split_axis >= parent_axis orelse recorded <> slot then
                  error "Weighted CRT lower-axis selector piece has incompatible coordinates"
                else
                  let
                    val _ = if child_common >= 0 then ()
                      else error "Weighted CRT lower-axis common weight is negative"
                    val _ = List.app (check_term_type "Weighted CRT child selector row" actionT)
                      restricted_rows
                    val (child_offset,child_tree) = action_parts
                      "Weighted CRT lower-axis child result" child_result
                    val child_prop = child_selector_proposition ctxt payloadT
                      parent_axis restricted_rows child_result
                    val _ = checked_closed_profile native_certify profile ctxt
                      "Weighted CRT lower-axis child selector"
                      child_prop child_equation
                    val restricted_eq = lower_port_rows_equation native_certify profile ctxt payloadT
                      split_axis slot input_rows input_rows_term input_vector
                      successor_equation child_common restricted_rows
                    val child_lifted = lift_selector_common native_certify profile ctxt payloadT parent_axis
                      child_common restricted_rows child_result child_equation
                    val actual_result = mk_action (child_common + child_offset) child_tree
                    val slot_fact = closed_simp native_certify profile "selector_port" ctxt
                      "Weighted CRT lower selector slot bound"
                      (HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less}
                        (numeral slot,Const (@{const_name comma_crt_axis_radix},natT --> natT) $
                          numeral split_axis))) [@{thm comma_crt_axis_radix_def}]
                    val equation = direct_lower_axis_port native_certify profile ctxt payloadT
                      parent_axis split_axis slot input_rows parent_axis_fact split_axis_fact
                      slot_fact exact_input_extent admissibility restricted_eq child_lifted
                      child_common child_offset child_tree
                  in (actual_result,equation) end)
          val pairs = map2 one (0 upto (split_radix - 1)) pieces
        in (map #1 pairs,pairs) end
      val port_list = port_terms
      val (source_for_diagonal,_,_,_,guarded_ports,port_vector) =
        prove_guarded_port_family native_certify profile ctxt payloadT split_axis source_tree port_facts
      val port_extent = port_extent_fact native_certify profile ctxt
        "Weighted CRT selector output extent"
        payloadT split_axis port_list port_vector
      val phase_radix = Const (@{const_name comma_crt_axis_radix},natT --> natT) $
        numeral split_axis
      val radix_equation = closed_simp native_certify profile "selector_diagonal" ctxt
        "Weighted CRT selector radix equation"
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (numeral split_radix,phase_radix)))
        [@{thm comma_crt_axis_radix_def}]
      val _ = if source_for_diagonal aconv source_tree then ()
        else error "Weighted CRT selector diagonal changed its source tree"
      val diagonal_rule = @{thm comma_weighted_crt_guarded_port_diagonal_forall} OF
        [fact_nat_lt native_certify profile ctxt "Weighted CRT selector diagonal axis bound"
           (numeral split_axis) (numeral 4),radix_equation,port_extent,
         guarded_ports]
      val diagonal_prop = HOLogic.mk_Trueprop (HOLogic.mk_all
        ("root_offset",natT,HOLogic.mk_all ("phase",natT,
          HOLogic.mk_eq
            (mk_apply payloadT (HOLogic.mk_prod
              (Free ("root_offset",natT),source_tree)) (Free ("phase",natT)),
             mk_apply payloadT (HOLogic.mk_prod
               (Free ("root_offset",natT),mk_branch payloadT split_axis port_list))
               (Free ("phase",natT))))))
      val diagonal = prove_profiled profile "selector_diagonal" ctxt [] [] diagonal_prop
        (fn {context,...} =>
          REPEAT_DETERM (resolve_tac context [@{thm allI}] 1)
          THEN resolve_tac context [diagonal_rule] 1)
        |> checked_closed_profile native_certify profile ctxt "Weighted CRT selector guarded diagonal"
          diagonal_prop
      val canonical =
        Comma_Semantic_Weighted_CRT_Branch_Transport.canonical_branch
          native_certify profile ctxt payloadT split_axis port_list result_action
      val root_offset = Free ("root_offset",natT)
      val phase = Free ("phase",natT)
      val source = HOLogic.mk_prod (root_offset,source_tree)
      val target = HOLogic.mk_prod
        (mk_add root_offset (numeral result_offset),result_tree)
      val application = apply_const payloadT
      val equation = Comma_Semantic_Weighted_CRT_Data_Transport.compose_pointwise_profile
        native_certify profile ctxt "Weighted CRT completed selector action" application root_offset phase
        source target [diagonal,canonical]
      val expected = mk_shape_proposition payloadT parent_axis input_rows result_action
      val _ = if Thm.prop_of equation aconv expected then ()
        else error "Weighted CRT completed selector theorem has a mismatched endpoint"
    in checked_closed_profile native_certify profile ctxt "Weighted CRT completed selector"
      expected equation end

end
