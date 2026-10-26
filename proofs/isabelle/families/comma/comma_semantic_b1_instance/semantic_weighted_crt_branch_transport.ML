(* Pure row and branch proof transport for weighted CRT normalization.
   Arena traversal, issuance, proof caching, and resource accounting remain in
   Comma_Semantic_Weighted_CRT_Data. *)
structure Comma_Semantic_Weighted_CRT_Branch_Transport =
struct
  open Comma_Semantic_Weighted_CRT_Data_Transport

  (* Transport a bottom-up child certificate through one literal parent row.
     The plan/cache owner supplies the ordered raw/completed rows and one
     all-offset child theorem per row; this helper owns no arena state. *)
  fun branch_children_refinement native_certify profile ctxt payloadT axis source_tree completed_tree
      raw_rows completed_rows child_equations = with_profile profile "branch_rows" (fn () =>
    let
      val dagT =
        Type (@{type_name comma_semantic_weighted_crt_dag}, [payloadT])
      val actionT = HOLogic.mk_prodT (natT,dagT)
      val action_listT = HOLogic.listT actionT
      val radix = check_axis axis
      val _ = check_term_type "Weighted CRT branch source" dagT source_tree
      val _ = check_term_type "Weighted CRT branch result" dagT completed_tree
      val _ = List.app (check_term_type "Weighted CRT raw row" actionT) raw_rows
      val _ = List.app (check_term_type "Weighted CRT completed row" actionT)
        completed_rows
      val _ = if length raw_rows = radix andalso length completed_rows = radix andalso
          length child_equations = radix then ()
        else error "Weighted CRT bottom-up branch rows have the wrong radix"
      val branch_const = Const
        (@{const_name Comma_Weighted_CRT_Branch},natT --> action_listT --> dagT)
      val raw_rows_term = HOLogic.mk_list actionT raw_rows
      val completed_rows_term = HOLogic.mk_list actionT completed_rows
      val raw_rows_vector = make_literal_vector ctxt raw_rows_term
      val completed_rows_vector = make_literal_vector ctxt completed_rows_term
      val raw_branch = branch_const $ nat axis $ raw_rows_term
      val completed_branch = branch_const $ nat axis $ completed_rows_term
      val _ = if source_tree aconv raw_branch andalso completed_tree aconv
          completed_branch then ()
        else error "Weighted CRT bottom-up rows do not match the parent branch terms"
      val apply_const = Const
        (@{const_name comma_weighted_crt_apply},
          actionT --> natT --> Type (@{type_name option},
            [HOLogic.mk_prodT (payloadT,natT)]))
      val plus_const = Const (@{const_name plus},natT --> natT --> natT)
      val fst_const = Const (@{const_name fst},actionT --> natT)
      val snd_const = Const (@{const_name snd},actionT --> dagT)
      val nth_const = Const (@{const_name nth},action_listT --> natT --> actionT)
      val scalar_context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
        [@{thm add.assoc}]
      fun dest_natural label term =
        (case HOLogic.dest_number term of
          (typ,value) =>
            if typ = natT andalso value >= 0 then value
            else error (label ^ " is not a natural numeral"))
      fun dest_apply term =
        (case strip_comb term of
          (Const (name,_),[action,phase]) =>
            if name = @{const_name comma_weighted_crt_apply} then (action,phase)
            else error "Weighted CRT child certificate applies another function"
        | _ => error "Weighted CRT child certificate has a malformed apply term")
      fun application action phase = apply_const $ action $ phase
      fun check_child_equation raw_child completed_child child_equation =
        let
          val proposition = Thm.prop_of child_equation
          val _ = if Thm.nprems_of child_equation = 0 andalso
              null (Thm.hyps_of child_equation) andalso
              null (Thm.tpairs_of child_equation) andalso
              not (Term.is_open proposition) andalso
              null (Term.add_frees proposition []) andalso
              null (Term.add_vars proposition []) andalso
              Context.subthy (Thm.theory_of_thm child_equation,
                Proof_Context.theory_of ctxt) then ()
            else error "Weighted CRT child certificate is not closed and native"
          val _ = ignore (native_certify child_equation)
          fun universal_body term =
            (case strip_comb term of
              (Const (name,_),[Abs (_,domainT,body)]) =>
                if name = @{const_name All} andalso domainT = natT then body
                else error "Weighted CRT child theorem has a non-natural universal"
            | _ => error "Weighted CRT child theorem has no universal interface")
          val body = universal_body
            (universal_body (HOLogic.dest_Trueprop proposition))
          val (source_application,target_application) =
            HOLogic.dest_eq body
          val (source_action,source_phase) = dest_apply source_application
          val (target_action,target_phase) = dest_apply target_application
          val (source_offset,source_tree_term) = HOLogic.dest_prod source_action
          val (target_offset,target_tree_term) = HOLogic.dest_prod target_action
          val (child_offset_term,identity) =
            if target_offset aconv Bound 1 then (nat 0,true)
            else (case strip_comb target_offset of
              (Const (name,_),[incoming,delta]) =>
                if name = @{const_name plus} andalso incoming aconv Bound 1 then
                  (delta,false)
                else error "Weighted CRT child result changed its incoming coordinate"
            | _ => error "Weighted CRT child result has no affine offset")
          val child_offset = dest_natural "Weighted CRT child normalization offset"
            child_offset_term
          val _ = if source_offset aconv Bound 1 andalso source_tree_term aconv raw_child
              andalso target_tree_term aconv completed_child andalso
              source_phase aconv Bound 0 andalso target_phase aconv Bound 0 then ()
            else error "Weighted CRT child certificate has foreign source or result terms"
        in (child_offset,child_offset_term,identity) end
      fun row_equation index =
        let
          val raw_row = List.nth (raw_rows,index)
          val completed_row = List.nth (completed_rows,index)
          val child_equation = List.nth (child_equations,index)
          val (raw_weight_term,raw_child) = HOLogic.dest_prod raw_row
          val (completed_weight_term,completed_child) =
            HOLogic.dest_prod completed_row
          val raw_weight = dest_natural "Weighted CRT raw edge weight"
            raw_weight_term
          val completed_weight = dest_natural "Weighted CRT completed edge weight"
            completed_weight_term
          val (child_offset,child_offset_term,identity) =
            check_child_equation raw_child completed_child child_equation
          val _ = if completed_weight = raw_weight + child_offset then ()
            else error "Weighted CRT completed row changed its accumulated edge weight"
          val root_offset = Free ("root_offset",natT)
          val phase = Free ("phase",natT)
          val incoming = plus_const $ root_offset $ raw_weight_term
          (* A completed child already quantifies both scalar coordinates.
             Shift that universal interface with one generic rule instead of
             opening and rebuilding its complete source/result trees per row. *)
          val quantified_root = if identity then
              Drule.infer_instantiate ctxt
                [(("weight",0),Thm.cterm_of ctxt raw_weight_term)]
                @{thm comma_weighted_crt_child_row_identity} OF [child_equation]
            else
              let
                val sum = Simplifier.rewrite scalar_context
                  (Thm.cterm_of ctxt (plus_const $ raw_weight_term $ child_offset_term))
                val _ = if Thm.term_of (Thm.rhs_of sum) aconv completed_weight_term then ()
                  else error "Weighted CRT child row sum has another result weight"
                val rule = Drule.infer_instantiate ctxt
                  [(("weight",0),Thm.cterm_of ctxt raw_weight_term),
                   (("total",0),Thm.cterm_of ctxt completed_weight_term)]
                  @{thm comma_weighted_crt_child_row_offset}
              in rule OF [child_equation,sum RS @{thm meta_eq_to_obj_eq}] end
          val expected = HOLogic.mk_Trueprop
            (HOLogic.mk_all ("root_offset",natT,
              HOLogic.mk_all ("phase",natT,
                HOLogic.mk_eq
                  (application (HOLogic.mk_prod (incoming,raw_child)) phase,
                   application (HOLogic.mk_prod
                     (plus_const $ root_offset $ completed_weight_term,
                      completed_child)) phase))))
        in checked_closed_profile native_certify profile ctxt
          "Weighted CRT bottom-up child-row theorem" expected quantified_root end
      val row_equations = map row_equation (0 upto (radix - 1))
      val slot = Free ("slot",natT)
      val root_offset = Free ("root_offset",natT)
      val phase = Free ("phase",natT)
      val source_row = nth_const $ raw_rows_term $ slot
      val target_row = nth_const $ completed_rows_term $ slot
      val source_row_action = HOLogic.mk_prod
        (plus_const $ root_offset $ (fst_const $ source_row),
          snd_const $ source_row)
      val target_row_action = HOLogic.mk_prod
        (plus_const $ root_offset $ (fst_const $ target_row),
          snd_const $ target_row)
      val row_predicate = Term.lambda slot (HOLogic.mk_imp
        (HOLogic.mk_binrel @{const_name less} (slot,nat radix),
          HOLogic.mk_all ("root_offset",natT,HOLogic.mk_all ("phase",natT,
            HOLogic.mk_eq
              (application source_row_action phase,
               application target_row_action phase)))))
      val successor_equation =
        Comma_Selected_List_Conversion.make_successor_equation ctxt
      val indexed_rows = Comma_Selected_List_Conversion.prove_indexed_list_all
        {ctxt=ctxt,predicate=row_predicate,bound=radix,
         zero_fact = @{thm comma_indexed_all_zero},
         step_fact = @{thm comma_indexed_all_Suc},
         successor_equation=successor_equation,
         prove_item=fn index =>
           let
             val row_fact = List.nth (row_equations,index)
             val selectedL =
               literal_nth_conversion_cterm ctxt successor_equation index raw_rows_vector
             val selectedR =
               literal_nth_conversion_cterm ctxt successor_equation index completed_rows_vector
             val item_term = row_predicate $ nat index
             val beta = Thm.beta_conversion false (Thm.cterm_of ctxt item_term)
             val beta_trueprop = Thm.combination
               (Thm.reflexive (Thm.cterm_of ctxt
                 (Const (@{const_name Trueprop},HOLogic.boolT --> @{typ prop})))) beta
             val theorem = Drule.infer_instantiate ctxt
               [(("bound",0),Thm.cterm_of ctxt (nat radix))]
               @{thm comma_weighted_crt_selected_row_all_offsets} OF
                 [selectedL RS @{thm meta_eq_to_obj_eq},
                  selectedR RS @{thm meta_eq_to_obj_eq},row_fact]
             val _ = if Thm.prop_of theorem aconv
                 HOLogic.mk_Trueprop (Thm.term_of (Thm.rhs_of beta)) then ()
               else error "Weighted CRT selected row theorem changed its predicate"
             val item = Thm.equal_elim (Thm.symmetric beta_trueprop) theorem
           in checked_closed_profile native_certify profile ctxt
             "Weighted CRT indexed completed row"
             (HOLogic.mk_Trueprop item_term) item end}
      val rows_proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
        ("slot",natT,HOLogic.mk_imp
          (HOLogic.mk_binrel @{const_name less} (slot,nat radix),
           HOLogic.mk_all ("root_offset",natT,HOLogic.mk_all ("phase",natT,
             HOLogic.mk_eq
               (application source_row_action phase,
                application target_row_action phase))))))
      val rows_theorem =
        (@{thm comma_weighted_crt_list_all_upt_implies_forall} OF [indexed_rows])
        |> checked_closed_profile native_certify profile ctxt
          "Weighted CRT completed row family" rows_proposition
      fun closed_fact label proposition = prove_profiled profile "branch_rows"
        ctxt [] [] proposition
        (fn {context,...} => simp_tac context 1)
        |> checked_closed_profile native_certify profile ctxt label proposition
      val axis_fact = closed_fact "Weighted CRT bottom-up axis bound"
        (HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less}
          (nat axis,nat 4)))
      fun extent_fact label rows_term =
        let
          val length_const = Const (@{const_name size},action_listT --> natT)
          val length_term = length_const $ rows_term
          val literal = Comma_Selected_List_Conversion.literal_length_conversion
            (fn () => ()) (Thm.cterm_of ctxt length_term)
          val scalar = with_profile profile "branch_rows" (fn () =>
            Simplifier.rewrite scalar_context (Thm.rhs_of literal))
          val length_eq = Thm.transitive literal scalar
          val _ = if Thm.term_of (Thm.lhs_of length_eq) aconv length_term andalso
              Thm.term_of (Thm.rhs_of length_eq) aconv nat radix then ()
            else error (label ^ " did not retain its literal radix")
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (length_term,nat radix))
        in checked_closed_profile native_certify profile ctxt label proposition
          (length_eq RS @{thm meta_eq_to_obj_eq}) end
      val raw_extent = extent_fact "Weighted CRT raw row extent" raw_rows_term
      val completed_extent = extent_fact "Weighted CRT completed row extent"
        completed_rows_term
      val radix_term = Const
        (@{const_name comma_crt_axis_radix},natT --> natT) $ nat axis
      val radix_conversion = Simplifier.rewrite
        (scalar_context addsimps [@{thm comma_crt_axis_radix_def}])
        (Thm.cterm_of ctxt radix_term)
      val _ = if Thm.term_of (Thm.rhs_of radix_conversion) aconv nat radix then ()
        else error "Weighted CRT branch radix has another literal extent"
      val radix_fact = Thm.symmetric radix_conversion RS @{thm meta_eq_to_obj_eq}
      val root_offset = Free ("root_offset",natT)
      val phase = Free ("phase",natT)
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
        ("root_offset",natT,HOLogic.mk_all ("phase",natT,
          HOLogic.mk_eq
            (application (HOLogic.mk_prod (root_offset,source_tree)) phase,
             application (HOLogic.mk_prod (root_offset,completed_tree)) phase))))
      val theorem = (@{thm comma_weighted_crt_literal_branch_all_offsets} OF
          [axis_fact,radix_fact,raw_extent,completed_extent,rows_theorem])
        |> checked_closed_profile native_certify profile ctxt
          "Weighted CRT bottom-up branch refinement"
          proposition
    in theorem end)

  (* Join the bottom-up child transport to the existing axis-normalization
     certificate.  The parent result offset is the only new weight here. *)
  fun certify_bottom_up_normalization native_certify profile ctxt payloadT axis source_tree
      completed_tree result_offset result_tree raw_rows completed_rows
      child_equations canonical_equation =
    let
      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
      val actionT = HOLogic.mk_prodT (natT,dagT)
      val resultT = HOLogic.mk_prodT (payloadT,natT)
      val _ = check_term_type "Weighted CRT normalization source tree" dagT source_tree
      val _ = check_term_type "Weighted CRT normalization intermediate tree"
        dagT completed_tree
      val _ = check_term_type "Weighted CRT normalization result tree" dagT result_tree
      val _ = check_term_type "Weighted CRT normalization result offset" natT
        result_offset
      val apply_const = Const
        (@{const_name comma_weighted_crt_apply},
          actionT --> natT --> Type (@{type_name option},[resultT]))
      val branch_equation = branch_children_refinement native_certify profile ctxt payloadT axis
        source_tree completed_tree raw_rows completed_rows child_equations
      val root_offset = Free ("root_offset",natT)
      val phase = Free ("phase",natT)
      val source = HOLogic.mk_prod (root_offset,source_tree)
      val target = HOLogic.mk_prod
        (Const (@{const_name plus},natT --> natT --> natT) $
          root_offset $ result_offset,result_tree)
    in compose_pointwise_profile native_certify profile ctxt
      "Weighted CRT bottom-up normalized action"
      apply_const root_offset phase source target
      [branch_equation,canonical_equation] end

  fun canonical_branch native_certify profile ctxt payloadT axis row_actions result_action =
    let
      val dagT =
        Type (@{type_name comma_semantic_weighted_crt_dag}, [payloadT])
      val edgeT = HOLogic.mk_prodT (natT,dagT)
      val edgeListT = HOLogic.listT edgeT
      val actionT = edgeT
      val radix = check_axis axis
      val _ = List.app (check_term_type "Weighted CRT canonical row" edgeT)
        row_actions
      val _ = check_term_type "Weighted CRT canonical result" actionT result_action
      val _ = if length row_actions = radix then ()
        else error "Weighted CRT canonical rows have the wrong radix"
      val apply_const = Const
        (@{const_name comma_weighted_crt_apply},
          actionT --> natT --> Type (@{type_name option},
            [HOLogic.mk_prodT (payloadT,natT)]))
      val branch_const = Const
        (@{const_name Comma_Weighted_CRT_Branch},
          natT --> edgeListT --> dagT)
      val replicate_const =
        Const (@{const_name replicate},natT --> edgeT --> edgeListT)
      val rows_term = HOLogic.mk_list edgeT row_actions
      fun dest_nat term =
        (case try HOLogic.dest_number term of
          SOME (typ,value) =>
            if typ=natT andalso value>=0 then IntInf.toInt value
            else error "Weighted CRT canonical row has a non-natural offset"
        | NONE => error "Weighted CRT canonical row offset is not numeric")
      fun dest_action action =
        (case HOLogic.dest_prod action of
          (offset,tree) => (dest_nat offset,tree))
      val rows = map dest_action row_actions
      val offsets = map #1 rows
      val common =
        (case offsets of
          [] => error "Weighted CRT normalized branch has no rows"
        | first :: rest =>
            fold (fn weight => fn minimum => Int.min (weight,minimum))
              rest first)
      val edges = map (fn (weight,tree) => (weight-common,tree)) rows
      val reduced =
        (case edges of
          [] => false
        | first :: rest => forall (fn edge => edge=first) rest)
      val root_offset = Free ("root_offset",natT)
      val phase = Free ("phase",natT)
      val source = HOLogic.mk_prod
        (root_offset,branch_const $ nat axis $ rows_term)
      val (result_offset,result_tree) = HOLogic.dest_prod result_action
      val target = HOLogic.mk_prod
        (HOLogic.mk_binop @{const_name plus}
          (root_offset,result_offset),result_tree)
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
        ("root_offset",natT,HOLogic.mk_all ("phase",natT,
          HOLogic.mk_eq (apply_const $ source $ phase,
            apply_const $ target $ phase))))
      fun quantify_object_equality equality =
        let
          val phase_all = Thm.forall_intr (Thm.cterm_of ctxt phase)
            equality COMP @{thm allI}
        in Thm.forall_intr (Thm.cterm_of ctxt root_offset)
          phase_all COMP @{thm allI} end
      val direct_identity = common = 0 andalso not reduced andalso
        dest_nat result_offset = 0 andalso result_tree aconv
          (branch_const $ nat axis $ rows_term)
      val theorem =
        if direct_identity then
          let
            val plus_zero = HOLogic.mk_binop @{const_name plus}
              (root_offset,nat 0)
            val plus_zero_eq = with_profile profile "branch_normalize" (fn () =>
              Simplifier.rewrite ctxt (Thm.cterm_of ctxt plus_zero))
            val _ = if Thm.term_of (Thm.lhs_of plus_zero_eq) aconv plus_zero andalso
                Thm.term_of (Thm.rhs_of plus_zero_eq) aconv root_offset then ()
              else error "Weighted CRT zero-offset simplification changed shape"
            val pairT = HOLogic.mk_prodT (natT,dagT)
            val pair_const = Const (@{const_name Pair},natT --> dagT --> pairT)
            val source_tree = branch_const $ nat axis $ rows_term
            val pair_function = Thm.reflexive (Thm.cterm_of ctxt pair_const)
            val pair_offset = Thm.combination pair_function plus_zero_eq
            val pair_trees = Thm.combination pair_offset
              (Thm.reflexive (Thm.cterm_of ctxt source_tree))
            val apply_function = Thm.reflexive (Thm.cterm_of ctxt apply_const)
            val apply_action = Thm.combination apply_function pair_trees
            val apply_phase = Thm.combination apply_action
              (Thm.reflexive (Thm.cterm_of ctxt phase))
            val oriented = (apply_phase RS @{thm meta_eq_to_obj_eq}) RS @{thm sym}
            val closed = quantify_object_equality oriented
          in checked_closed_profile native_certify profile ctxt
            "Weighted CRT zero-offset reflexivity"
            proposition closed end
        else if reduced then
          let
            val (edge_weight,edge_tree) = hd rows
            val edge_action = HOLogic.mk_prod (nat edge_weight,edge_tree)
            val repeated = replicate_const $ nat radix $ edge_action
            val repeated_prop = HOLogic.mk_Trueprop
              (HOLogic.mk_eq (rows_term,repeated))
            val repeated_theorem = prove_profiled profile "branch_normalize"
              ctxt [] [] repeated_prop
              (fn {context,...} => simp_tac context 1)
              |> checked_closed_profile native_certify profile ctxt
                "Weighted CRT collapsed-row identity"
                repeated_prop
            val _ = if dest_nat result_offset = edge_weight andalso
                result_tree aconv edge_tree then ()
              else error "Weighted CRT collapsed row disagrees with its normalized action"
            val collapse = Drule.infer_instantiate ctxt
              [(("axis",0),Thm.cterm_of ctxt (nat axis)),
               (("weight",0),Thm.cterm_of ctxt (nat edge_weight)),
               (("child",0),Thm.cterm_of ctxt edge_tree)]
              @{thm comma_weighted_crt_collapse_equal}
            val proof = prove_profiled profile "branch_normalize" ctxt [] [] proposition
              (fn {context,...} =>
                REPEAT_DETERM (resolve_tac context [@{thm allI}] 1)
                THEN rewrite_goals_tac context
                  [repeated_theorem RS @{thm eq_reflection}]
                THEN resolve_tac context [collapse] 1
                THEN asm_full_simp_tac (context addsimps
                  [@{thm comma_crt_axis_radix_def}]) 1)
              |> checked_closed_profile native_certify profile ctxt
                "Weighted CRT direct equal-row collapse"
                proposition
          in proof end
        else
          let
            val recenter = Drule.infer_instantiate ctxt
              [(("axis",0),Thm.cterm_of ctxt (nat axis)),
               (("rows",0),Thm.cterm_of ctxt rows_term),
               (("common",0),Thm.cterm_of ctxt (nat common))]
              @{thm comma_weighted_crt_recenter_exact}
            val proof = prove_profiled profile "branch_normalize" ctxt [] [] proposition
              (fn {context,...} =>
                asm_full_simp_tac (context addsimps
                  [recenter,@{thm comma_crt_axis_radix_def}]) 1)
              |> checked_closed_profile native_certify profile ctxt
                "Weighted CRT branch recenter"
                proposition
          in proof end
    in theorem end
end
