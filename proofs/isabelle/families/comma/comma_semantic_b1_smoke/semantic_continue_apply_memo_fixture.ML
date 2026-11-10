structure Comma_Semantic_Continue_Apply_Memo_Fixture =
struct
  structure Contract = Comma_Semantic_Continue_Observer_Contract
  val natT = @{typ nat}
  val columnT = @{typ comma_crt_column}
  val operationT = @{typ comma_crt_boolean_operation}
  val apply_name = @{const_name comma_crt_apply_shifted_from}
  val apply_type = natT --> natT --> operationT --> columnT --> columnT --> columnT
  val conversion_constants = [apply_name,@{const_name comma_crt_apply},
    @{const_name comma_crt_shift}]
  val zero_name = Axclass.unoverload_const (Proof_Context.theory_of @{context})
    (@{const_name Groups.zero_class.zero},natT)

  datatype column_view = Bool_View of bool | Node_View of int * term list

  fun bool_column value =
    @{term Comma_CRT_Bool} $ (if value then @{term True} else @{term False})

  fun node_column level children =
    Const (@{const_name Comma_CRT_Node},
      natT --> HOLogic.listT columnT --> columnT) $
      HOLogic.mk_number natT level $
      HOLogic.mk_list columnT children

  fun apply_term depth shift operation left right =
    list_comb (Const (apply_name,apply_type),
      [HOLogic.mk_number natT depth, HOLogic.mk_number natT shift,
       operation,left,right])

  fun natural_value term =
    (case try HOLogic.dest_number term of
      SOME (typ,value) => if typ=natT andalso value>=0 then SOME value else NONE
    | NONE =>
        (case Term.strip_comb term of
          (Const (name,typ),[]) =>
            if name=zero_name andalso typ=natT then SOME 0 else NONE
        | (Const (name,_),[previous]) =>
            if name = @{const_name Suc}
            then Option.map (fn value => value+1) (natural_value previous)
            else NONE
        | _ => NONE))

  fun column_view term =
    (case Term.strip_comb term of
      (Const (name,_),[value]) =>
        if name = @{const_name Comma_CRT_Bool}
        then if value aconv @{term True} then SOME (Bool_View true)
          else if value aconv @{term False} then SOME (Bool_View false)
          else NONE
        else NONE
    | (Const (name,_),[level,children]) =>
        if name = @{const_name Comma_CRT_Node}
        then
          (case (natural_value level,try HOLogic.dest_list children) of
            (SOME index,SOME values) => SOME (Node_View (index,values))
          | _ => NONE)
        else NONE
    | _ => NONE)

  fun same_column left right =
    let
      fun same l r =
        (case (column_view l,column_view r) of
          (SOME (Bool_View x),SOME (Bool_View y)) => x=y
        | (SOME (Node_View (level,xs)),SOME (Node_View (other_level,ys))) =>
            level=other_level andalso same_lists xs ys
        | _ => false)
      and same_lists [] [] = true
        | same_lists (x::xs) (y::ys) = same x y andalso same_lists xs ys
        | same_lists _ _ = false
    in same left right end

  fun apply_parts term =
    (case Term.strip_comb term of
      (Const (name,_),[depth,shift,operation,left,right]) =>
        if name=apply_name then SOME (depth,shift,operation,left,right) else NONE
    | _ => NONE)

  fun closed term = not (Term.is_open term) andalso
    null (Term.add_frees term []) andalso null (Term.add_vars term [])

  fun validate_result ctxt label input theorem =
    let
      val lhs=Thm.term_of (Thm.lhs_of theorem)
      val rhs=Thm.term_of (Thm.rhs_of theorem)
      val proposition=Thm.prop_of theorem
      val native=Thm.nprems_of theorem=0 andalso null (Thm.hyps_of theorem)
        andalso null (Thm.tpairs_of theorem) andalso closed proposition
        andalso proposition aconv Logic.mk_equals (input,rhs)
        andalso Context.subthy (Thm.theory_of_thm theorem,
          Proof_Context.theory_of ctxt)
        andalso null (Thm_Deps.all_oracles [theorem])
    in
      if lhs aconv input andalso native then theorem
      else error (label ^ " is not a closed native equation for its exact input")
    end

  fun make_equation_validator ctxt wrong_lhs_seen label lhs rhs theorem =
    if not (Thm.prop_of theorem aconv Logic.mk_equals (lhs,rhs)) then
      (if label="Continue Apply cached equation" then
         wrong_lhs_seen := true else ();
       error (label ^ " proves a different equation"))
    else validate_result ctxt label lhs theorem

  fun parent_entry facts shift operation left right =
    let
      fun matches (key,_) =
        (case apply_parts key of
          SOME (depth,offset,actual_operation,actual_left,actual_right) =>
            natural_value depth=SOME 1 andalso natural_value offset=SOME shift
              andalso actual_operation aconv operation
              andalso same_column actual_left left andalso
              same_column actual_right right
        | NONE => false)
    in
      (case filter matches (Termtab.dest facts) of
        [entry] => entry
      | entries => error ("expected one memoized Apply parent; found " ^
          Int.toString (length entries)))
    end

  fun rhs theorem = Thm.term_of (Thm.rhs_of theorem)

  fun run_conversion ctxt label conversion term =
    validate_result ctxt label term
      (conversion ctxt (Thm.cterm_of ctxt term))

  fun make_context ctxt facts hits misses wrong_lhs_seen =
    let
      val validator=make_equation_validator ctxt wrong_lhs_seen
      val proc=Comma_Semantic_Continue_Column_Proofs.apply_memo_proc
        ctxt facts validator hits misses
      val simpset=Comma_Semantic_Continue_Column_Proofs.column_code_context ctxt proc
      val conversion=Code_Simp.static_conv
        {ctxt=ctxt,simpset=SOME (Simplifier.simpset_of simpset),
         consts=conversion_constants}
    in conversion end

  fun run ctxt =
    let
      val _=Comma_Proof_Profile.report "Continue column smoke stage=start"
      val facts=Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val hits=Unsynchronized.ref 0
      val misses=Unsynchronized.ref 0
      val wrong_lhs_seen=Unsynchronized.ref false
      val memo=make_context ctxt facts hits misses wrong_lhs_seen
      val reference=Code_Simp.static_conv
        {ctxt=ctxt,simpset=NONE,consts=conversion_constants}
      val nested_observer_node=Contract.Continue_Applied
        (Contract.Continue_1,Contract.Continue_Endpoint)
      val nested_observer=Contract.observer_term nested_observer_node
      val fixture_program=Free ("continue_fixture_program",
        @{typ comma_semantic_port_program})
      val zero=HOLogic.mk_number natT 0
      val one_input=Contract.operator_term Contract.Continue_1 $
        nested_observer $ fixture_program $ zero
      val one_expected = @{term comma_continue_operator_step} $
        nested_observer $ fixture_program $ zero
      val one_rewrite=Contract.operator_application_conversion ctxt
        Contract.Continue_1 one_input
      val _=if Thm.term_of (Thm.rhs_of one_rewrite) aconv one_expected then ()
        else error "root-only Continue_1 rewrite unfolded its observer argument"
      val two_input=Contract.operator_term Contract.Continue_2 $
        nested_observer $ fixture_program $ zero
      val two_expected=Contract.operator_term Contract.Continue_1 $
        Contract.observer_term
          (Contract.Continue_Applied
            (Contract.Continue_1,nested_observer_node)) $
        fixture_program $ zero
      val two_rewrite=Contract.operator_application_conversion ctxt
        Contract.Continue_2 two_input
      val _=if Thm.term_of (Thm.rhs_of two_rewrite) aconv two_expected then ()
        else error "root-only Continue_2 rewrite changed its prefix observer"
      val true_column=bool_column true
      val false_column=bool_column false
      fun validate_native label theorem =
        if Thm.nprems_of theorem=0 andalso null (Thm.hyps_of theorem)
            andalso null (Thm.tpairs_of theorem) andalso closed (Thm.prop_of theorem)
        then (Comma_Proof_Dependency_Audit.require_native_clean ctxt label [theorem];
          theorem)
        else error (label ^ " is not a closed native theorem")
      val observer_proofs=Contract.observer_proofs validate_native ctxt
        (Unsynchronized.ref Termtab.empty) nested_observer_node
      val expected_observer_admission=HOLogic.mk_Trueprop
        (@{term comma_continue_observer_admitted} $ nested_observer)
      val expected_observer_matches=HOLogic.mk_Trueprop
        (@{term comma_continue_observer_matches} $ nested_observer $
          Contract.observer_predicate nested_observer_node)
      val _=if Thm.prop_of (#admitted observer_proofs) aconv
          expected_observer_admission andalso
          Thm.prop_of (#matches observer_proofs) aconv expected_observer_matches
        then () else error "specialized observer theorem changed its exact contract"
      val callbacks : Comma_Semantic_Continue_Masked_Columns.callbacks =
        {ctxt=ctxt, validate_native=validate_native,
         validate_equation=make_equation_validator ctxt (Unsynchronized.ref false),
         scalar=fn label => fn term => run_conversion ctxt label memo term,
         evaluate=fn label => fn term => run_conversion ctxt label
           (Code_Simp.static_conv {ctxt=ctxt,simpset=NONE,
             consts=[@{const_name comma_crt_supported}]}) term}
      val true_admitted =
        @{lemma "comma_crt_admitted 0 (Comma_CRT_Bool True)" by simp}
      val false_admitted =
        @{lemma "comma_crt_admitted 0 (Comma_CRT_Bool False)" by simp}
      val certified_true={column=true_column,admitted=true_admitted}
      val certified_false={column=false_column,admitted=false_admitted}
      val prune_callbacks : Comma_Semantic_Continue_Masked_Columns.callbacks =
        {ctxt=ctxt, validate_native=validate_native,
         validate_equation= #validate_equation callbacks,
         scalar=fn _ => fn _ => error "empty-mask pruning evaluated a child",
         evaluate=fn _ => fn _ => error "empty-mask pruning replayed support"}
      val pruned=Comma_Semantic_Continue_Masked_Columns.unsupported_intersection
        prune_callbacks "empty-mask theorem transport" certified_false true_column
        true_admitted @{lemma "\<not>comma_crt_supported (Comma_CRT_Bool False)" by simp}
      val _=if #column pruned aconv false_column then ()
        else error "empty-mask pruning did not publish False"
      val forged={column=false_column,admitted=true_admitted}
      val rejection=Exn.capture (fn () =>
        Comma_Semantic_Continue_Masked_Columns.intersect callbacks
          "mismatched mask admission" forged certified_true) ()
      val _=case rejection of Exn.Exn _ => ()
        | Exn.Res _ => error "a different mask's admission theorem was accepted"
      val retry=Comma_Semantic_Continue_Masked_Columns.intersect callbacks
        "mask retry after rejection" certified_false certified_true
      val _=if #column retry aconv false_column then ()
        else error "failed admission corrupted the subsequent intersection"
      val pullback=Comma_Semantic_Continue_Masked_Columns.pullback_one_tick
        callbacks "exact shifted admission specialization" certified_true certified_true
      val _=validate_native "closed one-tick pullback" (#actual_admitted pullback)
      val _=validate_native "closed one-tick equivalence" (#equivalent pullback)
      val operation = @{term Comma_CRT_And}
      val children=true_column :: replicate 10 false_column
      val node=node_column 3 children
      val huge_shift=1000000000923
      val _=Comma_Proof_Profile.report "Continue column smoke stage=large-clock-start"
      val huge_rotation=run_conversion ctxt "bounded large clock rotation" memo
        (@{term comma_crt_shift} $ HOLogic.mk_number natT huge_shift $ node)
      val residue=huge_shift mod length children
      val expected_rotation=node_column 3
        (drop residue children @ take residue children)
      val _=if same_column (rhs huge_rotation) expected_rotation then ()
        else error "large clock rotation changed its local residue or phase order"
      fun children_for fanout =
        if fanout=0 then []
        else map (fn index => bool_column (index mod 3=0))
          (0 upto (fanout-1))
      fun check_shift_case fanout shift =
        let
          val children=children_for fanout
          val input=node_column 5 children
          val expected_children=if fanout=0 then []
            else let val residue=shift mod fanout
              in drop residue children @ take residue children end
          val expected=node_column 5 expected_children
          val shifted = @{term comma_crt_shift} $
            HOLogic.mk_number natT shift $ input
          val label="fanout " ^ Int.toString fanout ^
            " shift " ^ Int.toString shift
          val memo_result=run_conversion ctxt (label ^ " memo") memo shifted
          val _=if same_column (rhs memo_result) expected then ()
            else error ("CRT shift disagrees with exact cyclic rotation: " ^ label)
        in () end
      fun check_fanout fanout =
        let
          val residues=if fanout=0 then [] else 0 upto (fanout-1)
          val shifts=residues @ [923,1000000000923]
        in List.app (check_shift_case fanout) shifts end
      val _=List.app check_fanout [0,1,3,4,7,11]
      val _=Comma_Proof_Profile.report "Continue column smoke stage=large-clock-done"
      val phase_zero=node_column 0
        [true_column,false_column,false_column,false_column]
      val phase_one=node_column 0
        [false_column,true_column,false_column,false_column]
      fun intersection left right =
        @{term comma_crt_apply} $ operation $ left $ right
      fun shifted amount column =
        @{term comma_crt_shift} $ HOLogic.mk_number natT amount $ column
      val disjoint=run_conversion ctxt "incoming mask prunes supported guard" memo
        (intersection phase_zero phase_one)
      val supported=run_conversion ctxt "compatible mask retains guard" memo
        (intersection phase_one phase_one)
      val _=if same_column (rhs disjoint) false_column andalso
          same_column (rhs supported) phase_one then ()
        else error "incoming mask was omitted from intersection or cache identity"
      fun literal_eval phase column =
        (case column_view column of
          SOME (Bool_View value) => value
        | SOME (Node_View (level,children)) =>
            if level<4 andalso length children=List.nth ([4,3,7,11],level)
            then literal_eval phase
              (List.nth (children,phase mod length children))
            else false
        | NONE => error "independent CRT evaluator received a nonliteral column")
      val late_axis=node_column 3 (true_column :: replicate 10 false_column)
      val mixed_axes=node_column 0
        [late_axis,false_column,true_column,late_axis]
      val proposal_columns=
        [false_column,true_column,phase_zero,phase_one,late_axis,mixed_axes]
      fun check_proposal left right =
        let
          val expected=List.exists (fn phase =>
            literal_eval phase left andalso literal_eval phase right) (0 upto 923)
          val proposed=Comma_Semantic_Continue_Masked_Columns.literal_support_intersection
            left right
        in if proposed=expected then ()
          else error "cofactor support proposal disagrees with independent phase evaluation"
        end
      val _=List.app (fn left => List.app (check_proposal left) proposal_columns)
        proposal_columns
      val pulled_back=run_conversion ctxt "inverse seam mask transport" memo
        (shifted 1 (intersection (shifted 923 phase_zero) true_column))
      val wrong_direction=run_conversion ctxt "reject forward seam mask transport" memo
        (shifted 1 (intersection (shifted 1 phase_zero) true_column))
      val _=if same_column (rhs pulled_back) phase_zero andalso
          not (same_column (rhs wrong_direction) phase_zero) then ()
        else error "seam mask transport lost its inverse clock orientation"
      val guard = @{term "comma_crt_shift 1 (comma_core_value_guard Comma_Core_7 1)"}
      val later_guard = @{term "comma_crt_shift 1 (comma_core_value_guard Comma_Core_7 2)"}
      fun core_choice selected child rest =
        @{term comma_crt_apply} $ @{term Comma_CRT_Or} $
          (@{term comma_crt_apply} $ @{term Comma_CRT_And} $ selected $ child) $ rest
      val fold_term=core_choice guard true_column
        (core_choice later_guard false_column false_column)
      val nested=core_choice guard fold_term false_column
      val _=if Comma_Semantic_Continue_Column_Proofs.is_literal_column fold_term orelse
          Comma_Semantic_Continue_Column_Proofs.is_literal_column nested then
          error "a raw guarded fold escaped the canonical column boundary"
        else ()
      val guard_context = Comma_Semantic_Continue_Column_Proofs.core_guard_context
        (#context (Comma_Semantic_Program_Arithmetic.make ctxt))
      fun with_guard_equations conversion context ct =
        let val guards=Simplifier.rewrite guard_context ct
        in Thm.transitive guards (conversion context (Thm.rhs_of guards)) end
      val selection_code_context=Comma_Semantic_Continue_Column_Proofs.column_code_context
        ctxt (Comma_Semantic_Continue_Column_Proofs.apply_memo_proc ctxt facts
          (make_equation_validator ctxt wrong_lhs_seen) hits misses)
      val selection_conversion=Code_Simp.static_conv
        {ctxt=ctxt,simpset=SOME (Simplifier.simpset_of selection_code_context),
         consts= @{const_name comma_continue_core_guard_union} ::
           @{const_name comma_phase_core_modulus} :: conversion_constants}
      val selection_callbacks : Comma_Semantic_Continue_Masked_Columns.callbacks =
        {ctxt=ctxt,validate_native=validate_native,
         validate_equation= #validate_equation callbacks,
         scalar=fn label => fn term => run_conversion ctxt label
           (with_guard_equations selection_conversion) term,
         evaluate= #evaluate callbacks}
      val zero_admitted= @{lemma
        "comma_crt_admitted 0 (Comma_CRT_Node 0
          [Comma_CRT_Bool True, Comma_CRT_Bool False,
           Comma_CRT_Bool False, Comma_CRT_Bool False])"
        by (simp add: comma_crt_period_def)}
      val one_admitted= @{lemma
        "comma_crt_admitted 0 (Comma_CRT_Node 0
          [Comma_CRT_Bool False, Comma_CRT_Bool True,
           Comma_CRT_Bool False, Comma_CRT_Bool False])"
        by (simp add: comma_crt_period_def)}
      val certified_zero={column=phase_zero,admitted=zero_admitted}
      val certified_one={column=phase_one,admitted=one_admitted}
      val selection_values=0 upto 10
      val _=Comma_Proof_Profile.report "Continue column smoke stage=core-selection-start"
      fun select_fixture label mask =
        (case Comma_Semantic_Continue_Masked_Columns.preselect_core_values
            selection_callbacks label mask @{term Comma_Core_11} 0 selection_values of
          SOME result => result
        | NONE => error (label ^ " rejected a complete core-value partition"))
      val zero_selected=select_fixture "phase-zero core selection" certified_zero
      val one_selected=select_fixture "phase-one core selection" certified_one
      val shifted_selected=Comma_Semantic_Continue_Masked_Columns.preselect_core_values
        selection_callbacks "shifted core selection" certified_zero
        @{term Comma_Core_11} 923 selection_values
      val _=case shifted_selected of
          SOME result => if #allowed result= #allowed one_selected then ()
            else error "core selection dropped its transported clock"
        | NONE => error "shifted core selection rejected complete coverage"
      val _=Comma_Proof_Profile.report "Continue column smoke stage=core-selection-done"
      fun expected_values core values mask =
        filter (fn wanted =>
          let
            val guard= @{term comma_core_value_guard} $ core $
              HOLogic.mk_number natT wanted
            val exact=run_conversion ctxt "independent selected guard"
              (with_guard_equations selection_conversion) guard
          in List.exists (fn phase => literal_eval phase mask andalso
              literal_eval phase (rhs exact)) (0 upto 923) end) values
      val _=if #allowed zero_selected=
          expected_values @{term Comma_Core_11} selection_values phase_zero andalso
          #allowed one_selected=
          expected_values @{term Comma_Core_11} selection_values phase_one andalso
          #allowed zero_selected <> #allowed one_selected then ()
        else error "core preselection lost its phase or disagreed with exact guards"
      val _=Comma_Proof_Profile.report "Continue column smoke stage=selection-oracle-done"
      fun rejects_domain label values proposed =
        (case Exn.capture (fn () =>
          Comma_Semantic_Continue_Masked_Columns.certify_core_preselection
            selection_callbacks label certified_zero @{term Comma_Core_11} 0
            values proposed) () of
          Exn.Exn _ => ()
        | Exn.Res _ => error (label ^ " accepted a malformed core domain"))
      val _=List.app (fn values => rejects_domain "invalid full core range" values [])
        [tl selection_values, rev selection_values, 0::selection_values]
      val _=List.app (rejects_domain "invalid proposed core values" selection_values)
        [[11],[0,0]]
      val stale_guard=Exn.capture (fn () =>
        Comma_Semantic_Continue_Masked_Columns.certify_with_guards
          selection_callbacks "wrong clock guard certificate" certified_zero
          @{term Comma_Core_11} 923 selection_values (#allowed zero_selected)
          (#guards zero_selected)) ()
      val _=case stale_guard of Exn.Exn _ => ()
        | Exn.Res _ => error "an unshifted guard certificate authorized another clock"
      val seventh_column=node_column 2 (true_column::replicate 6 false_column)
      val seventh_admitted= @{lemma
        "comma_crt_admitted 0 (Comma_CRT_Node 2
          [Comma_CRT_Bool True, Comma_CRT_Bool False, Comma_CRT_Bool False,
           Comma_CRT_Bool False, Comma_CRT_Bool False, Comma_CRT_Bool False,
           Comma_CRT_Bool False])" by (simp add: comma_crt_period_def)}
      val seventh_mask={column=seventh_column,admitted=seventh_admitted}
      val multi_axis=Comma_Semantic_Continue_Masked_Columns.preselect_core_values
        selection_callbacks "different-axis core selection" seventh_mask
        @{term Comma_Core_29} 0 (0 upto 28)
      val _=case multi_axis of
          SOME result => if #allowed result=
              expected_values @{term Comma_Core_29} (0 upto 28) seventh_column then ()
            else error "different-axis core selection changed phase support"
        | NONE => error "different-axis core selection rejected full coverage"
      val _=Comma_Proof_Profile.report "Continue column smoke stage=multi-axis-done"
      fun rejected_coverage label mask proposed =
        (case Comma_Semantic_Continue_Masked_Columns.certify_core_preselection
            selection_callbacks label mask @{term Comma_Core_11} 0
            selection_values proposed of
          NONE => ()
        | SOME _ => error (label ^ " granted authority to an incomplete partition"))
      val _=rejected_coverage "empty core partition" certified_true []
      val _=rejected_coverage "foreign phase core partition" certified_one
        (#allowed zero_selected)
      val selection_retry=select_fixture "selection retry after rejection" certified_one
      val _=if #allowed selection_retry= #allowed one_selected then ()
        else error "failed coverage left stale selection state"
      val _=Comma_Proof_Profile.report "Continue column smoke stage=selection-rejections-done"
      val fold_result=run_conversion ctxt "complete core fold"
        (with_guard_equations memo) fold_term
      val fold_reference=run_conversion ctxt "independent complete core fold"
        (with_guard_equations reference) fold_term
      val guard_reference=run_conversion ctxt "selected core guard"
        (with_guard_equations reference) guard
      val _=if same_column (rhs fold_result) (rhs fold_reference) andalso
          same_column (rhs fold_result) (rhs guard_reference) then ()
        else error "batched core fold changed exact phase support"
      val equality=Const (@{const_name HOL.equal},
        columnT --> columnT --> HOLogic.boolT)
      val malformed=node_column 3 []
      val malformed_other=node_column 3 [false_column]
      val reflexive_term=equality $ malformed $ malformed
      val reflexive=run_conversion ctxt "malformed column reflexivity" memo reflexive_term
      val different_term=equality $ malformed $ malformed_other
      val different=run_conversion ctxt "distinct malformed columns" memo different_term
      val different_reference=run_conversion ctxt "independent malformed comparison"
        reference different_term
      val _=if rhs reflexive aconv @{term True} andalso
          rhs different aconv @{term False} andalso
          rhs different aconv rhs different_reference then ()
        else error "column reflexivity changed unequal comparison or required admission"
      val cold_term=apply_term 1 1 operation true_column node
      val cold=run_conversion ctxt "cold memo conversion" memo cold_term
      val independent=run_conversion ctxt "independent cold reference"
        reference cold_term
      val cold_key=parent_entry (!facts) 1 operation true_column node |> #1
      val cold_equation=the (Termtab.lookup (!facts) cold_key)
      val _=validate_result ctxt "cached cold parent" cold_key cold_equation
      val _=if same_column (rhs cold) (rhs independent) andalso
          same_column (rhs cold) (rhs cold_equation) then ()
        else error "cold memo conversion differs from the independent code result"
      val hits_before_warm= !hits
      val warm=run_conversion ctxt "warm memo conversion" memo cold_term
      val _=if same_column (rhs warm) (rhs cold) andalso
          !hits>hits_before_warm then ()
        else error "same Apply request did not reuse its checked equation"

      val zero_term=apply_term 1 0 operation true_column node
      val zero=run_conversion ctxt "zero-shift conversion" memo zero_term
      val zero_reference=run_conversion ctxt "independent zero-shift reference"
        reference zero_term
      val zero_key=parent_entry (!facts) 0 operation true_column node |> #1
      val zero_equation=the (Termtab.lookup (!facts) zero_key)
      val _=validate_result ctxt "cached zero-shift parent" zero_key zero_equation
      val _=if not (cold_key aconv zero_key) andalso
          same_column (rhs zero) (rhs zero_reference) andalso
          not (same_column (rhs zero) (rhs cold)) then ()
        else error "different shifts aliased an Apply cache entry or result"

      val wrong_equation=zero_equation
      val _=if not (Thm.term_of (Thm.lhs_of wrong_equation) aconv cold_key) then ()
        else error "poison fixture unexpectedly has the target Apply left-hand side"
      val _=facts := Termtab.update (cold_key,wrong_equation) (!facts)
      val _=wrong_lhs_seen := false
      val poisoned=Exn.capture
        (fn () => run_conversion ctxt "poisoned cache request" memo cold_term) ()
      val _=case poisoned of
        Exn.Exn _ => if !wrong_lhs_seen then ()
          else error "poisoned cache did not fail at exact equation validation"
      | Exn.Res _ => error "poisoned cache equation was accepted"
      val _=facts := Termtab.update (cold_key,cold_equation) (!facts)
      val hits_before_retry= !hits
      val retry=run_conversion ctxt "retry after cache exception" memo cold_term
      val _=if same_column (rhs retry) (rhs cold) andalso
          !hits>hits_before_retry then ()
        else error "failed request left stale active state or unusable cache state"

      val bounded_facts=Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val bounded_hits=Unsynchronized.ref 0
      val bounded_misses=Unsynchronized.ref 0
      val bounded_context=make_context ctxt bounded_facts bounded_hits
        bounded_misses (Unsynchronized.ref false)
      val bounded_term=apply_term 5 0 operation false_column node
      val bounded_result=run_conversion ctxt "bounded decline conversion"
        bounded_context bounded_term
      val bounded_reference=run_conversion ctxt "independent bounded reference"
        reference bounded_term
      fun is_over_bound (key,_) =
        (case apply_parts key of
          SOME (depth,_,_,_,_) =>
            (case natural_value depth of SOME value => value>4 | NONE => false)
        | NONE => false)
      val _=if same_column (rhs bounded_result) (rhs bounded_reference) andalso
          not (exists is_over_bound (Termtab.dest (!bounded_facts))) then ()
        else error "bounded Apply request was memoized or changed its code result"
    in () end
end
