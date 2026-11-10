(* The source-bound 46-class instance.  Data construction is untrusted until
   the source-root, shallow shift, joint rank and indexed HOL certificates
   below all check in the current local-theory context. *)
structure Comma_Semantic_Phase_Class_Rank_Instance =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data
  structure Source = Comma_Semantic_Phase_Action_Program_Compiler
  structure Source_Certificate = Comma_Semantic_Phase_Action_Program_Certificate
  structure State_Certificate = Comma_Semantic_Phase_Action_State_Certificate
  structure Candidate = Comma_Semantic_Phase_Class_Rank_Candidate
  structure Shift = Comma_Semantic_Phase_Class_Rank_Shift_Certificate
  structure Joint = Comma_Semantic_Phase_Class_Rank_Relation_Compiler
  structure Shallow = Comma_Semantic_Weighted_CRT_Shallow_Certificate
  structure Transport = Comma_Semantic_Weighted_CRT_Data_Transport
  structure Certificate = Comma_Semantic_Phase_Class_Rank_Certificate

  structure Path_Table = Table
  (
    type key = (int * int) list
    val ord = list_ord (prod_ord int_ord int_ord)
  )

  val natT = @{typ nat}
  val actionT = @{typ comma_phase_rank_mask_action}
  val rankT = @{typ "nat comma_semantic_weighted_crt_dag"}
  val actionTreeT = @{typ
    "comma_phase_rank_mask_action comma_semantic_weighted_crt_dag"}

  fun nat n = HOLogic.mk_number natT n
  fun checked ctxt label proposition theorem =
    Transport.checked_closed ctxt label (HOLogic.mk_Trueprop proposition) theorem

  fun prove ctxt label proposition rules =
    let
      val theorem = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop proposition)
        (fn {context,...} => HEADGOAL (asm_full_simp_tac
          (Simplifier.add_simps rules
            (Transport.arithmetic_context context))))
    in checked ctxt label proposition theorem end

  fun root_sources ctxt =
    let
      val context = Simplifier.add_simps
        @{thms comma_offset_representatives_def} ctxt
      val reduction = Simplifier.rewrite context
        (Thm.cterm_of context @{term comma_offset_representatives})
      val checked_reduction = Transport.checked_closed ctxt
        "Canonical 46 source representatives"
        (Thm.prop_of reduction) reduction
      val representatives = HOLogic.dest_list
        (Thm.term_of (Thm.rhs_of checked_reduction))
      val entry = @{term "Comma_Entry 1 0"}
      val _ = if length representatives=46 then ()
        else error "Canonical phase-class domain has the wrong cardinality"
    in map (fn offset => entry $ offset) representatives end

  fun rank_list roots = HOLogic.mk_list rankT roots
  fun action_list roots = HOLogic.mk_list actionTreeT roots

  fun successor_function ranks =
    Term.betapply
      (@{term "\<lambda>(ranks::nat comma_semantic_weighted_crt_dag list) child.
        if child<46 then Some (comma_weighted_crt_shift 1 (ranks!child))
        else None"}, ranks)

  fun indexed_rows ctxt label expression facts =
    prove ctxt label expression
      (facts @ @{thms list_all_Nil_iff list_all_Cons_iff
        upt_rec nth_Cons' list.size})

  fun row_from_fact ctxt label expression facts =
    prove ctxt label expression
      (facts @ @{thms nth_Cons' comma_offset_representatives_def
        list.size list.map upt_rec})

  fun make initial_lthy =
    let
      val initial_ctxt = Local_Theory.target_of initial_lthy
      val arena = Data.make_arena 8192
      val sources = root_sources initial_ctxt
      val (_,lthy) = Candidate.with_shallow_transaction arena initial_lthy
        (fn transaction => let
      val action_publisher = Candidate.make_shallow_publisher transaction
        actionT "comma_phase_action"
      val state_certifier = State_Certificate.make_state_certifier
        initial_ctxt arena transaction action_publisher
      val compiled = Source.make initial_ctxt arena sources state_certifier
      val candidate = Candidate.construct_and_define_with_publisher
        transaction action_publisher (#roots compiled)
      val lthy = Candidate.current_local_theory transaction
      val ctxt = Local_Theory.target_of lthy
      val action_diagrams = #action_diagrams candidate
      val rank_diagrams = #rank_diagrams candidate
      val action_roots = #action_roots candidate
      val rank_roots = #rank_roots candidate
      val _ = if length action_diagrams=46 andalso
          length rank_diagrams=46 andalso length action_roots=46 andalso
          length rank_roots=46 then ()
        else error "Published phase-class roots lost canonical order"
      val (action_terms,action_roots_definition) =
        Candidate.define_in_shallow_transaction transaction
          (Binding.name "comma_semantic_phase_class_rank_action_roots")
          (action_list action_roots)
      val lthy = Candidate.current_local_theory transaction
      val ctxt = Local_Theory.target_of lthy
      val source_certificate = Source_Certificate.finish_roots ctxt arena compiled
        action_diagrams (#action_lookup candidate)
      val _ = if length (#root_apply_exactness source_certificate)=46 then ()
        else error "Source certificate did not cover all 46 action roots"
      val rank_terms = rank_list rank_roots
      val successors = successor_function rank_terms
      val action_shallow = Shallow.make ctxt arena actionT
        {lookup= #action_lookup candidate,ensure_named=NONE}
      val rank_shallow = Shallow.make ctxt arena natT
        {lookup= #rank_lookup candidate,ensure_named=NONE}
      fun required_rank_node diagram =
        (case #rank_lookup candidate diagram of
          SOME node => node
        | NONE => error "Rank shift refers to an unpublished node")
      val shift_certifier = Shift.make ctxt arena required_rank_node
      val shifted = Inttab.make (map (fn (child,diagram,_) =>
        (child,diagram)) (#shifted_rank_roots candidate))
      val shifted_facts = Inttab.make (map (fn (child,diagram,_) =>
        (child,#certify shift_certifier
          (List.nth (rank_diagrams,child)) diagram))
        (#shifted_rank_roots candidate))

      fun shifted_root child =
        (case Inttab.lookup shifted child of
          SOME diagram => diagram
        | NONE => error "Continue requested an unpublished shifted rank root")
      fun shifted_fact child =
        (case Inttab.lookup shifted_facts child of
          SOME theorem => theorem
        | NONE => error "Continue requested an uncertified rank shift")

      fun restrict path root =
        fold (fn (axis,slot) => fn (diagram,equations) =>
          let val result = #cofactor rank_shallow diagram axis slot
          in (#result result,#equation result :: equations) end)
          path (root,[])
      fun target_view path child = #1 (restrict path (shifted_root child))
      fun successors_at path =
        fold (fn (axis,slot) => fn prior =>
          Joint.pull_successors axis slot prior) path successors

      fun leaf_equations path action =
        let
          val child = (case Data.view arena action of
              Data.View_Leaf {offset=0,payload} =>
                (case Candidate.action_label payload of
                  Candidate.Continue child => child
                | _ => error "A terminal leaf requested a successor equation")
            | _ => error "A nonleaf requested a successor equation")
          val (target,equations) = restrict path (shifted_root child)
          val named = #named rank_shallow target
          val chosen = successors_at path $ nat child
          val some = Const (@{const_name Some},rankT -->
            Type (@{type_name option}, [rankT])) $ #term named
          val proposition = HOLogic.mk_eq (chosen,some)
          val checked_equation = prove ctxt "Selected Continue target"
            proposition (shifted_fact child :: rev equations @
              @{thms option.simps map_option_case fst_conv snd_conv
                nth_Cons' list.size})
        in [checked_equation] end

      val rank_shape_facts = map (fn diagram =>
        #shape rank_shallow diagram 0) rank_diagrams
      val rank_shape_rows = indexed_rows ctxt "Rank-root shape rows"
        (Term.betapply (@{term
          "\<lambda>(ranks::nat comma_semantic_weighted_crt_dag list).
            list_all (\<lambda>cid. comma_weighted_crt_shape 0 (ranks!cid))
              [0..<46]"},rank_terms)) rank_shape_facts
      val action_shape_facts = map (fn diagram =>
        #shape action_shallow diagram 0) action_diagrams
      val ranks_length = prove ctxt "Rank-root vector length"
        (HOLogic.mk_eq
          (@{term "length :: nat comma_semantic_weighted_crt_dag list \<Rightarrow> nat"} $
            rank_terms,nat 46)) @{thms list.size}
      val root_successor_shape =
        let
          val rule = @{thm comma_crt_rank_successor_shape}
            OF [ranks_length,rank_shape_rows]
        in rule end
      val shape_cache = Unsynchronized.ref
        (Path_Table.update ([],root_successor_shape) Path_Table.empty)
      fun successor_shape path =
        (case Path_Table.lookup (!shape_cache) path of
          SOME theorem => theorem
        | NONE =>
            let
              val prefix = take (length path-1) path
              val (axis,slot) = List.last path
              val prior = successor_shape prefix
              val source = successors_at prefix
              val rule = Drule.infer_instantiate ctxt
                [( ("axis",0),Thm.cterm_of ctxt (nat axis)),
                 ( ("slot",0),Thm.cterm_of ctxt (nat slot)),
                 ( ("successors",0),Thm.cterm_of ctxt source)]
                @{thm comma_crt_rank_successor_shape_cofactor}
              val axis_fact = prove ctxt "CRT successor axis bound"
                (HOLogic.mk_binrel @{const_name less} (nat axis,nat 4)) []
              val slot_fact = prove ctxt "CRT successor slot bound"
                (HOLogic.mk_binrel @{const_name less} (nat slot,
                  @{term comma_crt_axis_radix} $ nat axis))
                @{thms comma_crt_axis_radix_def}
              val theorem = rule OF [axis_fact,slot_fact,prior]
              val _ = shape_cache := Path_Table.update (path,theorem)
                (!shape_cache)
            in theorem end)

      val relation_compiler = Joint.make ctxt arena successors
        {action_named= #named action_shallow,
         rank_named= #named rank_shallow,
         action_shape= #shape action_shallow,
         rank_shape= #shape rank_shallow,
         action_cofactor= #cofactor action_shallow,
         rank_cofactor= #cofactor rank_shallow,
         target_view=target_view,leaf_equations=leaf_equations,
         successor_shape=successor_shape}
      val root_relations = map2 (fn action => fn rank =>
        #certify relation_compiler action rank)
        action_diagrams rank_diagrams
      val _ = if length root_relations=46 then ()
        else error "Joint relation certificate omitted a source class"
      val _ = #audit relation_compiler "All 46 joint rank roots"
        root_relations
      val _ = #audit shift_certifier "Selected successor rank shifts"
        (map #2 (Inttab.dest shifted_facts))

      val exact_row = @{term
        "\<lambda>(actions::comma_phase_rank_mask_action
          comma_semantic_weighted_crt_dag list) cid.
          \<forall>phase<924.
            comma_weighted_crt_apply (0,actions!cid) phase =
              Some (comma_rank_mask_action_of_b1_result
                (comma_semantic_b1_round_output phase
                  (Comma_Entry 1 0 (comma_offset_representatives!cid))),0)"}
      val relation_row = @{term
        "\<lambda>(actions::comma_phase_rank_mask_action
          comma_semantic_weighted_crt_dag list)
          (ranks::nat comma_semantic_weighted_crt_dag list) cid.
          \<forall>phase. comma_crt_rank_relation (actions!cid) (ranks!cid)
            (\<lambda>child. if child<46 then
              Some (comma_weighted_crt_shift 1 (ranks!child)) else None)
            phase"}
      val source_rows = map_index (fn (index,theorem) =>
        row_from_fact ctxt "Exact source class row"
          (Term.betapply (Term.betapply (exact_row,action_terms),nat index))
          [theorem,#source_order source_certificate,action_roots_definition])
        (#root_apply_exactness source_certificate)
      val relation_rows = map_index (fn (index,theorem) =>
        row_from_fact ctxt "Rank relation class row"
          (Term.betapply
            (Term.betapply (Term.betapply
              (relation_row,action_terms),rank_terms),nat index))
          [theorem,action_roots_definition]) root_relations
      fun indexed_predicate row =
        Const (@{const_name list_all},
          (natT --> HOLogic.boolT) --> HOLogic.listT natT -->
            HOLogic.boolT) $ row $
          (HOLogic.mk_list natT (map nat (0 upto 45)))
      val exact_rows = indexed_rows ctxt "All source-action rows"
        (indexed_predicate (Term.betapply (exact_row,action_terms)))
        source_rows
      val action_shape_row = @{term
        "\<lambda>(actions::comma_phase_rank_mask_action
          comma_semantic_weighted_crt_dag list) cid.
          comma_weighted_crt_shape 0 (actions!cid)"}
      val action_shape_rows = map_index (fn (index,theorem) =>
        row_from_fact ctxt "Source action shape row"
          (Term.betapply
            (Term.betapply (action_shape_row,action_terms),nat index))
          [theorem,action_roots_definition]) action_shape_facts
      val all_action_shape_rows = indexed_rows ctxt
        "All source action shape rows"
        (indexed_predicate (Term.betapply (action_shape_row,action_terms)))
        action_shape_rows
      val action_roots_length = prove ctxt "Source action root vector length"
        (HOLogic.mk_eq
          (@{term "length :: comma_phase_rank_mask_action
            comma_semantic_weighted_crt_dag list \<Rightarrow> nat"} $
            action_terms,nat 46)) (action_roots_definition :: @{thms list.size})
      val relations_rows = indexed_rows ctxt "All rank-relation rows"
        (indexed_predicate
          (Term.betapply (Term.betapply
            (relation_row,action_terms),rank_terms))) relation_rows
      val exact = prove ctxt "Exact class action from source roots"
        (Term.betapply (@{term
          "\<lambda>(actions::comma_phase_rank_mask_action
            comma_semantic_weighted_crt_dag list).
            \<forall>phase cid. phase<924 \<longrightarrow> cid<46 \<longrightarrow>
              (\<exists>move. comma_crt_payload (actions!cid) phase=Some move
                \<and> comma_phase_rank_mask_lift phase move =
                  comma_semantic_phase_class_step phase cid)"},action_terms))
        [exact_rows,@{thm comma_phase_class_exact_from_root_apply_rows}]
      val relations = prove ctxt "All class rank relations"
        (Term.betapply (Term.betapply (@{term
          "\<lambda>(actions::comma_phase_rank_mask_action
            comma_semantic_weighted_crt_dag list)
            (ranks::nat comma_semantic_weighted_crt_dag list).
            \<forall>phase cid. phase<924 \<longrightarrow> cid<46 \<longrightarrow>
              comma_crt_rank_relation (actions!cid) (ranks!cid)
                (\<lambda>child. if child<46 then
                  Some (comma_weighted_crt_shift 1 (ranks!child)) else None)
                phase"},action_terms),rank_terms))
        [relations_rows,@{thm comma_phase_class_relation_from_root_rows}]
      val rank_shapes = prove ctxt "All class rank shapes"
        (Term.betapply (@{term
          "\<lambda>(ranks::nat comma_semantic_weighted_crt_dag list).
            \<forall>cid. cid<46 \<longrightarrow>
              comma_weighted_crt_shape 0 (ranks!cid)"},rank_terms))
        [rank_shape_rows,@{thm comma_phase_class_rank_shape_from_root_rows}]
      val rank_check = Certificate.certify ctxt
        {relations=relations,rank_shapes=rank_shapes,exact_action=exact}
      val _ = Transport.checked_closed ctxt "Exact source-class rank check"
        (Thm.prop_of rank_check) rank_check
      val bounded_rule = @{thm comma_crt_rank_relations_sound(2)} OF
        [Object_Logic.rulify ctxt relations,
         Object_Logic.rulify ctxt rank_shapes,
         Object_Logic.rulify ctxt exact]
      val bounded_prop = Term.betapply (@{term
        "\<lambda>(ranks::nat comma_semantic_weighted_crt_dag list).
          \<forall>phase cid. comma_semantic_phase_class_valid phase cid
            \<longrightarrow> comma_crt_rank_at ranks phase cid\<le>26"},rank_terms)
      val bounded = Goal.prove ctxt [] []
        (HOLogic.mk_Trueprop bounded_prop)
        (fn {context,...} =>
          HEADGOAL (resolve_tac context [@{thm allI}]) THEN
          HEADGOAL (resolve_tac context [@{thm allI}]) THEN
          HEADGOAL (resolve_tac context [@{thm impI}]) THEN
          HEADGOAL (resolve_tac context [bounded_rule]))
      val bounded = checked ctxt "Bounded exact source-class rank"
        bounded_prop bounded
      val noted = Candidate.note_in_shallow_transaction transaction
        (Binding.name "comma_semantic_phase_class_rank_check_instance") [rank_check]
      val _ = if length noted=1 then ()
        else error "The exact rank theorem was not published"
      val bounds = Candidate.note_in_shallow_transaction transaction
        (Binding.name "comma_semantic_phase_class_rank_bound_instance") [bounded]
      val _ = if length bounds=1 then ()
        else error "The bounded rank theorem was not published"
      val source_rows_note = Candidate.note_in_shallow_transaction transaction
        (Binding.name "comma_semantic_phase_class_rank_source_apply_rows")
        [exact_rows]
      val _ = if length source_rows_note=1 then ()
        else error "Source action apply rows were not published"
      val shape_rows_note = Candidate.note_in_shallow_transaction transaction
        (Binding.name "comma_semantic_phase_class_rank_source_shape_rows")
        [all_action_shape_rows]
      val _ = if length shape_rows_note=1 then ()
        else error "Source action shape rows were not published"
      val roots_length_note = Candidate.note_in_shallow_transaction transaction
        (Binding.name "comma_semantic_phase_class_rank_action_roots_length")
        [action_roots_length]
      val _ = if length roots_length_note=1 then ()
        else error "Source action root length was not published"
       in () end)
    in lthy end
end
