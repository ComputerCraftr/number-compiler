(* Small independent shallow-node fixtures; no source/B32 authority is issued. *)
structure Comma_Weighted_CRT_Shallow_Fixture =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data
  structure Certificate = Comma_Semantic_Weighted_CRT_Shallow_Certificate
  structure Names = Table
  (
    type key = Data.identity
    val ord = Data.identity_ord
  )

  fun read_only_owner lookup = {lookup=lookup,ensure_named=NONE}

  fun literal_term arena diagram =
    let
      val treeT = @{typ "nat comma_semantic_weighted_crt_dag"}
      val edgeT = HOLogic.mk_prodT (@{typ nat},treeT)
      fun nat n = HOLogic.mk_number @{typ nat} n
    in case Data.view arena diagram of
      Data.View_Leaf {payload={value,...},...} =>
        Const (@{const_name Comma_Weighted_CRT_Leaf},@{typ nat} --> treeT) $ value
    | Data.View_Branch {axis,children,...} =>
        Const (@{const_name Comma_Weighted_CRT_Branch},
          @{typ nat} --> HOLogic.listT edgeT --> treeT) $ nat axis $
          HOLogic.mk_list edgeT (map (fn (weight,child) =>
            HOLogic.mk_prod (nat weight,literal_term arena child)) children)
    end

  fun literal_fallback ctxt arena previous diagram =
    (case previous diagram of
      SOME entry => SOME entry
    | NONE =>
        let
          val term = literal_term arena diagram
        in SOME {term=term,definition=Thm.reflexive (Thm.cterm_of ctxt term)} end)

  fun rejects label operation =
    (case Exn.capture operation () of
      Exn.Exn (ERROR _) => ()
    | Exn.Exn failure => Exn.reraise failure
    | Exn.Res _ => error ("Shallow certificate accepted " ^ label))

  fun run ctxt =
    let
      val _ = Comma_Proof_Profile.report "Shallow fixture stage=model-start"
      val arena = Data.make_arena 128
      val treeT = @{typ "nat comma_semantic_weighted_crt_dag"}
      val edgeT = HOLogic.mk_prodT (@{typ nat},treeT)
      fun nat n = HOLogic.mk_number @{typ nat} n
      fun leaf n =
        let
          val diagram = Data.leaf arena
            {key="shallow-fixture:" ^ Int.toString n,value=nat n}
          val term = Const (@{const_name Comma_Weighted_CRT_Leaf},
            @{typ nat} --> treeT) $ nat n
        in (diagram,{term=term,definition=Thm.reflexive (Thm.cterm_of ctxt term)}) end
      val children = map leaf [0,1,2,3]
      val root = Data.raw_branch arena 0 (map (fn (child,_) => (0,child)) children)
      val root_term = Const (@{const_name Comma_Weighted_CRT_Branch},
        @{typ nat} --> HOLogic.listT edgeT --> treeT) $ nat 0 $
        HOLogic.mk_list edgeT (map (fn (_,entry) =>
          HOLogic.mk_prod (nat 0,#term entry)) children)
      val root_entry = {term=root_term,
        definition=Thm.reflexive (Thm.cterm_of ctxt root_term)}
      val entries = (root,root_entry) :: children
      val names = fold (fn (diagram,entry) =>
        Names.update (Data.identity arena diagram,entry)) entries Names.empty
      fun lookup diagram = literal_fallback ctxt arena
        (fn value => Names.lookup names (Data.identity arena value)) diagram
      val factory = Certificate.make ctxt arena @{typ nat} (read_only_owner lookup)
      val _ = Comma_Proof_Profile.report "Shallow fixture stage=shape-start"
      val _ = #shape factory root 0
      val _ = Comma_Proof_Profile.report "Shallow fixture stage=shape-done"
      val _ = Comma_Proof_Profile.report "Shallow fixture stage=cofactor-start"
      val selected = #cofactor factory root 0 2
      val _ = Comma_Proof_Profile.report "Shallow fixture stage=cofactor-done"
      val _ = if Data.same_action arena (#result selected) (#1 (List.nth (children,2)))
        then () else error "Shallow cofactor selected the wrong column"
      val _ = Comma_Proof_Profile.report "Shallow fixture stage=positive-done"
      val stats = #stats factory ()
      val retained = Data.stats arena
      val _ = #cofactor factory root 0 2
      val _ = if #stats factory ()=stats andalso Data.stats arena=retained then ()
        else error "Shallow proof hit reconstructed its selected child"
      val _ = if #serialization_node_visits retained=0 then ()
        else error "Shallow certificates serialized a recursive tree"
      val ordered_children = map #1 children
      val bind_result = #named_bind factory 0 ordered_children root
      fun closed theorem =
        Thm.nprems_of theorem=0 andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem) andalso
        null (Term.add_frees (Thm.prop_of theorem) []) andalso
        null (Thm_Deps.all_oracles [theorem]) andalso
        not (Thm_Deps.has_skip_proof [theorem])
      fun same_theorems (left,right) = length left=length right andalso
        ListPair.allEq (fn (a,b) => Thm.eq_thm (a,b)) (left,right)
      val _ = if length (#children bind_result)=4 andalso
          length (#apply_slots bind_result)=4 andalso
          List.all closed (#apply_slots bind_result) then ()
        else error "Named selector/bind apply slots are not closed checked results"
      val bind_stats = #stats factory ()
      val bind_data_stats = Data.stats arena
      val bind_view_stats = Data.view_stats arena
      val repeated_bind = #named_bind factory 0 ordered_children root
      val repeated_stats = #stats factory ()
      val repeated_view_stats = Data.view_stats arena
      val _ = if same_theorems (#apply_slots bind_result,#apply_slots repeated_bind) andalso
          #named_bind_builds repeated_stats = #named_bind_builds bind_stats andalso
          #named_bind_hits repeated_stats = #named_bind_hits bind_stats + 1 andalso
          #zero_weight_checks repeated_stats = #zero_weight_checks bind_stats andalso
          #zero_weight_nodes repeated_stats = #zero_weight_nodes bind_stats andalso
          Data.stats arena=bind_data_stats andalso
          repeated_view_stats=bind_view_stats
        then () else error "Named bind memo hit rediscovered its checked child DAG"
      val _ = rejects "reordered named bind children" (fn () =>
        #named_bind factory 0 [#1 (List.nth (children,1)),
          #1 (List.nth (children,0)),#1 (List.nth (children,2)),
          #1 (List.nth (children,3))] root)
      val foreign_bind_arena = Data.make_arena 8
      val foreign_bind_child = Data.leaf foreign_bind_arena
        {key="foreign-bind-child",value=nat 0}
      val _ = rejects "a foreign named bind child" (fn () =>
        #named_bind factory 0
          [foreign_bind_child,#1 (List.nth (children,1)),
            #1 (List.nth (children,2)),#1 (List.nth (children,3))] root)
      val nonzero_edge_root = Data.raw_branch arena 0
        (map_index (fn (slot,child) => (if slot=2 then 1 else 0,child))
          ordered_children)
      val nonzero_root = Data.with_offset arena 1 root
      val _ = rejects "a named bind with a nonzero edge weight" (fn () =>
        #named_bind factory 0 ordered_children nonzero_edge_root)
      val _ = rejects "a named bind with a nonzero root weight" (fn () =>
        #named_bind factory 0 ordered_children nonzero_root)

      (* Scoped proof caches use the small single-axis fixture and nested
         reservations, matching the compiler's Goto-root ownership. *)
      val scoped_factory = Certificate.make ctxt arena @{typ nat}
        (read_only_owner lookup)
      val scoped_before = Data.stats arena
      val scoped_builds_before = #named_bind_builds (#stats scoped_factory ())
      val scoped_hits_before = #named_bind_hits (#stats scoped_factory ())
      val _ = Data.with_reservation arena (fn outer_reservation =>
        let
          val outer = #begin_scope scoped_factory outer_reservation
          val outer_result = #named_bind scoped_factory 0 ordered_children root
          val _ = if List.all closed (#apply_slots outer_result) then ()
            else error "Outer scoped named bind apply slots did not close"
          val _ = Data.with_reservation arena (fn inner_reservation =>
            let
              val inner = #begin_scope scoped_factory inner_reservation
              val inner_result = #named_bind scoped_factory 0 ordered_children root
              val _ = if List.all closed (#apply_slots inner_result) then ()
                else error "Nested scoped named bind apply slots did not close"
              val _ = #end_scope scoped_factory inner
            in () end)
          val restored = #named_bind scoped_factory 0 ordered_children root
          val _ = if same_theorems (#apply_slots outer_result,#apply_slots restored) then ()
            else error "Nested scope failed to restore its parent cache"
          val _ = #end_scope scoped_factory outer
        in () end)
      fun scoped_bind_once () = Data.with_reservation arena
        (fn reservation => let
          val token = #begin_scope scoped_factory reservation
          val result = #named_bind scoped_factory 0 ordered_children root
          val _ = if List.all closed (#apply_slots result) then ()
            else error "Root-scoped named bind apply slots did not close"
          val _ = #end_scope scoped_factory token
        in () end)
      val _ = scoped_bind_once ()
      val _ = scoped_bind_once ()
      val scoped_after = Data.stats arena
      val scoped_builds_after = #named_bind_builds (#stats scoped_factory ())
      val scoped_hits_after = #named_bind_hits (#stats scoped_factory ())
      val _ = if #proof_entries scoped_after = #proof_entries scoped_before andalso
          #scratch_entries scoped_after = #scratch_entries scoped_before andalso
          scoped_builds_after = scoped_builds_before + 4 andalso
          scoped_hits_after = scoped_hits_before + 1 then ()
        else error "Per-root Shallow proof caches escaped their scope"
      val expired_scope_before = Data.stats arena
      val expired_builds_before = #named_bind_builds (#stats scoped_factory ())
      val expired_token = Data.with_reservation arena (fn reservation =>
        let
          val token = #begin_scope scoped_factory reservation
          val _ = #named_bind scoped_factory 0 ordered_children root
        in token end)
      val expired_scope_after = Data.stats arena
      val _ = if #scratch_entries expired_scope_after =
          #scratch_entries expired_scope_before then ()
        else error "Expired shallow cache reservation retained scratch"
      val _ = rejects "a warm cache hit after its reservation expired" (fn () =>
        #named_bind scoped_factory 0 ordered_children root)
      val _ = #end_scope scoped_factory expired_token
      val expired_scope_closed = Data.stats arena
      val expired_builds_after = #named_bind_builds (#stats scoped_factory ())
      val _ = if expired_builds_after = expired_builds_before + 1 andalso
          #proof_entries expired_scope_closed = #proof_entries expired_scope_before
          andalso #scratch_entries expired_scope_closed =
            #scratch_entries expired_scope_before then ()
        else error "Expired shallow cache hit changed proof work or leaked its scope"
      val failed_scope_before = Data.stats arena
      val _ = Data.with_reservation arena (fn reservation =>
        let
          val token = #begin_scope scoped_factory reservation
          val _ = rejects "swapped children inside a shallow cache scope" (fn () =>
            #named_bind scoped_factory 0
              [#1 (List.nth (children,1)),#1 (List.nth (children,0)),
               #1 (List.nth (children,2)),#1 (List.nth (children,3))] root)
          val _ = #end_scope scoped_factory token
        in () end)
      val failed_scope_after = Data.stats arena
      val _ = if #proof_entries failed_scope_after = #proof_entries failed_scope_before
          andalso #scratch_entries failed_scope_after = #scratch_entries failed_scope_before
        then () else error "Failed scoped proof work escaped its owner"
      val token_checks = Data.with_reservation arena (fn reservation =>
        let
          val outer = #begin_scope scoped_factory reservation
          val inner = #begin_scope scoped_factory reservation
          val _ = rejects "an out-of-order shallow scope close" (fn () =>
            #end_scope scoped_factory outer)
          val _ = #end_scope scoped_factory inner
          val _ = rejects "a reclosed shallow scope token" (fn () =>
            #end_scope scoped_factory inner)
          val foreign_factory = Certificate.make ctxt arena @{typ nat}
            (read_only_owner lookup)
          val foreign = #begin_scope foreign_factory reservation
          val _ = rejects "a foreign shallow scope token" (fn () =>
            #end_scope scoped_factory foreign)
          val _ = #end_scope foreign_factory foreign
          val _ = #end_scope scoped_factory outer
        in outer end)
      val _ = rejects "a reclosed shallow scope after owner exit" (fn () =>
        #end_scope scoped_factory token_checks)
      val _ = Data.with_reservation foreign_bind_arena (fn reservation =>
        rejects "a foreign shallow scope reservation" (fn () =>
          #begin_scope scoped_factory reservation))
      val token_scope_stats = Data.stats arena
      val _ = if #proof_entries token_scope_stats = #proof_entries scoped_after andalso
          #scratch_entries token_scope_stats = #scratch_entries scoped_after then ()
        else error "Scope token rejection leaked its reservation"

      (* Exercise a parent bind whose normal form begins at an earlier axis,
         a collapsed parent selector, and a repeated axis cofactor. *)
      val multi_arena = Data.make_arena 512
      fun multi_leaf n = Data.leaf multi_arena
        {key="multi-fixture:" ^ Int.toString n,value=nat n}
      val multi_leaves = map multi_leaf (0 upto 11)
      fun rotated_child shift = Data.raw_branch multi_arena 0
        (map (fn slot => (0,List.nth (multi_leaves,shift+slot)))
          (0 upto 3))
      val multi_children = map rotated_child [0,4,8]
      val repeated_children = multi_children @ [List.hd multi_children]
      val collapsed_selected_leaf = Data.leaf multi_arena
        {key="multi-collapse-selected",value=nat 99}
      fun selected_column_child selected =
        Data.raw_branch multi_arena 1
          (map (fn slot => (0,
            if slot=selected then collapsed_selected_leaf
            else Data.leaf multi_arena
              {key="multi-collapse:" ^ Int.toString selected ^ ":" ^ Int.toString slot,
               value=nat (100 + selected*3 + slot)})) (0 upto 2))
      val selected_column_children = map selected_column_child (0 upto 2)
      fun make_selector axis = Data.raw_branch multi_arena axis
        (map (fn slot => (0,Data.leaf multi_arena
          {key="multi-selector:" ^ Int.toString axis ^ ":" ^ Int.toString slot,
           value=nat slot})) (0 upto (Data.axis_radix axis-1)))
      fun make_bind axis ordered =
        let
          fun choose ({value,...}: Data.payload) accumulated =
            let
              val slot = (case try HOLogic.dest_number value of
                SOME (typ,n) => if typ = @{typ nat} andalso n>=0 andalso
                    n<Int.toLarge (length ordered) then IntInf.toInt n
                  else error "Multi-axis fixture selector escaped its ordered rows"
              | NONE => error "Multi-axis fixture selector is not numeric")
              val _ = if accumulated=0 then ()
                else error "Multi-axis fixture selector accumulated a weight"
            in List.nth (ordered,slot) end
        in Data.normalize multi_arena
          (Data.bind multi_arena choose (make_selector axis)) end
      val multi_target = make_bind 1 multi_children
      val collapsed_target = make_bind 1 selected_column_children
      val repeated_target = make_bind 0 repeated_children
      val _ = (case Data.view multi_arena collapsed_target of
          Data.View_Leaf {payload={value,...},...} =>
            if value aconv nat 99 then ()
            else error "Collapsed selector leaf has another payload"
        | _ => error "Selected columns with equal outputs did not collapse")
      val _ = (case Data.view multi_arena multi_target of
          Data.View_Branch {axis=0,...} => ()
        | _ => error "Earlier-axis fixture did not normalize below its parent")
      fun term_of diagram =
        (case Data.view multi_arena diagram of
          Data.View_Leaf {payload={value,...},...} =>
            Const (@{const_name Comma_Weighted_CRT_Leaf},
              @{typ nat} --> treeT) $ value
        | Data.View_Branch {axis,children,...} =>
            Const (@{const_name Comma_Weighted_CRT_Branch},
              @{typ nat} --> HOLogic.listT edgeT --> treeT) $
              nat axis $ HOLogic.mk_list edgeT (map (fn (weight,child) =>
                HOLogic.mk_prod (nat weight,term_of child)) children))
      fun add_named diagram table =
        let val identity = Data.identity multi_arena diagram in
          if Names.defined table identity then table
          else
            let
              val term = term_of diagram
              val entry = {term=term,
                definition=Thm.reflexive (Thm.cterm_of ctxt term)}
              val next = Names.update (identity,entry) table
            in (case Data.view multi_arena diagram of
              Data.View_Leaf _ => next
            | Data.View_Branch {children,...} =>
                fold (fn (_,child) => fn current =>
                  add_named child current) children next) end
        end
      val multi_names = fold add_named
        (multi_target :: collapsed_target :: repeated_target ::
          selected_column_children @ multi_children)
        Names.empty
      fun multi_lookup diagram = literal_fallback ctxt multi_arena
        (fn value => Names.lookup multi_names (Data.identity multi_arena value)) diagram
      val multi_factory = Certificate.make ctxt multi_arena @{typ nat}
        (read_only_owner multi_lookup)
      val multi_normalization_visits_before =
        #normalization_node_visits (Data.stats multi_arena)
      val multi_result = #named_bind multi_factory 1 multi_children multi_target
      val multi_normalization_visits_after =
        #normalization_node_visits (Data.stats multi_arena)
      val _ = if multi_normalization_visits_after=multi_normalization_visits_before then ()
        else error "Canonical named bind rewalked its already-normalized target"
      val _ = if length (#apply_slots multi_result)=3 andalso
          List.all closed (#apply_slots multi_result) then ()
        else error "Earlier-axis named bind did not issue closed apply equations"
      val multi_before_hit = Data.stats multi_arena
      val multi_views_before_hit = Data.view_stats multi_arena
      val multi_builds_before_hit = #named_bind_builds (#stats multi_factory ())
      val multi_hits_before_hit = #named_bind_hits (#stats multi_factory ())
      val _ = #named_bind multi_factory 1 multi_children multi_target
      val multi_after_hit = Data.stats multi_arena
      val multi_views_after_hit = Data.view_stats multi_arena
      val _ = if Data.stats multi_arena=multi_before_hit andalso
          multi_views_after_hit=multi_views_before_hit andalso
          #named_bind_builds (#stats multi_factory ())=multi_builds_before_hit andalso
          #named_bind_hits (#stats multi_factory ())=multi_hits_before_hit+1 andalso
          #serialization_node_visits multi_after_hit=0 then ()
        else error "Multi-axis named-bind hit repeated checked graph work"
      val collapsed_result = #named_bind multi_factory 1
        selected_column_children collapsed_target
      val _ = if length (#apply_slots collapsed_result)=3 andalso
          List.all closed (#apply_slots collapsed_result) then ()
        else error "Collapsed parent selector lost its universal child equations"
      val repeated_result = #named_bind multi_factory 0 repeated_children repeated_target
      val _ = if length (#apply_slots repeated_result)=4 andalso
          List.all closed (#apply_slots repeated_result) then ()
        else error "Repeated-axis named bind did not certify its selected cofactors"
      val _ = rejects "reordered earlier-axis named-bind children" (fn () =>
        #named_bind multi_factory 1
          [List.nth (multi_children,1),List.nth (multi_children,0),
            List.nth (multi_children,2)] multi_target)
      val wrong_multi_target = Data.leaf multi_arena
        {key="multi-wrong-target",value=nat 99}
      val _ = rejects "a wrong earlier-axis named-bind target" (fn () =>
        #named_bind multi_factory 1 multi_children wrong_multi_target)
      val wrong_phase_target = Data.shift multi_arena 1 multi_target
      val _ = rejects "a phase-shifted earlier-axis named-bind target" (fn () =>
        #named_bind multi_factory 1 multi_children wrong_phase_target)

      val _ = rejects "an unresolved earlier axis" (fn () =>
        #cofactor factory root 1 0)
      val foreign_arena = Data.make_arena 8
      val foreign = Data.leaf foreign_arena {key="foreign",value=nat 0}
      val _ = rejects "a foreign handle" (fn () => #named factory foreign)
      val wrong_entry = #2 (hd children)
      val forged = Certificate.make ctxt arena @{typ nat}
        (read_only_owner (fn _ => SOME wrong_entry))
      val _ = rejects "a mismatched shallow definition" (fn () => #named forged root)

      (* A failed checked bind must publish no partial named-bind cache entry. *)
      val retry_arena = Data.make_arena 128
      fun retry_leaf n =
        let
          val diagram = Data.leaf retry_arena
            {key="retry-fixture:" ^ Int.toString n,value=nat n}
          val term = Const (@{const_name Comma_Weighted_CRT_Leaf},
            @{typ nat} --> treeT) $ nat n
        in (diagram,{term=term,
          definition=Thm.reflexive (Thm.cterm_of ctxt term)}) end
      val retry_children = map retry_leaf [10,11,12,13]
      val retry_root = Data.raw_branch retry_arena 0
        (map (fn (diagram,_) => (0,diagram)) retry_children)
      val retry_root_term = Const (@{const_name Comma_Weighted_CRT_Branch},
        @{typ nat} --> HOLogic.listT edgeT --> treeT) $ nat 0 $
        HOLogic.mk_list edgeT (map (fn (_,entry) =>
          HOLogic.mk_prod (nat 0,#term entry)) retry_children)
      val retry_root_entry = {term=retry_root_term,
        definition=Thm.reflexive (Thm.cterm_of ctxt retry_root_term)}
      val retry_entries = (retry_root,retry_root_entry) :: retry_children
      val retry_names = fold (fn (diagram,entry) =>
        Names.update (Data.identity retry_arena diagram,entry))
        retry_entries Names.empty
      val malformed_child = #1 (List.nth (retry_children,2))
      val malformed_term = Const (@{const_name Comma_Weighted_CRT_Leaf},
        @{typ nat} --> treeT) $ nat 99
      val malformed_names = Names.update
        (Data.identity retry_arena malformed_child,
          {term=malformed_term,
           definition=Thm.reflexive (Thm.cterm_of ctxt malformed_term)})
        retry_names
      val retry_lookup = Unsynchronized.ref malformed_names
      val retry_factory = Certificate.make ctxt retry_arena @{typ nat}
        (read_only_owner (fn diagram => literal_fallback ctxt retry_arena
          (fn value => Names.lookup (!retry_lookup)
            (Data.identity retry_arena value)) diagram))
      val before_failed_publication = Data.stats retry_arena
      val _ = rejects "a bad named child before bind publication" (fn () =>
        #named_bind retry_factory 0 (map #1 retry_children) retry_root)
      val after_failed_publication = Data.stats retry_arena
      val _ = if #nodes after_failed_publication = #nodes before_failed_publication
        andalso #scratch_entries after_failed_publication =
          #scratch_entries before_failed_publication
        andalso #named_bind_builds (#stats retry_factory ())=0 then ()
        else error "Failed named bind reconstructed data or published partial authority"
      val _ = retry_lookup := retry_names
      val retry_result = #named_bind retry_factory 0
        (map #1 retry_children) retry_root
      val _ = if List.all closed (#apply_slots retry_result) andalso
          #named_bind_builds (#stats retry_factory ())=1 andalso
          #nodes (Data.stats retry_arena)= #nodes before_failed_publication then ()
        else error "Correct named bind could not retry after failed publication"
      val _ = Comma_Proof_Profile.report "Shallow fixture stage=negative-done"
    in () end
end
