(* Shallow inspection must preserve weights and issued arena identity without
   invoking recursive term serialization or mutating the retained store. *)
structure Comma_Weighted_CRT_View_Fixture =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data
  structure Memo = Table(type key = Data.identity val ord = Data.identity_ord)

  fun run ctxt =
    let
      val alias_arena = Data.make_arena 3
      val first = Data.leaf alias_arena {key="canonical",value= @{term "1::nat"}}
      val alias = Data.leaf alias_arena {key="display-only",value= @{term "1::nat"}}
      val typed = Data.leaf alias_arena {key="integer",value= @{term "1::int"}}
      val alias_stats = Data.stats alias_arena
      val _ = if Data.same_action alias_arena first alias andalso
          not (Data.same_action alias_arena first typed) andalso
          #nodes alias_stats=2 andalso #payload_aliases alias_stats=1 andalso
          #used_entries alias_stats=3 then ()
        else error "Typed payload identity lost alias accounting or type separation"
      val _ = Data.leaf alias_arena {key="display-only",value= @{term "1::nat"}}
      fun reject_alias label payload =
        (case Exn.capture (fn () => Data.leaf alias_arena payload) () of
          Exn.Exn (ERROR _) => ()
        | Exn.Exn failure => Exn.reraise failure
        | Exn.Res _ => error ("Typed payload interning accepted " ^ label))
      val _ = reject_alias "a conflicting alias value"
        {key="display-only",value= @{term "2::nat"}}
      val _ = reject_alias "an uncharged alias beyond capacity"
        {key="additional-alias",value= @{term "1::nat"}}
      val _ = if #used_entries (Data.stats alias_arena)=3 andalso
          #payload_aliases (Data.stats alias_arena)=1 then ()
        else error "Failed payload interning mutated its retained alias charges"
      val after_failure = Data.leaf alias_arena
        {key="display-only",value= @{term "1::nat"}}
      val _ = if Data.same_action alias_arena first after_failure then ()
        else error "Failed payload publication corrupted a valid warm alias"
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt |>
        Simplifier.add_simps @{thms comma_crt_axis_radix_def comma_crt_axis_weight_def}
      fun check_parameter function expected axis =
        let
          val request = function $ HOLogic.mk_number @{typ nat} axis
          val equation = Simplifier.rewrite arithmetic (Thm.cterm_of ctxt request)
          val _ = if Thm.term_of (Thm.lhs_of equation) aconv request andalso
              Thm.term_of (Thm.rhs_of equation) aconv
                HOLogic.mk_number @{typ nat} (expected axis) andalso
              Thm.nprems_of equation=0 andalso null (Thm.hyps_of equation) andalso
              null (Thm.tpairs_of equation) then ()
            else error "Weighted CRT parameters differ from their checked clock"
        in () end
      val _ = List.app
        (check_parameter @{term comma_crt_axis_radix} Data.axis_radix) [0,1,2,3]
      val _ = List.app
        (check_parameter @{term comma_crt_axis_weight} Data.axis_weight) [0,1,2,3]
      val arena = Data.make_arena 32
      fun payload n = {key="view-fixture:" ^ Int.toString n,
        value=HOLogic.mk_number @{typ nat} n}
      val children = map (Data.leaf arena o payload) [0,1,2,3]
      val edges = map_index (fn (weight,child) => (weight,child)) children
      val root = Data.with_offset arena 9 (Data.raw_branch arena 0 edges)
      val initial = Data.stats arena
      val root_key = Data.identity arena root
      val memo = Memo.update (root_key,17) Memo.empty
      val _ = if Memo.lookup memo (Data.identity arena root)=SOME 17 then ()
        else error "Weighted CRT shallow memo lost an issued identity"
      val shifted = Data.with_offset arena 1 root
      val _ = if Memo.lookup memo (Data.identity arena shifted)=NONE then ()
        else error "Weighted CRT shallow memo erased the root offset"
      val _ = (case Data.view arena root of
        Data.View_Branch {offset,axis,children=actual} =>
          if offset=9 andalso axis=0 andalso length actual=4 andalso
              ListPair.allEq (fn ((weight,child),(expected,original)) =>
                weight=expected andalso Data.offset child=0 andalso
                Data.same_action arena child original) (actual,edges)
          then () else error "Weighted CRT shallow view changed a weighted edge"
      | Data.View_Leaf _ => error "Weighted CRT branch became a shallow leaf")
      val leaf = hd children
      val _ = (case Data.view arena leaf of
        Data.View_Leaf {offset,payload={value,...}} =>
          if offset=0 andalso value aconv #value (payload 0) then ()
          else error "Weighted CRT shallow view changed its leaf payload"
      | Data.View_Branch _ => error "Weighted CRT leaf became a shallow branch")
      val foreign_arena = Data.make_arena 32
      val foreign = Data.leaf foreign_arena (payload 0)
      val _ = if Data.identity_ord
          (Data.identity arena leaf,Data.identity foreign_arena foreign) <> EQUAL
        then () else error "Weighted CRT identity erased the arena generation"
      fun rejects label operation =
        (case Exn.capture operation () of
          Exn.Exn (ERROR _) => ()
        | Exn.Exn failure => Exn.reraise failure
        | Exn.Res _ => error ("Weighted CRT accepted " ^ label))
      val _ = rejects "a foreign view" (fn () => Data.view arena foreign)
      val _ = rejects "a foreign identity" (fn () => Data.identity arena foreign)
      val _ = rejects "a negative clock axis" (fn () => Data.axis_radix (~1))
      val _ = rejects "an exterior clock axis" (fn () => Data.axis_weight 4)
      val _ = if Data.stats arena=initial then ()
        else error "Weighted CRT shallow access traversed or mutated its store"
      val _ = if Data.view_stats arena={node_visits=2,edge_visits=4} then ()
        else error "Weighted CRT shallow inspection work was not charged exactly"
      fun check_collapsed_parent () =
        let
          val collapsed_arena = Data.make_arena 32
          val child = Data.leaf collapsed_arena (payload 99)
          val children = [child,child,child,child]
          val collapse_initial = Data.stats collapsed_arena
          val direct = Data.normalized_branch collapsed_arena 0 children
          val after_direct = Data.stats collapsed_arena
          val raw = Data.raw_branch collapsed_arena 0 (map (fn item => (0,item)) children)
          val normalized = Data.normalize collapsed_arena raw
          val after_raw = Data.stats collapsed_arena
          val _ = if Data.same_action collapsed_arena direct normalized then ()
            else error "Direct weighted parent changed the raw-normalized action"
          val _ = if #nodes after_direct = #nodes collapse_initial andalso
              #nodes after_raw = #nodes collapse_initial+1 andalso
              #scratch_entries after_direct=0 andalso
              #proof_entries after_direct= #proof_entries collapse_initial then ()
            else error "Collapsed source parent interned an avoidable raw node"
        in () end
      val _ = check_collapsed_parent ()
      fun check_scoped_selector () =
        let
          val scoped_arena = Data.make_arena 64
          val child = Data.leaf scoped_arena (payload 102)
          val children = [child,child,child,child]
          val initial = Data.stats scoped_arena
          val escaped = Data.with_normalized_branch scoped_arena 0 children
            (fn (result,selector) =>
              let
                val _ = if Data.same_action scoped_arena result child then ()
                  else error "Scoped selector changed collapsed parent"
                val _ = Data.with_selector_view scoped_arena selector (fn view =>
                  if #axis view=0 andalso length (#input_rows view)=4 then ()
                  else error "Scoped selector lost its exact ordered input view")
              in selector end)
          val _ = rejects "an escaped selector scope" (fn () =>
            Data.with_selector_view scoped_arena escaped (fn _ => ()))
          val _ = rejects "a failed selector consumer" (fn () =>
            Data.with_normalized_branch scoped_arena 0 children
              (fn _ => error "injected selector consumer failure"))
          val final = Data.stats scoped_arena
          val _ = if #nodes final= #nodes initial andalso
              #proof_entries final= #proof_entries initial andalso
              #scratch_entries final=0 then ()
            else error "Scoped selector retained a raw parent or leaked scratch"
        in () end
      val _ = check_scoped_selector ()
      fun check_global_child_ordering () =
        let
          val ordering_arena = Data.make_arena 128
          fun ordering_leaf n = Data.leaf ordering_arena
            {key="global-child-order-fixture:" ^ Int.toString n,
             value=HOLogic.mk_number @{typ nat} n}
          val leaves = map ordering_leaf [0,1,2,3]
          val child_a = Data.branch ordering_arena 0 leaves
          val child_b = Data.branch ordering_arena 0 (rev leaves)
          val children = map (fn slot => if slot mod 2=0 then child_a else child_b)
            (0 upto 10)
          val initial = Data.stats ordering_arena
          val direct = Data.normalized_branch ordering_arena 3 children
          val direct_stats = Data.stats ordering_arena
          val old_path = Data.normalize ordering_arena
            (Data.branch ordering_arena 3 children)
          val old_stats = Data.stats ordering_arena
          val _ = if Data.same_action ordering_arena direct old_path then ()
            else error "Direct parent failed to canonicalize a lower-axis global child"
          val _ = if #nodes direct_stats < #nodes old_stats then ()
            else error "Normalized parent still interned the redundant noncanonical root"
          val _ = if #scratch_entries direct_stats=0 andalso
              #proof_entries direct_stats= #proof_entries initial then ()
            else error "Normalized parent retained selector state or proof entries"
          val noncanonical = Data.raw_branch ordering_arena 3
            (map (fn child => (0,child)) children)
          val local_leaf = Data.leaf ordering_arena
            {key="global-child-rejection",value=HOLogic.mk_number @{typ nat} 90}
          val rejection_children = [noncanonical,local_leaf,local_leaf,local_leaf]
          val before_rejections = Data.stats ordering_arena
          val _ = rejects "a noncanonical child" (fn () =>
            Data.normalized_branch ordering_arena 0 rejection_children)
          val foreign_arena = Data.make_arena 8
          val foreign_child = Data.leaf foreign_arena
            {key="foreign-normalized-branch",value=HOLogic.mk_number @{typ nat} 91}
          val _ = rejects "a foreign normalized-branch child" (fn () =>
            Data.normalized_branch ordering_arena 0
              [foreign_child,local_leaf,local_leaf,local_leaf])
          val after_rejections = Data.stats ordering_arena
          val _ = if before_rejections=after_rejections then ()
            else error "Normalized branch rejection mutated its arena before admission"
        in () end
      val _ = check_global_child_ordering ()
      fun check_weighted_normalized_branch () =
        let
          val weighted_arena = Data.make_arena 128
          fun weighted_leaf n = Data.leaf weighted_arena
            {key="normalized-weighted-child:" ^ Int.toString n,
             value=HOLogic.mk_number @{typ nat} n}
          fun row start weights =
            let val leaves = map weighted_leaf (start upto (start+3))
            in Data.raw_branch weighted_arena 0 (ListPair.zip (weights,leaves)) end
          val rows = [row 20 [0,1,0,2],row 24 [0,2,1,0],row 28 [1,0,2,0]]
          val children = [Data.with_offset weighted_arena 3 (hd rows),
            Data.with_offset weighted_arena 1 (hd (tl rows)),
            Data.with_offset weighted_arena 2 (hd (tl (tl rows)))]
          val initial = Data.stats weighted_arena
          val direct = Data.normalized_branch weighted_arena 1 children
          val direct_stats = Data.stats weighted_arena
          val legacy = Data.normalize weighted_arena
            (Data.raw_branch_diagrams weighted_arena 1 children)
          val _ = if Data.same_action weighted_arena direct legacy then ()
            else error "Normalized branch changed weighted lower-axis composition"
          val _ = if #scratch_entries direct_stats=0 andalso
              #proof_entries direct_stats= #proof_entries initial then ()
            else error "Normalized branch retained selector scratch or proof state"
        in () end
      val _ = check_weighted_normalized_branch ()
      fun check_selector_scratch_rollback () =
        let
          val rollback_arena = Data.make_arena 8
          val source_leaf = Data.leaf rollback_arena
            {key="normalized-branch-scratch-rollback",
             value=HOLogic.mk_number @{typ nat} 101}
          val initial = Data.stats rollback_arena
          val _ = rejects "selector scratch exhaustion" (fn () =>
            Data.normalized_branch rollback_arena 0
              [source_leaf,source_leaf,source_leaf,source_leaf])
          val after_failure = Data.stats rollback_arena
          val _ = if #nodes after_failure = #nodes initial andalso
              #proof_entries after_failure = #proof_entries initial andalso
              #scratch_entries after_failure = 0 andalso
              Data.same_action rollback_arena source_leaf source_leaf then ()
            else error "Normalized branch failure retained scratch or invalidated its source"
        in () end
      val _ = check_selector_scratch_rollback ()
      fun check_compact_normalization () =
        let
          val compare_arena = Data.make_arena 128
          fun compare_payload n = {key="crossed-view-fixture:" ^ Int.toString n,
            value=HOLogic.mk_number @{typ nat} n}
          fun branch0 start weights =
            let
              val leaves = map (Data.leaf compare_arena o compare_payload)
                (start upto (start+3))
            in Data.raw_branch compare_arena 0 (ListPair.zip (weights,leaves)) end
          val crossed_rows = [branch0 10 [0,1,0,2],branch0 14 [0,2,1,0],
            branch0 18 [1,0,2,0]]
          val weighted_root = Data.with_offset compare_arena 5
            (Data.raw_branch compare_arena 1
              [(0,hd crossed_rows),(2,hd (tl crossed_rows)),
                (1,hd (tl (tl crossed_rows)))])
          val normalization_initial = Data.stats compare_arena
          val compact = Data.normalize compare_arena weighted_root
          val compact_stats = Data.stats compare_arena
          val full = Data.with_normalization_plan compare_arena weighted_root
            (fn plan => Data.plan_result compare_arena plan)
          val full_stats = Data.stats compare_arena
          val _ = if Data.same_action compare_arena compact full then ()
            else error "Compact data normalization changed a weighted crossed-axis result"
          val _ = if #scratch_entries compact_stats=0 andalso
              #scratch_entries full_stats=0 andalso
              #proof_entries compact_stats = #proof_entries normalization_initial andalso
              #proof_entries full_stats = #proof_entries normalization_initial then ()
            else error "Data-only normalization leaked scratch or published proof entries"
        in () end
      val _ = check_compact_normalization ()
    in () end
end
