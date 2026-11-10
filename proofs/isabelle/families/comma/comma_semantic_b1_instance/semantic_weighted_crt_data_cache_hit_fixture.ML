(* Native fixture for weighted-data normalization-cache reuse, reservation
   lifecycle, and arena-authority checks in the predecessor certificate session. *)
structure Comma_Weighted_CRT_Data_Cache_Hit_Fixture =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data

  exception Reservation_Cleanup_Failure
  exception Late_Cache_Failure
  exception Normalization_Plan_Failure

  val natT = @{typ nat}
  val list_natT = HOLogic.listT natT

  fun nat n = HOLogic.mk_number natT n

  fun used (stats: Data.stats) = #used_entries stats

  fun same_stats (left: Data.stats) (right: Data.stats) =
    #nodes left = #nodes right andalso
    #payload_aliases left = #payload_aliases right andalso
    #proof_entries left = #proof_entries right andalso
    #scratch_entries left = #scratch_entries right andalso
    #peak_entries left = #peak_entries right andalso
    #normalization_node_visits left = #normalization_node_visits right andalso
    #serialization_node_visits left = #serialization_node_visits right andalso
    #branch_calls left = #branch_calls right andalso
    #intern_hits left = #intern_hits right

  fun expect_rejection label action =
    (case Exn.capture action () of
      Exn.Exn (ERROR _) => ()
    | Exn.Res _ => error ("Weighted CRT cache fixture accepted " ^ label)
    | Exn.Exn failure => Exn.reraise failure)

  fun reservation_fixtures () =
    let
      val owner = Data.make_arena 8
      val foreign = Data.make_arena 8
      val stale_ref = Unsynchronized.ref (NONE: Data.reservation option)
      val _ = Data.with_reservation owner (fn lease =>
        (expect_rejection "a foreign-arena reservation use"
          (fn () => Data.reserve_external foreign lease);
         Data.reserve_external owner lease;
         stale_ref := SOME lease))
      val owner_after_scope = Data.stats owner
      val foreign_after_rejection = Data.stats foreign
      val _ = if #scratch_entries owner_after_scope = 0 andalso
          #scratch_entries foreign_after_rejection = 0 then ()
        else error "Weighted CRT reservation fixture leaked foreign or scoped scratch"
      val stale = (case !stale_ref of
          SOME lease => lease
        | NONE => error "Weighted CRT reservation fixture lost its stale lease")
      val _ = expect_rejection "a stale reservation use"
        (fn () => Data.reserve_external owner stale)

      val successful = Data.make_arena 8
      val _ = Data.with_reservation successful (fn lease =>
        (Data.reserve_external successful lease;
         Data.reserve_external successful lease;
         Data.retain_external successful lease 1))
      val successful_stats = Data.stats successful
      val _ = if #proof_entries successful_stats = 1 andalso
          #scratch_entries successful_stats = 0 then ()
        else error "Weighted CRT successful reservation did not commit its retained proof"

      val exceptional = Data.make_arena 8
      (* Catch only the intentional sentinel, so an earlier accounting error
         cannot masquerade as the expected exception-cleanup path. *)
      val cleanup_failed =
        ((Data.with_reservation exceptional (fn lease =>
            (Data.reserve_external exceptional lease;
             Data.reserve_external exceptional lease;
             Data.retain_external exceptional lease 1;
             raise Reservation_Cleanup_Failure));
          false)
         handle Reservation_Cleanup_Failure => true)
      val _ = if cleanup_failed then ()
        else error "Weighted CRT reservation cleanup fixture did not raise its sentinel"
      val exceptional_stats = Data.stats exceptional
      val _ = if #proof_entries exceptional_stats = 0 andalso
          #scratch_entries exceptional_stats = 0 then ()
        else error "Weighted CRT exceptional reservation did not roll back all counters"
    in () end

  fun action_meta_transport_fixture ctxt =
    let
      val arena = Data.make_arena 16
      val serializer = Data.make_serializer arena natT
      val zero = Data.leaf arena {key="action-meta:nat:0", value=nat 0}
      val one = Data.leaf arena {key="action-meta:nat:1", value=nat 1}
      val zero_action = Data.action serializer zero
      val one_action = Data.action serializer (Data.with_offset arena 1 one)
      val (_,one_tree) = HOLogic.dest_prod one_action
      val (zero_offset,zero_tree) = HOLogic.dest_prod zero_action
      val (one_offset,_) = HOLogic.dest_prod one_action
      val profile = Comma_Semantic_Weighted_CRT_Data_Transport.make_profile
        "weighted_crt_action_meta_fixture" ["selector_port"]
      fun compare_arithmetic_contexts label term =
        let
          val cterm = Thm.cterm_of ctxt term
          val existing = Simplifier.rewrite
            (Comma_Entry_Arithmetic.natural_context ctxt) cterm
          val prepared = Simplifier.rewrite
            (Comma_Semantic_Weighted_CRT_Selector_Transport.arithmetic_context ctxt)
            cterm
        in if Thm.term_of (Thm.lhs_of existing) aconv
              Thm.term_of (Thm.lhs_of prepared) andalso
            Thm.term_of (Thm.rhs_of existing) aconv
              Thm.term_of (Thm.rhs_of prepared) then ()
          else error ("Weighted CRT prepared arithmetic context changed " ^ label)
        end
      val _ = compare_arithmetic_contexts "literal arithmetic"
        (HOLogic.mk_binop @{const_name plus} (zero_offset,one_offset))
      val condition = Free ("selector_fixture_condition", HOLogic.boolT)
      val if_nat = Const (@{const_name If}, HOLogic.boolT --> natT --> natT --> natT)
      val if_expression = if_nat $ condition $
        HOLogic.mk_binop @{const_name plus} (zero_offset,one_offset) $
        HOLogic.mk_binop @{const_name plus} (one_offset,zero_offset)
      val _ = compare_arithmetic_contexts "if-congruence rewriting" if_expression
      fun check_reflexive_scalar label term =
        let val theorem =
          Comma_Semantic_Weighted_CRT_Selector_Transport.scalar_conversion
            ctxt profile term
        in if Thm.term_of (Thm.lhs_of theorem) aconv term andalso
            Thm.term_of (Thm.rhs_of theorem) aconv term then ()
          else error ("Weighted CRT " ^ label ^ " literal was not reflexive") end
      val _ = check_reflexive_scalar "zero" zero_offset
      val _ = check_reflexive_scalar "one" one_offset
      val direct = Comma_Semantic_Weighted_CRT_Selector_Transport.action_meta_equation
        ctxt profile natT one_action one_action
      val _ = if Thm.term_of (Thm.lhs_of direct) aconv one_action andalso
          Thm.term_of (Thm.rhs_of direct) aconv one_action then ()
        else error "Weighted CRT reflexive action fixture changed exact endpoints"
      val equal_offset_different_syntax = HOLogic.mk_binop
        @{const_name plus} (zero_offset, one_offset)
      val arithmetic_action = HOLogic.mk_prod (equal_offset_different_syntax, one_tree)
      val arithmetic = Comma_Semantic_Weighted_CRT_Selector_Transport.action_meta_equation
        ctxt profile natT arithmetic_action one_action
      val _ = if Thm.term_of (Thm.lhs_of arithmetic) aconv arithmetic_action andalso
          Thm.term_of (Thm.rhs_of arithmetic) aconv one_action then ()
        else error "Weighted CRT arithmetic-offset fixture lost its exact endpoints"
      val different_child = HOLogic.mk_prod (one_offset, zero_tree)
      val _ = expect_rejection "an action with a different child"
        (fn () => ignore
          (Comma_Semantic_Weighted_CRT_Selector_Transport.action_meta_equation
            ctxt profile natT different_child one_action))
      val two = Data.with_offset arena 2 one
      val two_action = Data.action serializer two
      val _ = expect_rejection "an action with a different weight"
        (fn () => ignore
          (Comma_Semantic_Weighted_CRT_Selector_Transport.action_meta_equation
            ctxt profile natT one_action two_action))
      val _ = Output.information
        "weighted_crt_action_meta_fixture=passed reflexivity=true scalar_normalization=true endpoint_rejection=true"
    in () end

  fun late_failure_cache_fixture ctxt =
    let
      val arena = Data.make_arena 128
      val serializer = Data.make_serializer arena natT
      val cache = Data.make_normalization_proof_cache ctxt arena natT
      val zero = Data.leaf arena {key="late-cache:nat:0", value=nat 0}
      val one = Data.leaf arena {key="late-cache:nat:1", value=nat 1}
      val repeated_axis = Data.raw_branch arena 0
        [(0,zero), (2,one), (3,zero), (1,one)]
      val outer = Data.raw_branch arena 0
        [(4,repeated_axis), (1,repeated_axis), (0,zero), (5,repeated_axis)]
      val initial = Data.with_offset arena 9 outer
      val published = Unsynchronized.ref (NONE: (Data.diagram * thm) option)
      (* A private sentinel distinguishes the intended late failure from any
         normalization or theorem-construction error before publication. *)
      val late_failure_seen =
        ((Data.with_reservation arena (fn lease =>
            let
              val _ = Data.reserve_external arena lease
              val certified = Data.certify_normalization ctxt arena natT
                serializer cache initial
              val _ = published := SOME (#normalized certified, #equation certified)
            in raise Late_Cache_Failure end);
          false)
         handle Late_Cache_Failure => true)
      val _ = if late_failure_seen then ()
        else error "Weighted CRT late-cache failure fixture did not raise its sentinel"
      val after_failure = Data.stats arena
      val _ = if #scratch_entries after_failure = 0 andalso
          #proof_entries after_failure > 0 then ()
        else error "Late failure lost a completed cache entry's proof charge"
      val saved = (case !published of
          SOME result => result
        | NONE => error "Late failure did not retain the completed cache result")

      (* A new parent may inspect its immediate cached child, but must not
         rediscover or serialize that child's already-certified descendants. *)
      val parent = Data.raw_branch arena 1 [(0,outer),(2,outer),(3,outer)]
      val before_parent = Data.stats arena
      val _ = Data.certify_normalization ctxt arena natT serializer cache parent
      val after_parent = Data.stats arena
      val parent_visits = #normalization_node_visits after_parent -
        #normalization_node_visits before_parent
      val _ = if 1 <= parent_visits andalso parent_visits <= 2 andalso
          #serialization_node_visits after_parent -
            #serialization_node_visits before_parent <=
              #nodes after_parent - #nodes before_parent + 2 andalso
          #scratch_entries after_parent = 0 then ()
        else error ("Weighted CRT new parent replayed its certified child subtree" ^
          " normalization_visits=" ^ Int.toString parent_visits ^
          " serialization_visits=" ^ Int.toString
            (#serialization_node_visits after_parent -
              #serialization_node_visits before_parent) ^
          " new_nodes=" ^ Int.toString (#nodes after_parent - #nodes before_parent) ^
          " scratch=" ^ Int.toString (#scratch_entries after_parent))

      fun fill next =
        let val current = Data.stats arena
        in
          if used current = 128 then ()
          else if used current > 128 then
            error "Late-cache fixture exceeded its exact arena capacity"
          else
            let
              val index = next + 20000
              val _ = Data.leaf arena
                {key="late-cache:capacity:" ^ Int.toString index,
                 value=nat index}
            in fill (next + 1) end
        end
      val _ = fill 0
      val full = Data.stats arena
      val _ = if used full = 128 andalso #scratch_entries full = 0 then ()
        else error "Late-cache fixture did not reach its exact capacity"
      val reused = Data.certify_normalization ctxt arena natT serializer cache initial
      val after_reuse = Data.stats arena
      val _ = if Data.same_action arena (#1 saved) (#normalized reused) andalso
          Thm.prop_of (#2 saved) aconv Thm.prop_of (#equation reused) then ()
        else error "Same-owner cache reuse failed after late publication failure"
      val _ = if #nodes after_reuse = #nodes full andalso
          #proof_entries after_reuse = #proof_entries full andalso
          #scratch_entries after_reuse = 0 andalso
          #peak_entries after_reuse = #peak_entries full then ()
        else error "Late-failure same-owner cache hit performed charged work"
    in () end

  fun normalization_plan_fixtures () =
    let
      val arena = Data.make_arena 32
      val foreign = Data.make_arena 32
      val zero = Data.leaf arena {key="plan:nat:0", value=nat 0}
      val one = Data.leaf arena {key="plan:nat:1", value=nat 1}
      val action = Data.raw_branch arena 0 [(0,zero), (2,one), (1,zero), (3,one)]
      val escaped = Unsynchronized.ref (NONE: Data.normalization_plan option)
      val _ = Data.with_normalization_plan arena action (fn plan =>
        let
          val before_owner = Data.stats arena
          val before_foreign = Data.stats foreign
          val _ = expect_rejection "a foreign-arena normalization-plan access"
            (fn () => ignore (Data.plan_source foreign plan))
          val after_owner = Data.stats arena
          val after_foreign = Data.stats foreign
          val _ = if same_stats before_owner after_owner andalso
              same_stats before_foreign after_foreign then ()
            else error "Foreign normalization-plan access performed lookup or accounting work"
          val _ = if Data.same_action arena (Data.plan_source arena plan) action then ()
            else error "Scoped normalization plan changed its source"
          val _ = escaped := SOME plan
        in () end)
      val after_scope = Data.stats arena
      val _ = if #scratch_entries after_scope = 0 then ()
        else error "Normalization-plan scope retained scratch after completion"
      val saved_plan = (case !escaped of
          SOME plan => plan
        | NONE => error "Normalization-plan fixture did not retain its escaped handle")
      val before_stale_access = Data.stats arena
      val _ = expect_rejection "an escaped normalization plan after scope exit"
        (fn () => ignore (Data.plan_result arena saved_plan))
      val after_stale_access = Data.stats arena
      val _ = if same_stats before_stale_access after_stale_access then ()
        else error "Stale normalization-plan access performed lookup or accounting work"

      val exceptional = Data.make_arena 32
      val exception_zero = Data.leaf exceptional
        {key="plan-exception:nat:0", value=nat 0}
      val exception_one = Data.leaf exceptional
        {key="plan-exception:nat:1", value=nat 1}
      val exception_action = Data.raw_branch exceptional 0
        [(0,exception_zero), (1,exception_one), (2,exception_zero), (3,exception_one)]
      val exception_plan = Unsynchronized.ref (NONE: Data.normalization_plan option)
      val sentinel_seen =
        ((Data.with_normalization_plan exceptional exception_action (fn plan =>
            (exception_plan := SOME plan;
             ignore (Data.plan_children exceptional plan);
             raise Normalization_Plan_Failure));
          false)
         handle Normalization_Plan_Failure => true)
      val _ = if sentinel_seen then ()
        else error "Normalization-plan exception fixture did not raise its sentinel"
      val after_exception = Data.stats exceptional
      val _ = if #scratch_entries after_exception = 0 then ()
        else error "Exceptional normalization-plan scope leaked scratch entries"
      val saved_exception_plan = (case !exception_plan of
          SOME plan => plan
        | NONE => error "Exceptional normalization-plan fixture lost its scoped handle")
      val before_exception_stale = Data.stats exceptional
      val _ = expect_rejection "a normalization plan after exceptional scope exit"
        (fn () => ignore (Data.plan_children exceptional saved_exception_plan))
      val after_exception_stale = Data.stats exceptional
      val _ = if same_stats before_exception_stale after_exception_stale then ()
        else error "Exceptional stale-plan access performed lookup or accounting work"
    in () end

  fun lower_axis_port_fixture ctxt arena serializer cache zero one two =
    let
      fun value_leaf value =
        if value = 0 then zero else if value = 1 then one else two
      fun child_action entries = Data.branch arena 0
        (map (fn (weight,value) =>
          Data.with_offset arena weight (value_leaf value)) entries)
      val child_a = child_action [(0,0),(1,1),(2,2),(3,0)]
      val child_b = child_action [(5,2),(0,0),(4,1),(1,1)]
      val certified_a = Data.certify_normalization ctxt arena natT serializer cache child_a
      val certified_b = Data.certify_normalization ctxt arena natT serializer cache child_b
      val _ = if Data.same_action arena child_a (#normalized certified_a) andalso
          Data.same_action arena child_b (#normalized certified_b) andalso
          Thm.nprems_of (#equation certified_a) = 0 andalso
          Thm.nprems_of (#equation certified_b) = 0 then ()
        else error "Weighted CRT lower-axis children were not retained as certified canonical rows"

      (* Axis 1 has three source rows.  Their axis 0 children have different
         phase values and weights, forcing the selector plan to use a genuine
         Lower_Axis_Port and restore a nonzero common row weight. *)
      val source = Data.raw_branch arena 1
        [(17,child_a),(19,child_b),(18,child_a)]
      val initial = Data.with_offset arena 2 source
      val expected_columns = [[0,7,1],[1,2,2],[2,6,3],[3,3,4]]
      val expected_commons = [0,1,2,3]
      val _ = Data.with_normalization_plan arena initial (fn plan =>
        let
          val selector = Data.plan_selector arena plan
          val common = Data.selector_common arena selector
          val _ = Data.with_selector_view arena selector (fn view =>
            let
              fun check_piece slot piece =
                (case piece of
                  Data.Lower_Axis_Port
                    {slot=recorded,restricted_rows,child_common,...} =>
                      recorded = slot andalso length restricted_rows = 3 andalso
                      map Data.offset restricted_rows = List.nth (expected_columns,slot) andalso
                      child_common = List.nth (expected_commons,slot)
                | Data.Same_Axis_Port _ => false)
              val pieces = #pieces view
              val correct = #axis view = 1 andalso #split_axis view = 0 andalso
                common = 17 andalso length pieces = 4 andalso
                map Data.offset (#input_rows view) = [0,2,1] andalso
                ListPair.allEq (fn (slot,piece) => check_piece slot piece)
                  (0 upto 3,pieces)
            in
              if correct then ()
              else error "Weighted CRT Lower_Axis_Port did not preserve selector commons"
            end)
        in () end)
      val certified = Data.certify_normalization ctxt arena natT serializer cache initial
      val normalized = #normalized certified
      val _ = if Data.offset normalized = 19 andalso
          Thm.nprems_of (#equation certified) = 0 then ()
        else error "Weighted CRT lower-axis normalization lost its common root weight"

      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag}, [natT])
      val resultT = HOLogic.mk_prodT (natT,natT)
      val option_resultT = Type (@{type_name option}, [resultT])
      val actionT = HOLogic.mk_prodT (natT,dagT)
      val apply = Const (@{const_name comma_weighted_crt_apply},
        actionT --> natT --> option_resultT)
      val some = Const (@{const_name Some}, resultT --> option_resultT)
      fun prove_point action phase value elapsed =
        let
          val expected = some $ HOLogic.mk_prod (nat value,nat elapsed)
          val proposition = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (apply $ action $ nat phase, expected))
          val theorem = Goal.prove ctxt [] [] proposition
            (fn {context,...} =>
              simp_tac (Simplifier.add_simps ((@{thms comma_weighted_crt_apply_def
                  comma_weighted_crt_eval.simps(1)
                  comma_weighted_crt_eval_selected comma_crt_axis_radix_def
                  nth_Cons_0 nth_Cons_Suc nth_Cons' list.map list.size fst_conv snd_conv
                  case_prod_beta option.map})) (Comma_Entry_Arithmetic.natural_context context)) 1)
          val _ = if Thm.nprems_of theorem = 0 then ()
            else error "Weighted CRT bounded point proof retained premises"
        in theorem end
      fun expected_point phase =
        let
          val row = phase mod 3
          val slot = phase mod 4
          val (parent_weight,values) = List.nth
            ([(17,[(0,0),(1,1),(2,2),(3,0)]),
              (19,[(5,2),(0,0),(4,1),(1,1)]),
              (18,[(0,0),(1,1),(2,2),(3,0)])],row)
          val (child_weight,value) = List.nth (values,slot)
          val elapsed = 2 + parent_weight + child_weight
        in (value,elapsed) end
      val source_term = Data.action serializer initial
      val normalized_term = Data.action serializer normalized
      val _ = List.app (fn phase =>
        let val (value,elapsed) = expected_point phase
        in ignore (prove_point source_term phase value elapsed);
           ignore (prove_point normalized_term phase value elapsed)
        end) (0 upto 11)
      val stats = Data.stats arena
      val _ = if #scratch_entries stats = 0 andalso used stats <= 128 then ()
        else error "Weighted CRT Lower_Axis_Port fixture exceeded its shared 128-entry arena"
    in () end

  (* Exercise the proof-producing selector path in a deliberately bounded
     arena.  Child selector theorems must be
     published before their detailed input/piece plans are reclaimed; the
     parent then consumes those theorem entries through its authenticated
     Lower_Axis_Port records. *)
  fun bounded_selector_reclamation_fixture ctxt =
    let
      val arena = Data.make_arena 64
      val serializer = Data.make_serializer arena natT
      val cache = Data.make_normalization_proof_cache ctxt arena natT
      val zero = Data.leaf arena {key="bounded-selector:nat:0", value=nat 0}
      val one = Data.leaf arena {key="bounded-selector:nat:1", value=nat 1}
      val two = Data.leaf arena {key="bounded-selector:nat:2", value=nat 2}
      fun child entries = Data.branch arena 0
        (map (fn (weight,value) => Data.with_offset arena weight
          (if value = 0 then zero else if value = 1 then one else two)) entries)
      val child_a = child [(0,0),(1,1),(2,2),(3,0)]
      val child_b = child [(5,2),(0,0),(4,1),(1,1)]
      val root = Data.raw_branch arena 1
        [(17,child_a),(19,child_b),(18,child_a)]
      val initial = Data.with_offset arena 2 root
      val certified = Data.certify_normalization ctxt arena natT serializer cache initial
      val normalized = #normalized certified
      val stats = Data.stats arena
      val _ = if #scratch_entries stats = 0 andalso used stats <= 64 andalso
          #peak_entries stats <= 64 andalso #proof_entries stats >= 4 andalso
          Thm.nprems_of (#equation certified) = 0 andalso
          Data.offset normalized = 19 then ()
        else error ("Weighted CRT bounded selector reclamation lost proof authority " ^
          "or exceeded its arena: used=" ^ Int.toString (used stats) ^
          " peak=" ^ Int.toString (#peak_entries stats) ^
          " proofs=" ^ Int.toString (#proof_entries stats) ^
          " scratch=" ^ Int.toString (#scratch_entries stats))

      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag}, [natT])
      val resultT = HOLogic.mk_prodT (natT,natT)
      val option_resultT = Type (@{type_name option}, [resultT])
      val actionT = HOLogic.mk_prodT (natT,dagT)
      val apply = Const (@{const_name comma_weighted_crt_apply},
        actionT --> natT --> option_resultT)
      val some = Const (@{const_name Some}, resultT --> option_resultT)
      fun prove_point action phase value elapsed =
        let
          val expected = some $ HOLogic.mk_prod (nat value,nat elapsed)
          val proposition = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (apply $ action $ nat phase, expected))
          val theorem = Goal.prove ctxt [] [] proposition
            (fn {context,...} =>
              simp_tac (Simplifier.add_simps ((@{thms comma_weighted_crt_apply_def
                  comma_weighted_crt_eval.simps(1)
                  comma_weighted_crt_eval_selected comma_crt_axis_radix_def
                  nth_Cons_0 nth_Cons_Suc nth_Cons' list.map list.size fst_conv snd_conv
                  case_prod_beta option.map})) (Comma_Entry_Arithmetic.natural_context context)) 1)
        in if Thm.nprems_of theorem = 0 then theorem
          else error "Weighted CRT bounded selector point retained premises" end
      fun expected_point phase =
        let
          val row = phase mod 3
          val slot = phase mod 4
          val (parent_weight,values) = List.nth
            ([(17,[(0,0),(1,1),(2,2),(3,0)]),
              (19,[(5,2),(0,0),(4,1),(1,1)]),
              (18,[(0,0),(1,1),(2,2),(3,0)])],row)
          val (child_weight,value) = List.nth (values,slot)
        in (value,2 + parent_weight + child_weight) end
      val source_action = Data.action serializer initial
      val normalized_action = Data.action serializer normalized
      val _ = List.app (fn phase =>
        let val (value,elapsed) = expected_point phase
        in ignore (prove_point source_action phase value elapsed);
           ignore (prove_point normalized_action phase value elapsed)
        end) (0 upto 11)
      val _ = Output.information
        ("weighted_crt_bounded_selector_reclamation=passed capacity=64 peak=" ^
          Int.toString (#peak_entries stats) ^ " exact_points=12")
    in () end

  fun run ctxt =
    let
      val _ = reservation_fixtures ()
      val _ = action_meta_transport_fixture ctxt
      val _ = Comma_Fast_Kernel.report "weighted fixture stage=late-failure"
      val _ = late_failure_cache_fixture ctxt
      val _ = Comma_Fast_Kernel.report "weighted fixture stage=plan"
      val _ = normalization_plan_fixtures ()
      val _ = Comma_Fast_Kernel.report "weighted fixture stage=main"
      val arena = Data.make_arena 128
      val serializer = Data.make_serializer arena natT
      val cache = Data.make_normalization_proof_cache ctxt arena natT
      val zero = Data.leaf arena {key="cache-hit:nat:0", value=nat 0}
      val one = Data.leaf arena {key="cache-hit:nat:1", value=nat 1}
      val two = Data.leaf arena {key="cache-hit:nat:2", value=nat 2}
      val inner = Data.raw_branch arena 0
        [(0,zero), (3,one), (1,two), (4,zero)]
      val alternate_inner = Data.raw_branch arena 0
        [(2,two), (0,zero), (5,one), (1,two)]
      val raw = Data.raw_branch arena 0
        [(5,inner), (0,alternate_inner), (3,inner), (2,alternate_inner)]
      val initial = Data.with_offset arena 7 raw
      val first = Data.certify_normalization ctxt arena natT serializer cache initial
      val after_first = Data.stats arena
      val _ = if #scratch_entries after_first = 0 andalso used after_first < 128 then ()
        else error "Weighted CRT cache fixture did not leave capacity for its reuse check"

      val alternate_root = Data.with_offset arena 17 raw
      val second = Data.certify_normalization ctxt arena natT serializer cache alternate_root
      val after_second = Data.stats arena
      val _ = if #nodes after_second = #nodes after_first andalso
          #proof_entries after_second = #proof_entries after_first andalso
          #scratch_entries after_second = 0 andalso
          #normalization_node_visits after_second =
            #normalization_node_visits after_first andalso
          #serialization_node_visits after_second =
            #serialization_node_visits after_first then ()
        else error "Weighted CRT cache hit allocated retained or scratch entries"
      val _ = if Thm.prop_of (#equation first) aconv Thm.prop_of (#equation second) then ()
        else error "Weighted CRT cache hit returned a different equation"
      val _ = if Data.same_action arena (#normalized second)
          (Data.with_offset arena 10 (#normalized first)) then ()
        else error "Weighted CRT cached normalization lost the occurrence root offset"

      val _ = Comma_Fast_Kernel.report "weighted fixture stage=lower-axis"
      val _ = lower_axis_port_fixture ctxt arena serializer cache zero one two
      val _ = bounded_selector_reclamation_fixture ctxt

      fun fill next =
        let val current = Data.stats arena
        in
          if used current = 128 then ()
          else if used current > 128 then
            error "Weighted CRT cache fixture exceeded its exact arena capacity"
          else
            let
              val index = next + 10000
              val _ = Data.leaf arena
                {key="cache-hit:capacity:" ^ Int.toString index,
                 value=nat index}
            in fill (next + 1) end
        end
      val _ = fill 0
      val full = Data.stats arena
      val _ = if used full = 128 andalso #scratch_entries full = 0 then ()
        else error "Weighted CRT cache fixture did not fill the shared capacity exactly"
      val repeated = Data.certify_normalization ctxt arena natT serializer cache initial
      val after_repeat = Data.stats arena
      val _ = if Data.same_action arena (#normalized first) (#normalized repeated) andalso
          Thm.prop_of (#equation first) aconv Thm.prop_of (#equation repeated) then ()
        else error "Weighted CRT full-capacity cache hit changed its result"
      val _ = if #nodes after_repeat = #nodes full andalso
          #proof_entries after_repeat = #proof_entries full andalso
          #scratch_entries after_repeat = #scratch_entries full andalso
          #peak_entries after_repeat = #peak_entries full andalso
          #normalization_node_visits after_repeat =
            #normalization_node_visits full andalso
          #serialization_node_visits after_repeat =
            #serialization_node_visits full then ()
        else error "Weighted CRT full-capacity cache hit performed charged work"

      val foreign_arena = Data.make_arena 128
      val _ = expect_rejection "a diagram from a foreign arena"
        (fn () => ignore (Data.certify_normalization ctxt foreign_arena natT
          serializer cache initial))
      val list_serializer = Data.make_serializer arena list_natT
      val _ = expect_rejection "a cache with the wrong payload type"
        (fn () => ignore (Data.certify_normalization ctxt arena list_natT
          list_serializer cache initial))
      val parent_theory = hd (Theory.parents_of (Proof_Context.theory_of ctxt))
      val parent_ctxt = Proof_Context.init_global parent_theory
      val _ = expect_rejection "a parent-theory context before cache lookup"
        (fn () => ignore (Data.certify_normalization parent_ctxt arena natT
          serializer cache initial))
      val _ = Output.information
        "weighted_crt_cache_hit_fixture=passed capacity=128 repeated_axes=true root_offsets=7,17"
    in () end
end
