(* Kernel replay for Arena's memoized bind witnesses.  The arena is only a
   proposal producer: every witness is checked against the Store's exact
   node equations and the generic bind constructors before it is returned. *)
signature COMMA_CRT_MDD_BIND_REPLAY =
sig
  type replay
  val make: Comma_CRT_MDD_Certificate_Store.store -> replay
  val certify_bind: replay -> Comma_CRT_MDD_Arena.bind_key -> thm
  val certify_cover: replay -> int -> int list -> thm
  val bind_eval_phase: replay -> Comma_CRT_MDD_Arena.bind_key -> thm
  val statistics: replay -> string
end

structure Comma_CRT_MDD_Bind_Replay:> COMMA_CRT_MDD_BIND_REPLAY =
struct
  open Comma_CRT_MDD_Bind_Replay_Support

  fun make store =
    let
      val ctxt = Store.context store
      val radices = map (Utils.dest_nat "MDD radix" natT)
        (HOLogic.dest_list (Store.radices store))
      val _ = if not (null radices) andalso List.all (fn radix => radix > 0) radices
        then () else error "Frozen MDD table has an invalid radix vector"
      val successor_cache = Comma_Selected_List_Conversion.make_successor_cache
        ctxt (fold (curry Int.max) radices 1)
      val _ = List.app (ignore o #equation successor_cache)
        (0 upto (fold (curry Int.max) radices 1 - 1))
      val state: state =
        {store=store, ctxt=ctxt, simp_ctxt=simp_context ctxt, radices=radices,
         slot_successor= #equation successor_cache, slot_vectors=Unsynchronized.ref Termtab.empty,
         bind_certificates=Unsynchronized.ref Key_Table.empty,
         public_bind_certificates=Unsynchronized.ref Key_Table.empty,
         cover_certificates=Unsynchronized.ref Cover_Table.empty,
         cofactor_families=Unsynchronized.ref Cofactor_Family_Table.empty,
         mapping_families=Unsynchronized.ref Mapping_Family_Table.empty,
         selected_cofactors=Unsynchronized.ref Selected_Cofactor_Table.empty,
         selected_targets=Unsynchronized.ref Selected_Target_Table.empty,
         radix_facts=Unsynchronized.ref Inttab.empty,
         support_cache=Unsynchronized.ref Inttab.empty,
         active=Unsynchronized.ref Key_Table.empty,
         bind_visits=Unsynchronized.ref 0, cover_visits=Unsynchronized.ref 0,
         cofactor_family_hits=Unsynchronized.ref 0,
         cofactor_family_builds=Unsynchronized.ref 0,
         mapping_family_hits=Unsynchronized.ref 0,
         mapping_family_builds=Unsynchronized.ref 0,
         radix_fact_hits=Unsynchronized.ref 0,
         radix_fact_builds=Unsynchronized.ref 0,
         identity_restrictions=Unsynchronized.ref 0,
         direct_branch_shapes=Unsynchronized.ref 0,
         direct_indexed_slots=Unsynchronized.ref 0,
         indexed_vector_builds=Unsynchronized.ref 0,
         selected_leaf_branches=Unsynchronized.ref 0,
         selected_leaf_rows=Unsynchronized.ref 0,
         selected_cofactor_hits=Unsynchronized.ref 0,
         selected_cofactor_builds=Unsynchronized.ref 0,
         selected_target_hits=Unsynchronized.ref 0,
         selected_target_builds=Unsynchronized.ref 0,
         first_public_checkpoint=Unsynchronized.ref false,
         proof_timings=Unsynchronized.ref []}
      val wf = Store.wellformed store
      val _ = Utils.ensure_closed_context ctxt "Frozen MDD table wellformedness" wf

      fun node_at root = Store.node store root

      fun support_of root =
        (case Inttab.lookup (!(#support_cache state)) root of
          SOME labels => labels
        | NONE =>
            let
              val labels = (case node_at root of
                Store.Leaf payload => [payload]
              | Store.Branch (_, children) =>
                  fold (fn child => fn accumulated =>
                    let
                      val _ = if child < root then ()
                        else error "Frozen MDD child is not earlier than its parent"
                    in union (op =) accumulated (support_of child) end) children [])
              val _ = #support_cache state := Inttab.update (root, labels)
                (!(#support_cache state))
            in labels end)

      fun cover root labels =
        let
          val _ = root_bound state root
          val expected = HOLogic.mk_Trueprop (cover_prop state labels root)
        in
          (case Cover_Table.lookup (!(#cover_certificates state)) (root, labels) of
            SOME theorem => Utils.exact_prop ctxt "Cached MDD payload cover" expected theorem
          | NONE =>
              let
                val actual = support_of root
                val _ = if List.all (fn payload => member (op =) labels payload) actual
                  then () else error "MDD payload cover omits a reachable leaf"
                val base =
                  (case Cover_Table.lookup (!(#cover_certificates state)) (root, actual) of
                    SOME theorem => Utils.exact_prop ctxt "Cached MDD minimal payload cover"
                      (HOLogic.mk_Trueprop (cover_prop state actual root)) theorem
                  | NONE =>
                      let
                        val _ = #cover_visits state := !(#cover_visits state) + 1
                        val bound = root_bound state root
                        val equation = lookup_equation state root
                        val theorem = (case node_at root of
                          Store.Leaf payload =>
                            let
                              val member_fact = prove_bool state "MDD leaf payload membership"
                                (HOLogic.mk_mem (nat payload, set_nat actual)) []
                            in @{thm comma_crt_mdd_payload_cover_leaf} OF
                              [bound, equation, member_fact] end
                        | Store.Branch (_, children) =>
                            let
                              val child_bounds = map (fn child =>
                                if child < root then
                                  prove_bool state "MDD payload child order"
                                    (mk_less (nat child, nat root)) []
                                else error "Frozen MDD branch child violates table order") children
                              val child_covers = map (fn child => cover child actual) children
                              val child = Free ("cover_child", natT)
                              val bound_prop = ball (set_nat children)
                                (Term.lambda child (mk_less (child, nat root)))
                              val covered_prop = ball (set_nat children)
                                (Term.lambda child (cover_term state actual child))
                              val all_bounds = prove_bool state "MDD payload branch child bounds"
                                bound_prop child_bounds
                              val all_covered = prove_bool state "MDD payload branch child coverage"
                                covered_prop child_covers
                            in @{thm comma_crt_mdd_payload_cover_branch} OF
                              [bound, equation, all_bounds, all_covered] end)
                        val theorem = Utils.exact_prop ctxt "MDD minimal payload cover"
                          (HOLogic.mk_Trueprop (cover_prop state actual root)) theorem
                        val _ = #cover_certificates state := Cover_Table.update
                          ((root, actual), theorem) (!(#cover_certificates state))
                      in theorem end)
                val theorem = if actual = labels then base
                  else
                    let
                      val setT = HOLogic.mk_setT natT
                      val subset = Const (@{const_name less_eq}, setT --> setT --> boolT)
                      val subset_fact = prove_bool state "MDD payload cover set inclusion"
                        (subset $ set_nat actual $ set_nat labels) []
                      val widened = @{thm comma_crt_mdd_payload_cover_mono} OF
                        [base, subset_fact]
                    in Utils.exact_prop ctxt "MDD widened payload cover" expected widened end
                val _ = #cover_certificates state := Cover_Table.update
                  ((root, labels), theorem) (!(#cover_certificates state))
              in Utils.exact_prop ctxt "MDD payload cover" expected theorem end)
        end

      fun radix_at axis = nth nat_listT natT (Store.radices store) (nat axis)
      fun radix_bound_conversion radix_equation slot =
        Thm.combination (Thm.reflexive (Thm.cterm_of ctxt
          (Const (@{const_name Trueprop}, boolT --> @{typ prop}))))
          (Thm.combination (Thm.reflexive (Thm.cterm_of ctxt
            (Const (@{const_name less}, natT --> natT --> boolT) $ slot)))
            (radix_equation RS @{thm eq_reflection}))
      fun axis_facts axis =
        let
          val _ = if 0 <= axis andalso axis < length radices then ()
            else error "MDD cofactor axis is outside the frozen radix vector"
          val bound_prop = mk_less (nat axis,
            Const (@{const_name size}, nat_listT --> natT) $ Store.radices store)
          val positive_prop = mk_less (nat 0, radix_at axis)
          val radix_value = nat (List.nth (radices, axis))
          val radix_equation_prop = HOLogic.mk_eq (radix_at axis, radix_value)
          val expected_bound = HOLogic.mk_Trueprop bound_prop
          val expected_positive = HOLogic.mk_Trueprop positive_prop
          val expected_radix_equation = HOLogic.mk_Trueprop radix_equation_prop
        in
          case Inttab.lookup (!(#radix_facts state)) axis of
            SOME (bound, positive, radix_equation) =>
              let
                val bound = Utils.exact_prop ctxt "Cached MDD radix axis bound"
                  expected_bound bound
                val positive = Utils.exact_prop ctxt "Cached MDD positive radix"
                  expected_positive positive
                val radix_equation = Utils.exact_prop ctxt
                  "Cached MDD axis radix equation" expected_radix_equation radix_equation
                val _ = #radix_fact_hits state := !(#radix_fact_hits state) + 1
              in (bound, positive, radix_equation) end
          | NONE =>
              let
                val bound = prove_bool state "MDD cofactor axis bound" bound_prop []
                val positive = prove_bool state "MDD cofactor radix positivity"
                  positive_prop []
                val bound = Utils.exact_prop ctxt "MDD cofactor axis bound"
                  expected_bound bound
                val positive = Utils.exact_prop ctxt "MDD cofactor radix positivity"
                  expected_positive positive
                val radix_equation = prove_bool state "MDD cofactor axis radix equation"
                  radix_equation_prop []
                val radix_equation = Utils.exact_prop ctxt
                  "MDD cofactor axis radix equation" expected_radix_equation radix_equation
                val _ = #radix_facts state := Inttab.update
                  (axis, (bound, positive, radix_equation)) (!(#radix_facts state))
                val _ = #radix_fact_builds state := !(#radix_fact_builds state) + 1
              in (bound, positive, radix_equation) end
        end

      fun family_admitted_at axis root =
        Const (@{const_name comma_crt_mdd_cofactor_family_admitted},
          nat_listT --> nodesT --> natT --> natT --> boolT) $
          Store.radices store $ Store.table store $ nat axis $ root

      fun family_admitted_term axis root = family_admitted_at axis (nat root)

      fun family_child_at axis root slot =
        Const (@{const_name comma_crt_mdd_cofactor_family_child},
          nat_listT --> nodesT --> natT --> natT --> natT --> natT) $
          Store.radices store $ Store.table store $ nat axis $ root $ slot

      fun family_child_term axis root slot = family_child_at axis (nat root) slot

      fun cofactor_family_prop axis root =
        let
          val slot = Free ("mdd_family_slot", natT)
          val width = nat (List.nth (radices, axis))
          val equation = HOLogic.mk_eq
            (cofactor_term state (nat axis) slot (nat root),
             some natT (family_child_term axis root slot))
        in Logic.all slot
          (Logic.mk_implies
            (HOLogic.mk_Trueprop (mk_less (slot, width)),
             HOLogic.mk_Trueprop equation)) end

      fun cofactor_family axis root =
        let
          val (axis_bound, positive, radix_equation) = axis_facts axis
          val bound = root_bound state root
          val equation = lookup_equation state root
          val _ = (case node_at root of
            Store.Leaf _ => ()
          | Store.Branch (node_axis, _) =>
              if axis <= node_axis then ()
              else error "MDD cofactor family selects below an operand branch")
          val expected = cofactor_family_prop axis root
        in
          case Cofactor_Family_Table.lookup (!(#cofactor_families state)) (root, axis) of
            SOME ({theorem}: cofactor_family) =>
              let
                val theorem = Utils.exact_prop ctxt "Cached MDD cofactor family" expected theorem
                val _ = #cofactor_family_hits state := !(#cofactor_family_hits state) + 1
              in {theorem=theorem}: cofactor_family end
          | NONE =>
              let
                val admission = prove_bool state "MDD cofactor family admission"
                  (family_admitted_term axis root) [axis_bound, positive, bound, equation]
                val admitted = @{thm comma_crt_mdd_cofactor_family_exact} OF
                  [Store.wellformed store, admission]
                val slot = Free ("mdd_family_slot", natT)
                val numeric_guard_ct = Thm.cterm_of ctxt
                  (HOLogic.mk_Trueprop (mk_less (slot, nat (List.nth (radices, axis)))))
                val theorem = Utils.exact_prop ctxt "MDD cofactor family" expected
                  (Thm.forall_intr (Thm.cterm_of ctxt slot)
                    (Thm.implies_intr numeric_guard_ct
                      (Thm.implies_elim
                        (Drule.infer_instantiate ctxt [(("slot",0),Thm.cterm_of ctxt slot)] admitted)
                        (Thm.equal_elim
                          (Thm.symmetric (radix_bound_conversion radix_equation slot))
                          (Thm.assume numeric_guard_ct)))))
                val family: cofactor_family = {theorem=theorem}
                val _ = #cofactor_families state := Cofactor_Family_Table.update
                  ((root, axis), family) (!(#cofactor_families state))
                val _ = #cofactor_family_builds state :=
                  !(#cofactor_family_builds state) + 1
              in family end
        end

      fun mapping_family_child_map axis mapping slot =
        let
          val payload = Free ("mdd_mapping_payload", natT)
          val root = Free ("mdd_mapping_root", natT)
          val child = family_child_at axis root slot
          val mapped_item = HOLogic.mk_prod (payload, child)
          val body = Term.lambda payload (Term.lambda root mapped_item)
          val mapper = Const (@{const_name case_prod},
            fastype_of body --> pairT --> pairT) $ body
          val map_const = Const (@{const_name map}, (pairT --> pairT) -->
            pair_listT --> pair_listT)
        in map_const $ mapper $ pair_list mapping end

      fun mapping_family_prop axis mapping =
        let
          val slot = Free ("mdd_mapping_family_slot", natT)
          val width = nat (List.nth (radices, axis))
          val equation = HOLogic.mk_eq
            (mapping_cofactor_term state (nat axis) slot (pair_list mapping),
             some pair_listT (mapping_family_child_map axis mapping slot))
        in Logic.all slot
          (Logic.mk_implies
            (HOLogic.mk_Trueprop (mk_less (slot, width)),
             HOLogic.mk_Trueprop equation)) end

      fun mapping_family axis mapping =
        let
          val roots = map #2 mapping
          val width = nat (List.nth (radices, axis))
          val family_root = Free ("mdd_mapping_family_root", natT)
          val family_slot = Free ("mdd_mapping_family_slot", natT)
          val mapped_roots = Const (@{const_name map},
            (pairT --> natT) --> pair_listT --> nat_listT) $
              Const (@{const_name snd}, pairT --> natT) $ pair_list mapping
          val root_body = HOLogic.mk_imp
            (mk_less (family_slot, width),
             HOLogic.mk_eq
               (cofactor_term state (nat axis) family_slot family_root,
                some natT (family_child_at axis family_root family_slot)))
          val root_predicate = Term.lambda family_root
            (Const (@{const_name All}, (natT --> boolT) --> boolT) $
              Term.lambda family_slot root_body)
          val expected = mapping_family_prop axis mapping
        in
          case Mapping_Family_Table.lookup (!(#mapping_families state))
              (axis, mapping) of
            SOME ({theorem}: mapping_family) =>
              let
                val theorem = Utils.exact_prop ctxt "Cached MDD mapping cofactor family"
                  expected theorem
                val _ = #mapping_family_hits state := !(#mapping_family_hits state) + 1
              in {theorem=theorem}: mapping_family end
          | NONE =>
              let
                fun add_family root table =
                  if Inttab.defined table root then table
                  else Inttab.update (root, cofactor_family axis root) table
                val families = fold add_family roots Inttab.empty
                val root_families = profile_stage state "mapping_root_families" (fn () =>
                  let
                    fun add_object_family root table =
                      if Inttab.defined table root then table
                      else
                        let
                          val family = the (Inttab.lookup families root)
                          val theorem = Conv.fconv_rule (Object_Logic.atomize ctxt)
                            (#theorem family)
                        in Inttab.update (root, theorem) table end
                    val object_table = fold add_object_family roots Inttab.empty
                    val object_families = map (fn root =>
                      the (Inttab.lookup object_table root)) roots
                    val literal = Utils.literal_list_all ctxt
                      "MDD ordered mapping-root cofactor families" root_predicate
                      (map nat roots) object_families
                    val roots_ctxt = put_simpset HOL_basic_ss ctxt
                      |> Simplifier.add_simps @{thms list.map snd_conv}
                    val roots_conversion = Simplifier.rewrite roots_ctxt
                      (Thm.cterm_of ctxt mapped_roots)
                    val _ = if Thm.term_of (Thm.rhs_of roots_conversion) aconv nat_list roots
                      then () else error "MDD mapping root vector changed during transport"
                    val all_head = Const (@{const_name list_all},
                      (natT --> boolT) --> nat_listT --> boolT) $ root_predicate
                    val all_conversion = Thm.combination
                      (Thm.reflexive (Thm.cterm_of ctxt all_head)) roots_conversion
                    val proposition_conversion = Thm.combination
                      (Thm.reflexive (Thm.cterm_of ctxt
                        (Const (@{const_name Trueprop}, boolT --> @{typ prop}))))
                      all_conversion
                  in Thm.equal_elim (Thm.symmetric proposition_conversion) literal end)
                val radix = width
                val rule = Drule.infer_instantiate ctxt
                  [( ("radices",0), Thm.cterm_of ctxt (Store.radices store)),
                   (("nodes",0), Thm.cterm_of ctxt (Store.table store)),
                   (("axis",0), Thm.cterm_of ctxt (nat axis)),
                   (("mapping",0), Thm.cterm_of ctxt (pair_list mapping)),
                   (("radix",0), Thm.cterm_of ctxt radix),
                   (("slot",0), Thm.cterm_of ctxt family_slot)]
                  @{thm comma_crt_mdd_cofactor_mapping_family_from_rows}
                val theorem = Thm.implies_elim rule root_families
                val theorem = Thm.forall_intr
                  (Thm.cterm_of ctxt family_slot) theorem
                val theorem = Utils.exact_prop ctxt "MDD mapping cofactor family"
                  expected theorem
                val family: mapping_family = {theorem=theorem}
                val _ = #mapping_families state := Mapping_Family_Table.update
                  ((axis, mapping), family) (!(#mapping_families state))
                val _ = #mapping_family_builds state :=
                  !(#mapping_family_builds state) + 1
              in family end
        end

      fun reflexive_prop label proposition_term =
        let
          val variable = (case Term.add_vars (Thm.prop_of @{thm HOL.refl}) [] of
            [item] => #1 item
          | _ => error "HOL reflexivity theorem has an unexpected schematic shape")
          val theorem = Drule.infer_instantiate ctxt
            [(variable, Thm.cterm_of ctxt proposition_term)] @{thm HOL.refl}
          val expected = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (proposition_term, proposition_term))
        in Utils.exact_prop ctxt label expected theorem end

      fun interval_term radix =
        Const (@{const_name upt}, natT --> natT --> nat_listT) $ nat 0 $ radix

      fun mapped_slots function radix =
        let
          val slot = Free ("mdd_family_slot", natT)
          val map_const = Const (@{const_name map}, (natT --> fastype_of (function slot)) -->
            nat_listT --> HOLogic.listT (fastype_of (function slot)))
        in map_const $ Term.lambda slot (function slot) $ interval_term radix end

      fun node_cofactor axis slot root =
        (case node_at root of
          Store.Leaf _ => root
        | Store.Branch (node_axis, children) =>
            if node_axis = axis then List.nth (children, slot)
            else if axis < node_axis then root
            else error "Arena bind selected an axis below an operand branch")

      fun mapping_cofactor axis slot mapping =
        map (fn (payload, root) => (payload, node_cofactor axis slot root)) mapping

      fun validate_key (source, fallback, mapping) =
        let
          val _ = ignore (root_bound state source)
          val _ = ignore (root_bound state fallback)
          val _ = List.app (fn (_, root) => ignore (root_bound state root)) mapping
          val _ = if unique (map #1 mapping) then ()
            else error "Arena bind witness has duplicate source labels"
        in () end

      fun admit_witness (key as (source, fallback, mapping)) =
        let
          val _ = validate_key key
        in profile_stage state "bind_source_admission" (fn () => let
          val witness = Store.bind_witness store key
          val labels = #support witness
          val normalized = (source, fallback, restrict_mapping labels mapping)
          val _ = if #key witness = normalized andalso
              same_set labels (support_of source) andalso
              List.all (fn label => label >= 0) labels then ()
            else error "Arena bind witness differs from requested support-normalized key"
        in witness end) end

      fun publish_bind table label (key as (source, fallback, mapping)) result certificate =
        profile_stage state "bind_publication" (fn () => let
          val expected = HOLogic.mk_Trueprop (bind_prop state mapping fallback source result)
          val theorem = Utils.exact_prop ctxt label expected certificate
          val _ = table := Key_Table.update (key, (result, theorem)) (!table)
        in theorem end)

      val slot_bounds = Unsynchronized.ref (Inttab.empty: thm Inttab.table Inttab.table)
      fun slot_bound axis slot =
        let
          val by_slot = the_default Inttab.empty (Inttab.lookup (!slot_bounds) axis)
        in case Inttab.lookup by_slot slot of
          SOME theorem => theorem
        | NONE => let
            val (_, _, radix_equation) = axis_facts axis
            val numeric = prove_bool state "Selected branch numeric slot bound"
              (mk_less (nat slot, nat (List.nth (radices, axis)))) []
            val theorem = Thm.equal_elim
              (Thm.symmetric (radix_bound_conversion radix_equation (nat slot))) numeric
            val _ = slot_bounds := Inttab.update
              (axis, Inttab.update (slot, theorem) by_slot) (!slot_bounds)
          in theorem end
        end

      fun selected_cofactor axis slot root child =
        profile_stage state "selected_cofactor" (fn () => let
          val key = (axis, (slot, root))
          val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (cofactor_term state (nat axis) (nat slot) (nat root), some natT (nat child)))
        in
          case Selected_Cofactor_Table.lookup (!(#selected_cofactors state)) key of
            SOME (cached_child, theorem) =>
              let
                val _ = if cached_child = child then ()
                  else error "Cached selected cofactor has a different child"
                val _ = #selected_cofactor_hits state := !(#selected_cofactor_hits state) + 1
              in Utils.exact_prop ctxt "Cached selected cofactor" expected theorem end
          | NONE =>
              let
                val (axis_fact, positive_fact, radix_equation) = axis_facts axis
                val theorem = (case node_at root of
                  Store.Branch (node_axis, children) =>
                    if node_axis = axis then
                      let
                        val _ = if slot >= 0 andalso slot < length children andalso
                            List.nth (children, slot) = child then ()
                          else error "Selected cofactor child/slot mismatch"
                        val child_list = Thm.cterm_of ctxt (nat_list children)
                        val slot_ct = Thm.cterm_of ctxt (nat slot)
                        val lookup = Slots.literal_nth (#slot_successor state) slot
                          (Slots.nth_ct ctxt child_list slot_ct)
                        val selected = lookup RS @{thm meta_eq_to_obj_eq}
                        val result = @{thm comma_crt_mdd_selected_branch_cofactor} OF
                          [axis_fact, positive_fact, slot_bound axis slot,
                           root_bound state root, lookup_equation state root,
                           Store.branch_width store root, selected]
                      in Utils.exact_prop ctxt "Selected branch cofactor" expected result end
                    else prove_bool state "Selected bind cofactor"
                      (HOLogic.dest_Trueprop expected)
                      [root_bound state root, lookup_equation state root,
                       axis_fact, positive_fact, radix_equation]
                | Store.Leaf _ => prove_bool state "Selected bind cofactor"
                    (HOLogic.dest_Trueprop expected)
                    [root_bound state root, lookup_equation state root,
                     axis_fact, positive_fact, radix_equation])
                val _ = #selected_cofactors state := Selected_Cofactor_Table.update
                  (key, (child, theorem)) (!(#selected_cofactors state))
                val _ = #selected_cofactor_builds state :=
                  !(#selected_cofactor_builds state) + 1
              in theorem end
        end)

      fun selected_target fallback mapping payload target =
        profile_stage state "selected_target" (fn () => let
          val key = (fallback, (payload, mapping))
          val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (bind_target_term (nat fallback) (pair_list mapping) (nat payload), nat target))
        in
          case Selected_Target_Table.lookup (!(#selected_targets state)) key of
            SOME (cached_target, theorem) =>
              let
                val _ = if cached_target = target then ()
                  else error "Cached selected mapping has a different target"
                val _ = #selected_target_hits state := !(#selected_target_hits state) + 1
              in Utils.exact_prop ctxt "Cached selected target" expected theorem end
          | NONE =>
              let
                val theorem = prove_bool state "Selected bind target"
                  (HOLogic.dest_Trueprop expected) []
                val _ = #selected_targets state := Selected_Target_Table.update
                  (key, (target, theorem)) (!(#selected_targets state))
                val _ = #selected_target_builds state :=
                  !(#selected_target_builds state) + 1
              in theorem end
        end)

      fun branch_facts source fallback mapping result_root axis children result_eq =
        let
          val radix = (case try List.nth (#radices state, axis) of
            SOME width => width
          | NONE => error "MDD bind axis is outside the radix vector")
          val _ = if radix > 0 andalso length children = radix then ()
            else error "MDD bind output count disagrees with radix"
          val branch_matches = (case node_at result_root of
            Store.Branch (result_axis, result_children) =>
              result_axis = axis andalso result_children = children
          | Store.Leaf _ => false)
          val alias_matches = List.all (fn child => child = result_root) children
          val _ = if branch_matches orelse alias_matches then ()
            else error "MDD bind output is neither the branch nor its alias"
          val children_term = nat_list children
          val shape_term = HOLogic.mk_disj
            (HOLogic.mk_eq
              (Const (@{const_name nth}, nodesT --> natT --> nodeT) $
                Store.table store $ nat result_root,
               Const (@{const_name Comma_CRT_MDD_Branch},
                 natT --> nat_listT --> nodeT) $ nat axis $ children_term),
             list_all
               (Term.lambda (Free ("bind_result_child", natT))
                 (HOLogic.mk_eq
                   (Free ("bind_result_child", natT), nat result_root)))
               children_term)
          val shape = if branch_matches then
              let
                val _ = #direct_branch_shapes state := !(#direct_branch_shapes state) + 1
              in intro_closed state "MDD bind output shape"
                (HOLogic.mk_Trueprop shape_term) @{thm disjI1} [result_eq] end
            else prove_bool state "MDD bind output shape" shape_term [result_eq]
          val (axis_fact, positive_fact, radix_equation) = axis_facts axis
          val width_fact = prove_bool state "MDD bind output width"
            (HOLogic.mk_eq
              (Const (@{const_name size}, nat_listT --> natT) $ children_term,
               radix_at axis)) []
          val operand_roots = source :: fallback :: map #2 mapping
          val operand = Free ("bind_operand", natT)
          val mapped_roots = Const (@{const_name map},
            (pairT --> natT) --> pair_listT --> nat_listT) $
              Const (@{const_name snd}, pairT --> natT) $ pair_list mapping
          val operand_terms = HOLogic.cons_const natT $ nat source $
            (HOLogic.cons_const natT $ nat fallback $ mapped_roots)
          val operand_set = Const (@{const_name set}, nat_listT --> HOLogic.mk_setT natT) $
            operand_terms
          val upper = fold (fn n => fn m => Int.max (n,m)) operand_roots 0
          val below = prove_bool state "MDD bind operand ceiling"
            (ball operand_set
              (Term.lambda operand (HOLogic.mk_binrel @{const_name less_eq}
                (operand, nat upper)))) []
          val operands = (@{thm comma_crt_mdd_operands_bounded_by_ceiling} OF
            [root_bound state upper, below])
            |> Utils.exact_prop ctxt "MDD bind operand bounds"
              (HOLogic.mk_Trueprop (ball operand_set
                (Term.lambda operand (mk_less (operand, table_size state)))))
        in (radix, children_term, shape, axis_fact, positive_fact,
            radix_equation, width_fact, operands) end

      fun restrict_certificate source labels full_mapping fallback result inner =
        let
          val reduced = restrict_mapping labels full_mapping
          val expected_inner = HOLogic.mk_Trueprop
            (bind_prop state reduced fallback source result)
          val _ = if Thm.prop_of inner aconv expected_inner then ()
            else error "MDD bind restriction inner certificate has the wrong mapping"
        in
          if reduced = full_mapping then
            (#identity_restrictions state := !(#identity_restrictions state) + 1; inner)
          else
            let
              val proposition = bind_prop state full_mapping fallback source result
              val intro = Drule.infer_instantiate ctxt
                [(("labels",0),Thm.cterm_of ctxt (nat_list labels))]
                @{thm comma_crt_mdd_bind_certificate.bind_restrict}
              val cover_thm = cover source labels
            in mk_intro state "MDD bind support restriction" proposition intro
              [root_bound state source, cover_thm, inner] end
        end

      fun certify_key (key as (source, fallback, mapping): Arena.bind_key) =
        (case Key_Table.lookup (!(#bind_certificates state)) key of
          SOME (result_root, theorem) =>
            let
              val _ = root_bound state result_root
              val expected = HOLogic.mk_Trueprop
                (bind_prop state mapping fallback source result_root)
            in Utils.exact_prop ctxt "Cached internal MDD bind certificate"
              expected theorem end
        | NONE =>
            if Key_Table.defined (!(#active state)) key then
              error "Arena bind witness contains a recursive key cycle"
            else
              let
                val _ = #active state := Key_Table.update (key, ()) (!(#active state))
                val result = Exn.capture (fn () =>
                  let
                    val _ = #bind_visits state := !(#bind_visits state) + 1
                    val visits = !(#bind_visits state)
                    val _ = if visits mod 256 = 0 then
                      checkpoint state ("cold-bind-start-" ^ Int.toString visits) else ()
                    val witness = admit_witness key
                    val _ = if #key witness = key then ()
                      else error "Arena bind witness key is not support-normalized"
                    val result_root = #result witness
                    val source_bound = root_bound state source
                    val source_eq = lookup_equation state source
                    val result_bound = root_bound state result_root
                    val result_eq = lookup_equation state result_root
                    val proposition = bind_prop state mapping fallback source result_root
                    val certificate = (case #step witness of
                      Arena.Bind_Leaf payload =>
                        let
                          val _ = (case node_at source of
                            Store.Leaf actual => if actual = payload then ()
                              else error "Arena bind leaf payload differs from source node"
                          | Store.Branch _ => error "Leaf witness has a branch source")
                          val chosen = the_default fallback (AList.lookup (op =) mapping payload)
                          val _ = if chosen = result_root then ()
                            else error "Arena bind leaf selected a different output root"
                          val chosen_fact = prove_bool state "MDD bind leaf target selection"
                            (HOLogic.mk_eq (nat result_root,
                              bind_target_term (nat fallback) (pair_list mapping) (nat payload))) []
                          val fallback_bound = root_bound state fallback
                          val mapped_bounds = map (root_bound state o #2) mapping
                          val mapped = Free ("mapped_root", natT)
                          val map_snd = Const (@{const_name map},
                            (pairT --> natT) --> pair_listT --> nat_listT) $
                              Const (@{const_name snd}, pairT --> natT)
                          val all_mapped = prove_bool state "MDD bind leaf mapped-root bounds"
                            (ball
                              (Const (@{const_name set}, nat_listT --> HOLogic.mk_setT natT) $
                                (map_snd $ pair_list mapping))
                              (Term.lambda mapped (mk_less (mapped, table_size state))))
                            mapped_bounds
                          val intro = Drule.infer_instantiate ctxt
                            [( ("payload",0), Thm.cterm_of ctxt (nat payload))]
                            @{thm comma_crt_mdd_bind_certificate.bind_leaf}
                        in intro_closed state "MDD bind leaf certificate"
                          (HOLogic.mk_Trueprop proposition) intro
                          [source_bound, source_eq, chosen_fact, result_bound,
                           fallback_bound, all_mapped] end
                    | Arena.Bind_Selected_Leaf_Branch (axis, selected) =>
                        let
                          val _ = #selected_leaf_branches state :=
                            !(#selected_leaf_branches state) + 1
                          val _ = #selected_leaf_rows state :=
                            !(#selected_leaf_rows state) + length selected
                          val radix = (case try List.nth (#radices state, axis) of
                            SOME width => width
                          | NONE => error "Selected bind axis is outside the radix vector")
                          val _ = if radix > 0 andalso length selected = radix then ()
                            else error "Selected bind row count disagrees with radix"
                          fun validate_row (slot,(child,payload,target,out)) =
                            let
                              val _ = if node_cofactor axis slot source = child then ()
                                else error "Selected bind source cofactor differs from witness"
                              val _ = (case node_at child of
                                Store.Leaf value => if value = payload then ()
                                  else error "Selected bind source payload differs from witness"
                              | Store.Branch _ => error "Selected bind source is not a leaf")
                              val chosen = the_default fallback (AList.lookup (op =) mapping payload)
                              val _ = if target = chosen andalso
                                  node_cofactor axis slot target = out then ()
                                else error "Selected bind target differs from its cofactor"
                            in () end
                          val _ = List.app validate_row (map_index I selected)
                          val children = map (fn (_,_,_,out) => out) selected
                          val child_sources = map (fn (child,_,_,_) => child) selected
                          val payloads = map (fn (_,payload,_,_) => payload) selected
                          val source_term = nat_list child_sources
                          val payload_term = nat_list payloads
                          val (_, child_term, shape, axis_fact, positive_fact,
                            radix_equation, width_fact, operands) =
                            branch_facts source fallback mapping result_root axis children result_eq
                          val slot = Free ("selected_bind_slot", natT)
                          val source_at = nth nat_listT natT source_term slot
                          val payload_at = nth nat_listT natT payload_term slot
                          val result_at = nth nat_listT natT child_term slot
                          val source_node = Const (@{const_name nth}, nodesT --> natT --> nodeT) $
                            Store.table store $ source_at
                          val target = bind_target_term (nat fallback) (pair_list mapping) payload_at
                          val row_body = HOLogic.mk_conj
                            (HOLogic.mk_eq (cofactor_term state (nat axis) slot (nat source),
                               some natT source_at),
                             HOLogic.mk_conj
                              (mk_less (source_at, table_size state),
                               HOLogic.mk_conj
                                (HOLogic.mk_eq
                                  (source_node, Const (@{const_name Comma_CRT_MDD_Leaf},
                                    natT --> nodeT) $ payload_at),
                                 HOLogic.mk_eq (cofactor_term state (nat axis) slot target,
                                   some natT result_at))))
                          val predicate = Term.lambda slot row_body
                          fun row_proof (index,(child,payload,target,out)) =
                            let
                              val source_cofactor = selected_cofactor axis index source child
                              val target_cofactor = selected_cofactor axis index target out
                              val selection = selected_target fallback mapping payload target
                            in profile_stage state "selected_row_packaging" (fn () =>
                              let
                                val target_equation = Thm.symmetric (selection RS @{thm eq_reflection})
                                val selected = Conv.fconv_rule
                                  (Conv.arg_conv (Conv.arg1_conv (Conv.arg_conv
                                    (Conv.rewr_conv target_equation)))) target_cofactor
                              in @{thm conjI} OF [source_cofactor,
                                @{thm conjI} OF [root_bound state child,
                                  @{thm conjI} OF [lookup_equation state child, selected]]] end) end
                          val proofs = map_index row_proof selected
                          val vector = Thm.reflexive o Thm.cterm_of ctxt
                          val fields = (vector source_term, vector payload_term, vector child_term)
                          val all_rows = indexed_slots state radix predicate proofs
                            (Slots.selected_conversion ctxt (#slot_successor state) fields)
                          val point_rule = Drule.infer_instantiate ctxt
                            [(("P",0),Thm.cterm_of ctxt predicate),
                             (("n",0),Thm.cterm_of ctxt (nat radix)),
                             (("i",0),Thm.cterm_of ctxt slot)]
                            @{thm comma_crt_mdd_indexed_allD}
                          val point_rule = Thm.implies_elim point_rule all_rows
                          val axis_guard = HOLogic.mk_Trueprop (mk_less (slot, radix_at axis))
                          val guard_ct = Thm.cterm_of ctxt axis_guard
                          val guard = Thm.assume guard_ct
                          val numeric_guard = Thm.equal_elim
                            (radix_bound_conversion radix_equation slot) guard
                          val point = Thm.implies_elim point_rule numeric_guard
                            |> Conv.fconv_rule Drule.beta_eta_conversion
                          val rows = Thm.forall_intr (Thm.cterm_of ctxt slot)
                            (Thm.implies_intr guard_ct point)
                          val rule = Drule.infer_instantiate ctxt
                            [(("axis",0),Thm.cterm_of ctxt (nat axis)),
                             (("children",0),Thm.cterm_of ctxt child_term),
                             (("source_child",0),Thm.cterm_of ctxt (Term.lambda slot source_at)),
                             (("payload",0),Thm.cterm_of ctxt (Term.lambda slot payload_at))]
                            @{thm comma_crt_mdd_bind_certificate.bind_selected_leaf_branch}
                        in intro_closed state "Selected bind branch certificate"
                          (HOLogic.mk_Trueprop proposition) rule
                          [source_bound, result_bound, shape, axis_fact,
                           positive_fact, width_fact, operands, rows] end
                    | Arena.Bind_Branch (axis, child_keys) =>
                        let
                          val radix = (case try List.nth (#radices state, axis) of
                            SOME width => width
                          | NONE => error "Arena bind axis is outside the radix vector")
                          val _ = if radix > 0 andalso length child_keys = radix then ()
                            else error "Arena bind witness child count disagrees with radix"
                          val _ = (case node_at source of
                            Store.Branch (source_axis, _) => if axis <= source_axis then ()
                              else error "Arena bind axis follows its source branch"
                          | Store.Leaf _ => error "Branch witness has a leaf source")
                          val source_family = cofactor_family axis source
                          val fallback_family = cofactor_family axis fallback
                          val mapping_family_proof = mapping_family axis mapping
                          fun child_info (slot, child_key) =
                            let
                              val (child_source, child_fallback, child_mapping) = child_key
                              val source_child = node_cofactor axis slot source
                              val fallback_child = node_cofactor axis slot fallback
                              val raw_mapping_child = mapping_cofactor axis slot mapping
                              val child_witness = Store.bind_witness store child_key
                              val child_labels = #support child_witness
                              val _ = if #key child_witness = child_key andalso
                                  child_source = source_child andalso
                                  child_fallback = fallback_child andalso
                                  child_mapping = restrict_mapping child_labels raw_mapping_child
                                then () else error "Arena bind child key differs from its cofactors"
                              val inner = certify_key child_key
                              val child_cert = restrict_certificate child_source child_labels
                                raw_mapping_child child_fallback (#result child_witness)
                                inner
                            in {result= #result child_witness,
                                certificate=child_cert} end
                          val infos = map_index child_info child_keys
                          val results = map #result infos
                          val (_, results_term, shape_fact, axis_fact, positive_fact,
                            radix_equation, width_fact, all_operands) =
                            branch_facts source fallback mapping result_root axis results result_eq
                          val radix_axis_term = radix_at axis
                          val radix_term = nat radix
                          val slot = Free ("bind_slot", natT)
                          val source_children_term = mapped_slots
                            (fn child_slot => family_child_term axis source child_slot)
                            radix_term
                          val fallback_children_term = mapped_slots
                            (fn child_slot => family_child_term axis fallback child_slot)
                            radix_term
                          val mapping_children_term = mapped_slots
                            (fn child_slot => mapping_family_child_map axis mapping child_slot)
                            radix_term
                          val slot_source = nth nat_listT natT source_children_term slot
                          val slot_fallback = nth nat_listT natT fallback_children_term slot
                          val slot_mapping = nth pair_list_listT pair_listT mapping_children_term slot
                          val slot_result = nth nat_listT natT results_term slot
                          val child_certificate = bind_term state slot_mapping slot_fallback
                            slot_source slot_result
                          val child_certificate_predicate =
                            Term.lambda slot child_certificate
                          val operand_roots = distinct (op =)
                            (source :: fallback :: map #2 mapping)
                          fun item_context () = Simplifier.add_simps
                            (map (lookup_equation state) operand_roots) (#simp_ctxt state)
                          val field_equations = map (slot_vector state item_context)
                            [mapping_children_term, fallback_children_term, source_children_term] @
                            [Thm.reflexive (Thm.cterm_of ctxt results_term)]
                          val child_certificates = indexed_slots state radix
                            child_certificate_predicate (map #certificate infos)
                            (Slots.bind_conversion ctxt (#slot_successor state) field_equations)
                          val source_children_exact = reflexive_prop
                            "MDD source cofactor-family vector" source_children_term
                          val fallback_children_exact = reflexive_prop
                            "MDD fallback cofactor-family vector" fallback_children_term
                          val mapping_children_exact = reflexive_prop
                            "MDD mapping cofactor-family vector" mapping_children_term
                          val row_slot = Free ("bind_row_slot", natT)
                          val row_rule = Drule.infer_instantiate ctxt
                            [(("radices",0),Thm.cterm_of ctxt (Store.radices store)),
                             (("nodes",0),Thm.cterm_of ctxt (Store.table store)),
                             (("mapping",0),Thm.cterm_of ctxt (pair_list mapping)),
                             (("axis",0),Thm.cterm_of ctxt (nat axis)),
                             (("radix",0),Thm.cterm_of ctxt radix_term),
                             (("source",0),Thm.cterm_of ctxt (nat source)),
                             (("fallback_root",0),Thm.cterm_of ctxt (nat fallback)),
                             (("source_children",0),Thm.cterm_of ctxt source_children_term),
                             (("fallback_children",0),Thm.cterm_of ctxt fallback_children_term),
                             (("result_children",0),Thm.cterm_of ctxt results_term),
                             (("mapping_children",0),Thm.cterm_of ctxt mapping_children_term),
                             (("slot",0),Thm.cterm_of ctxt row_slot)]
                            @{thm comma_crt_mdd_bind_branch_row_transport}
                          val row_theorem = Thm.implies_elim row_rule
                            (#theorem source_family)
                          val row_theorem = Thm.implies_elim row_theorem
                            (#theorem fallback_family)
                          val row_theorem = Thm.implies_elim row_theorem
                            (#theorem mapping_family_proof)
                          val row_theorem = Thm.implies_elim row_theorem
                            source_children_exact
                          val row_theorem = Thm.implies_elim row_theorem
                            fallback_children_exact
                          val row_theorem = Thm.implies_elim row_theorem
                            mapping_children_exact
                          val row_theorem = Thm.implies_elim row_theorem
                            child_certificates
                          val row_theorem = Thm.forall_intr
                            (Thm.cterm_of ctxt row_slot) row_theorem
                          val row_source = nth nat_listT natT source_children_term row_slot
                          val row_fallback = nth nat_listT natT fallback_children_term row_slot
                          val row_mapping = nth pair_list_listT pair_listT
                            mapping_children_term row_slot
                          val row_result = nth nat_listT natT results_term row_slot
                          val row_body = HOLogic.mk_conj
                            (HOLogic.mk_eq
                              (cofactor_term state (nat axis) row_slot (nat source),
                               some natT row_source),
                             HOLogic.mk_conj
                              (HOLogic.mk_eq
                                (cofactor_term state (nat axis) row_slot (nat fallback),
                                 some natT row_fallback),
                               HOLogic.mk_conj
                                (HOLogic.mk_eq
                                  (mapping_cofactor_term state (nat axis) row_slot
                                    (pair_list mapping), some pair_listT row_mapping),
                                 bind_term state row_mapping row_fallback row_source row_result)))
                          val row_expected = Logic.all row_slot
                            (Logic.mk_implies
                              (HOLogic.mk_Trueprop (mk_less (row_slot, radix_term)),
                               HOLogic.mk_Trueprop row_body))
                          val row_theorem = Utils.exact_prop ctxt
                            "MDD bind family row transport" row_expected row_theorem
                          val row_at = Drule.forall_elim_list
                            [Thm.cterm_of ctxt row_slot] row_theorem
                          val axis_guard = HOLogic.mk_Trueprop
                            (mk_less (row_slot, radix_axis_term))
                          val axis_guard_ct = Thm.cterm_of ctxt axis_guard
                          val axis_guard_fact = Thm.assume axis_guard_ct
                          val numeric_guard_fact = Thm.equal_elim
                            (radix_bound_conversion radix_equation row_slot) axis_guard_fact
                          val row_point = Thm.implies_elim row_at numeric_guard_fact
                          val combined_rows = Thm.forall_intr (Thm.cterm_of ctxt row_slot)
                            (Thm.implies_intr axis_guard_ct row_point)
                          val _ = Utils.exact_prop ctxt "MDD combined bind rows"
                            (Logic.all row_slot (Logic.mk_implies
                              (axis_guard, HOLogic.mk_Trueprop row_body))) combined_rows
                          val rule = Drule.infer_instantiate ctxt
                            [(("axis",0),Thm.cterm_of ctxt (nat axis)),
                             (("children",0),Thm.cterm_of ctxt results_term),
                             (("source_child",0),Thm.cterm_of ctxt
                               (Term.lambda row_slot row_source)),
                             (("default_child",0),Thm.cterm_of ctxt
                               (Term.lambda row_slot row_fallback)),
                             (("mapping_child",0),Thm.cterm_of ctxt
                               (Term.lambda row_slot row_mapping))]
                            @{thm comma_crt_mdd_bind_branch_combined_rows}
                        in intro_closed state "MDD bind branch certificate"
                          (HOLogic.mk_Trueprop proposition) rule
                          [source_bound, result_bound, shape_fact, axis_fact,
                           positive_fact, width_fact, all_operands, combined_rows] end)
                    val theorem = publish_bind (#bind_certificates state)
                      "MDD bind certificate" key result_root certificate
                    val _ = if visits mod 256 = 0 then
                      checkpoint state ("cold-bind-complete-" ^ Int.toString visits) else ()
                  in theorem end) ()
                val _ = #active state := Key_Table.delete key (!(#active state))
              in Exn.release result end)

      fun certify_public (input_key as (source, fallback, full_mapping)) =
        (case Key_Table.lookup (!(#public_bind_certificates state)) input_key of
          SOME (result_root, theorem) =>
            Utils.exact_prop ctxt "Cached public MDD bind certificate"
              (HOLogic.mk_Trueprop (bind_prop state full_mapping fallback source result_root)) theorem
        | NONE =>
            let
              val witness = admit_witness input_key
              val labels = #support witness
              val inner = certify_key (#key witness)
              val theorem = restrict_certificate source labels full_mapping fallback
                (#result witness) inner
              val theorem = publish_bind (#public_bind_certificates state)
                "Public MDD bind certificate" input_key (#result witness) theorem
              val _ = if not (!(#first_public_checkpoint state)) then
                (#first_public_checkpoint state := true;
                 checkpoint state "first-public-bind-complete")
                else ()
            in theorem end)

      val public: replay = {state=state, certify=certify_public, certify_cover=cover}
    in public end

  fun certify_bind ({certify, ...}: replay) key = certify key
  fun certify_cover ({certify_cover, ...}: replay) root labels = certify_cover root labels
  fun bind_eval_phase ({state={store, ctxt, ...}, certify, ...}: replay) key =
    let
      val certificate = certify key
      val theorem = @{thm comma_crt_mdd_bind_certificate_eval_phase} OF
        [Store.wellformed store, certificate]
      val _ = if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
          null (Thm.tpairs_of theorem) andalso
          Context.subthy (Thm.theory_of_thm theorem, Proof_Context.theory_of ctxt)
        then () else error "MDD bind phase transport is not a closed store theorem"
    in theorem end
  fun statistics ({state, ...}: replay) =
    let
      val {store, bind_visits, cover_visits, ...} = state
    in Store.statistics store ^
      " bind_certificate_nodes=" ^ Int.toString (!bind_visits) ^
      " payload_cover_nodes=" ^ Int.toString (!cover_visits) ^
      " " ^ proof_profile_summary state end
end
