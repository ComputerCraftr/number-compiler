(* Build exact DAG point-lookup equations in one top-down pass per
   authenticated source block.  The result is consumed by Mass_Rows; this
   module never infers rows from parsed producer data. *)
structure Comma_Semantic_B1_Mass_Source_Rows =
struct
  type source_binding = {
    base: int, extent: int, constant: term, definition: thm, interval: thm}

  val closed = Comma_Semantic_B1_Mass_Layout.closed

  fun make ctxt arithmetic_context dag node_count
      (bindings: source_binding list) =
    let
      val natT = @{typ nat}
      val boolT = @{typ bool}
      val blockT = @{typ comma_semantic_b1_crt_column_block}
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val lookupT = @{typ "(nat \<times> nat list) option"}
      val dag_lookup = Const
        (@{const_name comma_semantic_b1_crt_column_dag_lookup}, dagT --> natT --> lookupT)
      val block_lookup = Const
        (@{const_name comma_semantic_b1_crt_column_block_lookup}, blockT --> natT --> lookupT)
      val transport = Const
        (@{const_name comma_semantic_b1_crt_mass_source_lookup_transport},
          dagT --> natT --> natT --> blockT --> boolT)
      val less_eq = Const (@{const_name less_eq}, natT --> natT --> boolT)
      val less = Const (@{const_name less}, natT --> natT --> boolT)
      val nat = HOLogic.mk_number natT
      val dag_ct = Thm.cterm_of ctxt dag
      val pairT = HOLogic.mk_prodT (natT, HOLogic.listT natT)
      val optionT = @{typ "(nat \<times> nat list) option"}
      val some = Const (@{const_name Some}, pairT --> optionT)
      val lookup_facts = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      val visited = Unsynchronized.ref 0
      val requests = Unsynchronized.ref 0
      val missing = Unsynchronized.ref 0
      val provider_started = Time.now ()
      val _ = if node_count >= 2 andalso fastype_of dag = dagT andalso closed dag then () else
        error "B1 source-row provider has an invalid DAG authority or extent"

      fun clean theorem = Thm.nprems_of theorem = 0 andalso
        null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
        closed (Thm.prop_of theorem) andalso
        Context.subthy (Thm.theory_of_thm theorem, Proof_Context.theory_of ctxt)

      fun is_const term = (case term of Const _ => true | _ => false)

      fun validate_binding ({base, extent, constant, definition, interval}: source_binding) =
        let
          val upper_value = base + extent
          val upper_term = nat upper_value
          val body = Thm.term_of (Thm.rhs_of definition)
          val definition_expected = Logic.mk_equals (constant, body)
          val cid = Bound 0
          val interval_body = HOLogic.mk_imp
            (HOLogic.mk_conj (less_eq $ nat base $ cid, less $ cid $ upper_term),
             HOLogic.mk_eq (dag_lookup $ dag $ cid, block_lookup $ constant $ cid))
          val interval_expected = HOLogic.mk_Trueprop
            (HOLogic.mk_all ("cid", natT, interval_body))
          val _ = if base >= 2 andalso extent > 0 andalso extent <= 512 andalso
              upper_value <= node_count andalso is_const constant then () else
            error "B1 source-row block interval is malformed"
          val _ = if fastype_of constant = blockT andalso fastype_of body = blockT andalso
              closed constant andalso closed body andalso
              Thm.prop_of definition aconv definition_expected andalso clean definition then () else
            error "B1 source-row block definition changed its exact authority"
          val _ = if Thm.prop_of interval aconv interval_expected andalso clean interval then () else
            error "B1 source-row interval changed its exact DAG/block request"
        in (body, upper_value, upper_term) end

      val sorted = sort (int_ord o apply2 #base) bindings
      fun validate_order [] _ = ()
        | validate_order ((binding: source_binding) :: rest) previous_upper =
            let
              val base = #base binding
              val upper = base + #extent binding
              val _ = (case previous_upper of
                NONE => ()
              | SOME previous => if previous <= base then () else
                  error "B1 source-row intervals overlap or are out of order")
            in validate_order rest (SOME upper) end
      val _ = validate_order sorted NONE
      val validated = map (fn binding => (binding, validate_binding binding)) sorted
      val source_theorems = maps
        (fn (({definition, interval, ...}: source_binding), _) => [definition, interval]) validated
      val _ = if null (Thm_Deps.all_oracles source_theorems) then () else
        error "B1 source-row binding bundle depends on an oracle"

      val root_rule = @{thm comma_semantic_b1_crt_mass_source_lookup_transport_root}
      val split_rule = @{thm comma_semantic_b1_crt_mass_source_lookup_transport_split}

      (* Prepare each fixed, monomorphic kernel rule once.  The shared helper
         validates the complete schematic-variable layout and then uses typed
         instantiation, avoiding Drule's repeated type inference per node. *)
      val instantiate_root = Comma_Semantic_B1_Mass_Layout.prepare_rule root_rule
      val instantiate_split = Comma_Semantic_B1_Mass_Layout.prepare_rule split_rule

      fun apply_premises theorem premises =
        fold (fn premise => fn rule => Thm.implies_elim rule premise)
          premises theorem

      fun bounds lower_term key_term upper_term =
        Comma_Semantic_B1_Column_Lookup_Cache.natural_bound ctxt arithmetic_context
          (HOLogic.mk_conj
            (less_eq $ lower_term $ key_term, less $ key_term $ upper_term))

      fun dest_natural term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) =>
            if typ = natT andalso value >= 0 andalso term aconv nat value then value
            else error "B1 source-row block contains a non-canonical natural numeral"
        | NONE => error "B1 source-row block contains a non-numeric field")

      fun block_walk dag lower_value upper_value lower_term upper_term
          subtree subtree_ct transport_fact =
        (case strip_comb subtree of
          (Const (name, _), []) =>
            if name = @{const_name Comma_B1_CRT_Column_Block_Empty} then () else
              error "B1 source-row traversal found an unknown block leaf"
        | (Const (name, _), [key_term, level_term, children_term, left, right]) =>
            if name = @{const_name Comma_B1_CRT_Column_Block_Node} then
              let
                val key = dest_natural key_term
                val _ = if lower_value <= key andalso key < upper_value then () else
                  error "B1 source-row block key escaped its checked interval"
                val bound_prop = bounds lower_term key_term upper_term
                val lower_fact = @{thm conjunct1} OF [bound_prop]
                val upper_fact = @{thm conjunct2} OF [bound_prop]
                val (key_ct, level_ct, children_ct, left_ct, right_ct) =
                  (case Comma_Semantic_B1_Mass_Layout.application_arguments 5 subtree_ct of
                    [key_ct, level_ct, children_ct, left_ct, right_ct] =>
                      (key_ct, level_ct, children_ct, left_ct, right_ct)
                  | _ => error "B1 source block cterm has a malformed constructor spine")
                val split_rule = instantiate_split
                  [("dag", dag_ct),
                   ("lower", Thm.cterm_of ctxt lower_term),
                   ("key", key_ct),
                   ("upper", Thm.cterm_of ctxt upper_term),
                   ("level", level_ct),
                   ("children", children_ct),
                   ("left", left_ct),
                   ("right", right_ct)]
                val split_fact = apply_premises split_rule
                  [lower_fact, upper_fact, transport_fact]
                val key_fact = @{thm conjunct1} OF [split_fact]
                val children_transports = @{thm conjunct2} OF [split_fact]
                val left_transport = @{thm conjunct1} OF [children_transports]
                val right_transport = @{thm conjunct2} OF [children_transports]
                val expected_row = some $ HOLogic.mk_prod (level_term, children_term)
                val lhs = dag_lookup $ dag $ nat key
                val expected_key = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, expected_row))
                val expected_left = HOLogic.mk_Trueprop
                  (transport $ dag $ lower_term $ key_term $ left)
                val expected_right = HOLogic.mk_Trueprop
                  (transport $ dag $ HOLogic.mk_Suc key_term $ upper_term $ right)
                val expected_split = HOLogic.mk_Trueprop
                  (HOLogic.mk_conj (HOLogic.mk_eq (lhs, expected_row),
                    HOLogic.mk_conj
                      (transport $ dag $ lower_term $ key_term $ left,
                       transport $ dag $ HOLogic.mk_Suc key_term $ upper_term $ right)))
                val _ = if Thm.prop_of split_fact aconv expected_split andalso
                    Thm.prop_of key_fact aconv expected_key andalso
                    Thm.prop_of left_transport aconv expected_left andalso
                    Thm.prop_of right_transport aconv expected_right then () else
                  error "B1 source-row split theorem changed its exact DAG/child requests"
                val equation = key_fact RS @{thm eq_reflection}
                val _ = if Thm.prop_of equation aconv Logic.mk_equals (lhs, expected_row) andalso
                    clean equation then () else
                  error "B1 source-row lookup fact is not exact and standalone"
                val _ = if Inttab.defined (!lookup_facts) key then
                    error "B1 source-row traversal found duplicate CIDs"
                  else lookup_facts := Inttab.update (key, equation) (!lookup_facts)
                val _ = visited := !visited + 1
                val _ = if !visited mod 4096 = 0 then
                    Comma_Proof_Profile.report
                      ("B1 source block traversal nodes=" ^ Int.toString (!visited) ^
                       " elapsed_ms=" ^ LargeInt.toString
                         (Time.toMilliseconds (Time.- (Time.now (), provider_started))))
                  else ()
                fun visit_child subtree_ct child lower_n upper_n lower_t upper_t
                    child_transport =
                  (case strip_comb child of
                    (Const (empty, _), []) =>
                      if empty = @{const_name Comma_B1_CRT_Column_Block_Empty} then () else
                        error "B1 source-row traversal found an unknown child leaf"
                  | (Const (node, _), [_ , _, _, _, _]) =>
                      if node = @{const_name Comma_B1_CRT_Column_Block_Node} then
                        block_walk dag lower_n upper_n lower_t upper_t
                          child subtree_ct child_transport
                      else error "B1 source-row traversal found an unknown child node"
                  | _ => error "B1 source-row traversal found a malformed child")
                val _ = visit_child left_ct left lower_value key lower_term key_term
                  left_transport
                val _ = visit_child right_ct right (key + 1) upper_value
                  (HOLogic.mk_Suc key_term) upper_term right_transport
              in () end
            else error "B1 source-row traversal found an unknown block node"
        | _ => error "B1 source-row traversal found a malformed block")

      val _ = List.app
        (fn (({base, extent, constant, definition, interval, ...}: source_binding),
              (body, upper_value, upper_term)) =>
          let
            val root_equation = definition RS @{thm meta_eq_to_obj_eq}
            val before_nodes = !visited
            val block_started = Time.now ()
            val _ = Comma_Proof_Profile.report
              ("B1 source block start base=" ^ Int.toString base ^
               " extent=" ^ Int.toString extent)
            val body_ct = Thm.rhs_of definition
            val instantiated_root = instantiate_root
              [("dag", dag_ct),
               ("lower", Thm.cterm_of ctxt (nat base)),
               ("upper", Thm.cterm_of ctxt upper_term),
               ("constant", Thm.lhs_of definition),
               ("subtree", body_ct)]
            val root_transport = apply_premises instantiated_root [interval, root_equation]
            val expected_transport = HOLogic.mk_Trueprop
              (transport $ dag $ nat base $ upper_term $ body)
            val _ = if Thm.prop_of root_transport aconv expected_transport andalso
                clean root_transport then () else
              error "B1 source-row root transport changed its checked interval"
            val _ = block_walk dag base upper_value (nat base) upper_term body
              body_ct root_transport
            val _ = Comma_Proof_Profile.report
              ("B1 source block complete base=" ^ Int.toString base ^
               " nodes=" ^ Int.toString (!visited - before_nodes) ^
               " elapsed_ms=" ^ LargeInt.toString
                 (Time.toMilliseconds (Time.- (Time.now (), block_started))))
          in () end) validated

      fun lookup cid =
        (requests := !requests + 1;
         case Inttab.lookup (!lookup_facts) cid of
           SOME theorem => theorem
         | NONE => (missing := !missing + 1;
             error "B1 source-row CID has no exact authenticated block lookup"))
      fun counters () =
        " source_block_nodes=" ^ Int.toString (!visited) ^
        " source_block_point_facts=" ^ Int.toString (Inttab.size (!lookup_facts)) ^
        " source_point_fact_requests=" ^ Int.toString (!requests) ^
        " source_point_fact_missing=" ^ Int.toString (!missing) ^
        " source_block_elapsed_ms=" ^ LargeInt.toString
          (Time.toMilliseconds (Time.- (Time.now (), provider_started)))
    in {lookup = lookup, counters = counters} end
end
