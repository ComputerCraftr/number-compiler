(*
   Focused row certificate builder for the sparse mass-tree invariant.

   This file is loaded with the conversion helpers before the registered
   column regression hook.  It replaces the one large simp proof of
   mass_tree_rows_valid with a structural proof.  The published tree authority
   is kept separate from the candidate body.  In production that authority is
   a named alias, so row proofs never carry a free-equality premise containing
   the 31k-node candidate.

   Source rows are supplied by an already authenticated source lookup callback.
   The provider below specializes one checked interval and delegates the
   selected block path to Column_Lookup_Cache; it never trusts parsed rows.
*)
structure Comma_Semantic_B1_Mass_Rows =
struct
  type source_row = {cid: int, level: int, children: int list, theorem: thm}

  type request = {
      ctxt: Proof.context,
      arithmetic_context: Proof.context,
      dag: term,
      tree: term,
      tree_cterm: cterm,
      published_tree: term,
      root_equation: thm,
      ordered_fact: thm,
      node_count: int,
      source_row: int -> source_row
    }

  fun structurally_closed th =
    Thm.nprems_of th = 0 andalso null (Thm.hyps_of th) andalso
    null (Thm.tpairs_of th) andalso
    null (Term.add_frees (Thm.prop_of th) []) andalso
    null (Term.add_vars (Thm.prop_of th) [])

  fun closed th =
    structurally_closed th andalso null (Thm_Deps.all_oracles [th])

  fun check_source ctxt dag ({cid, level, children, theorem}: source_row) =
    let
      val natT = @{typ nat}
      val lookupT = @{typ "(nat \<times> nat list) option"}
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val lookup = Const
        (@{const_name comma_semantic_b1_crt_column_dag_lookup},
          dagT --> natT --> lookupT)
      val expected = lookup $ dag $ HOLogic.mk_number natT cid
      val pairT = HOLogic.mk_prodT (natT, HOLogic.listT natT)
      val optionT = @{typ "(nat \<times> nat list) option"}
      val some = Const (@{const_name Some}, pairT --> optionT)
      val expected_result = some $
        HOLogic.mk_prod
          (HOLogic.mk_number natT level,
           HOLogic.mk_list natT (map (HOLogic.mk_number natT) children))
      val proposition = Thm.prop_of theorem
      val _ = if Context.subthy
          (Thm.theory_of_thm theorem, Proof_Context.theory_of ctxt) then () else
        error "B1 mass row source theorem comes from a foreign theory"
      (* The source bundle is audited once before this helper is entered.
         Re-running Thm_Deps.all_oracles for every row is deliberately
         avoided; the final closed theorem is checked by closed. *)
      val _ = if structurally_closed theorem then () else
        error "B1 mass row source theorem is not closed"
      val _ = if proposition aconv
          HOLogic.mk_Trueprop (HOLogic.mk_eq (expected, expected_result)) then ()
        else error "B1 mass row source theorem changed exact DAG lookup"
    in () end

  (* A direct, selected-path evaluator for the annotation lookup.  It is
     deliberately separate from the source lookup evaluator: source lookup is
     delegated to Column_Conversion.controlled_lookup, while this evaluator
     only sees a closed balanced mass tree and follows one branch. *)
  fun lookup_equation ctxt arithmetic_context tree tree_ct lookup_ct cid =
    let
      val natT = @{typ nat}
      val cid_ct = Thm.cterm_of ctxt (HOLogic.mk_number natT cid)
      val request_ct = Thm.apply (Thm.apply lookup_ct tree_ct) cid_ct
      val request = Thm.term_of request_ct
      val lookup_node = @{thm comma_semantic_b1_crt_mass_tree_lookup.simps(2)}
        RS @{thm eq_reflection}
      val lookup_empty = @{thm comma_semantic_b1_crt_mass_tree_lookup.simps(1)}
        RS @{thm eq_reflection}
      val choose_if =
        Comma_Semantic_B1_Column_Conversion.choose_closed_if ctxt arithmetic_context
          ("B1 mass row lookup expected an if node",
           "B1 mass row lookup guard did not normalize",
           "B1 mass row lookup encountered malformed if")
      fun walk tree_term request_ct =
        (case strip_comb tree_term of
          (Const (name, _), []) =>
            if name = @{const_name Comma_B1_CRT_Mass_Tree_Empty} then
              Conv.rewr_conv lookup_empty request_ct
            else error "B1 mass row lookup found an unknown leaf"
        | (Const (name, _), [key, _, _, left, right]) =>
            if name = @{const_name Comma_B1_CRT_Mass_Tree_Node} then
              let
                val root = Conv.rewr_conv lookup_node
                  request_ct
                val first = choose_if (Thm.rhs_of root)
                val key_value = (case try HOLogic.dest_number key of
                  SOME (_, n) => n
                | NONE => error "B1 mass row lookup has a non-numeric key")
                val next =
                  if cid = key_value then first
                  else
                    let
                      val second = choose_if (Thm.rhs_of first)
                    in
                      if cid < key_value then
                        Thm.transitive first
                          (Thm.transitive second (walk left (Thm.rhs_of second)))
                      else
                        Thm.transitive first
                          (Thm.transitive second (walk right (Thm.rhs_of second)))
                    end
              in Thm.transitive root next end
            else error "B1 mass row lookup found an unknown node"
        | _ => error "B1 mass row lookup found malformed tree")
      val equation = walk tree request_ct
      val _ = if Thm.term_of (Thm.lhs_of equation) aconv request then () else
        error "B1 mass row lookup changed its requested root"
      val _ = if Thm.nprems_of equation = 0 andalso
          null (Thm.hyps_of equation) andalso
          null (Term.add_frees (Thm.term_of (Thm.rhs_of equation)) []) andalso
          null (Term.add_vars (Thm.term_of (Thm.rhs_of equation)) []) then () else
        error "B1 mass row lookup produced an open or conditional equation"
    in equation end

  type source_binding = {
      base: int, extent: int, constant: term, definition: thm, interval: thm}

  (* The source owner certifies each admitted block by one shared interval
     traversal.  This adapter only decodes its exact, named-DAG point theorem;
     it does not repeat directory bounds or block-root searches per row. *)
  fun source_row_provider ctxt arithmetic_context dag node_count
      (bindings: source_binding list) =
    let
      val provider = Comma_Semantic_B1_Mass_Source_Rows.make
        ctxt arithmetic_context dag node_count bindings
      val source_rows = Unsynchronized.ref 0
      fun dest_nat term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) => if typ = @{typ nat} andalso value >= 0 then value
            else error "B1 mass source row contains a non-natural numeral"
        | NONE => error "B1 mass source row contains a non-numeric field")
      fun lookup cid =
        let
          val equation = (#lookup provider) cid
          val rhs = Thm.term_of (Thm.rhs_of equation)
          val (level, children) =
            (case rhs of
              Const (name, _) $ pair =>
                if name = @{const_name Some} then
                  (case pair of
                    Const (pair_name, _) $ level_term $ children_term =>
                      if pair_name = @{const_name Pair} then
                        (dest_nat level_term,
                         map dest_nat (HOLogic.dest_list children_term))
                      else error "B1 mass row source lookup returned a malformed pair"
                  | _ => error "B1 mass row source lookup returned a malformed pair")
                else error "B1 mass row source lookup returned None"
            | _ => error "B1 mass row source lookup returned malformed option")
          val theorem = equation RS @{thm meta_eq_to_obj_eq}
          val row = {cid = cid, level = level, children = children,
            theorem = theorem}: source_row
          val _ = if cid >= 2 andalso cid < node_count then () else
            error "B1 mass row source CID is outside the checked node range"
          val _ = source_rows := !source_rows + 1
          val _ = if !source_rows mod 512 = 0 then
            Comma_Proof_Profile.report
              ("B1 mass source-row progress rows=" ^ Int.toString (!source_rows) ^
               ((#counters provider) ()))
            else ()
        in row end
      fun counters () = " source_rows=" ^ Int.toString (!source_rows) ^
        ((#counters provider) ())
    in {lookup = lookup, counters = counters} end

  fun make ({ctxt, arithmetic_context, dag, tree, tree_cterm, published_tree,
             root_equation, ordered_fact, node_count, source_row}: request) =
    let
      val natT = @{typ nat}
      val treeT = @{typ comma_semantic_b1_crt_mass_tree}
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val boolT = @{typ bool}
      val lookupT = @{typ "(nat \<times> nat) option"}
      val rows = Const
        (@{const_name comma_semantic_b1_crt_mass_tree_rows_valid},
          dagT --> treeT --> treeT --> boolT)
      val lookup = Const
        (@{const_name comma_semantic_b1_crt_mass_tree_lookup},
          treeT --> natT --> lookupT)
      val ordered = Const
        (@{const_name comma_semantic_b1_crt_mass_tree_ordered},
          natT --> natT --> treeT --> boolT)
      val lookup_transport = Const
        (@{const_name comma_semantic_b1_crt_mass_tree_lookup_transport},
          treeT --> natT --> natT --> treeT --> boolT)
      val lookup_ct = Thm.cterm_of ctxt lookup
      val row_fact_count = Unsynchronized.ref 0
      val source_row_calls = Unsynchronized.ref 0
      val source_row_elapsed = Unsynchronized.ref Time.zeroTime
      val source_check_elapsed = Unsynchronized.ref Time.zeroTime
      val row_summary_checks = Unsynchronized.ref 0
      val row_summary_elapsed = Unsynchronized.ref Time.zeroTime
      val row_started = Time.now ()
      val row_valid = Const
        (@{const_name comma_semantic_b1_crt_mass_tree_row_valid},
          dagT --> treeT --> natT --> natT --> natT --> boolT)
      val root_meta = root_equation
      val _ = if fastype_of published_tree = treeT andalso
          null (Term.add_frees published_tree []) andalso
          null (Term.add_vars published_tree []) then () else
        error "B1 mass row tree authority is open or ill-typed"
      val _ = if Thm.prop_of root_meta aconv Logic.mk_equals (published_tree, tree) andalso
          Thm.nprems_of root_meta = 0 andalso null (Thm.hyps_of root_meta) andalso
          null (Thm.tpairs_of root_meta) andalso closed root_meta andalso
          Context.subthy (Thm.theory_of_thm root_meta,
            Proof_Context.theory_of ctxt) then () else
        error "B1 mass row root equation changed its exact tree authority"
      val expected_ordered = HOLogic.mk_Trueprop
        (ordered $ HOLogic.mk_number natT 2 $
          HOLogic.mk_number natT node_count $ tree)
      val _ = if Thm.prop_of ordered_fact aconv expected_ordered andalso
          structurally_closed ordered_fact then () else
        error "B1 mass row layout theorem changed its exact candidate tree"
      val lookup_cache = Unsynchronized.ref
        (Inttab.empty: thm Inttab.table)
      val lookup_path_fallbacks = Unsynchronized.ref 0
      val _ = if null (Term.add_frees tree []) andalso
          null (Term.add_vars tree []) then () else
        error "B1 mass row candidate tree is open"
      val _ = if fastype_of (Thm.term_of tree_cterm) = treeT andalso
          Thm.term_of tree_cterm aconv tree then () else
        error "B1 mass row candidate cterm does not match its tree"
      val trueprop_ct = Thm.cterm_of ctxt @{term Trueprop}
      val dag_ct = Thm.cterm_of ctxt dag
      val published_tree_ct = Thm.lhs_of root_meta
      val rows_ct = Thm.cterm_of ctxt rows
      val rows_dag_ct = Thm.apply rows_ct dag_ct
      val rows_authority_ct = Thm.apply rows_dag_ct published_tree_ct

      val root_equality = root_meta RS @{thm meta_eq_to_obj_eq}
      val root_transport_rule = Drule.infer_instantiate ctxt
        [(("root", 0), published_tree_ct),
         (("lower", 0), Thm.cterm_of ctxt (HOLogic.mk_number natT 2)),
         (("upper", 0), Thm.cterm_of ctxt (HOLogic.mk_number natT node_count)),
         (("tree", 0), tree_cterm)] @{thm comma_semantic_b1_crt_mass_tree_lookup_transport_root}
      val root_transport = root_transport_rule OF [root_equality]
      val expected_root_transport = HOLogic.mk_Trueprop
        (lookup_transport $ published_tree $
          HOLogic.mk_number natT 2 $ HOLogic.mk_number natT node_count $ tree)
      val _ = if Thm.prop_of root_transport aconv expected_root_transport andalso
          Thm.nprems_of root_transport = 0 andalso
          null (Thm.hyps_of root_transport) then () else
        error "B1 mass row root interval transport changed its named authority"

      val cterm_arguments = Comma_Semantic_B1_Mass_Layout.application_arguments
      val prepare_rule = Comma_Semantic_B1_Mass_Layout.prepare_rule
      val split_rule = prepare_rule
        @{thm comma_semantic_b1_crt_mass_tree_lookup_transport_split}

      fun checked_fact label expected theorem =
        if Thm.prop_of theorem aconv expected andalso
            Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem) then theorem
        else error ("B1 mass row " ^ label ^ " changed its exact interval request")

      fun collect_lookup_facts (subtree, subtree_ct, lower_value, upper_value,
            lower_term, upper_term,
            subtree_ordered, subtree_transport) =
        let
          val expected_ordered = HOLogic.mk_Trueprop
            (ordered $ lower_term $ upper_term $ subtree)
          val _ = checked_fact "subtree layout" expected_ordered subtree_ordered
          val expected_transport = HOLogic.mk_Trueprop
            (lookup_transport $ published_tree $
              lower_term $ upper_term $ subtree)
          val _ = checked_fact "subtree transport" expected_transport subtree_transport
        in
          (case strip_comb subtree of
            (Const (name, _), []) =>
              if name = @{const_name Comma_B1_CRT_Mass_Tree_Empty} then ()
              else error "B1 mass lookup transport found an unknown leaf"
          | (Const (name, _), [cid, level, mass, left, right]) =>
              if name = @{const_name Comma_B1_CRT_Mass_Tree_Node} then
                let
                  val (cid_ct, level_ct, mass_ct, left_ct, right_ct) =
                    (case cterm_arguments 5 subtree_ct of
                      [cid_ct, level_ct, mass_ct, left_ct, right_ct] =>
                        (cid_ct, level_ct, mass_ct, left_ct, right_ct)
                    | _ => error "B1 mass transport node has malformed cterm spine")
                  val arguments =
                    [("lower", Thm.cterm_of ctxt lower_term),
                     ("upper", Thm.cterm_of ctxt upper_term),
                     ("key", cid_ct), ("level", level_ct), ("mass", mass_ct),
                     ("left", left_ct), ("right", right_ct)]
                  val transport_arguments = ("root", published_tree_ct) :: arguments
                  fun apply_transport rule =
                    Thm.implies_elim
                      (Thm.implies_elim (rule transport_arguments) subtree_ordered)
                      subtree_transport
                  val cid_value = (case try HOLogic.dest_number cid of
                    SOME (typ, value) =>
                      if typ = natT andalso value >= 0 then value
                      else error "B1 mass transport key is not a natural numeral"
                  | NONE => error "B1 mass transport key is not numeric")
                  val _ = if cid aconv HOLogic.mk_number natT cid_value then () else
                    error "B1 mass transport key is not a canonical numeral"
                  val _ = if lower_value <= cid_value andalso
                      cid_value < upper_value then () else
                    error "B1 mass transport key is outside its authenticated interval"
                  val split_fact = apply_transport split_rule
                  val key_fact = split_fact RS @{thm conjunct1}
                  val children_fact = split_fact RS @{thm conjunct2}
                  val pairT = HOLogic.mk_prodT (natT, natT)
                  val some = Const (@{const_name Some}, pairT --> lookupT)
                  val expected_lookup =
                    Logic.mk_equals
                      (lookup $ published_tree $ HOLogic.mk_number natT cid_value,
                       some $ HOLogic.mk_prod (level, mass))
                  val key_fact = key_fact RS @{thm eq_reflection}
                  val key_fact = checked_fact "point lookup" expected_lookup key_fact
                  val _ = (case Inttab.lookup (!lookup_cache) cid_value of
                    NONE => lookup_cache := Inttab.update (cid_value, key_fact) (!lookup_cache)
                  | SOME _ => error "B1 mass annotation contains a duplicate ordered key")
                  val left_ordered = children_fact RS @{thm conjunct1}
                  val right_and_transport = children_fact RS @{thm conjunct2}
                  val right_ordered = right_and_transport RS @{thm conjunct1}
                  val transports = right_and_transport RS @{thm conjunct2}
                  val left_transport = transports RS @{thm conjunct1}
                  val right_transport = transports RS @{thm conjunct2}
                  val _ = collect_lookup_facts
                    (left, left_ct, lower_value, cid_value,
                     lower_term, cid, left_ordered, left_transport)
                  val _ = collect_lookup_facts
                    (right, right_ct, cid_value + 1, upper_value,
                     Const (@{const_name Suc}, natT --> natT) $ cid,
                     upper_term, right_ordered, right_transport)
                in () end
              else error "B1 mass lookup transport found an unknown node"
          | _ => error "B1 mass lookup transport found a malformed tree")
        end

      val _ = collect_lookup_facts
        (tree, tree_cterm, 2, node_count,
         HOLogic.mk_number natT 2, HOLogic.mk_number natT node_count,
         ordered_fact, root_transport)
      val _ = Comma_Proof_Profile.report
        ("B1 mass interval lookup facts=" ^ Int.toString (Inttab.size (!lookup_cache)))

      fun fixed_lookup cid =
        (case Inttab.lookup (!lookup_cache) cid of
          SOME theorem => theorem
        | NONE =>
            let
              val _ = lookup_path_fallbacks := !lookup_path_fallbacks + 1
              val candidate = lookup_equation ctxt arithmetic_context tree tree_cterm
                lookup_ct cid
              val cid_ct = Thm.cterm_of ctxt (HOLogic.mk_number natT cid)
              val one_argument =
                Thm.combination (Thm.reflexive lookup_ct) root_meta
              val two_arguments =
                Thm.combination one_argument (Thm.reflexive cid_ct)
              val fixed = Thm.transitive two_arguments candidate
              val _ = if Thm.nprems_of fixed = 0 andalso
                  null (Thm.hyps_of fixed) andalso
                  null (Term.add_frees (Thm.prop_of fixed) []) then () else
                error "B1 mass row published-tree lookup is not standalone"
              val _ = lookup_cache := Inttab.update (cid, fixed) (!lookup_cache)
            in fixed end)

      val summaryT = @{typ comma_semantic_b1_crt_child_vector_summary}
      val summary_lookup = Const
        (@{const_name comma_semantic_b1_crt_child_vector_summary_of},
          treeT --> HOLogic.listT natT --> Type (@{type_name option}, [summaryT]))
      val summary_prefix = Thm.apply (Thm.cterm_of ctxt summary_lookup) published_tree_ct
      val scalar_context = arithmetic_context addsimps
        @{thms max_def min_def comma_crt_period_def nth_Cons'}
      val empty_summary_rule = prepare_rule
        @{thm comma_semantic_b1_crt_child_vector_summary_empty}
      val zero_summary_rule = prepare_rule
        @{thm comma_semantic_b1_crt_child_vector_summary_terminal_zero}
      val one_summary_rule = prepare_rule
        @{thm comma_semantic_b1_crt_child_vector_summary_terminal_one}
      val node_summary_rule = prepare_rule
        @{thm comma_semantic_b1_crt_child_vector_summary_node}
      val row_summary_rule = prepare_rule
        @{thm comma_semantic_b1_crt_mass_tree_row_valid_of_child_vector_summary}
      type vector_summary =
        {fact: thm, count: cterm, maximum: cterm, minimum: cterm, total: cterm}
      val vector_cache = Unsynchronized.ref (Termtab.empty: vector_summary Termtab.table)
      val vector_capacity = 8192
      val vector_builds = Unsynchronized.ref 0
      val vector_hits = Unsynchronized.ref 0
      val vector_refusals = Unsynchronized.ref 0
      fun apply_premises theorem premises =
        fold (fn premise => fn rule => Thm.implies_elim rule premise) premises theorem
      fun numeric_fact proposition =
        let
          val equation = Simplifier.rewrite scalar_context (Thm.cterm_of ctxt proposition)
          val _ = if Thm.nprems_of equation = 0 andalso
              Thm.term_of (Thm.lhs_of equation) aconv proposition andalso
              Thm.term_of (Thm.rhs_of equation) aconv @{term True} then () else
            (Comma_Proof_Profile.report
               ("B1 scalar obligation rejected: " ^ Syntax.string_of_term ctxt proposition ^
                " -> " ^ Syntax.string_of_term ctxt (Thm.term_of (Thm.rhs_of equation)));
             error "B1 mass row simplifier did not close the exact row predicate")
          val lifted = Thm.combination (Thm.reflexive trueprop_ct) equation
        in Thm.equal_elim (Thm.symmetric lifted) @{thm TrueI} end
      fun normalized_summary children_ct theorem =
        let
          val equation = theorem RS @{thm eq_reflection}
          (* Only the four scalar result fields are normalized. No summary
             recursion or mass-tree lookup rule belongs to this context. *)
          val reduced = Thm.transitive equation
            (Simplifier.rewrite scalar_context (Thm.rhs_of equation))
          val expected = Thm.term_of (Thm.apply summary_prefix children_ct)
          val _ = if Thm.term_of (Thm.lhs_of reduced) aconv expected andalso
              structurally_closed reduced then () else
            error "B1 child-vector summary changed its exact ordered request"
          val body_ct = #2 (Thm.dest_comb (Thm.rhs_of reduced))
          val fields = cterm_arguments 4 body_ct
          val _ = (case strip_comb (Thm.term_of (Thm.rhs_of reduced)) of
            (Const (some, _), [body]) =>
              if some = @{const_name Some} then
                (case strip_comb body of
                  (Const (constructor, _), [_, _, _, _]) =>
                    if constructor = @{const_name Comma_Semantic_B1_CRT_Child_Vector_Summary}
                      then () else error "B1 child-vector summary has a foreign constructor"
                | _ => error "B1 child-vector summary has malformed fields")
              else error "B1 child-vector summary is missing a nonterminal lookup"
          | _ => error "B1 child-vector summary is not a checked result")
          val _ = List.app (fn field =>
            ignore (Comma_Semantic_B1_Mass_Layout.dest_nat (Thm.term_of field)
              "B1 child-vector summary has a nonnumeric field")) fields
        in case fields of
          [count, maximum, minimum, total] =>
            {fact = reduced RS @{thm meta_eq_to_obj_eq}, count = count,
             maximum = maximum, minimum = minimum, total = total}: vector_summary
        | _ => error "B1 child-vector summary has the wrong arity" end
      fun child_vector_summary children_ct =
        let
          val children = Thm.term_of children_ct
        in case Termtab.lookup (!vector_cache) children of
          SOME result => (vector_hits := !vector_hits + 1; result)
        | NONE =>
            let
              val fact = (case strip_comb children of
                (Const (name, _), []) =>
                  if name = @{const_name Nil} then
                    empty_summary_rule [("tree", published_tree_ct)]
                  else error "B1 child-vector summary has an unknown list leaf"
              | (Const (name, _), [child, _]) =>
                  if name = @{const_name Cons} then
                    let
                      val (head, tail_ct) = Thm.dest_comb children_ct
                      val child_ct = #2 (Thm.dest_comb head)
                      val tail = child_vector_summary tail_ct
                      val child_value = Comma_Semantic_B1_Mass_Layout.dest_nat child
                        "B1 child-vector summary has a nonnumeric child"
                      val arguments = [("tree", published_tree_ct), ("children", tail_ct),
                        ("vector_count", #count tail), ("vector_maximum", #maximum tail),
                        ("vector_minimum", #minimum tail), ("vector_total", #total tail)]
                    in
                      if child_value = 0 then
                        Thm.implies_elim (zero_summary_rule arguments) (#fact tail)
                      else if child_value = 1 then
                        Thm.implies_elim (one_summary_rule arguments) (#fact tail)
                      else
                        let
                          val lookup = fixed_lookup child_value
                          val pair_ct = #2 (Thm.dest_comb (Thm.rhs_of lookup))
                          val (level_ct, mass_ct) =
                            (case cterm_arguments 2 pair_ct of
                              [level_ct, mass_ct] => (level_ct, mass_ct)
                            | _ => error "B1 child-vector lookup has malformed pair")
                          val rule = node_summary_rule
                            (("child", child_ct) :: ("child_level", level_ct) ::
                             ("child_mass", mass_ct) :: arguments)
                          val bound = numeric_fact
                            (HOLogic.mk_binrel @{const_name less_eq}
                              (HOLogic.mk_number natT 2, child))
                        in apply_premises rule
                          [#fact tail, bound, lookup RS @{thm meta_eq_to_obj_eq}] end
                    end
                  else error "B1 child-vector summary has an unknown list constructor"
              | _ => error "B1 child-vector summary has malformed ordered children")
              val result = normalized_summary children_ct fact
              val _ = vector_builds := !vector_builds + 1
              val _ = if Termtab.size (!vector_cache) < vector_capacity then
                  vector_cache := Termtab.update (children, result) (!vector_cache)
                else vector_refusals := !vector_refusals + 1
            in result end
        end

      fun row_request cid level mass =
        row_valid $ dag $ published_tree $ HOLogic.mk_number natT cid $
          HOLogic.mk_number natT level $ HOLogic.mk_number natT mass

      fun small_row_fact cid level mass =
        let
          val _ = if 2 <= cid andalso cid < node_count then () else
            error "B1 mass row candidate CID is outside the authenticated node range"
          val source_started = Time.now ()
          val source_result = source_row cid
          val _ = source_row_calls := !source_row_calls + 1
          val _ = source_row_elapsed := Time.+ (!source_row_elapsed,
            Time.- (Time.now (), source_started))
          val {cid = source_cid, level = source_level, children, theorem} =
            source_result
          val source = {cid = source_cid, level = source_level,
            children = children, theorem = theorem}: source_row
          val source_check_started = Time.now ()
          val _ = check_source ctxt dag source
          val _ = source_check_elapsed := Time.+ (!source_check_elapsed,
            Time.- (Time.now (), source_check_started))
          val _ = if source_cid = cid andalso source_level = level then () else
            error "B1 mass row candidate disagrees with authenticated source row"
          val _ = if forall (fn child => child >= 0 andalso child < node_count) children
            then () else error "B1 mass row source contains a foreign child CID"
          val children_ct = #2 (Thm.dest_comb (#2 (Thm.dest_comb
            (#2 (Thm.dest_comb (#2 (Thm.dest_comb (Thm.cprop_of theorem))))))))
          val _ = if Thm.term_of children_ct aconv
              HOLogic.mk_list natT (map (HOLogic.mk_number natT) children) then () else
            error "B1 mass row child-vector cterm changed its source order"
          val summary_started = Time.now ()
          val summary = child_vector_summary children_ct
          val request = row_request cid level mass
          val rule = row_summary_rule
            [("dag", dag_ct), ("tree", published_tree_ct),
             ("cid", Thm.cterm_of ctxt (HOLogic.mk_number natT cid)),
             ("level", Thm.cterm_of ctxt (HOLogic.mk_number natT level)),
             ("mass", Thm.cterm_of ctxt (HOLogic.mk_number natT mass)),
             ("children", children_ct), ("vector_count", #count summary),
             ("vector_maximum", #maximum summary), ("vector_minimum", #minimum summary),
             ("vector_total", #total summary)]
          val premises = Logic.strip_imp_prems (Thm.prop_of rule)
          val facts = map_index (fn (position, premise) =>
            if position = 0 then theorem
            else if position = 3 then #fact summary
            else numeric_fact (HOLogic.dest_Trueprop premise)) premises
          val fact = apply_premises rule facts
          val _ = row_summary_checks := !row_summary_checks + 1
          val _ = row_summary_elapsed := Time.+ (!row_summary_elapsed,
            Time.- (Time.now (), summary_started))
          val _ = if Thm.prop_of fact aconv HOLogic.mk_Trueprop request andalso
              structurally_closed fact then () else
            error "B1 mass row summary proof changed its exact row predicate"
          val _ = row_fact_count := !row_fact_count + 1
          val _ = if !row_fact_count mod 512 = 0 then
            Comma_Proof_Profile.report
              ("B1 mass row proofs=" ^ Int.toString (!row_fact_count) ^
               " vector_summary_builds=" ^ Int.toString (!vector_builds) ^
               " vector_summary_hits=" ^ Int.toString (!vector_hits) ^
               " vector_summary_capacity_refusals=" ^ Int.toString (!vector_refusals) ^
               " source_row_calls=" ^ Int.toString (!source_row_calls) ^
               " source_row_elapsed_ms=" ^ LargeInt.toString
                 (Time.toMilliseconds (!source_row_elapsed)) ^
               " source_check_elapsed_ms=" ^ LargeInt.toString
                 (Time.toMilliseconds (!source_check_elapsed)) ^
               " row_summary_checks=" ^ Int.toString (!row_summary_checks) ^
               " row_summary_elapsed_ms=" ^ LargeInt.toString
                 (Time.toMilliseconds (!row_summary_elapsed)) ^
               " elapsed_ms=" ^ LargeInt.toString
                 (Time.toMilliseconds (Time.- (Time.now (), row_started))))
            else ()
        in fact end

      fun conjunction [] = error "B1 mass rows cannot combine an empty fact list"
        | conjunction [fact] = fact
        | conjunction (fact :: rest) = @{thm conjI} OF [fact, conjunction rest]

      fun rows_fact (subtree, subtree_ct) =
        (case strip_comb subtree of
          (Const (name, _), []) =>
            if name = @{const_name Comma_B1_CRT_Mass_Tree_Empty} then
              let
                val request_ct = Thm.apply rows_authority_ct subtree_ct
                val equation = Conv.rewr_conv
                  (@{thm comma_semantic_b1_crt_mass_tree_rows_valid.simps(1)}
                    RS @{thm eq_reflection}) request_ct
                val proposition = Thm.combination
                  (Thm.reflexive trueprop_ct) equation
                val fact = Thm.equal_elim
                  (Thm.symmetric proposition) @{thm TrueI}
              in fact end
            else error "B1 mass rows found an unknown leaf"
        | (Const (name, _), [cid, level, mass, left, right]) =>
            if name = @{const_name Comma_B1_CRT_Mass_Tree_Node} then
              let
                val (left_ct, right_ct) =
                  (case cterm_arguments 5 subtree_ct of
                    [_, _, _, left_ct, right_ct] =>
                      (left_ct, right_ct)
                  | _ => error "B1 mass node cterm has malformed constructor spine")
                val cid_value = (case try HOLogic.dest_number cid of
                  SOME (_, n) => n | NONE => error "B1 mass row key is not numeral")
                val level_value = (case try HOLogic.dest_number level of
                  SOME (_, n) => n | NONE => error "B1 mass row level is not numeral")
                val mass_value = (case try HOLogic.dest_number mass of
                  SOME (_, n) => n | NONE => error "B1 mass row value is not numeral")
                val row_fact = small_row_fact cid_value level_value mass_value
                val left_fact = rows_fact (left, left_ct)
                val right_fact = rows_fact (right, right_ct)
                val request_ct = Thm.apply rows_authority_ct subtree_ct
                val unfold = Conv.rewr_conv
                  (@{thm comma_semantic_b1_crt_mass_tree_rows_valid.simps(2)}
                    RS @{thm eq_reflection}) request_ct
                val proposition = Thm.combination
                  (Thm.reflexive trueprop_ct) unfold
              in Thm.equal_elim (Thm.symmetric proposition)
                   (conjunction [row_fact, left_fact, right_fact]) end
            else error "B1 mass rows found an unknown node"
        | _ => error "B1 mass rows found malformed tree")

      (* The candidate subtree is concrete only in the third argument.  The
         first tree argument remains the published authority throughout. *)
      val local_fact = rows_fact (tree, tree_cterm)
      val rows_dag = Thm.combination
        (Thm.reflexive rows_ct) (Thm.reflexive dag_ct)
      val rows_dag_tree = Thm.combination rows_dag
        (Thm.reflexive published_tree_ct)
      val root_substitution = Thm.combination rows_dag_tree root_meta
      val root_proposition = Thm.combination
        (Thm.reflexive trueprop_ct) root_substitution
      val result = Thm.equal_elim (Thm.symmetric root_proposition) local_fact
      (* The enclosing validity certificate is audited once at publication.
         Keep structural checks here without rescanning its full dependency
         graph; small_row_fact still checks each supplied row proposition. *)
      val _ = if structurally_closed result then () else
        error "B1 mass rows did not produce a closed published-tree theorem"
      val frozen_lookup_cache = !lookup_cache
      val _ = if Inttab.size frozen_lookup_cache = !row_fact_count then () else
        error "B1 mass row lookup cache does not cover each proven node"
      val _ = Comma_Proof_Profile.report
        ("B1 mass lookup summary interval_facts=" ^
         Int.toString (Inttab.size (!lookup_cache)) ^
         " root_search_fallbacks=" ^ Int.toString (!lookup_path_fallbacks) ^
         " source_row_calls=" ^ Int.toString (!source_row_calls) ^
         " source_row_elapsed_ms=" ^ LargeInt.toString
           (Time.toMilliseconds (!source_row_elapsed)) ^
         " source_check_elapsed_ms=" ^ LargeInt.toString
           (Time.toMilliseconds (!source_check_elapsed)) ^
         " row_summary_checks=" ^ Int.toString (!row_summary_checks) ^
         " row_summary_elapsed_ms=" ^ LargeInt.toString
           (Time.toMilliseconds (!row_summary_elapsed)))
      (* Keep the exact, already-certified named-root point facts with this
         proof owner.  The mass invariant specializes these facts directly;
         it must not repeat a root-to-leaf search for the same annotation. *)
      fun published_lookup_fact cid =
        let
          val _ = if cid >= 0 andalso cid < node_count then () else
            error "B1 mass row cached lookup CID is outside the checked extent"
          val theorem = (case Inttab.lookup frozen_lookup_cache cid of
            SOME fact => fact
          | NONE => error "B1 mass row cached lookup does not cover the requested CID")
          val nat_cid = HOLogic.mk_number natT cid
          val expected_lhs = lookup $ published_tree $ nat_cid
          val lhs = Thm.term_of (Thm.lhs_of theorem)
          val rhs = Thm.term_of (Thm.rhs_of theorem)
          val _ = if lhs aconv expected_lhs andalso fastype_of rhs = lookupT andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem) andalso
              Context.subthy (Thm.theory_of_thm theorem,
                Proof_Context.theory_of ctxt) andalso
              null (Term.add_frees (Thm.prop_of theorem) []) andalso
              null (Term.add_vars (Thm.prop_of theorem) []) then () else
            error "B1 mass row cached lookup changed its exact named authority"
          val _ = (case rhs of
            Const (name, _) $ (Const (pair_name, _) $ level $ mass) =>
              if name = @{const_name Some} andalso pair_name = @{const_name Pair} andalso
                  fastype_of level = natT andalso fastype_of mass = natT then () else
                error "B1 mass row cached lookup has a malformed result"
          | _ => error "B1 mass row cached lookup is not a successful point lookup")
        in theorem end
    in {theorem = result, lookup_fact = published_lookup_fact,
        lookup_facts = Inttab.size frozen_lookup_cache} end

  (* A deliberately tiny regression for the published-tree proof boundary.  It
     uses the same one-node DAG shape as the checked HOL mass-annotation
     regression: level 0 has radix 4 and the child vector repeats CID 1.
     The wrong-source callback keeps the authenticated theorem but changes
     the claimed child vector, so acceptance would indicate that row labels
     were being trusted independently of the exact DAG equation. *)
  fun check_fixture ctxt =
    let
      val natT = @{typ nat}
      val blockT = @{typ comma_semantic_b1_crt_column_block}
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val treeT = @{typ comma_semantic_b1_crt_mass_tree}
      fun nat n = HOLogic.mk_number natT n
      fun ids xs = HOLogic.mk_list natT (map nat xs)
      val empty_block = @{term Comma_B1_CRT_Column_Block_Empty}
      val block_node = Const (@{const_name Comma_B1_CRT_Column_Block_Node},
        natT --> natT --> HOLogic.listT natT --> blockT --> blockT --> blockT)
      val row = block_node $ nat 2 $ nat 0 $ ids [1, 1, 0, 0] $
        empty_block $ empty_block
      val dag_block = Const (@{const_name Comma_B1_CRT_Column_DAG_Block},
        natT --> natT --> blockT --> dagT)
      val dag = dag_block $ nat 2 $ nat 1 $ row
      val lookupT = @{typ "(nat \<times> nat list) option"}
      val lookup = Const (@{const_name comma_semantic_b1_crt_column_dag_lookup},
        dagT --> natT --> lookupT)
      val source_request = lookup $ dag $ nat 2
      val source_context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
        @{thms comma_semantic_b1_crt_column_dag_lookup.simps
          comma_semantic_b1_crt_column_block_lookup.simps}
      val source_theorem = Simplifier.rewrite source_context
        (Thm.cterm_of ctxt source_request) RS @{thm meta_eq_to_obj_eq}
      val tree_empty = @{term Comma_B1_CRT_Mass_Tree_Empty}
      val tree_node = Const (@{const_name Comma_B1_CRT_Mass_Tree_Node},
        natT --> natT --> natT --> treeT --> treeT --> treeT)
      fun mass_node key mass left right =
        tree_node $ nat key $ nat 0 $ nat mass $ left $ right
      val mass_lookup = Const
        (@{const_name comma_semantic_b1_crt_mass_tree_lookup},
          treeT --> natT --> @{typ "(nat \<times> nat) option"})
      val mass_lookup_ct = Thm.cterm_of ctxt mass_lookup
      val pairT = HOLogic.mk_prodT (natT, natT)
      val mass_lookupT = @{typ "(nat \<times> nat) option"}
      val some = Const (@{const_name Some}, pairT --> mass_lookupT)
      val none = Const (@{const_name None}, mass_lookupT)
      fun found level mass = some $ HOLogic.mk_prod (nat level, nat mass)
      val left_tree = mass_node 2 10 tree_empty tree_empty
      val right_tree = mass_node 8 20 tree_empty tree_empty
      val branch_tree = mass_node 5 30 left_tree right_tree
      val branch_cterm = Thm.cterm_of ctxt branch_tree
      fun check_lookup cid expected =
        let
          val equation = lookup_equation ctxt source_context branch_tree
            branch_cterm mass_lookup_ct cid
          val actual = Thm.term_of (Thm.rhs_of equation)
        in if actual aconv expected then () else
          error "B1 mass-row lookup fixture selected the wrong branch" end
      val _ = check_lookup 2 (found 0 10)
      val _ = check_lookup 8 (found 0 20)
      val _ = check_lookup 1 none
      val tree = tree_node $ nat 2 $ nat 0 $ nat 462 $ tree_empty $ tree_empty
      val tree_cterm = Thm.cterm_of ctxt tree
      val tree_ordered_fact =
        Comma_Semantic_B1_Mass_Layout.make ctxt source_context 3 tree
      val published_tree = tree
      val root_equation = Thm.reflexive tree_cterm
      val rows = Const (@{const_name comma_semantic_b1_crt_mass_tree_rows_valid},
        dagT --> treeT --> treeT --> @{typ bool})
      fun source_row children =
        {cid = 2, level = 0, children = children, theorem = source_theorem}:
          source_row
      val request = {ctxt = ctxt, arithmetic_context = source_context,
        dag = dag, tree = tree, tree_cterm = tree_cterm,
        published_tree = published_tree, root_equation = root_equation,
        ordered_fact = tree_ordered_fact, node_count = 3,
        source_row = fn _ => source_row [1, 1, 0, 0]}: request
      val {theorem = result, lookup_fact, lookup_facts} = make request
      val expected = HOLogic.mk_Trueprop (rows $ dag $ tree $ tree)
      val _ = if Thm.prop_of result aconv expected then () else
        error "B1 mass-row fixture returned the wrong published-tree proposition"
      val _ = if lookup_facts = 1 andalso
          Thm.term_of (Thm.lhs_of (lookup_fact 2)) aconv
            (mass_lookup $ tree $ nat 2) then () else
        error "B1 mass-row fixture did not retain its exact named-root lookup"
      val _ = (case Exn.capture (fn () => lookup_fact 1) () of
        Exn.Exn (ERROR "B1 mass row cached lookup does not cover the requested CID") => ()
      | Exn.Exn exn => Exn.reraise exn
      | Exn.Res _ => error "B1 mass-row fixture accepted an uncached in-range CID")
      val _ = (case Exn.capture (fn () => lookup_fact 3) () of
        Exn.Exn (ERROR "B1 mass row cached lookup CID is outside the checked extent") => ()
      | Exn.Exn exn => Exn.reraise exn
      | Exn.Res _ => error "B1 mass-row fixture accepted an out-of-range CID")
      fun expect_wrong_mass_rejected operation =
        (case Exn.capture operation () of
          Exn.Exn (ERROR message) =>
            if message =
                "B1 mass row simplifier did not close the exact row predicate" then ()
            else error ("B1 wrong-mass fixture failed for the wrong reason: " ^ message)
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error "B1 mass-row fixture accepted a false mass")
      val wrong_tree = mass_node 2 461 tree_empty tree_empty
      val wrong_tree_cterm = Thm.cterm_of ctxt wrong_tree
      val wrong_tree_ordered_fact =
        Comma_Semantic_B1_Mass_Layout.make ctxt source_context 3 wrong_tree
      val _ = expect_wrong_mass_rejected (fn () => make
        ({ctxt = ctxt, arithmetic_context = source_context,
          dag = dag, tree = wrong_tree, tree_cterm = wrong_tree_cterm,
          published_tree = wrong_tree, root_equation = Thm.reflexive wrong_tree_cterm,
          ordered_fact = wrong_tree_ordered_fact,
          node_count = 3,
          source_row = fn _ => source_row [1, 1, 0, 0]}: request))
      fun changed_source _ = source_row [1, 1, 0, 1]
      fun expect_rejected operation =
        (case Exn.capture operation () of
          Exn.Exn (ERROR message) =>
            if message = "B1 mass row source theorem changed exact DAG lookup" then ()
            else error ("B1 mass-row negative fixture failed for the wrong reason: " ^ message)
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error "B1 mass-row negative fixture accepted a changed source row")
      val _ = expect_rejected (fn () => make
        ({ctxt = ctxt, arithmetic_context = source_context,
          dag = dag, tree = tree, tree_cterm = tree_cterm,
          published_tree = published_tree, root_equation = root_equation,
          ordered_fact = tree_ordered_fact, node_count = 3,
          source_row = changed_source}: request))
    in () end

end
