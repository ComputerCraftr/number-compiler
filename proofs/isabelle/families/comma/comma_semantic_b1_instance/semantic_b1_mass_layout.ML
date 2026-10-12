(*
   Consume the generic layout theorem for the published mass tree.

   The annotation is certified directly as a carried cterm tree.  Each
   recursive result contains the child ordered and height facts, so a parent
   unfolds only its own constructor.  No row list, sort, midpoint builder, or
   whole-subtree simplifier is part of the production proof path.
*)
structure Comma_Semantic_B1_Mass_Layout =
struct
  val closed = Comma_Selected_List_Conversion.closed

  (* Prepare exact monomorphic theorem instantiation once, then reuse its
     checked variable layout while constructing one fact per source/tree node. *)
  fun prepare_rule theorem =
    let
      val type_vars = Term.add_tvars (Thm.prop_of theorem) []
      val vars = Term.add_vars (Thm.prop_of theorem) []
      val _ = if null type_vars then () else
        error "B1 prepared kernel rule unexpectedly has type variables"
      fun variable_key name =
        (case filter (fn ((variable_name, _), _) => variable_name = name) vars of
          [key] => key
        | _ => error ("B1 prepared kernel rule variable is missing or duplicated: " ^ name))
      fun instantiate arguments =
        let
          val entries = map
            (fn (name, cterm) => (variable_key name, cterm)) arguments
          val _ = if length entries = length vars andalso
              length (distinct (op =) (map fst entries)) = length vars then () else
            error "B1 prepared kernel rule instantiation omitted a schematic variable"
        in Thm.instantiate (TVars.empty, Vars.make entries) theorem end
    in instantiate end

  fun application_arguments count cterm =
    let
      fun descend 0 _ arguments = arguments
        | descend remaining current arguments =
            let val (head, argument) = Thm.dest_comb current
            in descend (remaining - 1) head (argument :: arguments) end
    in descend count cterm [] end

  fun nat_term n = HOLogic.mk_number @{typ nat} n

  fun dest_nat term message =
    (case try HOLogic.dest_number term of
      SOME (typ, value) =>
        if typ = @{typ nat} andalso value >= 0 then value
        else error message
    | NONE => error message)

  fun clean ctxt theorem =
    Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
    null (Thm.tpairs_of theorem) andalso closed (Thm.prop_of theorem) andalso
    Context.subthy (Thm.theory_of_thm theorem, Proof_Context.theory_of ctxt) andalso
    null (Thm_Deps.all_oracles [theorem])

  (* Certify the published tree directly.  The recursive call carries one
     cterm for each child and the already-proved ordered/height facts, so a
     parent only unfolds its own constructor.  In particular, no source row
     list, sorted_wrt proof, midpoint builder, or whole-subtree simp is used
     on this path. *)
  fun direct_ordered_fact ctxt arithmetic_context node_count annotation =
    let
      val natT = @{typ nat}
      val boolT = @{typ bool}
      val treeT = @{typ comma_semantic_b1_crt_mass_tree}
      val summary = Const
        (@{const_name comma_semantic_b1_crt_mass_tree_summary},
          natT --> natT --> @{typ "nat option"} --> natT -->
            treeT --> boolT)
      val less_eq = Const (@{const_name less_eq}, natT --> natT --> boolT)
      val less = Const (@{const_name less}, natT --> natT --> boolT)
      val suc = Const (@{const_name Suc}, natT --> natT)
      val max = Const (@{const_name max}, natT --> natT --> natT)
      val trueprop_ct = Thm.cterm_of ctxt @{term Trueprop}
      val empty_name = @{const_name Comma_B1_CRT_Mass_Tree_Empty}
      val node_name = @{const_name Comma_B1_CRT_Mass_Tree_Node}
      val option_natT = @{typ "nat option"}
      val none_root = Const (@{const_name None}, option_natT)
      val some_root = Const (@{const_name Some}, natT --> option_natT)
      val summary_empty = @{thm comma_semantic_b1_crt_mass_tree_summary_empty}
      val summary_node = @{thm comma_semantic_b1_crt_mass_tree_summary_node}
      val summary_ordered = @{thm comma_semantic_b1_crt_mass_tree_summary_ordered}
      (* These summary rules are monomorphic.  Resolve their complete variable
         layouts once, then use typed kernel instantiation at every tree node
         instead of repeating type inference in Drule.infer_instantiate. *)
      val instantiate_empty = prepare_rule summary_empty
      val instantiate_node = prepare_rule summary_node
      val height_context = arithmetic_context addsimps @{thms max_def}
      val nodes = Unsynchronized.ref 0
      type scalar_height_facts =
        {left_balance: thm, right_balance: thm, height_equation: thm}
      val scalar_height_cache =
        Unsynchronized.ref (Symtab.empty: scalar_height_facts Symtab.table)
      val scalar_height_capacity = 512
      val scalar_height_calls = Unsynchronized.ref 0
      val scalar_height_hits = Unsynchronized.ref 0
      val scalar_height_builds = Unsynchronized.ref 0
      val scalar_height_refusals = Unsynchronized.ref 0
      val none_root_ct = Thm.cterm_of ctxt none_root
      val zero_height_ct = Thm.cterm_of ctxt (nat_term 0)
      val some_root_ct = Thm.cterm_of ctxt some_root

      fun tree_shape current =
        (case strip_comb (Thm.term_of current) of
          (Const (name, _), []) =>
            if name = empty_name then NONE
            else error "B1 direct mass layout found an unknown leaf"
        | (Const (name, _), [_, _, _, _, _]) =>
            if name = node_name then
              let
                val (node4, right) = Thm.dest_comb current
                val (node3, left) = Thm.dest_comb node4
                val (node2, mass) = Thm.dest_comb node3
                val (node1, level) = Thm.dest_comb node2
                val (node_ct, cid) = Thm.dest_comb node1
                val _ = (case strip_comb (Thm.term_of node_ct) of
                  (Const (actual, _), []) =>
                    if actual = node_name then ()
                    else error "B1 direct mass layout node head changed"
                | _ => error "B1 direct mass layout node head is malformed")
              in SOME (cid, level, mass, left, right) end
            else error "B1 direct mass layout found an unknown node"
        | _ => error "B1 direct mass layout tree is open or malformed")

      fun small_true label proposition =
        let
          val normalized = Simplifier.rewrite arithmetic_context
            (Thm.cterm_of ctxt proposition)
          val _ = if Thm.term_of (Thm.rhs_of normalized) aconv @{term True} then ()
            else error ("B1 direct mass layout rejected " ^ label)
          val proposition_equation = Thm.combination
            (Thm.reflexive trueprop_ct) normalized
        in Thm.equal_elim (Thm.symmetric proposition_equation) @{thm TrueI} end

      (* Height arithmetic repeats for only a small set of closed numeral
         pairs.  Cache these exact scalar propositions/equations per invocation;
         interval bounds and subtree certificates remain node-local. *)
      fun scalar_facts left_height right_height =
        let
          val key = Int.toString left_height ^ ":" ^ Int.toString right_height
          val _ = scalar_height_calls := !scalar_height_calls + 1
        in
          (case Symtab.lookup (!scalar_height_cache) key of
            SOME facts => (scalar_height_hits := !scalar_height_hits + 1; facts)
          | NONE =>
              let
                val left_term = nat_term left_height
                val right_term = nat_term right_height
                val left_balance = small_true "a left AVL balance violation"
                  (less_eq $ left_term $ (suc $ right_term))
                val right_balance = small_true "a right AVL balance violation"
                  (less_eq $ right_term $ (suc $ left_term))
                val raw_height = suc $ (max $ left_term $ right_term)
                val expected_height = nat_term
                  (1 + Int.max (left_height, right_height))
                val height_equation = Simplifier.rewrite height_context
                  (Thm.cterm_of ctxt raw_height)
                val _ = if Thm.term_of (Thm.lhs_of height_equation) aconv raw_height andalso
                    Thm.term_of (Thm.rhs_of height_equation) aconv expected_height then () else
                  error "B1 direct mass layout height did not normalize to its numeral"
                val facts : scalar_height_facts =
                  {left_balance = left_balance, right_balance = right_balance,
                   height_equation = height_equation}
                val _ = scalar_height_builds := !scalar_height_builds + 1
                val _ = if Symtab.size (!scalar_height_cache) < scalar_height_capacity then
                    scalar_height_cache := Symtab.update (key, facts) (!scalar_height_cache)
                  else scalar_height_refusals := !scalar_height_refusals + 1
              in facts end)
        end

      (* The summary rule exposes the height as Suc (max ...).  Rewrite that
         one conclusion argument immediately, then carry only its numeral;
         retaining the expression would make every ancestor re-simplify the
         complete height expression. *)
      fun normalize_height height_equation expected_height theorem =
        let
          val normalized = Thm.term_of (Thm.rhs_of height_equation)
          val _ = if normalized aconv expected_height then () else
            error "B1 direct mass layout height did not normalize to its numeral"
          val proposition = Thm.cprop_of theorem
          val conversion = Conv.arg_conv
            (Comma_Semantic_B1_CRT_Operation_Conversion.argument_at 1
              (Conv.rewr_conv height_equation))
          val proposition_equation = conversion proposition
        in Thm.equal_elim proposition_equation theorem end

      fun make_empty current lower upper =
        let
          val rule = instantiate_empty
            [("lower", Thm.cterm_of ctxt lower),
             ("upper", Thm.cterm_of ctxt upper)]
          val expected = HOLogic.mk_Trueprop
            (summary $ lower $ upper $ none_root $ nat_term 0 $
              Thm.term_of current)
          val _ = if Thm.prop_of rule aconv expected then () else
            error "B1 direct mass layout empty summary changed its request"
        in {fact = rule, root = none_root_ct,
            height_ct = zero_height_ct, height = 0} end

      fun make_node current lower upper (cid_ct, level_ct, mass_ct, left_ct, right_ct) =
        let
          val cid = dest_nat (Thm.term_of cid_ct)
            "B1 direct mass layout node key is not numeric"
          val _ = if cid >= 2 andalso cid < node_count then () else
            error "B1 direct mass layout node key is outside the checked extent"
          val cid_term = Thm.term_of cid_ct
          val level_term = Thm.term_of level_ct
          val mass_term = Thm.term_of mass_ct
          val left = build left_ct lower cid_term
          val right = build right_ct (suc $ cid_term) upper
          val left_height = #height_ct left
          val right_height = #height_ct right
          val left_height_value = #height left
          val right_height_value = #height right
          val lower_fact = small_true "a lower-bound violation"
            (less_eq $ lower $ cid_term)
          val upper_fact = small_true "an upper-bound violation"
            (less $ cid_term $ upper)
          val {left_balance, right_balance, height_equation} =
            scalar_facts left_height_value right_height_value
          val rule = instantiate_node
            [("lower", Thm.cterm_of ctxt lower),
             ("upper", Thm.cterm_of ctxt upper),
             ("cid", cid_ct),
             ("left_height", left_height),
             ("right_height", right_height),
             ("left_root", #root left),
             ("right_root", #root right),
             ("left", left_ct),
             ("right", right_ct),
             ("level", level_ct),
             ("mass", mass_ct)]
          (* Every argument above instantiates a named variable of the generic
             rule, so its six premises are already the exact requests.  Apply
             them in declaration order without `OF`'s repeated higher-order
             premise unification (in particular, avoid re-unifying the large
             child-tree terms at every ancestor).  implies_elim still checks
             each premise against its certified theorem exactly. *)
          val fact = fold
            (fn premise => fn theorem => Thm.implies_elim theorem premise)
            [lower_fact, upper_fact, left_balance, right_balance,
             #fact left, #fact right] rule
          val root = Thm.apply some_root_ct cid_ct
          val height_value = 1 + Int.max (left_height_value, right_height_value)
          val height_term = nat_term height_value
          val fact = normalize_height height_equation height_term fact
          val _ = nodes := !nodes + 1
          val _ = if !nodes mod 4096 = 0 then
              Comma_Proof_Profile.report
                ("B1 direct mass layout node checkpoint nodes=" ^
                 Int.toString (!nodes))
            else ()
        in {fact = fact, root = root, height_ct =
              Thm.cterm_of ctxt height_term, height = height_value} end

      and build current lower upper =
        (case tree_shape current of
          NONE => make_empty current lower upper
        | SOME parts => make_node current lower upper parts)

      val tree_ct = Thm.cterm_of ctxt annotation
      val root = build tree_ct (nat_term 2) (nat_term node_count)
      val ordered_fact = summary_ordered OF [#fact root]
      val _ = if Thm.nprems_of ordered_fact = 0 andalso
          null (Thm.hyps_of ordered_fact) andalso
          null (Thm.tpairs_of ordered_fact) then () else
        error "B1 direct mass layout produced a conditional theorem"
      val _ = Comma_Proof_Profile.report
        ("B1 direct mass layout complete nodes=" ^ Int.toString (!nodes) ^
         " height_scalar_calls=" ^ Int.toString (!scalar_height_calls) ^
         " height_scalar_builds=" ^ Int.toString (!scalar_height_builds) ^
         " height_scalar_hits=" ^ Int.toString (!scalar_height_hits) ^
         " height_scalar_capacity_refusals=" ^
           Int.toString (!scalar_height_refusals))
    in ordered_fact end

  fun make ctxt arithmetic_context node_count annotation =
    let
      val started = Time.now ()
      val natT = @{typ nat}
      val treeT = @{typ comma_semantic_b1_crt_mass_tree}
      val boolT = @{typ bool}
      val _ = if node_count >= 2 then () else
        error "B1 mass layout has an invalid column extent"
      val _ = if fastype_of annotation = treeT andalso closed annotation then () else
        error "B1 mass layout requires a closed, typed annotation"
      val ordered = Const
        (@{const_name comma_semantic_b1_crt_mass_tree_ordered},
          natT --> natT --> treeT --> boolT)
      val result = direct_ordered_fact ctxt arithmetic_context node_count annotation
      val expected = HOLogic.mk_Trueprop
        (ordered $ nat_term 2 $ nat_term node_count $ annotation)
      val _ = if Thm.prop_of result aconv expected then () else
        error "B1 mass layout transport changed its exact ordered-tree request"
      val _ = if clean ctxt result then () else
        error "B1 mass layout theorem is not a clean oracle-free theorem"
      val _ = Comma_Proof_Profile.report
        ("B1 mass layout ordered theorem complete elapsed_ms=" ^
         Comma_Proof_Profile.elapsed_ms started)
    in result end

  (* Opt-in shape fixture for the integration owner.  Layout rejects
     unbalanced, duplicate-key, out-of-range, and out-of-order trees before
     the separate mass/source invariant is consulted. *)
  fun fixture ctxt =
    let
      val arithmetic_context = Comma_Entry_Arithmetic.natural_context ctxt
      val natT = @{typ nat}
      val treeT = @{typ comma_semantic_b1_crt_mass_tree}
      val node = Const (@{const_name Comma_B1_CRT_Mass_Tree_Node},
        natT --> natT --> natT --> treeT --> treeT --> treeT)
      val empty = Const (@{const_name Comma_B1_CRT_Mass_Tree_Empty}, treeT)
      fun tree cid level value left right =
        node $ nat_term cid $ nat_term level $ nat_term value $ left $ right
      val left = tree 2 0 20 empty empty
      val right = tree 4 0 40 empty empty
      val valid = tree 3 0 30 left right
      val valid_skew = tree 3 0 30 left
        (tree 4 0 40 empty (tree 5 0 50 empty empty))
      val unbalanced = tree 2 0 20 empty (tree 3 0 30 empty right)
      val out_of_order = tree 3 0 30 left
        (tree 2 0 20 empty empty)
      val duplicate = tree 3 0 30 (tree 3 0 30 empty empty) right
      val foreign = tree 8 0 80 empty empty
      val open_annotation = node $ nat_term 2 $ Free ("level", natT) $
        nat_term 20 $ empty $ empty
      fun rejected label expected work =
        (case Exn.capture work () of
          Exn.Res _ => error ("B1 mass layout fixture accepted " ^ label)
        | Exn.Exn (ERROR message) =>
            if String.isSubstring expected message then ()
            else error ("B1 mass layout fixture rejected " ^ label ^
              " for the wrong reason: " ^ message)
        | Exn.Exn failure => Exn.reraise failure)
      val _ = make ctxt arithmetic_context 8 empty
      val _ = make ctxt arithmetic_context 8 valid
      val _ = make ctxt arithmetic_context 8 valid_skew
      val _ = rejected "an open annotation" "requires a closed, typed annotation"
        (fn () => (ignore (make ctxt arithmetic_context 8 open_annotation)))
      val _ = rejected "a wrong annotation type" "requires a closed, typed annotation"
        (fn () => (ignore (make ctxt arithmetic_context 8 (nat_term 0))))
      val _ = rejected "an invalid extent" "invalid column extent"
        (fn () => (ignore (make ctxt arithmetic_context 1 empty)))
      val _ = rejected "an unbalanced tree" "right AVL balance violation"
        (fn () => (ignore (make ctxt arithmetic_context 8 unbalanced)))
      val _ = rejected "a duplicate CID" "an upper-bound violation"
        (fn () => (ignore (make ctxt arithmetic_context 8 duplicate)))
      val _ = rejected "a foreign CID" "outside the checked extent"
        (fn () => (ignore (make ctxt arithmetic_context 8 foreign)))
      val _ = rejected "out-of-order rows" "a lower-bound violation"
        (fn () => (ignore (make ctxt arithmetic_context 8 out_of_order)))
    in () end
end
