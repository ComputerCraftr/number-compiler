(* Lazy owner-local proofs that a checked directory root selects one checked
   block throughout its CID interval, and that the block root agrees with one
   checked subtree.  This file is loaded before
   semantic_b1_column_conversion.ML by the owning theory. *)
structure Comma_Semantic_B1_Column_Lookup_Cache =
struct
  fun closed term = not (Term.is_open term) andalso
    null (Term.add_frees term []) andalso null (Term.add_vars term [])

  (* Bound checks are closed scalar conversions, not fresh tactic goals.  The
     returned fact still contains the exact requested inequality/conjunction. *)
  fun natural_bound ctxt numeral_context proposition =
    let
      val _ = if closed proposition andalso fastype_of proposition = @{typ bool}
        then () else error "B1 lookup bound is not a closed Boolean request"
      val equation = Simplifier.rewrite numeral_context
        (Thm.cterm_of ctxt proposition)
      val _ = if Thm.term_of (Thm.lhs_of equation) aconv proposition andalso
          Thm.term_of (Thm.rhs_of equation) aconv @{term True} andalso
          Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation) andalso
          null (Thm.tpairs_of equation) then ()
        else error "B1 lookup bound did not reduce to a closed truth"
      val lifted = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) equation
    in Thm.equal_elim (Thm.symmetric lifted) @{thm TrueI} end

  fun make ctxt numeral_context capacity =
    let
      val block_lookup = Const
        (@{const_name comma_semantic_b1_crt_column_block_lookup},
          @{typ comma_semantic_b1_crt_column_block} --> @{typ nat} -->
            @{typ "(nat \<times> nat list) option"})
      val natT = @{typ nat}
      val blockT = @{typ comma_semantic_b1_crt_column_block}
      val block_lookup_name = @{const_name comma_semantic_b1_crt_column_block_lookup}
      val empty_name = @{const_name Comma_B1_CRT_Column_Block_Empty}
      val node_name = @{const_name Comma_B1_CRT_Column_Block_Node}
      val nat = HOLogic.mk_number natT

      fun clean theorem =
        Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
          null (Thm.tpairs_of theorem) andalso
          closed (Thm.prop_of theorem)

      fun instantiate bindings theorem = Drule.infer_instantiate ctxt
        (map (fn (name, term) => ((name, 0), Thm.cterm_of ctxt term)) bindings)
        theorem

      val natural_bound = natural_bound ctxt numeral_context

      fun bound_pair lower key upper =
        let
          val lower_term = HOLogic.mk_binrel @{const_name less_eq} (lower, key)
          val upper_term = HOLogic.mk_binrel @{const_name less} (key, upper)
          (* Discharge both concrete bounds in one closed simplifier goal;
             the interval lemmas still receive the exact two premises. *)
          val combined = natural_bound (HOLogic.mk_conj (lower_term, upper_term))
          val lower_fact = @{thm conjunct1} OF [combined]
          val upper_fact = @{thm conjunct2} OF [combined]
        in (lower_fact, upper_fact, combined) end

      fun interval_key lower upper = HOLogic.mk_prod (nat lower, nat upper)

      type block_state = {
        constant: term,
        body: term,
        definition: thm,
        lower: int,
        upper: int,
        facts: thm Termtab.table Unsynchronized.ref
      }

      val blocks = Unsynchronized.ref (Termtab.empty: block_state Termtab.table)
      val retained = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val misses = Unsynchronized.ref 0
      val capacity_misses = Unsynchronized.ref 0

      fun interval_fact (state: block_state) lower upper lower_term upper_term =
        let
          val key = interval_key lower upper
        in
          (case Termtab.lookup (!(#facts state)) key of
            SOME theorem => (hits := !hits + 1; theorem)
          | NONE =>
              let
                val _ = misses := !misses + 1
                val theorem =
                  if lower = #lower state andalso upper = #upper state andalso
                      lower_term aconv nat lower andalso
                      upper_term aconv nat upper then
                    let
                      val block_equality = #definition state RS @{thm meta_eq_to_obj_eq}
                      val rule = instantiate
                        [("root", #constant state), ("subtree", #body state),
                         ("lower", lower_term), ("upper", upper_term)]
                        @{thm comma_semantic_b1_crt_column_block_lookup_interval_cong}
                    in rule OF [block_equality] end
                  else error "B1 interval cache lost its checked block root"
                val _ = if clean theorem then ()
                  else error "B1 block root interval theorem is not clean"
                val _ = if !retained < capacity then
                    (retained := !retained + 1;
                     (#facts state) := Termtab.update (key, theorem) (!(#facts state)))
                  else capacity_misses := !capacity_misses + 1
              in theorem end)
        end

      fun make_state block_constant block_definition lower upper =
        let
          val definition_left = Thm.term_of (Thm.lhs_of block_definition)
          val root = Thm.term_of (Thm.rhs_of block_definition)
          val _ = if definition_left aconv block_constant andalso
              fastype_of block_constant = blockT andalso fastype_of root = blockT andalso
              clean block_definition andalso
              null (Thm_Deps.all_oracles [block_definition]) then ()
            else error "B1 interval cache received another block definition"
          val state: block_state =
            {constant = block_constant, body = root, definition = block_definition,
             lower = lower,
             upper = upper, facts = Unsynchronized.ref Termtab.empty}
          val _ = blocks := Termtab.update (block_constant, state) (!blocks)
          val _ = interval_fact state lower upper (nat lower) (nat upper)
        in state end

      fun state_for block_constant block_definition lower upper =
        (case Termtab.lookup (!blocks) block_constant of
          SOME state =>
            if #lower state = lower andalso #upper state = upper andalso
                (pointer_eq (block_definition, #definition state) orelse
                  Thm.eq_thm_prop (block_definition, #definition state)) then state
            else error "B1 interval cache changed a block's root or bounds"
        | NONE => make_state block_constant block_definition lower upper)

      fun derive_child state parent_fact lower upper lower_term upper_term key key_term
          level children left right side =
        let
          val child_lower = if side = "left" then lower else key + 1
          val child_upper = if side = "left" then key else upper
          val cache_key = interval_key child_lower child_upper
        in
          (case Termtab.lookup (!(#facts state)) cache_key of
            SOME theorem => (hits := !hits + 1; theorem)
          | NONE =>
              let
                val _ = misses := !misses + 1
                val (lower_key, key_upper, _) =
                  bound_pair lower_term key_term upper_term
                val rule_name = if side = "left"
                  then @{thm comma_semantic_b1_crt_column_block_lookup_interval_left}
                  else @{thm comma_semantic_b1_crt_column_block_lookup_interval_right}
                val rule = instantiate
                  [("root", #constant state), ("lower", lower_term),
                   ("upper", upper_term), ("key", key_term),
                   ("level", level), ("children", children),
                   ("left", left), ("right", right)] rule_name
                val theorem = rule OF [lower_key, key_upper, parent_fact]
                val _ = if clean theorem then ()
                  else error "B1 child interval theorem is not clean"
                val _ = if !retained < capacity then
                    (retained := !retained + 1;
                     (#facts state) := Termtab.update (cache_key, theorem)
                       (!(#facts state)))
                  else capacity_misses := !capacity_misses + 1
              in theorem end)
        end

      fun point_from_interval interval_fact lower_term upper_term cid root subtree =
        let
          val cid_term = nat cid
          val (_, _, combined) = bound_pair lower_term cid_term upper_term
          val specialize = Drule.infer_instantiate ctxt
            [(("x", 0), Thm.cterm_of ctxt cid_term)] @{thm spec}
          val pointwise = specialize OF [interval_fact]
          val point = @{thm mp} OF [pointwise, combined]
          val expected_left = block_lookup $ root $ cid_term
          val expected_right = block_lookup $ subtree $ cid_term
          val _ = if HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of point)) =
              (expected_left, expected_right) then ()
            else error "B1 interval point application changed its endpoints"
        in point RS @{thm eq_reflection} end

      fun node_view subtree =
        (case strip_comb subtree of
          (Const (name, _), []) =>
            if name = empty_name then NONE
            else error "B1 interval cache encountered an unknown empty node"
        | (Const (name, _), [key, level, children, left, right]) =>
            if name = node_name then SOME (key, level, children, left, right)
            else error "B1 interval cache encountered a malformed block node"
        | _ => error "B1 interval cache encountered a malformed subtree")

      fun lookup visits block_constant block_definition base extent cid request_ct =
        let
          val request = Thm.term_of request_ct
          val upper = base + extent
          val _ = if extent > 0 andalso extent <= 512 andalso
              base <= cid andalso cid < upper then ()
            else error "B1 interval lookup CID is outside its checked block"
          val _ = (case strip_comb request of
            (Const (name, _), [actual_block, cid_term]) =>
              if name = block_lookup_name andalso actual_block aconv block_constant andalso
                  HOLogic.dest_number cid_term = (natT, cid) then ()
              else error "B1 interval lookup changed its block constant or CID"
          | _ => error "B1 interval lookup received a malformed request")
          val block_state = state_for block_constant block_definition base upper
          val root_fact = interval_fact block_state base upper (nat base) (nat upper)

          fun walk lower upper lower_term upper_term subtree fact =
            let
              val _ = visits := !visits + 1
            in
              (case node_view subtree of
                NONE => error "B1 interval lookup selected an empty subtree"
              | SOME (key_term, level, children, left, right) =>
                  let
                    val key = #2 (HOLogic.dest_number key_term)
                    val _ = if lower <= key andalso key < upper then ()
                      else error "B1 interval node key escaped its cached bounds"
                  in
                    if cid = key then
                      let
                        val point = point_from_interval fact lower_term upper_term cid
                          (#constant block_state) subtree
                        val node_rule = instantiate
                          [("key", key_term), ("level", level),
                           ("children", children), ("left", left), ("right", right)]
                          @{thm comma_semantic_b1_crt_column_block_lookup_node_key}
                        val node_eq = node_rule RS @{thm eq_reflection}
                        val result = Thm.transitive point node_eq
                        val expected_left = block_lookup $ (#constant block_state) $ nat cid
                        val _ = if Thm.term_of (Thm.lhs_of result) aconv expected_left then ()
                          else error "B1 interval node-key theorem changed its root request"
                      in result end
                    else if cid < key then
                      let
                        val child_fact = derive_child block_state fact lower upper
                          lower_term upper_term key key_term
                          level children left right "left"
                      in walk lower key lower_term key_term left child_fact end
                    else
                      let
                        val child_fact = derive_child block_state fact lower upper
                          lower_term upper_term key key_term
                          level children left right "right"
                      in walk (key + 1) upper (HOLogic.mk_Suc key_term)
                        upper_term right child_fact end
                  end)
            end

          val result = walk base upper (nat base) (nat upper)
            (#body block_state) root_fact
          val theorem = result
          val expected_left = request
          val _ = if Thm.term_of (Thm.lhs_of theorem) aconv expected_left andalso clean theorem
            then () else error "B1 interval lookup returned a non-clean source theorem"
        in theorem end

      fun counters () =
        " column_lookup_interval_cache_hits=" ^ Int.toString (!hits) ^
        " column_lookup_interval_cache_misses=" ^ Int.toString (!misses) ^
        " column_lookup_interval_cache_retained=" ^ Int.toString (!retained) ^
        " column_lookup_interval_cache_capacity_misses=" ^
          Int.toString (!capacity_misses)
    in
      {lookup = lookup, counters = counters,
       retained = fn () => !retained}
    end

  (* Build one exact interval theorem per selected directory leaf.  The
     checked definition and block root are fixed when the owner is created;
     cache keys also include both roots and the interval so a theorem cannot
     be reused for a different publication authority. *)
  fun make_directory ctxt numeral_context capacity dag_constant dag_definition =
    let
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val blockT = @{typ comma_semantic_b1_crt_column_block}
      val natT = @{typ nat}
      val nat = HOLogic.mk_number natT
      val dag_lookup = Const
        (@{const_name comma_semantic_b1_crt_column_dag_lookup},
          dagT --> natT --> @{typ "(nat \<times> nat list) option"})
      val block_lookup = Const
        (@{const_name comma_semantic_b1_crt_column_block_lookup},
          blockT --> natT --> @{typ "(nat \<times> nat list) option"})
      val branch_name = @{const_name Comma_B1_CRT_Column_DAG_Branch}
      val block_name = @{const_name Comma_B1_CRT_Column_DAG_Block}
      val empty_name = @{const_name Comma_B1_CRT_Column_DAG_Empty}
      val dag_left = Thm.term_of (Thm.lhs_of dag_definition)
      val dag_body = Thm.term_of (Thm.rhs_of dag_definition)

      fun clean_shape theorem = Thm.nprems_of theorem = 0 andalso
        null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
        closed (Thm.prop_of theorem)

      fun clean theorem = clean_shape theorem andalso
        null (Thm_Deps.all_oracles [theorem])

      val _ = if dag_left aconv dag_constant andalso fastype_of dag_constant = dagT
          andalso fastype_of dag_body = dagT andalso clean dag_definition then ()
        else error "B1 directory cache received another DAG definition"

      fun instantiate bindings theorem = Drule.infer_instantiate ctxt
        (map (fn (name, term) => ((name, 0), Thm.cterm_of ctxt term)) bindings)
        theorem

      val natural_bound = natural_bound ctxt numeral_context

      fun interval_key block_constant base upper =
        HOLogic.mk_prod (dag_constant,
          HOLogic.mk_prod (block_constant, HOLogic.mk_prod (nat base, nat upper)))

      type directory_state = {
        base: int,
        extent: int,
        definition: thm,
        theorem: thm
      }

      val facts = Unsynchronized.ref (Termtab.empty: directory_state Termtab.table)
      val retained = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val misses = Unsynchronized.ref 0
      val capacity_misses = Unsynchronized.ref 0
      val directory_nodes = Unsynchronized.ref 0

      fun build block_constant block_definition base extent =
        let
          val upper = base + extent
          val block_left = Thm.term_of (Thm.lhs_of block_definition)
          val block_body = Thm.term_of (Thm.rhs_of block_definition)
          val _ = if extent > 0 andalso extent <= 512 andalso
              fastype_of block_constant = blockT andalso
              block_left aconv block_constant andalso fastype_of block_body = blockT andalso
              clean block_definition then ()
            else error "B1 directory cache received another checked block definition"
          val lower_term = nat base
          val upper_term = nat upper
          val root_definition = dag_definition RS @{thm meta_eq_to_obj_eq}
          val root_fact =
            (instantiate [("root", dag_constant), ("body", dag_body),
               ("lower", lower_term), ("upper", upper_term)]
               @{thm comma_semantic_b1_crt_column_dag_lookup_interval_rootdef})
              OF [root_definition]

          fun dest_nat term =
            (case try HOLogic.dest_number term of
              SOME (typ, value) =>
                if typ = natT andalso value >= 0 then value
                else error "B1 directory contains a non-natural coordinate"
            | NONE => error "B1 directory contains a non-literal coordinate")

          fun finish_block base_term extent_term actual_block parent =
            let
              val actual_base = dest_nat base_term
              val actual_extent = dest_nat extent_term
              val _ = if actual_base = base andalso actual_extent = extent andalso
                  actual_block aconv block_constant then ()
                else error "B1 directory leaf differs from selected block authority"
              val lower_bound = HOLogic.mk_binrel @{const_name less_eq}
                (base_term, lower_term)
              val upper_bound = HOLogic.mk_binrel @{const_name less_eq}
                (upper_term, HOLogic.mk_binop @{const_name plus}
                  (base_term, extent_term))
              val bounds = natural_bound (HOLogic.mk_conj (lower_bound, upper_bound))
              val lower_fact = @{thm conjunct1} OF [bounds]
              val upper_fact = @{thm conjunct2} OF [bounds]
              val rule = instantiate
                [("root", dag_constant), ("lower", lower_term),
                 ("upper", upper_term), ("base", base_term),
                 ("extent", extent_term), ("block", block_constant)]
                @{thm comma_semantic_b1_crt_column_dag_lookup_interval_block}
              val theorem = rule OF [lower_fact, upper_fact, parent]
              val proposition = HOLogic.dest_Trueprop (Thm.prop_of theorem)
              val _ = (case proposition of
                Const (@{const_name All}, _) $ _ => ()
              | _ => error "B1 directory interval theorem has an unexpected shape")
            in theorem end

          fun walk subtree parent =
            let
              val _ = directory_nodes := !directory_nodes + 1
            in
              (case strip_comb subtree of
                (Const (name, _), []) =>
                  if name = empty_name then
                    error "B1 selected directory interval reaches an empty leaf"
                  else error "B1 directory contains an unknown nullary constructor"
              | (Const (name, _), [first, second, third]) =>
                  if name = branch_name then
                    let
                      val split_term = first
                      val left = second
                      val right = third
                      val split = dest_nat split_term
                      val upper_split = HOLogic.mk_binrel @{const_name less_eq}
                        (upper_term, split_term)
                      val split_lower = HOLogic.mk_binrel @{const_name less_eq}
                        (split_term, lower_term)
                    in
                      if upper <= split then
                        let
                          val bound = natural_bound upper_split
                          val rule = instantiate
                            [("root", dag_constant), ("lower", lower_term),
                             ("upper", upper_term), ("split", split_term),
                             ("left", left), ("right", right)]
                            @{thm comma_semantic_b1_crt_column_dag_lookup_interval_left}
                          val child_fact = rule OF [bound, parent]
                        in walk left child_fact end
                      else if split <= base then
                        let
                          val bound = natural_bound split_lower
                          val rule = instantiate
                            [("root", dag_constant), ("lower", lower_term),
                             ("upper", upper_term), ("split", split_term),
                             ("left", left), ("right", right)]
                            @{thm comma_semantic_b1_crt_column_dag_lookup_interval_right}
                          val child_fact = rule OF [bound, parent]
                        in walk right child_fact end
                      else error "B1 selected block interval straddles a directory split"
                    end
                  else if name = block_name then
                    finish_block first second third parent
                  else error "B1 selected directory subtree has an unknown constructor"
              | _ => error "B1 selected directory subtree is malformed")
            end

          val body_fact = walk dag_body root_fact
          val theorem =
            (case HOLogic.dest_Trueprop (Thm.prop_of body_fact) of
              Const (@{const_name All}, _) $ _ => body_fact
            | _ => error "B1 directory builder produced a malformed interval fact")
          val _ = if clean theorem then ()
            else error "B1 directory interval theorem is not a clean theorem"
        in
          {base = base, extent = extent, definition = block_definition,
           theorem = theorem}: directory_state
        end

      fun interval_fact block_constant block_definition base extent =
        let
          val key = interval_key block_constant base (base + extent)
        in
          (case Termtab.lookup (!facts) key of
            SOME state =>
              if #base state = base andalso #extent state = extent andalso
                  pointer_eq (block_definition, #definition state) then
                (hits := !hits + 1; #theorem state)
              else error "B1 directory interval cache changed block authority"
          | NONE =>
              let
                val _ = misses := !misses + 1
                val state = build block_constant block_definition base extent
                val _ = if !retained < capacity then
                    (retained := !retained + 1;
                     facts := Termtab.update (key, state) (!facts))
                  else capacity_misses := !capacity_misses + 1
              in #theorem state end)
        end

      fun lookup block_constant block_definition base extent cid request_ct =
        let
          val upper = base + extent
          val request = Thm.term_of request_ct
          val cid_term = nat cid
          val _ = if extent > 0 andalso extent <= 512 andalso
              base <= cid andalso cid < upper then ()
            else error "B1 directory lookup CID is outside its checked block"
          val _ = (case strip_comb request of
            (Const (name, _), [actual_dag, actual_cid]) =>
              if name = @{const_name comma_semantic_b1_crt_column_dag_lookup} andalso
                  actual_dag aconv dag_constant andalso actual_cid aconv cid_term then ()
              else error "B1 directory lookup changed its checked DAG root or CID"
          | _ => error "B1 directory lookup received a malformed request")
          val universal = interval_fact block_constant block_definition base extent
          val specialize = Drule.infer_instantiate ctxt
            [( ("x", 0), Thm.cterm_of ctxt cid_term)]
            @{thm spec}
          val pointwise = specialize OF [universal]
          val lower_term = nat base
          val upper_term = nat upper
          val bound = natural_bound (HOLogic.mk_conj
            (HOLogic.mk_binrel @{const_name less_eq} (lower_term, cid_term),
             HOLogic.mk_binrel @{const_name less} (cid_term, upper_term)))
          val point = @{thm mp} OF [pointwise, bound]
          val expected_left = dag_lookup $ dag_constant $ cid_term
          val expected_right = block_lookup $ block_constant $ cid_term
          val _ = if HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of point)) =
              (expected_left, expected_right) then ()
            else error "B1 directory point theorem changed its endpoints"
          val theorem = point RS @{thm eq_reflection}
          val _ = if Thm.term_of (Thm.lhs_of theorem) aconv request andalso
              clean_shape theorem
            then () else error "B1 directory lookup returned a non-clean theorem"
        in theorem end

      fun counters () =
        " column_lookup_directory_cache_hits=" ^ Int.toString (!hits) ^
        " column_lookup_directory_cache_misses=" ^ Int.toString (!misses) ^
        " column_lookup_directory_cache_retained=" ^ Int.toString (!retained) ^
        " column_lookup_directory_cache_capacity_misses=" ^
          Int.toString (!capacity_misses) ^
        " column_lookup_directory_nodes=" ^ Int.toString (!directory_nodes)

      fun stats () =
        {hits = !hits, misses = !misses, retained = !retained,
         capacity_misses = !capacity_misses, directory_nodes = !directory_nodes}
    in
      {lookup = lookup, counters = counters,
       interval = interval_fact, retained = fn () => !retained, stats = stats}
    end
end
