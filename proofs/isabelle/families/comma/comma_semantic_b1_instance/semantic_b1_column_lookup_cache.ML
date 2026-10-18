(* Lazy owner-local proofs that a checked directory root selects one checked
   block throughout its CID interval, and that the block root agrees with one
   checked subtree.  This file is loaded before
   semantic_b1_column_conversion.ML by the owning theory. *)
structure Comma_Semantic_B1_Column_Lookup_Cache =
struct
  fun closed term = not (Term.is_open term) andalso
    null (Term.add_frees term []) andalso null (Term.add_vars term [])

  fun argument_at index conversion ct =
    if index = 0 then Conv.arg_conv conversion ct
    else Conv.fun_conv (argument_at (index - 1) conversion) ct

  (* Keep a map's function argument opaque while its input is being checked.
     The result type is independent of the input type, so this one polymorphic
     congruence serves both column-to-column lifts and digit-to-column actions. *)
  val weak_map_input_congruence =
    @{lemma "xs = ys \<Longrightarrow> map f xs = map f ys" by simp}

  fun shape_summary nat_value term =
    let
      fun short_nat value =
        (case nat_value value of SOME n => Int.toString n | NONE => "?")
      fun bool_literal value = value aconv @{term True} orelse value aconv @{term False}
      fun list_width value =
        let
          fun collect 0 rest count =
                (case strip_comb rest of
                  (Const (name, _), []) =>
                    if name = @{const_name Nil} then SOME count else NONE
                | _ => NONE)
            | collect remaining rest count =
                (case strip_comb rest of
                  (Const (name, _), []) =>
                    if name = @{const_name Nil} then SOME count else NONE
                | (Const (name, _), [_, tail]) =>
                    if name = @{const_name Cons} then collect (remaining - 1) tail
                      (count + 1) else NONE
                | _ => NONE)
        in collect 11 value 0 end
    in
      (case strip_comb term of
        (Const (name, _), [first, second, third]) =>
          if name = @{const_name comma_crt_source_axis_column} then
            "SourceAxis(level=" ^ short_nat first ^ ",divisor=" ^
              short_nat second ^ ",residue=" ^ short_nat third ^ ")"
          else if name = @{const_name If} then
            "If(guard=" ^ (if bool_literal first then
              (if first aconv @{term True} then "true" else "false")
              else "nonliteral") ^ ")"
          else Long_Name.base_name name ^ "/3"
      | (Const (name, _), [flag]) =>
          if name = @{const_name Comma_CRT_Bool} then
            "Bool(" ^ (if bool_literal flag then "literal" else "nonliteral") ^ ")"
          else Long_Name.base_name name ^ "/1"
      | (Const (name, _), [level, children]) =>
          if name = @{const_name Comma_CRT_Node} then
            "Node(level=" ^ short_nat level ^ ",children=" ^
              (case list_width children of SOME width => Int.toString width
              | NONE => "nonliteral") ^ ")"
          else Long_Name.base_name name ^ "/2"
      | (Const (name, _), arguments) =>
          Long_Name.base_name name ^ "/" ^ Int.toString (length arguments)
      | _ => "nonconstant")
    end

  (* Shared certified selection of one closed Boolean conditional branch. *)
  fun choose_closed_if ctxt numeral_context
      (expected_if, guard_not_boolean, malformed_if) ct =
    (case strip_comb (Thm.term_of ct) of
      (Const (name, _), [condition, _, _]) =>
        if name <> @{const_name If} then error expected_if
        else if fastype_of condition <> @{typ bool} orelse not (closed condition) then
          error guard_not_boolean
        else
          let
            val condition_fact = Simplifier.rewrite numeral_context
              (Thm.cterm_of ctxt condition)
            val condition_value = Thm.term_of (Thm.rhs_of condition_fact)
            val exposed = argument_at 2 (Conv.rewr_conv condition_fact) ct
            val rule =
              if condition_value aconv @{term True} then
                @{thm if_True} RS @{thm eq_reflection}
              else if condition_value aconv @{term False} then
                @{thm if_False} RS @{thm eq_reflection}
              else error guard_not_boolean
          in Thm.transitive exposed (Conv.rewr_conv rule (Thm.rhs_of exposed)) end
    | _ => error malformed_if)

  fun normalize_lookup_rules ctxt rules =
    map (Local_Defs.meta_rewrite_rule ctxt) rules

  (* Reduce one selected lookup branch at a time; broad simp traverses the directory. *)
  fun controlled_lookup ctxt numeral_context lookup_rules visits block_authority request_ct =
    let
      val dag_lookup_name =
        @{const_name comma_semantic_b1_crt_column_dag_lookup}
      val block_lookup_name =
        @{const_name comma_semantic_b1_crt_column_block_lookup}
      val choose_selected_if = choose_closed_if ctxt numeral_context
        ("B1 controlled lookup expected an if node",
         "B1 controlled lookup guard did not normalize to a Boolean",
         "B1 controlled lookup encountered a malformed if node")

      fun is_lookup term =
        (case strip_comb term of
          (Const (name, _), _) =>
            name = dag_lookup_name orelse name = block_lookup_name
        | _ => false)

      fun is_if term =
        (case strip_comb term of
          (Const (name, _), _) => name = @{const_name If}
        | _ => false)

      fun open_selected_block ct =
        (case block_authority of
          NONE => Thm.reflexive ct
        | SOME (block_constant, block_definition) =>
            (case strip_comb (Thm.term_of ct) of
              (Const (name, _), [block_term, _]) =>
                if name <> block_lookup_name then Thm.reflexive ct
                else if block_term aconv block_constant then
                  argument_at 1 (Conv.rewr_conv block_definition) ct
                else Thm.reflexive ct
            | _ => Thm.reflexive ct))

      fun walk ct =
        let val term = Thm.term_of ct in
          if is_if term then
            let val selected = choose_selected_if ct
                val rest = Thm.rhs_of selected
            in if is_lookup (Thm.term_of rest) orelse
                  is_if (Thm.term_of rest) then
                 Thm.transitive selected (walk rest)
               else selected end
          else if is_lookup term then
            let
              val opened = open_selected_block ct
              val equation = Conv.rewrs_conv lookup_rules (Thm.rhs_of opened)
              val step = Thm.transitive opened equation
              val _ = visits := !visits + 1
              val rest = Thm.rhs_of step
            in
              if is_lookup (Thm.term_of rest) orelse is_if (Thm.term_of rest)
              then Thm.transitive step (walk rest)
              else step
            end
          else Thm.reflexive ct
        end
    in walk request_ct end

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

  (* Compare closed columns by their checked structure, opening only the pair
     of owned references currently under comparison.  Cache one canonical
     orientation of each exact HOL equality.  The reverse orientation is
     obtained by a kernel-checked equality rewrite; no CID ordering is
     interpreted as semantic equality or inequality. *)
  fun make_column_comparison ctxt base_context columnT
      {valid_column, known_column, resolve_column, valid_step} =
    let
      val capacity = 8192
      val maximum_depth = 32
      val facts = Synchronized.var "semantic_b1_column_comparisons"
        (Termtab.empty: thm Termtab.table)
      val hits = Synchronized.var "semantic_b1_column_comparison_hits" 0
      val misses = Synchronized.var "semantic_b1_column_comparison_misses" 0
      val publications = Synchronized.var "semantic_b1_column_comparison_publications" 0
      val resolutions = Synchronized.var "semantic_b1_column_comparison_resolutions" 0

      fun is_boolean term = term aconv @{term True} orelse term aconv @{term False}
      fun clean theorem = null (Thm.prems_of theorem) andalso
        null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
      fun equality left right = HOLogic.mk_eq (left, right)
      fun equation_boolean proposition rewrite_context =
        let
          val theorem = Simplifier.rewrite rewrite_context
            (Thm.cterm_of ctxt proposition)
          val left = Thm.term_of (Thm.lhs_of theorem)
          val right = Thm.term_of (Thm.rhs_of theorem)
        in
          if left aconv proposition andalso is_boolean right andalso clean theorem
          then SOME theorem else NONE
        end

      fun bounded_list term =
        let
          fun collect 0 current acc =
                (case strip_comb current of
                  (Const (name, _), []) =>
                    if name = @{const_name Nil} then SOME (rev acc) else NONE
                | _ => NONE)
            | collect remaining current acc =
                (case strip_comb current of
                  (Const (name, _), []) =>
                    if name = @{const_name Nil} then SOME (rev acc) else NONE
                | (Const (name, _), [head, tail]) =>
                    if name = @{const_name Cons} then
                      collect (remaining - 1) tail (head :: acc)
                    else NONE
                | _ => NONE)
        in collect 11 term [] end

      fun term_pair proposition =
        (case try HOLogic.dest_eq proposition of
          SOME (left, right) => SOME (left, right)
        | NONE => NONE)

      fun canonical_orientation proposition =
        (case term_pair proposition of
          SOME (left, right) =>
            if Term_Ord.fast_term_ord (left, right) <> GREATER then
              (proposition, Thm.reflexive (Thm.cterm_of ctxt proposition))
            else
              let
                val canonical = equality right left
                val conversion = Conv.rewr_conv
                  (@{thm eq_commute} RS @{thm eq_reflection})
                  (Thm.cterm_of ctxt proposition)
                val _ = if Thm.term_of (Thm.lhs_of conversion) aconv proposition andalso
                    Thm.term_of (Thm.rhs_of conversion) aconv canonical andalso
                    clean conversion then ()
                  else error "B1 column comparison could not canonicalize equality orientation"
              in (canonical, conversion) end
        | NONE => error "B1 column comparison received a non-equality")

      fun add_facts rewrite_facts = base_context addsimps rewrite_facts

      fun resolve_reference current active depth position reference recurse =
        (case resolve_column reference of
          SOME step =>
            if not (valid_step reference step) then
              error "B1 column comparison received an invalid owned step"
            else
              let
                val _ = Synchronized.change resolutions (fn count => count + 1)
                val ct = Thm.cterm_of ctxt current
                val rewrite =
                  (case try Logic.dest_equals (Thm.prop_of step) of
                    SOME _ => step
                  | NONE => step RS @{thm eq_reflection})
                val opened = argument_at position (Conv.rewr_conv rewrite) ct
              in
                Option.map (Thm.transitive opened)
                  (recurse (current :: active) (depth + 1)
                    (Thm.term_of (Thm.rhs_of opened)))
              end
        | NONE => NONE)

      fun publish proposition theorem =
        let
          val _ = if clean theorem andalso
              Thm.term_of (Thm.lhs_of theorem) aconv proposition andalso
              is_boolean (Thm.term_of (Thm.rhs_of theorem)) then ()
            else error "B1 column comparison produced a malformed theorem"
        in
          Synchronized.change facts (fn table =>
            if Termtab.defined table proposition orelse
                Termtab.size table >= capacity then table
            else
              (Synchronized.change publications (fn count => count + 1);
               Termtab.update (proposition, theorem) table));
          theorem
        end

      fun compute active depth current =
        let
          val (canonical, orientation) = canonical_orientation current
          fun restore theorem = Thm.transitive orientation theorem
        in
          (case Synchronized.change_result facts (fn table =>
              (Termtab.lookup table canonical, table)) of
            SOME theorem =>
              (Synchronized.change hits (fn count => count + 1);
               if clean theorem andalso
                  Thm.term_of (Thm.lhs_of theorem) aconv canonical andalso
                  is_boolean (Thm.term_of (Thm.rhs_of theorem)) then
                 SOME (restore theorem)
               else error "B1 column comparison cache contains a foreign theorem")
          | NONE =>
            if depth > maximum_depth orelse member (op aconv) active canonical
            then NONE
            else
              let
                val _ = Synchronized.change misses (fn count => count + 1)
                fun calculate () =
                  (case term_pair canonical of
                    NONE => NONE
                  | SOME (left, right) =>
                    if fastype_of left <> columnT orelse fastype_of right <> columnT orelse
                        not (valid_column left) orelse not (valid_column right) then NONE
                    else if left aconv right then equation_boolean canonical base_context
                    else
                      let
                        val left_reference = known_column left
                        val right_reference = known_column right
                      in
                        if left_reference then
                          resolve_reference canonical active depth 1 left compute
                        else if right_reference then
                          resolve_reference canonical active depth 0 right compute
                        else
                          (case (strip_comb left, strip_comb right) of
                            ((Const (left_name, _), [left_level, left_children]),
                             (Const (right_name, _), [right_level, right_children])) =>
                              if left_name <> @{const_name Comma_CRT_Node} orelse
                                  right_name <> @{const_name Comma_CRT_Node} then
                                equation_boolean canonical base_context
                              else
                                (case (bounded_list left_children,
                                    bounded_list right_children) of
                                  (SOME left_items, SOME right_items) =>
                                    if length left_items <> length right_items orelse
                                        not (left_level aconv right_level) then
                                      equation_boolean canonical base_context
                                    else
                                      let
                                        fun compare_children [] [] accumulated =
                                              equation_boolean canonical
                                                (add_facts (rev accumulated))
                                          | compare_children (x :: xs) (y :: ys) accumulated =
                                              if x aconv y then
                                                compare_children xs ys accumulated
                                              else
                                                (case compute (canonical :: active)
                                                    (depth + 1) (equality x y) of
                                                  NONE => NONE
                                                | SOME child_fact =>
                                                    if Thm.term_of (Thm.rhs_of child_fact)
                                                        aconv @{term False} then
                                                      equation_boolean canonical
                                                        (add_facts (child_fact :: accumulated))
                                                    else compare_children xs ys
                                                      (child_fact :: accumulated))
                                          | compare_children _ _ _ = NONE
                                      in compare_children left_items right_items [] end
                                | _ => NONE)
                            | _ => equation_boolean canonical base_context)
                      end)
              in Option.map (fn theorem => restore (publish canonical theorem))
                  (calculate ()) end)
        end

      fun convert ct =
        let val proposition = Thm.term_of ct in
          (case term_pair proposition of
            SOME (left, right) =>
              if fastype_of left = columnT andalso fastype_of right = columnT
              then
                if left aconv right andalso valid_column left then
                  let
                    (* Identity needs no source exposure or retained comparison. *)
                    val theorem = Thm.reflexive (Thm.cterm_of ctxt left)
                      RS @{thm meta_eq_to_obj_eq} RS @{thm eqTrueI}
                      RS @{thm eq_reflection}
                    val _ = if clean theorem andalso
                        Thm.term_of (Thm.lhs_of theorem) aconv proposition andalso
                        Thm.term_of (Thm.rhs_of theorem) aconv @{term True}
                      then () else error "B1 reflexive column comparison lost its endpoints"
                  in SOME theorem end
                else compute [] 0 proposition
              else NONE
          | NONE => NONE)
        end

      val left = Var (("left_column", 0), columnT)
      val right = Var (("right_column", 0), columnT)
      val pattern = equality left right
      val procedure = Simplifier.make_simproc ctxt
        {name = "comma_semantic_b1_checked_column_comparison",
         kind = Simplifier.Congproc false, lhss = [pattern],
         proc = fn _ => fn _ => convert, identifier = []}
    in
      {convert = convert,
       add_to_context = Simplifier.add_proc procedure,
       hits = fn () => Synchronized.value hits,
       misses = fn () => Synchronized.value misses,
       publications = fn () => Synchronized.value publications,
       resolutions = fn () => Synchronized.value resolutions}
    end

  fun make ctxt numeral_context capacity =
    let
      val block_lookup = Const
        (@{const_name comma_semantic_b1_crt_column_block_lookup},
          @{typ comma_semantic_b1_crt_column_block} --> @{typ nat} -->
            @{typ "(nat \<times> nat list) option"})
      val natT = @{typ nat}
      val blockT = @{typ comma_semantic_b1_crt_column_block}
      val boolT = @{typ bool}
      val pointT = @{typ "(nat \<times> nat list) option"}
      val block_lookup_name = @{const_name comma_semantic_b1_crt_column_block_lookup}
      val empty_name = @{const_name Comma_B1_CRT_Column_Block_Empty}
      val node_name = @{const_name Comma_B1_CRT_Column_Block_Node}
      val nat = HOLogic.mk_number natT
      val interval_facts = Comma_Semantic_B1_Term_LRU.make
        "column-interval" capacity
      val recomputes = Unsynchronized.ref 0

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

      type block_state = {
        constant: term,
        body: term,
        definition: thm,
        lower: int,
        upper: int
      }

      val blocks = Unsynchronized.ref (Termtab.empty: block_state Termtab.table)

      (* Within one fixed checked block, its validated node key partitions a
         half-open interval into strictly smaller left/right intervals.  Thus
         a block constant and interval identify one subtree without copying
         the subtree into each hot cache key. *)
      fun interval_key (state: block_state) lower upper =
        HOLogic.mk_prod (#constant state,
          HOLogic.mk_prod (nat lower, nat upper))

      fun interval_proposition (state: block_state) lower_term upper_term subtree =
        let
          val cid = Bound 0
          val less_eq = Const (@{const_name less_eq}, natT --> natT --> boolT)
          val less = Const (@{const_name less}, natT --> natT --> boolT)
          val conjunction = Const (@{const_name HOL.conj}, boolT --> boolT --> boolT)
          val implication = Const (@{const_name HOL.implies}, boolT --> boolT --> boolT)
          val equality = Const (@{const_name HOL.eq}, pointT --> pointT --> boolT)
          val bounds = conjunction $ (less_eq $ lower_term $ cid) $
            (less $ cid $ upper_term)
          val values = equality $ (block_lookup $ #constant state $ cid) $
            (block_lookup $ subtree $ cid)
          val interval_body = implication $ bounds $ values
        in HOLogic.mk_Trueprop (HOLogic.mk_all ("cid", natT, interval_body)) end

      fun checked_interval (state: block_state) lower_term upper_term subtree theorem =
        if clean theorem andalso
            Thm.prop_of theorem aconv
              (interval_proposition state lower_term upper_term subtree)
        then theorem
        else error "B1 interval cache theorem changed its exact block or bounds"

      (* State validation precedes every lookup; entries are private to this
         immutable owner and were endpoint-checked before publication. *)
      fun cached_interval state lower upper =
        Comma_Semantic_B1_Term_LRU.lookup interval_facts
          (interval_key state lower upper)

      fun publish_interval state lower upper lower_term upper_term subtree theorem =
        let
          val exact = checked_interval state lower_term upper_term subtree theorem
          val _ = Comma_Semantic_B1_Term_LRU.insert_completed interval_facts
            (interval_key state lower upper) exact
        in exact end

      fun interval_fact (state: block_state) lower upper lower_term upper_term =
        (case cached_interval state lower upper of
          SOME theorem => theorem
        | NONE =>
            let
              val _ = recomputes := !recomputes + 1
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
            in publish_interval state lower upper lower_term upper_term
              (#body state) theorem end)

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
             lower = lower, upper = upper}
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
        in
          (case cached_interval state child_lower child_upper of
            SOME theorem => theorem
          | NONE =>
              let
                val _ = recomputes := !recomputes + 1
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
                val child_lower_term = if side = "left" then lower_term
                  else HOLogic.mk_Suc key_term
                val child_upper_term = if side = "left" then key_term else upper_term
              in publish_interval state child_lower child_upper
                child_lower_term child_upper_term
                (if side = "left" then left else right) theorem end)
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
        " column_lookup_interval_cache_hits=" ^ Int.toString
          (Comma_Semantic_B1_Term_LRU.hits interval_facts) ^
        " column_lookup_interval_cache_misses=" ^ Int.toString
          (Comma_Semantic_B1_Term_LRU.misses interval_facts) ^
        " column_lookup_interval_cache_retained=" ^ Int.toString
          (Comma_Semantic_B1_Term_LRU.completed_size interval_facts) ^
        " column_lookup_interval_cache_capacity_misses=" ^
          Int.toString (Comma_Semantic_B1_Term_LRU.refusals interval_facts) ^
        " column_lookup_interval_cache_evictions=" ^ Int.toString
          (Comma_Semantic_B1_Term_LRU.evictions interval_facts) ^
        " column_lookup_interval_cache_recomputes=" ^ Int.toString (!recomputes)
      fun stats () =
        {hits = Comma_Semantic_B1_Term_LRU.hits interval_facts,
         misses = Comma_Semantic_B1_Term_LRU.misses interval_facts,
         retained = Comma_Semantic_B1_Term_LRU.completed_size interval_facts,
         capacity_misses = Comma_Semantic_B1_Term_LRU.refusals interval_facts,
         evictions = Comma_Semantic_B1_Term_LRU.evictions interval_facts,
         recomputes = !recomputes}
    in
      {lookup = lookup, counters = counters, stats = stats,
       retained = fn () => Comma_Semantic_B1_Term_LRU.completed_size interval_facts}
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
