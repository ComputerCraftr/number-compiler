(* Proof-producing, extent-checked traversal of literal list definitions.
   The selected path is reduced with kernel list equations; the full list is
   never normalized by the generic simplifier. *)
structure Comma_Selected_List_Conversion =
struct
  fun closed term = null (Term.add_frees term []) andalso
    null (Term.add_vars term []) andalso not (Term.is_open term)

  fun schematize pattern =
    Term.map_aterms
      (fn Free (name, typ) => Var ((name, 0), typ) | atom => atom) pattern

  fun head_name term =
    (case Term.head_of term of
      Const (name, _) => SOME name
    | _ => NONE)

  fun timed elapsed failures f x =
    let
      val start = Time.now ()
      val result = Exn.capture f x
      val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), start))
      val _ = if Exn.is_exn result then failures := !failures + 1 else ()
    in Exn.release result end

  fun equation_shape_valid request theorem =
    let
      val lhs = Thm.term_of (Thm.lhs_of theorem)
    in
      lhs aconv request andalso
          Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
          null (Thm.tpairs_of theorem)
    end

  fun validate_equation request theorem =
    let val rhs = Thm.term_of (Thm.rhs_of theorem)
    in
      if equation_shape_valid request theorem andalso closed rhs then theorem
      else error "selected-list conversion returned an open or mismatched theorem"
    end

  fun make_cached_equation_validator () =
    let
      val closed_rhs = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
      val closed_reuse_hits = Unsynchronized.ref 0
      val closed_rhs_capacity = 8192

      fun validate request theorem =
        let
          val rhs = Thm.term_of (Thm.rhs_of theorem)
          val shape_valid = equation_shape_valid request theorem
          val already_closed = shape_valid andalso
            Termtab.defined (!closed_rhs) rhs
          val rhs_closed =
            if not shape_valid then false
            else if already_closed then
              (closed_reuse_hits := !closed_reuse_hits + 1; true)
            else if closed rhs then
              (if Termtab.size (!closed_rhs) < closed_rhs_capacity then
                 closed_rhs := Termtab.update (rhs, ()) (!closed_rhs)
               else ();
               true)
            else false
        in
          if shape_valid andalso rhs_closed then theorem
          else error "selected-list conversion returned an open or mismatched theorem"
        end

      fun reuse_hits () = !closed_reuse_hits
    in {validate = validate, closed_reuse_hits = reuse_hits} end

  fun checked_successor_equation successor_equation index =
    let
      val natT = @{typ nat}
      fun numeral value = HOLogic.mk_number natT value
      val request = Const (@{const_name Suc}, natT --> natT) $ numeral index
      val theorem = validate_equation request (successor_equation index)
      val _ = if Thm.term_of (Thm.rhs_of theorem) aconv numeral (index + 1)
        then () else error "Indexed successor cache returned another numeral"
    in theorem end

  fun make_successor_equation ctxt =
    let
      val natT = @{typ nat}
      val context = Comma_Entry_Arithmetic.natural_context ctxt
      fun numeral value = HOLogic.mk_number natT value
    in
      fn index =>
        if index < 0 then error "Indexed successor request is negative"
        else checked_successor_equation
          (fn _ => Simplifier.rewrite context (Thm.cterm_of ctxt
            (Const (@{const_name Suc}, natT --> natT) $ numeral index))) index
    end

  fun make_successor_cache ctxt capacity =
    let
      val _ = if capacity > 0 andalso capacity <= 65536 then ()
        else error "Indexed successor cache extent is outside 1..65536"
      val normalize = make_successor_equation ctxt
      val equations = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      val hits = Unsynchronized.ref 0
      val misses = Unsynchronized.ref 0
      fun equation index =
        if index < 0 orelse index >= capacity then
          error "Indexed successor cache exceeded its declared extent"
        else
          (case Inttab.lookup (!equations) index of
            SOME theorem => (hits := !hits + 1; theorem)
          | NONE =>
              let
                val theorem = normalize index
                val _ = equations := Inttab.update (index, theorem) (!equations)
                val _ = misses := !misses + 1
              in theorem end)
      fun stats () = "successor_equation_hits=" ^ Int.toString (!hits) ^
        " successor_equation_misses=" ^ Int.toString (!misses)
      fun clear () =
        (equations := Inttab.empty; hits := 0; misses := 0)
    in {equation = equation, stats = stats, clear = clear,
        hits = fn () => !hits} end

  fun prove_indexed_list_all
      {ctxt, predicate, bound, prove_item, zero_fact, step_fact,
       successor_equation} =
    let
      val natT = @{typ nat}
      val list_type = @{typ "nat list"}
      val _ = if fastype_of predicate = @{typ "nat => bool"} andalso
          0 <= bound andalso bound <= 65536
        then () else error "Invalid bounded indexed list_all request"
      fun numeral value = HOLogic.mk_number natT value
      val list_all = Const (@{const_name list_all},
        fastype_of predicate --> list_type --> @{typ bool}) $ predicate
      fun named_variable name theorem =
        (case filter (fn ((variable_name, _), _) => variable_name = name)
            (Term.add_vars (Thm.prop_of theorem) []) of
          [key] => key
        | _ => error ("Indexed list_all theorem variable is missing or duplicated: " ^ name))
      val zero_rule = Thm.instantiate (TVars.empty,
        Vars.make [(named_variable "P" zero_fact,
          Thm.cterm_of ctxt predicate)]) zero_fact
      val zero_endpoint = Const (@{const_name upt}, natT --> natT --> list_type) $
        numeral 0 $ numeral 0
      val _ = if Thm.prop_of zero_rule aconv
          HOLogic.mk_Trueprop (list_all $ zero_endpoint)
        then () else error "Indexed list_all zero theorem has the wrong interval"
      val step_index_variable = named_variable "n" step_fact
      val step_template = Thm.instantiate (TVars.empty,
        Vars.make [(named_variable "P" step_fact, Thm.cterm_of ctxt predicate)]) step_fact
      fun advance index prefix =
        if index = bound then prefix
        else
          let
            val index_term = numeral index
            val head_proof = prove_item index
            val expected_head = HOLogic.mk_Trueprop (predicate $ index_term)
            val _ = if Thm.prop_of head_proof aconv expected_head andalso
                Thm.nprems_of head_proof = 0 andalso null (Thm.hyps_of head_proof) andalso
                null (Thm.tpairs_of head_proof)
              then () else error "Indexed list_all item proof has the wrong proposition"
            val step_rule = Thm.instantiate (TVars.empty,
              Vars.make [(step_index_variable, Thm.cterm_of ctxt index_term)])
              step_template
            val raw_step = Thm.implies_elim
              (Thm.implies_elim step_rule prefix) head_proof
            val successor_equation = checked_successor_equation successor_equation index
            val successor_conversion = Conv.arg_conv
              (Conv.arg_conv (Conv.arg_conv
                (Conv.rewr_conv successor_equation)))
              (Thm.cprop_of raw_step)
            val step = Thm.equal_elim successor_conversion raw_step
            val expected = HOLogic.mk_Trueprop
              (list_all $ (Const (@{const_name upt}, natT --> natT --> list_type) $
                numeral 0 $ numeral (index + 1)))
            val _ = if Thm.prop_of step aconv expected then ()
              else error "Indexed list_all recurrence produced the wrong interval"
          in advance (index + 1) step end
    in advance 0 zero_rule end

  (* Prepare only the Boolean variables of conjI.  Recursive proof assembly
     must not re-unify or inspect the complete operand propositions at each
     enclosing conjunction; callers retain their exact final-root checks. *)
  val conjunction_variables =
    let
      val variables = Term.add_vars (Thm.prop_of @{thm conjI}) []
      fun named name =
        (case filter (fn ((variable_name, _), _) => variable_name = name) variables of
          [key] => key
        | _ => error "Selected-list conjunction rule has unexpected variables")
    in (named "P", named "Q") end

  fun conjoin left right =
    let
      val (left_key, right_key) = conjunction_variables
      val rule = Thm.instantiate (TVars.empty,
        Vars.make [(left_key, Thm.dest_arg (Thm.cprop_of left)),
          (right_key, Thm.dest_arg (Thm.cprop_of right))]) @{thm conjI}
    in Thm.implies_elim (Thm.implies_elim rule left) right end

  fun literal_list_length term =
    let
      fun count list total =
        (case strip_comb list of
          (Const (name, _), []) =>
            if name = @{const_name Nil} then total
            else error "Selected-list extent requires a literal list spine"
        | (Const (name, _), [_, tail]) =>
            if name = @{const_name Cons} then count tail (total + 1)
            else error "Selected-list extent requires a literal list spine"
        | _ => error "Selected-list extent requires a literal list spine")
    in count term 0 end

  (* Kernel list-size conversion shared by catalogue and occurrence metadata.
     Only the Cons/Nil spine is visited; list heads remain opaque. *)
  fun literal_length_conversion note_cell cterm =
    let
      val (head, arguments) = strip_comb (Thm.term_of cterm)
      val contents = (case (head, arguments) of
          (Const (name, _), [value]) =>
            if name = @{const_name size} then value
            else error "Selected-list size expected a length request"
        | _ => error "Selected-list size expected one list argument")
      val constructor = (case Term.head_of contents of
          Const (name, _) => name
        | _ => error "Selected-list size encountered an open list spine")
      val _ = note_cell ()
      val rule =
        if constructor = @{const_name Nil} then @{thm comma_selected_length_nil}
        else if constructor = @{const_name Cons} then @{thm comma_selected_length_cons}
        else error "Selected-list size expected a literal Cons/Nil cell"
      val step = Conv.rewr_conv (rule RS @{thm eq_reflection}) cterm
    in
      if constructor = @{const_name Nil} then step
      else Thm.transitive step
        (Conv.arg_conv (literal_length_conversion note_cell) (Thm.rhs_of step))
    end

  fun literal_nested_extents depth root_body =
    let
      fun literal_list term =
        (case try HOLogic.dest_list term of
          SOME values => values
        | NONE => error "Selected-list nested extent requires literal list spines")
      val _ = if depth > 0 then ()
        else error "Selected-list nested extent depth must be positive"
      fun dimensions 0 _ = []
        | dimensions remaining tables =
            if remaining = 1 then
              [fold (fn table => fn maximum =>
                Int.max (literal_list_length table, maximum)) tables 0]
            else
              let
                val lists = map literal_list tables
                val extent = fold (fn values => fn maximum =>
                  Int.max (length values, maximum)) lists 0
              in extent :: dimensions (remaining - 1) (maps I lists) end
    in dimensions depth [root_body] end

  fun make_with_child_definitions extent_of_table
      child_name_prefix child_definitions
      {ctxt, name, root_definition, table_pattern} =
    let
      val natT = @{typ nat}
      val scalar_context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
        @{thms pred_numeral_simps}
      val arithmetic = Simplifier.rewrite scalar_context
      fun canonical_nat term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) => typ = natT andalso value >= 0
        | NONE => false)
      fun normalize_scalar index_context cterm =
        if canonical_nat (Thm.term_of cterm) then Thm.reflexive cterm
        else
          let
            (* Code_Simp presents concrete natural zero/successor constants in
               unoverloaded class form.  Restore the typed numeral first so
               both the extent check and the scalar arithmetic see the same
               canonical natural index. *)
            val overloaded = Axclass.overload_conv ctxt cterm
            val selected = Simplifier.rewrite index_context (Thm.rhs_of overloaded)
            val normalized = arithmetic (Thm.rhs_of selected)
            (* Simplification can expose the instance constant again (for
               example `zero_nat_inst.zero_nat`).  Canonicalize it after
               selection/arithmetic, while leaving already canonical numerals
               alone on the common path. *)
            val normalized_term = Thm.term_of (Thm.rhs_of normalized)
            val canonical = if canonical_nat normalized_term
              then Thm.reflexive (Thm.rhs_of normalized)
              else Axclass.overload_conv ctxt (Thm.rhs_of normalized)
          in Thm.transitive overloaded
            (Thm.transitive selected (Thm.transitive normalized canonical)) end
      val code_zero = Const
        (Sign.intern_const (Proof_Context.theory_of ctxt) "zero_nat_inst.zero_nat", natT)
      val code_zero_equation = normalize_scalar scalar_context
        (Thm.cterm_of ctxt code_zero)
      val _ = if equation_shape_valid code_zero code_zero_equation andalso
          Thm.term_of (Thm.rhs_of code_zero_equation) aconv HOLogic.mk_number natT 0
        then () else error "Selected-list code-form zero did not normalize to numeral zero"
      val root = (if can Logic.dest_equals (Thm.prop_of root_definition)
        then root_definition else root_definition RS @{thm eq_reflection})
      val root_term = Thm.term_of (Thm.lhs_of root)
      val _ = validate_equation root_term root
      val root_body = Thm.term_of (Thm.rhs_of root)
      fun child_equation (index, (definition, declared_extent)) =
        let
          val equation = if can Logic.dest_equals (Thm.prop_of definition)
            then definition else definition RS @{thm eq_reflection}
          val child_term = Thm.term_of (Thm.lhs_of equation)
          val expected_name = Sign.intern_const (Proof_Context.theory_of ctxt)
            (child_name_prefix ^ Int.toString index)
          val _ = (case child_term of
            Const (actual_name, _) => if actual_name = expected_name then ()
              else error "Named selected-list child has a foreign canonical name"
          | _ => error "Named selected-list child definition lhs is not a constant")
          val _ = validate_equation child_term equation
          val child_rhs = Thm.term_of (Thm.rhs_of equation)
          val _ = if literal_list_length child_rhs = declared_extent andalso
              declared_extent >= 0 then ()
            else error "Named selected-list child has an inconsistent row extent"
          val _ = if null (Thm_Deps.all_oracles [equation]) then ()
            else error "Named selected-list child definition has an oracle"
        in (child_term, equation, declared_extent) end
      val checked_children = map_index
        (fn (index, definition) => child_equation (index, definition)) child_definitions
      val child_definitions_table = fold (fn (term, equation, _) => fn table =>
        if Termtab.defined table term then
          error "Named selected-list child definition is duplicated"
        else Termtab.update (term, equation) table)
          checked_children Termtab.empty
      val child_extent_table = fold (fn (term, _, extent) => fn table =>
        Termtab.update (term, extent) table) checked_children Termtab.empty
      val _ = if null child_definitions then ()
        else
          let
            val root_children = (case try HOLogic.dest_list root_body of
              SOME values => values
            | NONE => error "Named selected-list root is not a literal child list")
            val expected_children = map #1 checked_children
            val root_type = fastype_of root_body
            val child_type = (case root_type of
              Type (list_name, [typ]) =>
                if list_name = @{type_name list} then typ
                else error "Named selected-list root is not a list"
            | _ => error "Named selected-list root is not a list")
            val _ = if length root_children = length expected_children andalso
                ListPair.allEq (fn (actual, expected) => actual aconv expected)
                  (root_children, expected_children)
              then () else error
                "Named selected-list root child order disagrees with its definitions"
            val _ = if List.all (fn child => fastype_of child = child_type)
                root_children then ()
              else error "Named selected-list root child has the wrong list type"
            val _ = if null (Thm_Deps.all_oracles [root]) then ()
              else error "Named selected-list root definition has an oracle"
          in () end
      val extents = extent_of_table root_body
      val _ = if not (null extents) andalso
          List.all (fn extent => extent > 0) extents
        then () else error "Selected-list extents must be positive"
      val nth_via_drop_rule = @{thm nth_via_drop}
      val nth_via_drop_type_vars = Term.add_tvars
        (Thm.prop_of nth_via_drop_rule) []
      val nth_via_drop_vars = Term.add_vars (Thm.prop_of nth_via_drop_rule) []
      val _ = if length nth_via_drop_type_vars = 1 andalso
          sort string_ord (map (fn ((name, _), _) => name) nth_via_drop_vars) =
            ["n", "xs", "y", "ys"] andalso
          forall (fn ((_, index), _) => index = 0) nth_via_drop_vars
        then () else error "Selected-list nth_via_drop theorem has an unexpected shape"
      fun instantiate_nth_via_drop index_ct table_ct head_ct tail_ct =
        let
          val index_type = Thm.typ_of_cterm index_ct
          val table_type = Thm.typ_of_cterm table_ct
          val head_type = Thm.typ_of_cterm head_ct
          val tail_type = Thm.typ_of_cterm tail_ct
          val element_type =
            (case table_type of
              Type (name, [element]) =>
                if name = @{type_name list} then element
                else error "Selected-list nth table cterm is not a list"
            | _ => error "Selected-list nth table cterm is not a list")
          val _ = if index_type = @{typ nat} andalso
              head_type = element_type andalso tail_type = table_type
            then () else error "Selected-list nth cterms have mismatched types"
          val [type_key] = nth_via_drop_type_vars
          val type_instance = Thm.instantiate
            (TVars.make [(type_key, Thm.ctyp_of ctxt element_type)],
             Vars.empty) nth_via_drop_rule
          val instantiated_vars = Term.add_vars (Thm.prop_of type_instance) []
          fun variable name =
            (case filter (fn ((variable_name, _), _) => variable_name = name)
                instantiated_vars of
              [entry] => entry
            | _ => error "Selected-list nth_via_drop variable is missing or duplicated")
          val term_instance = Vars.make
            [(variable "n", index_ct),
             (variable "xs", table_ct),
             (variable "y", head_ct),
             (variable "ys", tail_ct)]
        in Thm.instantiate (TVars.empty, term_instance) type_instance end
      fun equality_pair proposition =
        (case try Logic.dest_equals proposition of
          SOME pair => pair
        | NONE => HOLogic.dest_eq (HOLogic.dest_Trueprop proposition))
      fun equality_variable term =
        (case term of
          Var (key, _) => key
        | _ => error "Selected-list equality bridge expected schematic endpoints")
      fun instantiated_equality_variable term =
        (case term of
          Var (name_index, typ) => (name_index, typ)
        | _ => error "Selected-list equality bridge lost a schematic endpoint")
      (* Instantiate the tiny generic equality bridge from the already
         selected endpoint cterms.  RS would re-unify the complete literal
         list in these endpoints for every selected cell. *)
      fun instantiate_equality_bridge rule left_ct right_ct premise =
        let
          val (rule_premise, _) = Logic.dest_implies (Thm.prop_of rule)
          val (left_var, right_var) = equality_pair rule_premise
          val left_index = equality_variable left_var
          val right_index = equality_variable right_var
          val left_type = Thm.typ_of_cterm left_ct
          val right_type = Thm.typ_of_cterm right_ct
          val _ = if left_type = right_type then ()
            else error "Selected-list equality bridge endpoint types differ"
          val [type_key] = Term.add_tvars (Thm.prop_of rule) []
          val type_instance = Thm.instantiate
            (TVars.make [(type_key, Thm.ctyp_of ctxt left_type)], Vars.empty) rule
          val (instantiated_premise, _) =
            Logic.dest_implies (Thm.prop_of type_instance)
          val (instantiated_left, instantiated_right) =
            equality_pair instantiated_premise
          val left_key = instantiated_equality_variable instantiated_left
          val right_key = instantiated_equality_variable instantiated_right
          val _ = if #1 left_key = left_index andalso #1 right_key = right_index then ()
            else error "Selected-list equality bridge changed endpoint variables"
          val instance = Thm.instantiate (TVars.empty,
            Vars.make [(left_key, left_ct), (right_key, right_ct)]) type_instance
          val _ = if length (Thm.prems_of instance) = 1 then ()
            else error "Selected-list equality bridge premise changed"
        in Thm.implies_elim instance premise end
      val memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      (* A second, request-local table stores proof-carrying suffixes.  It is
         deliberately keyed by the exact drop expression (which includes the
         source table), so unrelated roots and nested rows cannot alias. *)
      val suffix_memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      fun prefix_capacity [] _ total = total
        | prefix_capacity (extent :: rest) product total =
            let
              val multiplier = IntInf.fromInt extent
              val next_product = product * multiplier
              val next_total = total + next_product
            in prefix_capacity rest next_product next_total end
      val suffix_capacity_big = prefix_capacity extents 1 0
      val _ = if suffix_capacity_big <= IntInf.fromInt 131072 then ()
        else error "Selected-list suffix cache exceeds the proof-session cap"
      val suffix_capacity = Int.max (1, IntInf.toInt suffix_capacity_big)
      val active = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
      val lookups = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val internal_publications = Unsynchronized.ref 0
      val leaf_evaluations = Unsynchronized.ref 0
      val retained = Unsynchronized.ref 0
      val peak_retained = Unsynchronized.ref 0
      val evicted = Unsynchronized.ref 0
      val selected_cells = Unsynchronized.ref 0
      val suffix_lookups = Unsynchronized.ref 0
      val suffix_hits = Unsynchronized.ref 0
      val suffix_misses = Unsynchronized.ref 0
      val suffix_steps = Unsynchronized.ref 0
      val length_spine_nodes = Unsynchronized.ref 0
      val elapsed = Unsynchronized.ref Time.zeroTime
      val failures = Unsynchronized.ref 0
      val trace_nested_pieces =
        name = "semantic_b1_construction_piece_refs" orelse
        name = "regression_construction_piece_refs"
      val trace_counts = Synchronized.var
        ("selected-list-trace-" ^ name) (Symtab.empty: int Symtab.table)
      fun trace_stage label limit f =
        if not trace_nested_pieces then f ()
        else
          Comma_Proof_Profile.trace_stage (Comma_Proof_Profile.enabled ())
            trace_counts
            (fn counts =>
              let val current = the_default 0 (Symtab.lookup counts label)
              in (current, Symtab.update (label, current + 1) counts) end)
            limit ("B1 selected-list " ^ name) label f

      fun selector_depth table =
        if table aconv root_term then SOME 0
        else if Termtab.defined child_definitions_table table then SOME 1
        else
          (case strip_comb table of
            (Const (constant, _), [parent, _]) =>
              if constant = @{const_name nth} then
                Option.map (fn depth => depth + 1) (selector_depth parent)
              else NONE
          | _ => NONE)

      fun extent_at [] _ = NONE
        | extent_at (extent :: _) 0 = SOME extent
        | extent_at (_ :: rest) depth = extent_at rest (depth - 1)

      fun excerpt term =
        let
          val rendered = XML.content_of
            (YXML.parse_body (Syntax.string_of_term ctxt term))
          val count = Int.min (String.size rendered, 96)
        in String.substring (rendered, 0, count) end

      fun report_extent_failure index_context cterm =
        (case strip_comb (Thm.term_of cterm) of
          (Const (constant, _), [table, raw_index]) =>
            if constant = @{const_name nth} then
              let
                val depth = selector_depth table
                val expected = Option.mapPartial
                  (fn value => extent_at extents value) depth
                val normalized = Exn.capture (fn () =>
                  Thm.term_of (Thm.rhs_of (normalize_scalar index_context
                    (Thm.cterm_of ctxt raw_index)))) ()
                val normalized_text =
                  (case normalized of
                    Exn.Res value => excerpt value
                  | Exn.Exn _ => "<normalization-failed>")
                val depth_text =
                  (case depth of SOME value => Int.toString value | NONE => "foreign")
                val bound_text =
                  (case expected of SOME value => Int.toString value | NONE => "none")
              in
                Comma_Proof_Profile.report
                  ("selected-list extent failure owner=" ^ name ^
                   " depth=" ^ depth_text ^ " extent=" ^ bound_text ^
                   " root_table=" ^ Bool.toString (table aconv root_term) ^
                   " raw_index=" ^ excerpt raw_index ^
                   " normalized_index=" ^ normalized_text)
              end
            else ()
        | _ => ())

      fun in_extent index_context cterm =
        (case strip_comb (Thm.term_of cterm) of
          (Const (constant, _), [table, raw_index]) =>
            if constant <> @{const_name nth} then NONE
            else
              (case selector_depth table of
                NONE => NONE
              | SOME depth =>
                  (case extent_at extents depth of
                    NONE => NONE
                    | SOME extent =>
                      let
                        val index_conversion = trace_stage "index-normalize" 12 (fn () =>
                          normalize_scalar index_context (Thm.cterm_of ctxt raw_index))
                        val index = Thm.term_of (Thm.rhs_of index_conversion)
                      in
                        (case try HOLogic.dest_number index of
                          SOME (typ, value) =>
                            if typ = @{typ nat} andalso 0 <= value andalso value < extent
                            then SOME index_conversion else NONE
                        | NONE => NONE)
                      end))
        | _ => NONE)

      fun length_definition cterm =
        (case strip_comb (Thm.term_of cterm) of
          (Const (constant, _), [table]) =>
            (* HOL's `length` is an abbreviation for the size class constant. *)
            if constant <> @{const_name size} then NONE
            else if table aconv root_term then SOME root
            else Termtab.lookup child_definitions_table table
        | _ => NONE)

      fun concat_definition cterm =
        (case strip_comb (Thm.term_of cterm) of
          (Const (constant, _), [table]) =>
            if constant = @{const_name concat}
            then Termtab.lookup child_definitions_table table
            else NONE
        | _ => NONE)

      (* Once a selector's table spine reaches this conversion's root, an
         out-of-extent numeral is malformed input to this owner, not an
         unrelated term that another simplifier is free to reduce.  The
         lookup path performs the depth-specific bound check and rejects it. *)
      fun owned_selector cterm =
        (case strip_comb (Thm.term_of cterm) of
          (Const (constant, _), [table, _]) =>
            constant = @{const_name nth} andalso
              (case selector_depth table of
                SOME depth => Option.isSome (extent_at extents depth)
              | NONE => false)
        | _ => false)

      fun drop_term index table =
        let
          val list_type = fastype_of table
          val drop_type = @{typ nat} --> list_type --> list_type
        in Const (@{const_name drop}, drop_type) $ index $ table end

      fun validate_suffix key theorem =
        let
          val lhs = Thm.term_of (Thm.lhs_of theorem)
        in
          if lhs aconv key andalso Thm.nprems_of theorem = 0 andalso
              null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
          then theorem
          else error "selected-list suffix proof is open or has the wrong key"
        end

      val list_size_spine = literal_length_conversion
        (fn () => length_spine_nodes := !length_spine_nodes + 1)

      fun suffix table index =
        let
          val index_term = HOLogic.mk_number @{typ nat} index
          val key = drop_term index_term table
          val cterm = Thm.cterm_of ctxt key
          val _ = suffix_lookups := !suffix_lookups + 1
        in
          case Termtab.lookup (!suffix_memo) key of
            SOME theorem => (suffix_hits := !suffix_hits + 1; theorem)
          | NONE =>
              let
                val _ = suffix_misses := !suffix_misses + 1
                val theorem =
                  if index = 0 then
                    let
                      val zero = Conv.rewr_conv
                        (@{thm drop_0} RS @{thm eq_reflection}) cterm
                    in
                      (case if table aconv root_term then SOME root
                            else Termtab.lookup child_definitions_table table of
                        SOME definition => Thm.transitive zero
                          (Conv.rewr_conv definition (Thm.rhs_of zero))
                      | NONE => zero)
                    end
                  else
                    let
                      val previous = suffix table (index - 1)
                      val numeral_suc = Conv.fun_conv
                        (Conv.arg_conv (Conv.rewr_conv
                          ((if index = 1 then @{thm One_nat_def}
                            else @{thm numeral_eq_Suc}) RS @{thm eq_reflection}))) cterm
                      val indexed =
                        if index = 1 then numeral_suc
                        else
                          let
                            val numeral_arg =
                              (case Term.dest_comb index_term of
                                (_, value) => value)
                            val predecessor =
                              Const (@{const_name pred_numeral},
                                @{typ num} --> @{typ nat}) $ numeral_arg
                            val predecessor_eq = arithmetic
                              (Thm.cterm_of ctxt predecessor)
                            val predecessor_value =
                              Thm.term_of (Thm.rhs_of predecessor_eq)
                            val expected_predecessor = HOLogic.mk_number
                              @{typ nat} (index - 1)
                            val _ = if predecessor_value aconv expected_predecessor then ()
                              else error "Selected-list numeral predecessor did not normalize"
                            val reduce_predecessor = Conv.fun_conv
                              (Conv.arg_conv (Conv.arg_conv
                                (Conv.rewr_conv predecessor_eq)))
                              (Thm.rhs_of numeral_suc)
                          in Thm.transitive numeral_suc reduce_predecessor end
                      val after_drop_suc = Conv.rewr_conv
                        (@{thm drop_Suc} RS @{thm eq_reflection})
                        (Thm.rhs_of indexed)
                      val after_drop_tl = Conv.rewr_conv
                        (@{thm drop_tl} RS @{thm eq_reflection})
                        (Thm.rhs_of after_drop_suc)
                      (* `drop_tl` leaves `tl (drop k table)`.  Apply the
                         cached drop equation by kernel congruence instead
                         of asking the rewrite matcher to rediscover the
                         same potentially large root table in its lhs. *)
                      val after_drop_tl_rhs = Thm.rhs_of after_drop_tl
                      val (tl_function, _) =
                        Thm.dest_comb after_drop_tl_rhs
                      val tl_name =
                        (case Thm.term_of tl_function of
                          Const (constant, _) => constant
                        | _ => "")
                      val _ = if tl_name = @{const_name tl} then ()
                        else error "Selected-list drop_tl result is not a tail application"
                      val lifted_previous = Thm.combination
                        (Thm.reflexive tl_function) previous
                      val after_previous = Thm.transitive after_drop_tl lifted_previous
                      val after_one_cell = Conv.rewr_conv
                        (@{thm list.sel(3)} RS @{thm eq_reflection})
                        (Thm.rhs_of after_previous)
                      val one_step = Thm.transitive indexed
                        (Thm.transitive after_drop_suc
                          (Thm.transitive after_previous after_one_cell))
                    in one_step end
                (* The root equation is validated once above.  Each later
                   right side is obtained by dropping one constructor from
                   that already-closed tail, so rescanning the growing tail
                   here would recreate quadratic validation work. *)
                val checked = validate_suffix key theorem
                val _ = if index = 0 then () else suffix_steps := !suffix_steps + 1
                val _ = if Termtab.size (!suffix_memo) < suffix_capacity then
                    suffix_memo := Termtab.update (key, checked) (!suffix_memo)
                  else error "Selected-list suffix proof cache capacity exceeded"
              in checked end
        end

      fun lookup index_context cterm =
        let
          val key = Thm.term_of cterm
          val _ = lookups := !lookups + 1
        in
          (case in_extent index_context cterm of
            NONE =>
              (report_extent_failure index_context cterm;
               error "Selected-list nested index exceeds its depth-specific extent")
          | SOME index_conversion =>
          case Termtab.lookup (!memo) key of
            SOME theorem => (hits := !hits + 1; theorem)
          | NONE =>
              let
                val _ = if Termtab.defined (!active) key then
                    error "Recursive selected-list conversion"
                  else active := Termtab.update (key, ()) (!active)
                val attempt = Exn.capture (fn () =>
                  let
                    val theorem =
                      if key aconv root_term then root
                      else
                        (case strip_comb key of
                          (Const (constant, _), [table, _]) =>
                            if constant = @{const_name nth} then
                              let
                                val lookup_table =
                                  (case Term.head_of table of
                                    Const (name, _) => name = @{const_name nth}
                                  | _ => false)
                                val prepared = if lookup_table then
                                    Conv.fun_conv
                                      (Conv.arg_conv (lookup index_context)) cterm
                                  else Thm.reflexive cterm
                              in Thm.transitive prepared
                                (nth index_context (Thm.rhs_of prepared)
                                  index_conversion) end
                            else error "Selected-list cache received a non-selector term"
                        | _ => error "Selected-list cache received an unowned term")
                  in trace_stage "selected-request-validation" 12 (fn () =>
                    validate_equation key theorem) end) ()
                val _ = active := Termtab.delete key (!active)
                val theorem =
                  (case attempt of
                    Exn.Res result => result
                  | Exn.Exn exn => Exn.reraise exn)
                val _ = if fastype_of key = @{typ nat} then
                    leaf_evaluations := !leaf_evaluations + 1
                  else
                    let
                      val _ = if !retained < 8192 then () else
                        (evicted := !evicted + !retained;
                         memo := Termtab.empty; retained := 0)
                      val _ = memo := Termtab.update (key, theorem) (!memo)
                      val _ = retained := !retained + 1
                      val _ = peak_retained := Int.max (!peak_retained, !retained)
                    in internal_publications := !internal_publications + 1 end
              in theorem end)
        end

      and nth index_context cterm index_conversion =
        let
          val request_step = Conv.arg_conv
            (Conv.rewr_conv index_conversion) cterm
          val normalized_request = Thm.rhs_of request_step
          val (nth_function_ct, index_ct) = Thm.dest_comb normalized_request
          val (nth_constant_ct, table_ct) = Thm.dest_comb nth_function_ct
          val nth_constant = Thm.term_of nth_constant_ct
          val table = Thm.term_of table_ct
          val normalized_index = Thm.term_of index_ct
          val _ = if (case nth_constant of Const (name, _) =>
                name = @{const_name nth} | _ => false)
            then () else error "Selected-list conversion expected the nth constant"
          val (index_type, index) =
            (case try HOLogic.dest_number normalized_index of
              SOME result => result
            | NONE => error "Selected-list index is not a closed numeral")
          val _ = if index_type = @{typ nat} andalso index >= 0 andalso
              index < fold (fn extent => fn maximum => Int.max (extent, maximum))
                extents 0
            then () else error "Selected-list index exceeds its declared extent"
          val _ = (case Termtab.lookup child_extent_table table of
            SOME extent => if index < extent then ()
              else error "Named selected-list row index exceeds its source extent"
          | NONE => ())
          val _ = selected_cells := !selected_cells + 1
          val selected_suffix = trace_stage "suffix-select" 12 (fn () =>
            suffix table index)
          val suffix_value = Thm.term_of (Thm.rhs_of selected_suffix)
          val is_cons =
            (case Term.head_of suffix_value of
              Const (constant, _) => constant = @{const_name Cons}
            | _ => false)
          val _ = if is_cons then ()
            else error "Selected-list index points beyond the literal table"
          val selected = trace_stage "nth-via-drop" 12 (fn () =>
            let
              val suffix_ct = Thm.rhs_of selected_suffix
              val (cons_function_ct, tail_ct) = Thm.dest_comb suffix_ct
              val (cons_constant_ct, head_ct) = Thm.dest_comb cons_function_ct
              val cons_constant = Thm.term_of cons_constant_ct
              val _ = if (case cons_constant of Const (name, _) =>
                    name = @{const_name Cons} | _ => false)
                then () else error "Selected-list suffix lost its Cons head"
              val suffix_equation = instantiate_equality_bridge
                @{thm meta_eq_to_obj_eq} (Thm.lhs_of selected_suffix)
                (Thm.rhs_of selected_suffix) selected_suffix
              val nth_rule = instantiate_nth_via_drop index_ct table_ct head_ct tail_ct
              val _ = if length (Thm.prems_of nth_rule) = 1 then ()
                else error "Selected-list nth rule changed its premise shape"
              val selected_object = Thm.implies_elim nth_rule suffix_equation
              val selected = instantiate_equality_bridge @{thm eq_reflection}
                normalized_request head_ct selected_object
            in selected end)
          val theorem = Thm.transitive request_step selected
        in trace_stage "nth-result-validation" 12 (fn () =>
          validate_equation (Thm.term_of cterm) theorem) end

      fun lookup_length definition cterm =
        let
          val key = Thm.term_of cterm
          val _ = lookups := !lookups + 1
        in
          case Termtab.lookup (!memo) key of
            SOME theorem => (hits := !hits + 1; theorem)
          | NONE =>
              let
                val selected = Conv.arg_conv (Conv.rewr_conv definition) cterm
                val spine_count = list_size_spine (Thm.rhs_of selected)
                (* Only the tiny unary count is normalized here; the list
                   payload has already been left opaque by the spine walk. *)
                val numeral = arithmetic (Thm.rhs_of spine_count)
                val reduced = Thm.transitive spine_count numeral
                val theorem = validate_equation key (Thm.transitive selected reduced)
                val _ = if !retained < 8192 then () else
                  (evicted := !evicted + !retained;
                   memo := Termtab.empty; retained := 0)
                val _ = memo := Termtab.update (key, theorem) (!memo)
                val _ = retained := !retained + 1
                val _ = peak_retained := Int.max (!peak_retained, !retained)
                val _ = internal_publications := !internal_publications + 1
              in theorem end
        end

      fun lookup_concat definition cterm =
        let
          val key = Thm.term_of cterm
          val _ = lookups := !lookups + 1
        in
          case Termtab.lookup (!memo) key of
            SOME theorem => (hits := !hits + 1; theorem)
          | NONE =>
              let
                val selected = Conv.arg_conv (Conv.rewr_conv definition) cterm
                val flatten_context = put_simpset HOL_basic_ss ctxt
                  addsimps (@{thms concat.simps append.simps})
                val flattened = Simplifier.rewrite flatten_context (Thm.rhs_of selected)
                val composed = Thm.transitive selected flattened
                val flattened_value = Thm.term_of (Thm.rhs_of composed)
                val _ = if can HOLogic.dest_list flattened_value then ()
                  else error "Named selected source did not flatten to a literal list"
                val theorem = validate_equation key composed
                val _ = if !retained < 8192 then () else
                  (evicted := !evicted + !retained;
                   memo := Termtab.empty; retained := 0)
                val _ = memo := Termtab.update (key, theorem) (!memo)
                val _ = retained := !retained + 1
                val _ = peak_retained := Int.max (!peak_retained, !retained)
                val _ = internal_publications := !internal_publications + 1
              in theorem end
        end

      fun convert index_context cterm =
        let val term = Thm.term_of cterm in
          if not (closed term) then NONE
          else
            (case length_definition cterm of
              SOME definition =>
                SOME (timed elapsed failures (lookup_length definition) cterm)
            | NONE =>
                (case concat_definition cterm of
                  SOME definition =>
                    SOME (timed elapsed failures (lookup_concat definition) cterm)
                | NONE => if owned_selector cterm then
                    SOME (timed elapsed failures (lookup index_context) cterm)
                  else NONE))
        end

      val pattern = table_pattern
        |> Term.map_aterms
          (fn Free (variable, typ) => Var ((variable, 0), typ) | atom => atom)
      (* The broad head pattern makes the outermost nested selector visible
         before the simplifier descends into its table argument.  Ownership is
         then checked against the original root spine by [owned_selector]. *)
      val selector_pattern = schematize @{term "selected_table ! selected_index"}
      val length_pattern = schematize @{term "length selected_table"}
      val concat_pattern = schematize @{term "concat selected_table"}
      val procedure = Simplifier.make_simproc ctxt
        {name = "comma_selected_list_" ^ name,
         kind = Simplifier.Congproc false,
         lhss = [pattern, selector_pattern, length_pattern, concat_pattern],
         proc = fn _ => fn index_context => convert index_context, identifier = []}
      val post_procedure = Simplifier.make_simproc ctxt
        {name = "comma_selected_list_after_operands_" ^ name,
         kind = Simplifier.Simproc,
         lhss = [pattern, selector_pattern, length_pattern, concat_pattern],
         proc = fn _ => convert, identifier = []}

      fun stats () = name ^ "_lookups=" ^ Int.toString (!lookups) ^
        " " ^ name ^ "_hits=" ^ Int.toString (!hits) ^
        " " ^ name ^ "_leaf_evaluations=" ^ Int.toString (!leaf_evaluations) ^
        " " ^ name ^ "_internal_publications=" ^
          Int.toString (!internal_publications) ^
        " " ^ name ^ "_internal_retained=" ^ Int.toString (!retained) ^
        " " ^ name ^ "_internal_peak=" ^ Int.toString (!peak_retained) ^
        " " ^ name ^ "_evicted=" ^ Int.toString (!evicted) ^
        " " ^ name ^ "_selected_cells=" ^ Int.toString (!selected_cells) ^
        " " ^ name ^ "_suffix_lookups=" ^ Int.toString (!suffix_lookups) ^
        " " ^ name ^ "_suffix_hits=" ^ Int.toString (!suffix_hits) ^
        " " ^ name ^ "_suffix_misses=" ^ Int.toString (!suffix_misses) ^
        " " ^ name ^ "_spine_node_visits=" ^ Int.toString (!suffix_steps) ^
        " " ^ name ^ "_length_spine_nodes=" ^
          Int.toString (!length_spine_nodes) ^
        " " ^ name ^ "_suffix_retained=" ^
          Int.toString (Termtab.size (!suffix_memo)) ^
        " " ^ name ^ "_failed=" ^ Int.toString (!failures) ^
        " " ^ name ^ "_lookup_ms=" ^
          LargeInt.toString (Time.toMilliseconds (!elapsed))
    in {procedure = procedure, post_procedure = post_procedure, stats = stats} end

  fun make_with_extents extent_of_table child_definitions
      {ctxt, name, root_definition, table_pattern} =
    make_with_child_definitions extent_of_table "" child_definitions
      {ctxt = ctxt, name = name, root_definition = root_definition,
       table_pattern = table_pattern}

  fun make {ctxt, name, root_definition, table_pattern, extents} =
    make_with_extents (fn _ => extents) []
      {ctxt = ctxt, name = name, root_definition = root_definition,
       table_pattern = table_pattern}

  fun make_nested {ctxt, name, root_definition, table_pattern, depth} =
    make_with_extents (literal_nested_extents depth) []
      {ctxt = ctxt, name = name, root_definition = root_definition,
       table_pattern = table_pattern}

  fun make_named_children
      {ctxt, name, root_definition, table_pattern, child_name_prefix,
       child_definitions, child_row_extents} =
    let
      val _ = if length child_definitions = length child_row_extents andalso
          List.all (fn extent => extent >= 0) child_row_extents
        then () else error "Named selected-list child extents are malformed"
      val max_rows = fold
        (fn extent => fn maximum => Int.max (extent, maximum))
        child_row_extents 0
      val entries = ListPair.zip (child_definitions, child_row_extents)
    in
      make_with_child_definitions
        (fn _ => [length entries, Int.max (1, max_rows)])
        child_name_prefix entries
        {ctxt = ctxt, name = name, root_definition = root_definition,
         table_pattern = table_pattern}
    end

  fun make_named_children_from_source
      {ctxt, name, table_pattern, child_name_prefix, get_definitions} =
    let
      val {root_definition, child_definitions, child_row_extents} =
        get_definitions ctxt
    in
      make_named_children
        {ctxt = ctxt, name = name, root_definition = root_definition,
         table_pattern = table_pattern, child_name_prefix = child_name_prefix,
         child_definitions = child_definitions,
         child_row_extents = child_row_extents}
    end

end
