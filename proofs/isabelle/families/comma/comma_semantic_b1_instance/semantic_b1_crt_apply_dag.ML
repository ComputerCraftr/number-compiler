(* Proof-producing, context-owned memo for the recursive shifted CRT apply. *)
signature COMMA_SEMANTIC_B1_CRT_APPLY_DAG =
sig
  type column_authority =
   {known_column: term -> bool,
    column_id: term -> int option,
    column_value: int -> term,
    cofactor_node_level: int -> int option,
    prove_admitted: int * int -> thm,
    resolve_column: term -> thm option,
    cofactor_transition: int * int * int -> {target_cid: int, theorem: thm},
    reify_column: cterm -> thm}
  type owner =
   {convert: cterm -> thm option,
    stats: unit -> string,
    add_to_context: Proof.context -> Proof.context,
    check_fixtures: unit -> unit,
    check_production_context: Proof.context -> unit,
    shortcut_applications: unit -> int,
    requests: unit -> int,
    recursive_certifications: unit -> int,
    cache_hits: unit -> int,
    fallbacks: unit -> int,
    derive_rejections: unit -> int,
    retained_keys: unit -> int}
  val make: Proof.context -> column_authority -> owner
  val crt_operation_simp_rules: Proof.context -> thm list
  val apply_depth_simp_rules: Proof.context -> thm list
  val operation_context: bool -> Proof.context -> Proof.context
end

structure Comma_Semantic_B1_CRT_Apply_DAG:
  COMMA_SEMANTIC_B1_CRT_APPLY_DAG =
struct
  type column_authority =
   {known_column: term -> bool,
    column_id: term -> int option,
    column_value: int -> term,
    cofactor_node_level: int -> int option,
    prove_admitted: int * int -> thm,
    resolve_column: term -> thm option,
    cofactor_transition: int * int * int -> {target_cid: int, theorem: thm},
    reify_column: cterm -> thm}
  type owner =
   {convert: cterm -> thm option,
    stats: unit -> string,
    add_to_context: Proof.context -> Proof.context,
    check_fixtures: unit -> unit,
    check_production_context: Proof.context -> unit,
    shortcut_applications: unit -> int,
    requests: unit -> int,
    recursive_certifications: unit -> int,
    cache_hits: unit -> int,
    fallbacks: unit -> int,
    derive_rejections: unit -> int,
    retained_keys: unit -> int}

  fun apply_depth_simp_rules ctxt =
    let
      val natT = @{typ nat}
      fun numeral n = HOLogic.mk_number natT n
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
        addsimps @{thms power_0 power_one_right power_numeral_even power_numeral_odd}
      fun specialize depth =
        Simplifier.simplify arithmetic
          (Drule.infer_instantiate ctxt
            [( ("remaining", 0), Thm.cterm_of ctxt (numeral depth))]
            @{thm comma_crt_apply_shifted_from.simps(2)})
    in map specialize (0 upto 3) end

  fun crt_operation_simp_rules _ =
    @{thms comma_crt_period_def
      comma_crt_admitted.simps comma_crt_supported.simps(1)
      comma_crt_supported_node_short_circuit
      comma_crt_node_def comma_crt_node_cons
      comma_crt_negate.simps comma_crt_cofactor.simps
      comma_crt_apply_shortcut_def comma_crt_shifted_apply_shortcut_def
      comma_crt_cofactor_or_false_def comma_crt_shifted_cofactor_or_false_def
      comma_crt_boolean_value_def comma_crt_column.case
      comma_crt_result_at_def comma_crt_equiv_check_def
      comma_crt_apply_from_def comma_crt_apply_def
      comma_crt_apply_shifted_def comma_crt_apply_shifted_from.simps
      comma_crt_shift.simps rotate_drop_take drop_Nil take_Nil
      drop_Cons' take_Cons'
      comma_semantic_b1_weight_after_def
      option.inject option.distinct
      comma_crt_column.inject comma_crt_column.distinct
      comma_semantic_b1_result.inject comma_semantic_b1_result.distinct
      list.map list.case list.size list.inject list.distinct
      list_all_Nil_iff list_all_Cons_iff list_ex_Nil_iff list_ex_Cons_iff
      id_def List.map_filter_simps list.sel map_of.simps fun_upd_apply
      concat.simps append.simps filter.simps upt_rec nth_Cons' Let_def
      prod.case option.case fst_conv snd_conv case_prod_beta
      comma_semantic_b1_result.case comma_crt_boolean_operation.case
      comma_finite_move.case comma_finite_position.case comma_round_result.case}

  val operation_congs =
    @{thms option.case_cong_weak
      comma_semantic_b1_result.case_cong_weak
      comma_crt_column.case_cong_weak
      comma_crt_boolean_operation.case_cong_weak}

  fun operation_context recursive_apply ctxt =
    let
      val recursive = @{thms comma_crt_apply_shifted_from.simps}
      val depth_rules = apply_depth_simp_rules ctxt
      val rules = crt_operation_simp_rules ctxt @ depth_rules
      val selected_rules =
        if recursive_apply then rules
        else filter_out (fn rule => List.exists
          (fn recursive_rule => Thm.eq_thm_prop (rule, recursive_rule))
          (recursive @ depth_rules)) rules
      val result = fold Simplifier.add_cong operation_congs
        (ctxt addsimps selected_rules)
    in
      if recursive_apply then result
      else result delsimps (recursive @ depth_rules)
    end

  fun conversion_rule theorem =
    (case try Logic.dest_equals (Thm.prop_of theorem) of
      SOME _ => theorem
    | NONE => theorem RS @{thm eq_reflection})

  type counters =
   {requests: int, hits: int, misses: int, recursive: int,
    fallbacks: int, publications: int, parse_rejects: int,
    derive_rejects: int}
  type state = {facts: thm Termtab.table, counts: counters}
  val capacity = 65536

  fun counters requests hits misses recursive fallbacks publications
      parse_rejects derive_rejects =
    {requests = requests, hits = hits, misses = misses,
     recursive = recursive, fallbacks = fallbacks,
     publications = publications, parse_rejects = parse_rejects,
     derive_rejects = derive_rejects}: counters

  fun make ctxt authority : owner =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val known_column = #known_column authority
      val column_id = #column_id authority
      val cofactor_node_level = #cofactor_node_level authority
      val prove_admitted = #prove_admitted authority
      val resolve_column = #resolve_column authority
      val cofactor_transition = #cofactor_transition authority
      val reify_column = #reify_column authority
      val nat_zero = Thm.term_of (Thm.rhs_of
        (Axclass.unoverload_conv ctxt (Thm.cterm_of ctxt @{term "0::nat"})))
      val scalar_context = Comma_Entry_Arithmetic.natural_context ctxt
      val apply_name = @{const_name comma_crt_apply_shifted_from}
      val wrapper_names =
        [@{const_name comma_crt_apply_shifted},
         @{const_name comma_crt_apply_from}, @{const_name comma_crt_apply}]
      val applyT = @{typ "nat => nat => comma_crt_boolean_operation => comma_crt_column => comma_crt_column => comma_crt_column"}
      val rec_rules = @{thms comma_crt_apply_shifted_from.simps}
      val depth_rules = apply_depth_simp_rules ctxt
      val rec_conversion_rules = map conversion_rule rec_rules
      val depth_conversion_rules = map conversion_rule depth_rules
      (* Start from the family arithmetic base, not the caller's operation
         context: it contains an occurrence-cache simproc that can recursively
         rewrite the same apply terms and bypass this DAG owner. Keep all
         nonrecursive operation rules, but leave both general and specialized
         recursive apply equations to the proof-producing child conversion. *)
      val nonrecursive_rules =
        filter_out (fn rule => List.exists
          (fn recursive => Thm.eq_thm_prop (rule, recursive)) rec_rules)
          (crt_operation_simp_rules ctxt)
      val bounded_context_base =
        (Comma_Entry_Arithmetic.natural_context ctxt addsimps nonrecursive_rules)
        delsimps (rec_rules @ depth_rules)
        addsimps @{thms upt_0 upt_Suc upt_rec upt_rec_numeral}
      val store = Synchronized.var "semantic_b1_crt_apply_dag"
        ({facts = Termtab.empty,
          counts = counters 0 0 0 0 0 0 0 0}: state)
      val capacity_refusals = Synchronized.var "semantic_b1_crt_apply_dag_capacity_refusals" 0
      val shortcut_owner = Comma_Semantic_B1_CRT_Apply_Shortcuts.make ctxt
      val shift_owner = Comma_Semantic_B1_Shift_Quotient.make ctxt
      val depth_owner = Comma_Semantic_B1_Apply_Depth_Quotient.make ctxt
        {known_column = known_column,
         column_id = column_id,
         column_value = #column_value authority,
         cofactor_node_level = cofactor_node_level,
         prove_admitted = prove_admitted}
      val right_shift_owner = Comma_Semantic_B1_Right_Shift_Quotient.make ctxt
      val clock_owner = Comma_Semantic_B1_Apply_Clock_Quotient.make
        (#rewrite shift_owner) right_shift_owner (#right_support depth_owner)
      val root_exposure_attempts = Synchronized.var
        "semantic_b1_crt_apply_dag_root_exposure_attempts" 0
      val apply_stage_profile = Comma_Proof_Profile.make_stage_totals "apply_dag"
        ["request_lookup", "scalar_normalization", "shortcut_preflight_inclusive",
         "opened_shortcut_preflight_inclusive", "operand_normalization",
         "depth_quotient", "clock_quotient", "canonical_lookup",
         "derive_total_inclusive", "operand_exposure", "root_equation",
         "recursive_full_rewrite_inclusive", "reification", "theorem_validation"]
      fun profile_stage name work = Comma_Proof_Profile.time_stage apply_stage_profile name work
      val shortcut_applications = #applications shortcut_owner
      val parse_reason_counts = Synchronized.var
        "semantic_b1_crt_apply_dag_parse_reason_counts"
        (Symtab.empty: int Symtab.table)

      fun bump update = Synchronized.change store (fn old =>
        {facts = #facts old, counts = update (#counts old)}: state)

      fun is_closed term =
        null (Term.add_frees term []) andalso null (Term.add_vars term [])

      fun nat_value term =
        if fastype_of term <> natT then NONE
        else
          (case try HOLogic.dest_number term of
            SOME (typ, value) =>
              if typ = natT andalso value >= 0 then SOME value else NONE
          | NONE =>
              if term aconv nat_zero then SOME 0
              else (case strip_comb term of
                (Const (name, _), [predecessor]) =>
                  if name = @{const_name Suc} then
                    Option.map (fn number => number + 1) (nat_value predecessor)
                  else NONE
              | _ => NONE))

      fun canonical_nat value = HOLogic.mk_number natT value

      fun canonical_numeral term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) => typ = natT andalso value >= 0
        | NONE => false)

      (* Overloaded zero and constructor-form numerals occur in the production
         code-simplifier output. Normalize those scalar leaves with a kernel
         conversion before using them in a memo key or a specialized equation. *)
      fun normalize_nat ct =
        if canonical_numeral (Thm.term_of ct) then Thm.reflexive ct
        else
          let
            (* Code_Simp and theorem constructors can expose either overloaded
               numerals or instance constants such as Nat.zero. Normalize by
               overloading first, simplify the closed arithmetic, then restore
               canonical numeral syntax if simplification exposed an instance
               constant again. Every step is a kernel conversion. *)
            val overloaded = Axclass.overload_conv ctxt ct
            val simplified = Simplifier.rewrite scalar_context (Thm.rhs_of overloaded)
            val simplified_term = Thm.term_of (Thm.rhs_of simplified)
            val canonical =
              if canonical_numeral simplified_term then Thm.reflexive (Thm.rhs_of simplified)
              else Axclass.overload_conv ctxt (Thm.rhs_of simplified)
            val theorem = Thm.transitive overloaded (Thm.transitive simplified canonical)
            val rhs = Thm.term_of (Thm.rhs_of theorem)
          in
            (case nat_value rhs of
              SOME value =>
                if rhs aconv canonical_nat value then theorem
                else raise TERM ("cannot canonicalize admitted nat", [rhs])
            | NONE => raise TERM ("not a closed nat numeral", [rhs]))
          end

      fun normalize_nat_subterms ct =
        Conv.bottom_conv (fn _ => fn child =>
          if fastype_of (Thm.term_of child) = natT then normalize_nat child
          else Conv.all_conv child) ctxt ct

      val argument_at = Comma_Semantic_B1_Column_Lookup_Cache.argument_at

      (* The Apply head owns exactly two scalar coordinates.  Normalize those
         directly instead of bottom-walking both potentially large column
         operands; their scalar fields are normalized by the column owner. *)
      fun normalize_apply_scalars ct =
        let
          val depth = argument_at 4 normalize_nat ct
          val shift = argument_at 3 normalize_nat (Thm.rhs_of depth)
        in Thm.transitive depth shift end

      fun mk_apply depth shift operation left right =
        list_comb (Const (apply_name, applyT),
          [canonical_nat depth, canonical_nat shift,
           operation, left, right])

      fun bool_value term =
        Term.head_of term = @{term True} orelse Term.head_of term = @{term False}

      fun list_items term =
        let
          fun collect 0 current items =
                (case strip_comb current of
                  (Const (name, _), []) =>
                    if name = @{const_name Nil} then SOME (rev items) else NONE
                | _ => NONE)
            | collect remaining current items =
                (case strip_comb current of
                  (Const (name, _), []) =>
                    if name = @{const_name Nil} then SOME (rev items) else NONE
                | (Const (name, _), [head, tail]) =>
                    if name = @{const_name Cons} then
                      collect (remaining - 1) tail (head :: items)
                    else NONE
                | _ => NONE)
        in collect 11 term [] end

      (* Diagnostics must not pretty-print a whole rejected column: production
         requests can contain large closed trees.  Show only the root shape and
         bounded scalar/list metadata needed to identify the refused case. *)
      val short_shape = Comma_Semantic_B1_Column_Lookup_Cache.shape_summary nat_value
      fun short_nat term =
        (case nat_value term of SOME value => Int.toString value | NONE => "?")

      fun request_summary term =
        (case strip_comb term of
          (Const (name, _), [depth, shift, operation, left, right]) =>
            Long_Name.base_name name ^ "(depth=" ^ short_nat depth ^
            ",shift=" ^ short_nat shift ^ ",op=" ^ short_shape operation ^
            ",left=" ^ short_shape left ^ ",right=" ^ short_shape right ^ ")"
        | _ => "head=" ^ short_shape (Term.head_of term) ^
            ",arity=" ^ Int.toString (length (snd (strip_comb term))))

      fun column_shape term =
        let
          fun check level current =
            if level > 4 orelse fastype_of current <> columnT orelse
                not (is_closed current) then false
            else if known_column current then true
            else
              (case strip_comb current of
                (Const (name, _), [flag]) =>
                  name = @{const_name Comma_CRT_Bool} andalso bool_value flag
              | (Const (name, _), [node_level, children]) =>
                  if name <> @{const_name Comma_CRT_Node} then false
                  else
                    (case (nat_value node_level, list_items children) of
                      (SOME node_level, SOME values) => node_level <= 4 andalso
                        level < 4 andalso
                        List.all (check (level + 1)) values
                    | _ => false)
              | _ => false)
        in check 0 term end

      fun operation_shape term =
        (case strip_comb term of
          (Const (name, _), []) =>
            member (op =) [@{const_name Comma_CRT_And},
              @{const_name Comma_CRT_Or}] name
        | _ => false)

      fun parse term =
        (case strip_comb term of
          (Const (name, _), [depth, shift, operation, left, right]) =>
            if name <> apply_name then (NONE, "wrong-head")
            else
              (case nat_value depth of
                NONE => (NONE, "depth-not-numeral")
              | SOME d =>
                  if d > 4 then (NONE, "depth-bound:" ^ Int.toString d)
                  else
                    (case nat_value shift of
                      NONE => (NONE, "shift-not-numeral")
                    | SOME s =>
                        if s > 923 then
                          (NONE, "shift-bound:" ^ Int.toString s)
                        else if not (operation_shape operation) then
                          (NONE, "operation-shape:" ^ short_shape operation)
                        else if not (column_shape left) then
                          (NONE, "left-column-shape:" ^ short_shape left)
                        else if not (column_shape right) then
                          (NONE, "right-column-shape:" ^ short_shape right)
                        else (SOME (d, s, operation, left, right), "")))
        | (Const (name, _), _) =>
            if name = apply_name then (NONE, "wrong-arity")
            else (NONE, "wrong-head")
        | _ => (NONE, "not-apply-request"))

      fun canonical_request (depth, shift, operation, left, right) =
        mk_apply depth shift operation left right

      fun valid_theorem request theorem =
        profile_stage "theorem_validation" (fn () => let
          val lhs = Thm.term_of (Thm.lhs_of theorem)
          val rhs = Thm.term_of (Thm.rhs_of theorem)
        in null (Thm.prems_of theorem) andalso null (Thm.hyps_of theorem) andalso
          null (Thm.tpairs_of theorem) andalso
          lhs aconv request andalso fastype_of rhs = columnT andalso
          is_closed rhs andalso column_shape rhs end)

      (* Published entries are private immutable kernel theorems in this
         context-owned table. Rechecking their complete result grammar on
         every exact-request hit would redo the expensive projection work. *)
      fun valid_cached_theorem request theorem =
        Thm.term_of (Thm.lhs_of theorem) aconv request andalso
        null (Thm.prems_of theorem) andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem) andalso
        fastype_of (Thm.term_of (Thm.rhs_of theorem)) = columnT

      fun valid_column_step reference theorem =
        let
          val lhs = Thm.term_of (Thm.lhs_of theorem)
          val rhs = Thm.term_of (Thm.rhs_of theorem)
        in null (Thm.prems_of theorem) andalso null (Thm.hyps_of theorem) andalso
          null (Thm.tpairs_of theorem) andalso lhs aconv reference andalso
          fastype_of rhs = columnT andalso is_closed rhs andalso column_shape rhs
        end

      val column_comparison =
        Comma_Semantic_B1_Column_Lookup_Cache.make_column_comparison
          ctxt bounded_context_base columnT
          {valid_column = column_shape, known_column = known_column,
           resolve_column = resolve_column, valid_step = valid_column_step}
      val comparison_context =
        #add_to_context column_comparison bounded_context_base

      fun column_reference_conversion ct =
        (case strip_comb (Thm.term_of ct) of
          (Const (name, _), [_, _]) =>
            if name <> @{const_name comma_semantic_b1_crt_column_at} then
              Conv.all_conv ct
            else
              let
                val scalar_equation = argument_at 0 normalize_nat ct
                val canonical_ct = Thm.rhs_of scalar_equation
                val reference = Thm.term_of canonical_ct
              in
                if not (known_column reference) then Conv.all_conv ct
                else
                  (Synchronized.change root_exposure_attempts (fn count => count + 1);
                   case resolve_column reference of
                    SOME theorem =>
                      if valid_column_step reference theorem then
                        Thm.transitive scalar_equation
                          (Conv.rewr_conv (conversion_rule theorem) canonical_ct)
                      else error "B1 apply DAG received a malformed owned column step"
                  | NONE => error "B1 apply DAG could not resolve an owned column reference")
              end
        | _ => Conv.all_conv ct)

      val convert_callback : (cterm -> thm option) Unsynchronized.ref =
        Unsynchronized.ref (fn _ => NONE)
      val derived_rhs_context_ref = Unsynchronized.ref (NONE: Proof.context option)
      val {normalize = normalize_column_expression,
           stats = source_column_normalizer_stats} =
        Comma_Semantic_B1_Source_Column_Normalizer.make bounded_context_base
          {known_column = known_column, valid_column = column_shape,
           column_value = #column_value authority,
           nat_value = nat_value,
           normalize_scalars = (fn scalar_ct => try normalize_nat_subterms scalar_ct),
           cofactor_transition = cofactor_transition,
           open_column_reference = column_reference_conversion,
           reify_column = reify_column, convert = convert_callback}
      fun normalize_apply_operands ct =
        let
          val left = argument_at 1 normalize_column_expression ct
          val right = argument_at 0 normalize_column_expression (Thm.rhs_of left)
        in Thm.transitive left right end

      fun open_apply_operands ct =
        let
          val left = argument_at 1 column_reference_conversion ct
          val both = argument_at 0 column_reference_conversion (Thm.rhs_of left)
        in Thm.transitive left both end

      fun lookup key =
        Synchronized.change_result store (fn old =>
          let
            val count = #counts old
            val facts = #facts old
            val found = Termtab.lookup facts key
            val counts =
              (case found of
                SOME _ => counters (#requests count) (#hits count + 1)
                  (#misses count) (#recursive count) (#fallbacks count)
                  (#publications count) (#parse_rejects count)
                  (#derive_rejects count)
              | NONE => counters (#requests count) (#hits count)
                  (#misses count + 1) (#recursive count) (#fallbacks count)
                  (#publications count) (#parse_rejects count)
                  (#derive_rejects count))
          in (found, {facts = facts, counts = counts}: state) end)

      fun publish key theorem =
        Synchronized.change store (fn old =>
          if Termtab.defined (#facts old) key then old
          else if Termtab.size (#facts old) >= capacity then
            (Synchronized.change capacity_refusals (fn count => count + 1); old)
          else
            let val count = #counts old
            in {facts = Termtab.update (key, theorem) (#facts old),
              counts = counters (#requests count) (#hits count) (#misses count)
                (#recursive count) (#fallbacks count)
                (#publications count + 1) (#parse_rejects count)
                (#derive_rejects count)}: state end)

      fun record_request () = bump (fn count => counters (#requests count + 1)
        (#hits count) (#misses count) (#recursive count)
        (#fallbacks count) (#publications count) (#parse_rejects count)
        (#derive_rejects count))

      fun fallback () = bump (fn count => counters (#requests count)
        (#hits count) (#misses count) (#recursive count)
        (#fallbacks count + 1) (#publications count) (#parse_rejects count)
        (#derive_rejects count))

      fun reason_key reason =
        let
          fun prefix [] reversed = String.implode (rev reversed)
            | prefix (#":" :: _) reversed = String.implode (rev reversed)
            | prefix (char :: rest) reversed = prefix rest (char :: reversed)
        in prefix (String.explode reason) [] end

      fun note_reject kind reason diagnostic_term =
        let
          val ordinal = Synchronized.change_result store (fn old =>
            let
              val count = #counts old
              val (next, counts) =
                if kind = "parse" then
                  (#parse_rejects count + 1,
                   counters (#requests count) (#hits count) (#misses count)
                     (#recursive count) (#fallbacks count) (#publications count)
                     (#parse_rejects count + 1) (#derive_rejects count))
                else
                  (#derive_rejects count + 1,
                   counters (#requests count) (#hits count) (#misses count)
                     (#recursive count) (#fallbacks count) (#publications count)
                     (#parse_rejects count) (#derive_rejects count + 1))
            in (next, {facts = #facts old, counts = counts}: state) end)
          val _ = if kind = "parse" then
            let
              val key = reason_key reason
            in Synchronized.change parse_reason_counts
              (Symtab.map_default (key, 0) (fn n => n + 1)) end
            else ()
        in
          if ordinal <= 8 then
            Comma_Proof_Profile.report
              ("B1 CRT apply DAG " ^ kind ^ " rejection: " ^ reason ^
                (case diagnostic_term of
                  SOME term => " request=" ^ request_summary term
                | NONE => ""))
          else ()
        end

      fun stats () =
        let val snapshot = Synchronized.value store
            val count = #counts snapshot
        in "apply_dag_requests=" ^ Int.toString (#requests count) ^
          " apply_dag_keys=" ^ Int.toString (Termtab.size (#facts snapshot)) ^
          " apply_dag_capacity_refusals=" ^
            Int.toString (Synchronized.value capacity_refusals) ^
          " apply_dag_hits=" ^ Int.toString (#hits count) ^
          " apply_dag_misses=" ^ Int.toString (#misses count) ^
          " apply_dag_column_comparison_hits=" ^
            Int.toString (#hits column_comparison ()) ^
          " apply_dag_column_comparison_misses=" ^
            Int.toString (#misses column_comparison ()) ^
          " apply_dag_column_comparison_publications=" ^
            Int.toString (#publications column_comparison ()) ^
          " apply_dag_column_comparison_resolutions=" ^
            Int.toString (#resolutions column_comparison ()) ^
          " apply_dag_shortcut_applications=" ^
            Int.toString (shortcut_applications ()) ^
          " apply_dag_shift_rules=" ^ Int.toString (#retained_rules shift_owner ()) ^
          " apply_dag_shift_rule_hits=" ^ Int.toString (#rule_hits shift_owner ()) ^
          " apply_dag_shift_rule_builds=" ^ Int.toString (#rule_builds shift_owner ()) ^
          " apply_dag_unused_level_strips=" ^
            Int.toString (#strips depth_owner ()) ^
          " apply_dag_unused_level_transport_rule_hits=" ^
            Int.toString (#transport_rule_hits depth_owner ()) ^
          " apply_dag_unused_level_transport_rule_builds=" ^
            Int.toString (#transport_rule_builds depth_owner ()) ^
          " apply_dag_unused_level_transport_capacity_refusals=" ^
            Int.toString (#transport_capacity_refusals depth_owner ()) ^
          " apply_dag_unused_level_transport_rules=" ^
            Int.toString (#retained_transport_rules depth_owner ()) ^
          " apply_dag_owned_root_exposure_attempts=" ^
            Int.toString (Synchronized.value root_exposure_attempts) ^
          " apply_dag_recursive_certifications=" ^ Int.toString (#recursive count) ^
          " apply_dag_fallbacks=" ^ Int.toString (#fallbacks count) ^
          " apply_dag_publications=" ^ Int.toString (#publications count) ^
          " apply_dag_parse_rejects=" ^ Int.toString (#parse_rejects count) ^
          " apply_dag_derive_rejects=" ^ Int.toString (#derive_rejects count) ^
          " " ^ #stats clock_owner () ^ " apply_dag_parse_reasons={" ^
            String.concatWith "," (map (fn (reason, n) =>
              reason ^ "=" ^ Int.toString n)
              (Symtab.dest (Synchronized.value parse_reason_counts))) ^ "} " ^
            Comma_Proof_Profile.stage_profile_stats apply_stage_profile ^ " " ^ source_column_normalizer_stats ()
        end

      fun recursive_certifications () = #recursive (#counts (Synchronized.value store))
      fun requests () = #requests (#counts (Synchronized.value store))
      fun cache_hits () = #hits (#counts (Synchronized.value store))
      fun retained_keys () = Termtab.size (#facts (Synchronized.value store))

      val report_progress = Comma_Proof_Profile.make_progress "B1 CRT apply DAG"
        stats requests recursive_certifications
        (fn () => #fallbacks (#counts (Synchronized.value store)))

      fun wrapper_rule name request =
        let
          val expected_arity =
            if name = @{const_name comma_crt_apply} then 3 else 4
          val (_, arguments) = strip_comb request
        in
          if length arguments <> expected_arity then NONE
          else if name = @{const_name comma_crt_apply_shifted}
            then SOME (conversion_rule @{thm comma_crt_apply_shifted_def})
          else if name = @{const_name comma_crt_apply_from}
            then SOME (conversion_rule @{thm comma_crt_apply_from_def})
          else if name = @{const_name comma_crt_apply}
            then SOME (conversion_rule @{thm comma_crt_apply_def})
          else NONE
        end

      and derive request depth opened_operands =
        let
          val result = profile_stage "derive_total_inclusive" (fn () => let
          val root_rule =
            if depth = 0 then hd rec_conversion_rules
            else List.nth (depth_conversion_rules, depth - 1)
          (* Expose only each operand's root reference.  Its shallow node keeps
             all child CIDs opaque; a recursive apply opens only the selected
             child when that child becomes an operand on the next call. *)
          val exposed = profile_stage "operand_exposure" (fn () =>
            (case opened_operands of
              SOME theorem =>
                if Thm.term_of (Thm.lhs_of theorem) aconv request andalso
                    null (Thm.prems_of theorem) andalso null (Thm.hyps_of theorem) andalso
                    null (Thm.tpairs_of theorem) andalso
                    is_closed (Thm.term_of (Thm.rhs_of theorem)) andalso
                    fastype_of (Thm.term_of (Thm.rhs_of theorem)) = columnT
                then theorem
                else error "B1 apply-DAG reused a foreign operand exposure"
            | NONE => open_apply_operands (Thm.cterm_of ctxt request)))
          val root = profile_stage "root_equation" (fn () =>
            Conv.rewr_conv root_rule (Thm.rhs_of exposed))
          val recursive_context =
            (case !derived_rhs_context_ref of
              SOME context => context
            | NONE => error "B1 apply-DAG recursive context was not initialized")
          val normalized_rhs = profile_stage "recursive_full_rewrite_inclusive" (fn () =>
            Simplifier.full_rewrite recursive_context (Thm.rhs_of root))
          val raw_theorem = Thm.transitive exposed (Thm.transitive root normalized_rhs)
          (* Publish the canonical shallow column form owned by the column
             authority, just as the former column evaluator did.  This keeps
             equivalent completed actions interned to the same authenticated
             DAG references while preserving the exact request equation. *)
          val canonical_result = profile_stage "reification" (fn () =>
            reify_column (Thm.rhs_of raw_theorem))
          val theorem = Thm.transitive raw_theorem canonical_result
          val valid = valid_theorem request theorem
        in
          if valid then
            (bump (fn count => counters (#requests count) (#hits count)
              (#misses count) (#recursive count + 1) (#fallbacks count)
              (#publications count) (#parse_rejects count)
              (#derive_rejects count)); SOME theorem)
          else
            (note_reject "derive" ("result-shape=" ^
              short_shape (Thm.term_of (Thm.rhs_of theorem))) (SOME request); NONE)
        end)
          val _ = (case result of SOME _ => report_progress "recursive-certification"
            | NONE => ())
        in result end

      and shortcut_preflight request scalar =
        let
          val normalized = Thm.rhs_of scalar
          fun shortcut_theorems () =
            (case #rewrite shortcut_owner normalized of
              NONE => NONE
            | SOME rule =>
                let
                  val inner = Thm.transitive rule
                    (reify_column (Thm.rhs_of rule))
                  val exact = Thm.transitive scalar inner
                in
                  if valid_theorem request exact then SOME (inner, exact)
                  else error "B1 admitted Apply shortcut changed its exact request"
                end)
        in
          if not (#candidate shortcut_owner normalized) then NONE
          else
            (case parse (Thm.term_of normalized) of
              (NONE, _) => NONE
            | (SOME (depth, shift, operation, left, right), _) =>
                let
                  val (canonical_depth, canonical_ct, depth_equation, strips) =
                    profile_stage "depth_quotient" (fn () => #reduce depth_owner
                      depth shift operation left right normalized)
                  val _ = #record depth_owner strips
                  val (canonical_shift, shift_equation) =
                    profile_stage "clock_quotient" (fn () => #rewrite clock_owner
                      canonical_depth shift canonical_ct)
                  val key = canonical_request (canonical_depth, canonical_shift,
                    operation, left, right)
                  val canonicalization = Thm.transitive depth_equation shift_equation
                  val normalized_term = Thm.term_of normalized
                  val _ = if Thm.term_of (Thm.lhs_of canonicalization) aconv
                      normalized_term andalso
                      Thm.term_of (Thm.rhs_of canonicalization) aconv key then ()
                    else error "B1 shortcut canonicalization changed its exact request"
                  val cached = profile_stage "canonical_lookup" (fn () =>
                    if key aconv request then NONE else lookup key)
                in
                  (case cached of
                    SOME theorem =>
                      if not (valid_cached_theorem key theorem) then
                        error "B1 canonical shortcut memo is malformed"
                      else
                        let
                          val exact = Thm.transitive scalar
                            (Thm.transitive canonicalization theorem)
                        in
                          if valid_theorem request exact then SOME exact
                          else error "B1 canonical shortcut memo changed its request"
                        end
                  | NONE =>
                      (case shortcut_theorems () of
                        NONE => NONE
                      | SOME (inner, exact) =>
                          let
                            val canonical_theorem =
                              Thm.transitive (Thm.symmetric canonicalization) inner
                            val _ = if valid_theorem key canonical_theorem then
                                publish key canonical_theorem else error
                                  "B1 shortcut theorem did not bind its canonical key"
                          in SOME exact end))
                end)
        end

      and opened_shortcut_preflight request scalar =
        (case try (fn () => profile_stage "operand_exposure" (fn () =>
          open_apply_operands (Thm.rhs_of scalar))) () of
          NONE => (NONE, NONE)
        | SOME opened =>
            let
              val shallow = Thm.rhs_of opened
              val shallow_request = Thm.term_of shallow
            in
              (case parse shallow_request of
                (SOME _, _) =>
                  (case #rewrite shortcut_owner shallow of
                    SOME rule =>
                      let
                        val exact = Thm.transitive scalar (Thm.transitive opened rule)
                        val theorem = Thm.transitive exact
                          (reify_column (Thm.rhs_of exact))
                      in
                        if valid_theorem request theorem then
                          (SOME theorem, SOME opened)
                        else error "B1 admitted Apply shortcut changed its exact request"
                      end
                  | NONE => (NONE, SOME opened))
              | _ => (NONE, SOME opened))
            end)

      and convert ct =
        let
          val request = Thm.term_of ct
        in
          (case Term.head_of request of
            Const (name, _) =>
              if member (op =) wrapper_names name then
                (case wrapper_rule name request of
                  NONE => (fallback (); report_progress "wrapper-fallback"; NONE)
                | SOME definition =>
                    (case try (Conv.rewr_conv definition) ct of
                      NONE => (fallback (); report_progress "wrapper-fallback"; NONE)
                    | SOME unfolded =>
                        (case convert (Thm.rhs_of unfolded) of
                          SOME child =>
                            let val theorem = Thm.transitive unfolded child
                            in if valid_theorem request theorem then SOME theorem
                              else error "B1 shifted-apply wrapper changed its authority" end
                        | NONE => (fallback (); report_progress "wrapper-fallback"; NONE))))
              else if name <> apply_name then NONE
              else
              let
                val _ = record_request ()
                val exact_result = profile_stage "request_lookup" (fn () => lookup request)
                (* Record milestones on exact hits too; long sessions may time out. *)
                val _ = report_progress "request-lookup"
              in
                (case exact_result of
                  SOME theorem =>
                    if valid_cached_theorem request theorem then SOME theorem
                    else error "B1 shifted-apply exact-request memo is malformed"
                | NONE =>
                  if Term.is_open request orelse
                      not (null (Term.add_frees request [])) orelse
                      not (null (Term.add_vars request [])) then
                    (fallback ();
                     note_reject "parse" "open-or-schematic-request" (SOME request);
                     report_progress "open-request-fallback"; NONE)
                  else
                  let
                    val scalar = profile_stage "scalar_normalization" (fn () =>
                      (case try normalize_apply_scalars ct of
                        NONE =>
                          (note_reject "parse" "natural-scalar normalization failed"
                             (SOME request); NONE)
                      | SOME theorem => SOME theorem))
                  in
                    (case scalar of
                      NONE => (fallback (); report_progress "fallback"; NONE)
                    | SOME scalar_equation =>
                      let
                        (* Avoid opening owned references before the canonical probe. *)
                        val shortcut_result = profile_stage "shortcut_preflight_inclusive" (fn () =>
                          shortcut_preflight request scalar_equation)
                      in
                        (case shortcut_result of
                          SOME theorem => SOME theorem
                        | NONE =>
                          let
                            (* Keep references shallow until after the canonical probe. *)
                            val normalized = profile_stage "operand_normalization" (fn () =>
                              (case try normalize_apply_operands
                                  (Thm.rhs_of scalar_equation) of
                                SOME operands => SOME (Thm.transitive scalar_equation operands)
                              | NONE => NONE))
                          in
                            (case normalized of
                              NONE =>
                                (note_reject "parse" "column-operand normalization failed"
                                   (SOME (Thm.term_of (Thm.rhs_of scalar_equation)));
                                 fallback (); report_progress "fallback"; NONE)
                            | SOME normalization =>
                              let
                                val normalized_ct = Thm.rhs_of normalization
                                val normalized_request = Thm.term_of normalized_ct
                                val (parsed, reason) = parse normalized_request
                              in
                                (case parsed of
                                  NONE =>
                                    (note_reject "parse" reason
                                      (SOME normalized_request);
                                     fallback (); report_progress "fallback"; NONE)
                                | SOME (depth, shift, operation, left, right) =>
                                  let
                                    val (canonical_depth, canonical_ct,
                                      depth_equation, depth_strips) = profile_stage
                                        "depth_quotient" (fn () => #reduce depth_owner
                                          depth shift operation left right normalized_ct)
                                    val _ = #record depth_owner depth_strips
                                    val normalization = Thm.transitive normalization
                                      depth_equation
                                    val (canonical_shift, shift_equation) = profile_stage
                                      "clock_quotient" (fn () => #rewrite clock_owner
                                        canonical_depth shift canonical_ct)
                                    val normalization = Thm.transitive normalization
                                      shift_equation
                                    val key = canonical_request
                                      (canonical_depth, canonical_shift,
                                       operation, left, right)
                                    (* Probe the canonical memo before opening operand roots. *)
                                    val result = profile_stage "canonical_lookup" (fn () =>
                                      if key aconv request then NONE else lookup key)
                                    val _ = report_progress "canonical-lookup"
                                    fun publish_result theorem =
                                      let
                                        val result = Thm.transitive normalization theorem
                                        val _ = if valid_cached_theorem request result then ()
                                          else error
                                            "B1 shifted-apply derivation changed its request"
                                        (* Return aliases exactly, but memoize only the canonical key. *)
                                        val _ = if request aconv key then
                                            publish request result else ()
                                      in SOME result end
                                  in
                                    (case result of
                                      SOME theorem =>
                                        if valid_cached_theorem key theorem then
                                          publish_result theorem
                                        else error
                                          "B1 shifted-apply memo has a foreign or malformed theorem"
                                    | NONE =>
                                    (case profile_stage "opened_shortcut_preflight_inclusive"
                                      (fn () => opened_shortcut_preflight request normalization) of
                                        (SOME theorem, _) =>
                                          let
                                            val canonical_theorem = Thm.transitive
                                              (Thm.symmetric normalization) theorem
                                            val _ = if valid_theorem key canonical_theorem then
                                                publish key canonical_theorem
                                              else error
                                                "B1 opened shortcut did not bind its canonical key"
                                          in SOME theorem end
                                      | (NONE, opened) =>
                                        (case try (fn () => derive key canonical_depth opened) () of
                                          SOME (SOME theorem) =>
                                            (publish key theorem; publish_result theorem)
                                        | SOME NONE =>
                                            (fallback ();
                                             report_progress "fallback"; NONE)
                                        | NONE =>
                                            (note_reject "derive"
                                              "recursive proof conversion rejected root"
                                              (SOME key);
                                             fallback ();
                                             report_progress "fallback"; NONE))))
                                  end)
                              end)
                          end)
                      end)
                  end)
              end
          | _ => NONE)
        end

      val apply_patterns =
        [@{term "comma_crt_apply operation left right"},
         @{term "comma_crt_apply_from depth operation left right"},
         @{term "comma_crt_apply_shifted operation shift left right"},
         @{term "comma_crt_apply_shifted_from depth shift operation left right"},
         @{term "comma_crt_apply_shortcut operation left right"},
         @{term "comma_crt_shifted_apply_shortcut operation shift left right"}]
      val apply_procedure = Simplifier.make_simproc ctxt
        {name = "comma_semantic_b1_crt_apply_dag",
         kind = Simplifier.Congproc false,
         lhss = map Comma_Selected_List_Conversion.schematize apply_patterns,
         proc = fn _ => fn _ => convert, identifier = []}

      val derived_rhs_context =
        fold Simplifier.add_cong
          [Comma_Semantic_B1_Column_Lookup_Cache.weak_map_input_congruence]
          (Simplifier.add_proc apply_procedure comparison_context)
      val _ = derived_rhs_context_ref := SOME derived_rhs_context
      val _ = convert_callback := convert

      fun check_fixtures () =
        let
          val isolated = make ctxt authority
          val isolated_right_shift_owner =
            Comma_Semantic_B1_Right_Shift_Quotient.make ctxt
          val apply_view:
            Comma_Semantic_B1_CRT_Apply_DAG_Production_Fixture.apply_owner =
            {convert = #convert isolated, stats = #stats isolated,
             requests = #requests isolated,
             recursive_certifications = #recursive_certifications isolated,
             cache_hits = #cache_hits isolated,
             retained_keys = #retained_keys isolated,
             fallbacks = #fallbacks isolated,
             derive_rejections = #derive_rejections isolated,
             shortcut_applications = #shortcut_applications isolated}
          val comparison_view:
            Comma_Semantic_B1_CRT_Apply_DAG_Production_Fixture.column_comparison =
            {convert = #convert column_comparison, hits = #hits column_comparison,
             misses = #misses column_comparison,
             publications = #publications column_comparison,
             resolutions = #resolutions column_comparison}
        in
          Comma_Semantic_B1_CRT_Apply_DAG_Production_Fixture.check_owner_fixtures
            ctxt apply_view comparison_view valid_theorem;
          Comma_Semantic_B1_Shift_Quotient.check_application ctxt
            {convert = #convert isolated, cache_hits = #cache_hits isolated,
             recursive_certifications = #recursive_certifications isolated};
          #check_fixture isolated_right_shift_owner ()
        end

      fun check_production_context production_context =
        (#check_fixture depth_owner
          {convert = convert, recursive_certifications = recursive_certifications,
           cache_hits = cache_hits,
           root_exposures = fn () => Synchronized.value root_exposure_attempts};
        Comma_Semantic_B1_CRT_Apply_DAG_Production_Fixture.check ctxt
          production_context
          {convert = convert, stats = stats, requests = requests,
           recursive_certifications = recursive_certifications,
           cache_hits = cache_hits,
           shortcut_applications = shortcut_applications,
           retained_keys = retained_keys,
           fallbacks = fn () => #fallbacks (#counts (Synchronized.value store)),
           derive_rejections = fn () => #derive_rejects (#counts (Synchronized.value store))}
          {known_column = known_column, column_value = #column_value authority,
           cofactor_transition = cofactor_transition,
           valid_column = column_shape, reify_column = reify_column,
         normalize_column = normalize_column_expression}
          {convert = #convert column_comparison, hits = #hits column_comparison,
           misses = #misses column_comparison,
           publications = #publications column_comparison,
           resolutions = #resolutions column_comparison}
        )

    in
      {convert = convert, stats = stats,
       add_to_context = Simplifier.add_proc apply_procedure,
       check_fixtures = check_fixtures,
       check_production_context = check_production_context,
       shortcut_applications = shortcut_applications,
       requests = requests,
       recursive_certifications = recursive_certifications,
       cache_hits = cache_hits,
       fallbacks = fn () => #fallbacks (#counts (Synchronized.value store)),
       derive_rejections = fn () => #derive_rejects (#counts (Synchronized.value store)),
       retained_keys = retained_keys}: owner
    end
end
