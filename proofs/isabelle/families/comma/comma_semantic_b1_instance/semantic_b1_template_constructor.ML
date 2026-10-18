(* Candidate-only B1 quotienting over source-level CRT tables. One generated
   packet-slot evaluator discovers normalized sources by sector layers and its
   retained slot actions feed the shared CRT/MDD algebra. It emits template
   CIDs and compact slot/lift references; all remain untrusted until the
   importing theory proves the corresponding certificates. *)
structure Comma_Semantic_B1_Template_Constructor =
struct
  open Comma_Semantic_B1_MDD
  datatype output = Live of int | Stop of int | Invalid
  datatype lift_ref = Terminal_Ref of int * int
    | Goto_Ref of int * int * int
  datatype pending_lift_ref = Pending_Terminal of int * output * mdd
    | Pending_Goto of int * int * int
  type lift_descriptor =
    {period: int, slot: int, template_cid: int, net_shift: int}
  type lift_entry = {lift_cid: int, geometry: mdd list}
  type representative =
    {template_cid: int, keys: mdd list}
  type occurrence =
    {root: int option, source: term, template_cid: int, return_shift: int,
     binding: output list, lift_refs: lift_ref list}

  val natT = @{typ nat}
  val resultT = @{typ comma_semantic_b1_result}
  val columnT = @{typ comma_crt_column}
  val action_listT = @{typ "comma_source_continuation_action list"}
  val action_rowsT = HOLogic.listT action_listT
  val source_action_batch_size = 128

  (* Compile the direct packet-slot evaluator once and reuse its results for
     discovery and the symbolic table fold.  The batch form amortizes code
     evaluation setup while retaining one result row for every source. *)
  val slot_actions_computation =
    @{computation "Code_Evaluation.term"
      terms:
        "Code_Evaluation.term_of :: (comma_source_continuation_action list) list \<Rightarrow> Code_Evaluation.term"
        "numeral :: num \<Rightarrow> nat"
        "nat_of_num :: num \<Rightarrow> nat"
        "one_nat_inst.one_nat :: nat"
        "map :: (comma_finite_position \<Rightarrow> comma_source_continuation_action list) \<Rightarrow> comma_finite_position list \<Rightarrow> comma_source_continuation_action list list"
        "comma_semantic_b1_source_slot_actions :: comma_finite_position \<Rightarrow> comma_source_continuation_action list"
      datatypes: nat num comma_finite_position comma_source_continuation_action
        "comma_finite_position list"
        "comma_source_continuation_action list"
        "comma_source_continuation_action list list"}
      (fn post => post o the)

  fun nat n = HOLogic.mk_number natT n

  fun dest_nat term =
    let val (typ, number) = HOLogic.dest_number term
    in if typ = natT andalso number >= 0 then number
      else error "B1 candidate contains a non-natural scope coordinate" end

  fun compare_output (left, right) =
    (case (left, right) of
      (Invalid, Invalid) => EQUAL
    | (Invalid, _) => LESS
    | (_, Invalid) => GREATER
    | (Live a, Live b) => int_ord (a, b)
    | (Live _, Stop _) => LESS
    | (Stop _, Live _) => GREATER
    | (Stop a, Stop b) => int_ord (a, b))

  fun output_term (Live root) = @{term Comma_Semantic_B1_Live} $ nat root
    | output_term (Stop position) = @{term Comma_Semantic_B1_Stop} $ nat position
    | output_term Invalid = @{term Comma_Semantic_B1_Invalid}

  fun binding_outputs (template_keys: mdd list) (source_keys: mdd list)
      (source_outputs: output list) =
    let
      val _ = if length source_keys = length source_outputs then ()
        else error "B1 source output labels lost MDD column alignment"
      val output_index = fold (fn (key, output) => fn index =>
        (case MDDtab.lookup index key of
          NONE => MDDtab.update (key, output) index
        | SOME prior => if compare_output (prior, output) = EQUAL then index
            else error "B1 source partition assigns conflicting outputs to one column"))
        (source_keys ~~ source_outputs) MDDtab.empty
    in map (fn key => case MDDtab.lookup output_index key of
        SOME output => output
      | NONE => error "B1 canonical template column has no occurrence binding")
      template_keys end

  fun lift_template_slot_with slot_key_for translate_key period slot net_shift
      template_keys =
    let
      val slot_key = slot_key_for period slot
      val negative_shift = (clock_size - (net_shift mod clock_size)) mod clock_size
    in map (fn key => mdd_and (slot_key, translate_key negative_shift key))
      template_keys end

  fun lift_template_slot period slot net_shift template_keys =
    lift_template_slot_with
      (fn period => fn slot => scope_column_key [(period, slot)])
      translate_mdd period slot net_shift template_keys

  fun mdd_eval_phase MDD_False _ = false
    | mdd_eval_phase MDD_True _ = true
    | mdd_eval_phase (MDD_Node (level, children)) phase =
        let
          val digit = phase mod nth character_periods level
        in digit < length children andalso mdd_eval_phase (nth children digit) phase end

  fun representative_values ctxt =
    let
      val evaluation = put_simpset HOL_basic_ss ctxt addsimps
        @{thms comma_offset_representatives_def list.map upt_rec}
      val theorem = Simplifier.full_rewrite evaluation
        (Thm.cterm_of ctxt @{term comma_offset_representatives})
      fun value term =
        let val (typ, number) = HOLogic.dest_number term
        in if typ = natT andalso number >= 0 then number
          else error "B1 representative catalog did not reduce to natural literals" end
    in map value (HOLogic.dest_list (Thm.term_of (Thm.rhs_of theorem))) end

  fun source_base_term term =
    (case strip_comb term of
      (Const (name, _), [sector, _, coordinate]) =>
        if name = @{const_name Comma_Entry} then
          @{term Comma_Entry} $ sector $ nat 0 $ coordinate
        else if name = @{const_name Comma_Near} then
          @{term Comma_Near} $ sector $ nat 0 $ coordinate
        else error "B1 source discovery received an unknown source constructor"
    | _ => error "B1 source discovery received a non-literal source")

  fun source_sector term =
    (case strip_comb term of
      (Const (name, _), [sector, shift, _]) =>
        if (name = @{const_name Comma_Entry} orelse
            name = @{const_name Comma_Near}) andalso dest_nat shift = 0
        then dest_nat sector
        else error "B1 source-order key is not a normalized source"
    | _ => error "B1 source-order key is not a finite-position constructor")

  fun source_order_key term =
    (case strip_comb term of
      (Const (name, _), [sector, shift, coordinate]) =>
        let
          val f = dest_nat sector
          val delta = dest_nat shift
          val value = dest_nat coordinate
          val _ = if delta = 0 andalso 1 <= f andalso f <= 9 then ()
            else error "B1 source-order key requires a normalized sector source"
          val kind_offset =
            if name = @{const_name Comma_Entry} then 0
            else if name = @{const_name Comma_Near} then 100
            else error "B1 source-order key received an unknown source constructor"
        in (9 - f) * 1024 + kind_offset + value end
    | _ => error "B1 source-order key received a non-literal source")

  fun source_action_batch_terms ctxt sources =
    let
      val sourceT = @{typ comma_finite_position}
      val sourcesT = HOLogic.listT sourceT
      val map_actions = Const (@{const_name map},
        (sourceT --> action_listT) --> sourcesT --> action_rowsT) $
          @{term comma_semantic_b1_source_slot_actions} $
          HOLogic.mk_list sourceT sources
      val term_of_actions = Const (@{const_name Code_Evaluation.term_of},
        action_rowsT --> @{typ Code_Evaluation.term}) $ map_actions
      val value = slot_actions_computation ctxt term_of_actions
      val rows = map HOLogic.dest_list (HOLogic.dest_list value)
      val _ = if length rows = length sources then ()
        else error "B1 batched source-action evaluation changed source extent"
    in rows end

  fun goto_child action =
    (case strip_comb action of
      (Const (name, _), [child, shift]) =>
        if name = @{const_name Comma_Continuation_Goto}
        then SOME (child, dest_nat shift) else NONE
    | _ => NONE)

  fun action_goto_child action = Option.map #1 (goto_child action)

  (* Template discovery and its data fold share this nine-layer scheduler. *)
  fun discover_source_order_by_layers roots discover_layer =
    let
      val visited = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
      val layers = Array.array (10, []: (int * term) list)
      fun schedule_normalized sector source =
        let
          val _ = if 1 <= sector andalso sector <= 9 then ()
            else error "B1 source discovery escaped sectors 1 through 9"
        in
          if Termtab.defined (!visited) source then ()
          else
            let
              val order_key = source_order_key source
              val _ = visited := Termtab.update (source, ()) (!visited)
            in Array.update (layers, sector,
                 (order_key, source) :: Array.sub (layers, sector)) end
        end
      fun schedule raw_source =
        let
          val source = source_base_term raw_source
          val sector = source_sector source
        in schedule_normalized sector source end
      val _ = List.app schedule roots
      fun visit (sector, order) =
        if sector = 10 then order
        else
          let
            val current = sort (fn ((left_key, _), (right_key, _)) =>
              int_ord (left_key, right_key))
              (Array.sub (layers, sector))
            val current_sources = map #2 current
            val _ = discover_layer sector current_sources schedule_normalized
          in visit (sector + 1, current_sources @ order) end
      val ordered = visit (1, [])
      val _ = if length ordered = Termtab.size (!visited) then ()
        else error "B1 source-order traversal lost a visited source"
    in ordered end

  fun take_source_batch maximum sources =
    let
      fun take 0 remaining reversed = (rev reversed, remaining)
        | take _ [] reversed = (rev reversed, [])
        | take count (source :: remaining) reversed =
            take (count - 1) remaining (source :: reversed)
    in take maximum sources [] end

  fun discover_template_source_order ctxt roots =
    let
      val actions_by_source =
        Unsynchronized.ref (Termtab.empty: term list Termtab.table)
      val source_action_batch_calls = Unsynchronized.ref 0
      val source_action_batch_sources = Unsynchronized.ref 0
      fun discover_layer sector sources schedule_normalized =
        let
          fun visit_batches [] = ()
            | visit_batches remaining =
                let
                  val (batch, rest) =
                    take_source_batch source_action_batch_size remaining
                  val rows = source_action_batch_terms ctxt batch
                  val _ = source_action_batch_calls :=
                    !source_action_batch_calls + 1
                  val _ = source_action_batch_sources :=
                    !source_action_batch_sources + length batch
                  val _ = if length batch = length rows then ()
                    else error "B1 source-action batch lost source alignment"
                  fun discover_from (source, actions) =
                    let
                      val _ = if Termtab.defined (!actions_by_source) source
                        then error "B1 source-action batch duplicated a discovered source"
                        else ()
                      val _ = actions_by_source :=
                        Termtab.update (source, actions) (!actions_by_source)
                      fun add child =
                        let
                          val normalized = source_base_term child
                          val next_sector = source_sector normalized
                          val _ = if sector < next_sector andalso next_sector <= 9 then ()
                            else error "B1 Goto source violates strict sector progress"
                        in schedule_normalized next_sector normalized end
                    in List.app add (map_filter action_goto_child actions) end
                  val _ = List.app discover_from (batch ~~ rows)
                in visit_batches rest end
          val _ = visit_batches sources
        in () end
      val ordered = discover_source_order_by_layers roots discover_layer
      val _ = if Termtab.size (!actions_by_source) = length ordered then ()
        else error "B1 template traversal did not retain each packet-action list"
    in (ordered, !actions_by_source,
        !source_action_batch_calls, !source_action_batch_sources) end

  fun offset_orbit offset =
    let
      val x = IntInf.fromInt offset
      val digit = IntInf.fromInt (offset mod 10)
      val digit_sum = 5 * digit * digit - 4 * digit
      val residue = IntInf.mod (x - digit_sum, IntInf.fromInt 460)
    in IntInf.toInt (IntInf.div (residue, IntInf.fromInt 10)) end

  fun terminal_output action =
    (case strip_comb action of
      (Const (name, _), [target, _]) =>
        if name = @{const_name Comma_Continuation_Exit} then
          (case strip_comb target of
            (Const (entry_name, _), [field, delta, offset]) =>
              if entry_name = @{const_name Comma_Entry} then
                let
                  val f = dest_nat field
                  val d = dest_nat delta
                  val x = dest_nat offset
                in if f = 1 andalso d = 0 andalso x <= 90
                   then Live (offset_orbit x) else Invalid end
              else if entry_name = @{const_name Comma_Near} then Invalid
              else error "B1 Exit target has an unknown source constructor"
          | _ => error "B1 Exit target is not a finite position")
        else if name = @{const_name Comma_Continuation_Fork} then
          let val a = dest_nat target
          in if 2 <= a andalso a <= 9 then Stop (a - 2) else Invalid end
        else error "B1 binary terminal action is neither Exit nor Fork"
    | (Const (name, _), [_]) =>
        if name = @{const_name Comma_Continuation_Landmine} then Stop 8
        else error "B1 unary terminal action is not Landmine"
    | (Const (name, _), []) =>
        if name = @{const_name Comma_Continuation_Invalid} then Invalid
        else error "B1 nullary terminal action is not Invalid"
    | _ => error "B1 candidate has an unknown terminal action")

  fun add_mdd_output output key columns =
    if key = MDD_False then columns
    else
      let
        fun insert [] = [(output, key)]
          | insert ((prior_output, prior_key) :: rest) =
              (case compare_output (output, prior_output) of
                LESS => (output, key) :: ((prior_output, prior_key) :: rest)
              | EQUAL =>
                  let val result = mdd_or (prior_key, key)
                  in (prior_output, result) :: rest end
              | GREATER =>
                  (prior_output, prior_key) :: insert rest)
      in insert columns end

  fun check_mdd_partition cardinality_of mdd_columns =
    let
      val _ = if null mdd_columns then
          error "B1 symbolic source has no terminal columns" else ()
      val keys = map #2 mdd_columns
      val key_cardinalities = map (fn key => (key, cardinality_of key)) keys
      val cardinality = fold (fn (_, count) => fn total => total + count)
        key_cardinalities 0
      val _ = if cardinality = clock_size then ()
        else error "B1 symbolic source table does not cover the clock"
      (* Check each new column against the accumulated union.  Canonical MDD
         conjunction makes this an exact disjointness test, while avoiding
         the quadratic all-pairs product. *)
      fun disjoint_union [] _ = ()
        | disjoint_union (key :: rest) union =
            if mdd_and (union, key) = MDD_False then
              disjoint_union rest (mdd_or (union, key))
            else error "B1 symbolic source columns overlap"
      val _ = disjoint_union keys MDD_False
    in (keys, key_cardinalities) end

  type artifact =
    {template_keys: mdd list list, occurrence_descriptors_term: term,
     normalized_sources_term: term,
     root_occurrence_indices_term: term,
     lift_descriptors: lift_descriptor list,
     lift_refs: lift_ref list list,
     lift_column_keys: mdd list list,
     stats: unit -> string}

  fun discover_template_sources lthy =
    let
      val started = Time.now ()
      val _ = Comma_Proof_Profile.report
        "B1 candidate stage=template source discovery status=started"
      val ctxt = Local_Theory.target_of lthy
      val root_representatives = representative_values ctxt
      val sources = map (fn representative =>
        @{term Comma_Entry} $ nat 1 $ nat 0 $ nat representative)
        root_representatives
      val (source_order, actions_by_source,
        source_action_batch_calls, source_action_batch_sources) =
        discover_template_source_order ctxt sources
      val _ = if length sources = 46 then ()
        else error "B1 candidate must retain all forty-six roots"
      val _ = Comma_Proof_Profile.report
        ("B1 candidate stage=template source discovery status=complete elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms started)
      val _ = Comma_Proof_Profile.report
        ("B1 candidate stage=template source discovery action_batches=" ^
          Int.toString source_action_batch_calls ^
          " action_sources=" ^ Int.toString source_action_batch_sources)
    in
      (sources, source_order, actions_by_source)
    end

  (* Data-only candidate fold; published records are untrusted. *)
  fun make lthy =
    let
      fun log_start name =
        (Comma_Proof_Profile.report
          ("B1 candidate stage=" ^ name ^ " status=started"); Time.now ())
      fun log_done name started =
        Comma_Proof_Profile.report
          ("B1 candidate stage=" ^ name ^ " status=complete elapsed_ms=" ^
            Comma_Proof_Profile.elapsed_ms started)

      val (sources, source_order, actions_by_source) = discover_template_sources lthy
      val root_numbers = fold_index (fn (root, source) => fn prior =>
        Termtab.update (source_base_term source, root) prior) sources Termtab.empty
      val _ = if Termtab.size root_numbers = length sources then ()
        else error "B1 root address table contains duplicates"
      (* Immutable canonical MDDs and slot scopes are memoized only for this
         fold, so repeated source/candidate work shares exact data results. *)
      val scope_cover_cache = Unsynchronized.ref MDDtab.empty
      val scope_cover_hits = Unsynchronized.ref 0
      val cardinality_cache = Unsynchronized.ref MDDtab.empty
      val cardinality_cache_hits = Unsynchronized.ref 0
      val cardinality_cache_misses = Unsynchronized.ref 0
      val slot_scope_cache = Unsynchronized.ref ScopeTab.empty
      val slot_scope_cache_hits = Unsynchronized.ref 0
      val slot_scope_cache_misses = Unsynchronized.ref 0
      val shift_cache = Unsynchronized.ref MDDShiftTab.empty
      val shift_cache_hits = Unsynchronized.ref 0
      val slot_lift_cache = Unsynchronized.ref SlotLiftTab.empty
      val slot_lift_cache_hits = Unsynchronized.ref 0
      val slot_lift_descriptors_rev = Unsynchronized.ref ([]: lift_descriptor list)
      val lift_geometry_by_id = Unsynchronized.ref
        (Inttab.empty: mdd list Inttab.table)
      val slot_lift_count = Unsynchronized.ref 0
      val retained_lift_columns = Unsynchronized.ref 0
      fun cached_cardinality key =
        (case MDDtab.lookup (!cardinality_cache) key of
          SOME count =>
            (cardinality_cache_hits := !cardinality_cache_hits + 1; count)
        | NONE =>
            let
              val count = mdd_cardinality key
              val _ = cardinality_cache_misses := !cardinality_cache_misses + 1
              val _ = cardinality_cache := MDDtab.update
                (key, count) (!cardinality_cache)
            in count end)
      fun cached_slot_scope period slot =
        let val key = (period, slot)
        in
          (case ScopeTab.lookup (!slot_scope_cache) key of
            SOME column =>
              (slot_scope_cache_hits := !slot_scope_cache_hits + 1; column)
          | NONE =>
              let
                val column = scope_column_key [key]
                val _ = slot_scope_cache_misses := !slot_scope_cache_misses + 1
                val _ = slot_scope_cache :=
                  ScopeTab.update (key, column) (!slot_scope_cache)
              in column end)
        end
      fun cached_scope_cover key =
        (case MDDtab.lookup (!scope_cover_cache) key of
          SOME scopes =>
            (scope_cover_hits := !scope_cover_hits + 1; scopes)
        | NONE =>
            let
              val scopes = maximal_scope_cover key
              val _ = scope_cover_cache :=
                MDDtab.update (key, scopes) (!scope_cover_cache)
            in scopes end)
      fun cached_translate_key shift key =
        let
          val normalized_shift = shift mod clock_size
          val cache_key = (key, normalized_shift)
        in
          (case MDDShiftTab.lookup (!shift_cache) cache_key of
            SOME translated =>
              (shift_cache_hits := !shift_cache_hits + 1; translated)
          | NONE =>
              let
                val translated = translate_mdd normalized_shift key
                val _ = shift_cache :=
                  MDDShiftTab.update (cache_key, translated) (!shift_cache)
              in translated end)
        end
      (* Keep first-seen CIDs in a scalar counter and cons the rows.  Repeated
         list length plus append made interning quadratic in the number of
         distinct templates; reverse once when the public artifact is built. *)
      val representatives_rev = Unsynchronized.ref ([]: representative list)
      val representative_count = Unsynchronized.ref 0
      val representative_index = Unsynchronized.ref MDDListTab.empty
      val representative_by_id = Unsynchronized.ref (Inttab.empty: representative Inttab.table)
      val occurrences = Unsynchronized.ref ([]: occurrence list)
      val occurrence_by_source = Unsynchronized.ref
        (Termtab.empty: occurrence Termtab.table)
      val translation_checks = Unsynchronized.ref 0
      val template_reuse_hits = Unsynchronized.ref 0
      fun representative_for cid =
        (case Inttab.lookup (!representative_by_id) cid of
          SOME representative => representative
        | NONE => error "B1 occurrence references an unpublished template geometry")
      fun cached_slot_lift period slot template_cid net_shift =
        let
          val normalized_shift = net_shift mod clock_size
          val key = (period, slot, template_cid, normalized_shift)
        in
          (case SlotLiftTab.lookup (!slot_lift_cache) key of
            SOME ({lift_cid, geometry}: lift_entry) =>
              (slot_lift_cache_hits := !slot_lift_cache_hits + 1;
               (lift_cid, geometry))
          | NONE =>
              let
                val representative = representative_for template_cid
                val geometry = lift_template_slot_with cached_slot_scope
                  cached_translate_key period slot normalized_shift
                  (#keys representative)
                val lift_cid = !slot_lift_count
                val entry = {lift_cid = lift_cid, geometry = geometry}: lift_entry
                val descriptor = {period = period, slot = slot,
                  template_cid = template_cid, net_shift = normalized_shift}:
                  lift_descriptor
                val _ = slot_lift_cache :=
                  SlotLiftTab.update (key, entry) (!slot_lift_cache)
                val _ = slot_lift_descriptors_rev :=
                  descriptor :: !slot_lift_descriptors_rev
                val _ = lift_geometry_by_id :=
                  Inttab.update (lift_cid, geometry) (!lift_geometry_by_id)
                val _ = slot_lift_count := lift_cid + 1
                val _ = retained_lift_columns :=
                  !retained_lift_columns + length geometry
              in (lift_cid, geometry) end)
        end
      fun occurrence_for source =
        (case Termtab.lookup (!occurrence_by_source) source of
          SOME occurrence => occurrence
        | NONE => error "B1 Goto child occurrence was not published before its parent")
      val occurrence_index_by_source = fold_index (fn (index, source) => fn prior =>
        Termtab.update (source, index) prior) source_order Termtab.empty
      fun publish_source source mdd_columns source_cardinalities pending_refs_rev =
        let
          val source_outputs = map #1 mdd_columns
          val source_keys = map #2 mdd_columns
          val (shift, checked, canonical_keys, column_keys) =
            canonical_partition_rebase_with_cardinalities cached_scope_cover
              cached_translate_key source_keys source_cardinalities
          val _ = translation_checks := !translation_checks + checked
          val matched = MDDListTab.lookup (!representative_index) canonical_keys
          val template =
            (case matched of
              SOME representative =>
                (template_reuse_hits := !template_reuse_hits + 1; representative)
            | NONE =>
                let
                  val cid = !representative_count
                  val item = {template_cid = cid, keys = canonical_keys}: representative
                  val _ = representatives_rev := item :: !representatives_rev
                  val _ = representative_count := cid + 1
                  val _ = representative_index :=
                    MDDListTab.update (canonical_keys, item) (!representative_index)
                  val _ = representative_by_id :=
                    Inttab.update (cid, item) (!representative_by_id)
                in item end)
          val binding = binding_outputs (#keys template) column_keys source_outputs
          val root = Termtab.lookup root_numbers source
          val binding_output_indices = fold_index (fn (index, output) => fn prior =>
            let val key = output_term output
            in if Termtab.defined prior key then
                 error "B1 online fold output binding is not label-unique"
               else Termtab.update (key, index) prior end)
            binding Termtab.empty
          fun parent_column output =
            (case Termtab.lookup binding_output_indices (output_term output) of
              SOME index => index
            | NONE => error "B1 online fold ref has no canonical parent output column")
          fun finish_ref (Pending_Terminal (slot, output, key)) =
                if key = MDD_False then
                  error "B1 terminal online fold ref unexpectedly has empty support"
                else Terminal_Ref (slot, parent_column output)
            | finish_ref (Pending_Goto (slot, child_index, lift_cid)) =
                Goto_Ref (slot, child_index, lift_cid)
          val lift_refs = map finish_ref (rev pending_refs_rev)
          val occurrence = {root = root, source = source,
            template_cid = #template_cid template, return_shift = shift,
            binding = binding, lift_refs = lift_refs}: occurrence
          val _ = occurrences := occurrence :: !occurrences
          val _ = occurrence_by_source :=
            Termtab.update (source, occurrence) (!occurrence_by_source)
        in
          occurrence
        end
      val fold_started = log_start "symbolic source fold and template interning"
      val completed = Unsynchronized.ref 0
      val source_order_count = length source_order
      val source_fold_started = Time.now ()
      fun build_source source =
        let
          val actions = (case Termtab.lookup actions_by_source source of
              SOME values => values
            | NONE => error "B1 symbolic fold lost discovered slot actions")
          val period = length actions
          val _ = if period > 0 andalso clock_size mod period = 0 then ()
            else error "B1 source slot period is not an admitted CRT divisor"
          fun compose_slot (slot, action) (prior_columns, prior_refs) =
            (case goto_child action of
              SOME (raw_child, shift) =>
                let
                  val child = source_base_term raw_child
                  val occurrence = occurrence_for child
                  val child_index = (case Termtab.lookup occurrence_index_by_source child of
                    SOME index => index
                  | NONE => error "B1 Goto child has no online fold source index")
                  val parent_index = (case Termtab.lookup occurrence_index_by_source source of
                    SOME index => index
                  | NONE => error "B1 online fold parent has no source index")
                  val _ = if child_index < parent_index then ()
                    else error "B1 online fold child does not precede its parent"
                  val net_shift = (shift + #return_shift occurrence) mod clock_size
                  val (lift_cid, geometry) = cached_slot_lift period slot
                    (#template_cid occurrence) net_shift
                  val _ = if length geometry = length (#binding occurrence) then ()
                    else error "B1 child geometry and occurrence binding lost alignment"
                  fun add_child_outputs [] [] accumulated = accumulated
                    | add_child_outputs (key :: keys) (output :: outputs) accumulated =
                        add_child_outputs keys outputs (add_mdd_output output key accumulated)
                    | add_child_outputs _ _ _ =
                        error "B1 child geometry and binding lengths differ"
                  val columns = add_child_outputs geometry
                    (#binding occurrence) prior_columns
                in
                  (columns, Pending_Goto (slot, child_index, lift_cid) :: prior_refs)
                end
            | NONE =>
                let
                  val slot_key = cached_slot_scope period slot
                  val output = terminal_output action
                  val columns = add_mdd_output output slot_key prior_columns
                in
                  (columns,
                   Pending_Terminal (slot, output, slot_key) :: prior_refs)
                end)
          val (raw_columns, pending_refs_rev) = fold_index
            (fn (slot, action) => fn prior => compose_slot (slot, action) prior)
            actions ([], [])
          val (_, source_cardinalities) =
            check_mdd_partition cached_cardinality raw_columns
          val _ = publish_source source raw_columns source_cardinalities pending_refs_rev
          val _ = completed := !completed + 1
          val count = !completed
          val _ = if count mod 32 = 0 orelse count = source_order_count then
            Comma_Proof_Profile.report
              ("B1 candidate stage=online_template_fold progress=" ^
                Int.toString count ^ " sources elapsed_ms=" ^
                Comma_Proof_Profile.elapsed_ms source_fold_started)
            else ()
        in () end
      val _ = List.app build_source source_order
      val source_count = !completed
      val _ = log_done "symbolic source fold and template interning" fold_started
      val representative_data = rev (!representatives_rev)
      val occurrence_data = rev (!occurrences)
      val normalized_sources = map #source occurrence_data
      val _ = if normalized_sources = source_order then ()
        else error "B1 candidate occurrence order differs from its normalized source map"
      val _ = if source_count = length source_order then ()
        else error "B1 template publisher lost a discovered source"
      val _ = if length occurrence_data = source_count then ()
        else error "B1 template publisher did not retain every source occurrence"
      val root_occurrence_pairs = map_filter (fn (index, ({root, ...}: occurrence)) =>
        Option.map (fn root_index => (root_index, index)) root)
        (map_index I occurrence_data)
        |> sort (prod_ord int_ord int_ord)
      val _ = if map #1 root_occurrence_pairs = (0 upto 45) then ()
        else error "B1 template publisher lost or duplicated a root occurrence"
      val _ = List.app (fn (root_index, occurrence_index) =>
        if source_base_term (#source (nth occurrence_data occurrence_index)) =
            source_base_term (nth sources root_index) then ()
        else error "B1 root occurrence index names a different source")
        root_occurrence_pairs
      val nonroot_count = source_count - length root_occurrence_pairs
      val _ = if map #template_cid representative_data =
          (0 upto (length representative_data - 1)) then ()
        else error "B1 candidate template list is not indexed by its template IDs"
      val _ = List.app (fn item =>
        if #return_shift item < clock_size then ()
        else error "B1 template return shift escaped the 924 clock") occurrence_data

      val template_column_count = fold (fn
        ({keys, ...}: representative) => fn total => total + length keys)
        representative_data 0
      val all_binding_entries = fold (fn
        ({binding, ...}: occurrence) => fn total => total + length binding)
        occurrence_data 0
      val root_binding_entries = fold (fn
        ({root, binding, ...}: occurrence) => fn total =>
          if is_some root then total + length binding else total) occurrence_data 0
      val source_count_stat = source_count
      val root_count_stat = Termtab.size root_numbers
      val representative_count_stat = !representative_count
      val template_column_count_stat = template_column_count
      val root_binding_entries_stat = root_binding_entries
      val all_binding_entries_stat = all_binding_entries
      val translation_checks_stat = !translation_checks
      val scope_cover_hits_stat = !scope_cover_hits
      val scope_cover_entries_stat = MDDtab.size (!scope_cover_cache)
      val cardinality_cache_hits_stat = !cardinality_cache_hits
      val cardinality_cache_misses_stat = !cardinality_cache_misses
      val slot_scope_cache_hits_stat = !slot_scope_cache_hits
      val slot_scope_cache_misses_stat = !slot_scope_cache_misses
      val shift_cache_hits_stat = !shift_cache_hits
      val shift_cache_entries_stat = MDDShiftTab.size (!shift_cache)
      val slot_lift_cache_hits_stat = !slot_lift_cache_hits
      val slot_lift_cache_entries_stat = SlotLiftTab.size (!slot_lift_cache)
      val lift_descriptors = rev (!slot_lift_descriptors_rev)
      val lift_column_keys = map (fn lift_cid =>
        (case Inttab.lookup (!lift_geometry_by_id) lift_cid of
          SOME keys => keys
        | NONE => error "B1 lift output table lost a descriptor CID"))
        (0 upto (!slot_lift_count - 1))
      val retained_lift_columns_stat = !retained_lift_columns
      val template_reuse_hits_stat = !template_reuse_hits
      val template_keys = map #keys representative_data
      val descriptorT = HOLogic.mk_prodT (natT,
        HOLogic.mk_prodT (natT, HOLogic.listT resultT))
      val occurrence_descriptors_term = HOLogic.mk_list descriptorT
        (map (fn ({template_cid, return_shift, binding, ...}: occurrence) =>
          HOLogic.mk_prod (nat template_cid,
            HOLogic.mk_prod (nat return_shift,
              HOLogic.mk_list resultT (map output_term binding)))) occurrence_data)
      val normalized_sources_term =
        HOLogic.mk_list @{typ comma_finite_position} normalized_sources
      val root_occurrence_indices_term = HOLogic.mk_list natT
        (map (nat o #2) root_occurrence_pairs)
      val lift_refs = map #lift_refs occurrence_data
      val compact_lift_ref_count =
        fold (fn refs => fn count => count + length refs) lift_refs 0
      fun stats () =
        "b1_template_sources=" ^ Int.toString source_count_stat ^
        " b1_template_roots=" ^ Int.toString root_count_stat ^
        " b1_template_source_occurrence_bindings=" ^
          Int.toString (length occurrence_data) ^
        " b1_template_nonroot_bindings=" ^ Int.toString nonroot_count ^
        " b1_template_representatives=" ^ Int.toString representative_count_stat ^
        " b1_template_reuse_hits=" ^ Int.toString template_reuse_hits_stat ^
        " b1_template_columns=" ^ Int.toString template_column_count_stat ^
        " b1_template_root_binding_entries=" ^ Int.toString root_binding_entries_stat ^
        " b1_template_all_binding_entries=" ^ Int.toString all_binding_entries_stat ^
        " b1_template_translation_checks=" ^ Int.toString translation_checks_stat ^
        " b1_template_scope_cover_cache_hits=" ^ Int.toString scope_cover_hits_stat ^
        " b1_template_scope_cover_cache_entries=" ^
          Int.toString scope_cover_entries_stat ^
        " b1_template_cardinality_cache_hits=" ^
          Int.toString cardinality_cache_hits_stat ^
        " b1_template_cardinality_cache_misses=" ^
          Int.toString cardinality_cache_misses_stat ^
        " b1_template_slot_scope_cache_hits=" ^
          Int.toString slot_scope_cache_hits_stat ^
        " b1_template_slot_scope_cache_misses=" ^
          Int.toString slot_scope_cache_misses_stat ^
        " b1_template_shift_cache_hits=" ^ Int.toString shift_cache_hits_stat ^
        " b1_template_shift_cache_entries=" ^
          Int.toString shift_cache_entries_stat ^
        " b1_template_slot_lift_cache_hits=" ^ Int.toString slot_lift_cache_hits_stat ^
        " b1_template_slot_lift_cache_entries=" ^
          Int.toString slot_lift_cache_entries_stat ^
        " b1_template_unique_lifts=" ^ Int.toString (!slot_lift_count) ^
        " b1_template_reused_lifts=" ^ Int.toString slot_lift_cache_hits_stat ^
        " b1_template_retained_lift_columns=" ^
          Int.toString retained_lift_columns_stat ^
        " b1_template_compact_slot_refs=" ^
          Int.toString compact_lift_ref_count
    in
      ({template_keys = template_keys,
        occurrence_descriptors_term = occurrence_descriptors_term,
        normalized_sources_term = normalized_sources_term,
        root_occurrence_indices_term = root_occurrence_indices_term,
        lift_descriptors = lift_descriptors,
        lift_refs = lift_refs,
        lift_column_keys = lift_column_keys,
        stats = stats}: artifact, lthy)
    end

end
