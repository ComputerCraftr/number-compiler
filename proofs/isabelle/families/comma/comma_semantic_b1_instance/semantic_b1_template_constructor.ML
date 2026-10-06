(* Candidate-only B1 quotienting over source-level CRT tables.  One generated
   packet-slot evaluator discovers normalized sources by sector layers and its
   retained slot actions feed a bottom-up symbolic CRT/MDD fold.  The result is
   candidate data only and has no theorem authority.  Physical graph CIDs and
   per-source row theorems are outside this production path. *)
structure Comma_Semantic_B1_Template_Constructor =
struct
  datatype output = Live of int | Stop of int | Invalid
  datatype mdd = MDD_False | MDD_True | MDD_Node of int * mdd list
  datatype lift_ref = Terminal_Ref of int * int
    | Goto_Ref of int * int * int
  datatype pending_lift_ref = Pending_Terminal of int * output * mdd
    | Pending_Goto of int * int * int
  type lift_descriptor =
    {period: int, slot: int, template_cid: int, net_shift: int}
  type lift_entry = {lift_cid: int, geometry: mdd list}
  type scope = int * int
  type cube = int list list
  type representative =
    {template_cid: int, keys: mdd list}
  type occurrence =
    {root: int option, source: term, template_cid: int, return_shift: int,
     binding: output list, lift_refs: lift_ref list}

  val clock_size = 924
  val natT = @{typ nat}
  val resultT = @{typ comma_semantic_b1_result}
  val columnT = @{typ comma_crt_column}
  val action_listT = @{typ "comma_source_continuation_action list"}

  (* Compile the direct packet-slot evaluator once and reuse its results for
     discovery and the symbolic table fold. *)
  val slot_actions_computation =
    @{computation "Code_Evaluation.term"
      terms:
        "Code_Evaluation.term_of :: comma_source_continuation_action list \<Rightarrow> Code_Evaluation.term"
        "numeral :: num \<Rightarrow> nat"
        "nat_of_num :: num \<Rightarrow> nat"
        "one_nat_inst.one_nat :: nat"
        "comma_semantic_b1_source_slot_actions :: comma_finite_position \<Rightarrow> comma_source_continuation_action list"
      datatypes: nat num comma_finite_position comma_source_continuation_action
        "comma_source_continuation_action list"}
      (fn post => post o the)

  fun nat n = HOLogic.mk_number natT n

  fun dest_nat term =
    let val (typ, number) = HOLogic.dest_number term
    in if typ = natT andalso number >= 0 then number
      else error "B1 candidate contains a non-natural scope coordinate" end

  fun gcd a b =
    if b = 0 then a else gcd b (a mod b)

  fun extended_gcd a b =
    if b = 0 then (a, 1, 0)
    else
      let val (g, x, y) = extended_gcd b (a mod b)
      in (g, y, x - (a div b) * y) end

  fun scope_admitted (period, residue) =
    period > 0 andalso clock_size mod period = 0 andalso
      0 <= residue andalso residue < period

  (* The intersection of two cyclotomic cylinders is one cylinder or empty. *)
  fun scope_meet (p, a) (q, b) =
    if not (scope_admitted (p, a) andalso scope_admitted (q, b)) then
      error "B1 template received a non-admitted phase scope"
    else
      let
        val g = gcd p q
      in
        if (b - a) mod g <> 0 then NONE
        else
          let
            val q' = q div g
            val (_, inverse, _) = extended_gcd (p div g) q'
            val step = if q' = 1 then 0
              else (((b - a) div g * inverse) mod q' + q') mod q'
            val period = p * q'
            val residue = (a + p * step) mod period
            val result = (period, residue)
            val _ = if scope_admitted result then ()
              else error "B1 CRT intersection escaped the 924 clock"
          in SOME result end
      end

  fun compare_scope ((p, a): scope, (q, b): scope) =
    (case int_ord (p, q) of EQUAL => int_ord (a, b) | order => order)

  fun compare_output (left, right) =
    (case (left, right) of
      (Invalid, Invalid) => EQUAL
    | (Invalid, _) => LESS
    | (_, Invalid) => GREATER
    | (Live a, Live b) => int_ord (a, b)
    | (Live _, Stop _) => LESS
    | (Stop _, Live _) => GREATER
    | (Stop a, Stop b) => int_ord (a, b))

  (* A congruence scope is represented over the valid CRT characters
     C4 x C3 x C7 x C11; no padded coordinates or invalid branches occur. *)
  val character_periods = [4, 3, 7, 11]
  val clock_domains = character_periods
  val clock_valid = map (fn period => 0 upto (period - 1)) character_periods

  fun member_int value values = exists (fn other => value = other) values

  fun cube_subset (left: cube, right: cube) =
    ListPair.allEq (fn (a, b) => forall (fn value => member_int value b) a)
      (left, right)

  fun minimal_cubes (cubes: cube list) =
    let val unique = distinct (op =) cubes
    in filter (fn cube => not (exists (fn other =>
      cube <> other andalso cube_subset (cube, other)) unique)) unique end

  fun scope_cube ((period, residue): scope): cube =
    let
      val factor4 = if period mod 4 = 0 then 4
        else if period mod 2 = 0 then 2 else 1
      val factors = [factor4,
        if period mod 3 = 0 then 3 else 1,
        if period mod 7 = 0 then 7 else 1,
        if period mod 11 = 0 then 11 else 1]
      fun coordinate (factor, valid) =
        if factor = 1 then valid
        else filter (fn value => value mod factor = residue mod factor) valid
      fun build_masks ([], []) = []
        | build_masks (factor :: factors, valid :: valids) =
            coordinate (factor, valid) :: build_masks (factors, valids)
        | build_masks _ = error "B1 MDD clock dimensions are inconsistent"
    in build_masks (factors, clock_valid) end

  fun compare_mdd (MDD_False, MDD_False) = EQUAL
    | compare_mdd (MDD_False, _) = LESS
    | compare_mdd (_, MDD_False) = GREATER
    | compare_mdd (MDD_True, MDD_True) = EQUAL
    | compare_mdd (MDD_True, _) = LESS
    | compare_mdd (_, MDD_True) = GREATER
    | compare_mdd (MDD_Node (left_level, left_children),
        MDD_Node (right_level, right_children)) =
        (case int_ord (left_level, right_level) of
          EQUAL => compare_mdd_lists (left_children, right_children)
        | order => order)
  and compare_mdd_lists ([], []) = EQUAL
    | compare_mdd_lists ([], _ :: _) = LESS
    | compare_mdd_lists (_ :: _, []) = GREATER
    | compare_mdd_lists (left :: lefts, right :: rights) =
        (case compare_mdd (left, right) of
          EQUAL => compare_mdd_lists (lefts, rights)
        | order => order)

  fun equal_children [] = true
    | equal_children (first :: rest) = forall (fn item => item = first) rest

  fun scope_column_key (scopes: scope list) =
    let
      val cubes = minimal_cubes (map scope_cube scopes)
      fun build level active =
        if null active then MDD_False
        else if level = 4 then MDD_True
        else
          let
            val domain = nth clock_domains level
            fun cofactor value =
              active
              |> filter (fn (mask :: _) => member_int value mask
                | _ => error "B1 CRT MDD encountered a malformed cube")
              |> map (fn (_ :: tail) => tail
                | [] => error "B1 CRT MDD encountered an empty cube")
              |> minimal_cubes
            val children = map (fn value => build (level + 1) (cofactor value))
              (0 upto (domain - 1))
          in
            if equal_children children then hd children
            else MDD_Node (level, children)
          end
    in build 0 cubes end

  fun compare_mdd_lists_key (left, right) = compare_mdd_lists (left, right)

  structure MDDtab = Table(type key = mdd val ord = compare_mdd)
  structure MDDListTab = Table(type key = mdd list val ord = compare_mdd_lists_key)
  structure MDDShiftTab = Table(type key = mdd * int val ord =
    prod_ord compare_mdd int_ord)

  fun compare_slot_lift_key ((p, slot, cid, shift), (q, other_slot, other_cid, other_shift)) =
    (case int_ord (p, q) of EQUAL =>
      (case int_ord (slot, other_slot) of EQUAL =>
        (case int_ord (cid, other_cid) of EQUAL => int_ord (shift, other_shift)
        | order => order)
      | order => order)
    | order => order)

  structure SlotLiftTab = Table(type key = int * int * int * int
    val ord = compare_slot_lift_key)

  fun lcm left right = left div gcd left right * right

  fun mdd_cofactor key level value =
    (case key of
      MDD_Node (node_level, children) =>
        if node_level = level then nth children value
        else if node_level > level then key
        else error "B1 MDD cofactor moved behind its current level"
    | _ => key)

  fun mdd_node level children =
    if equal_children children then hd children else MDD_Node (level, children)

  fun mdd_and (MDD_False, _) = MDD_False
    | mdd_and (_, MDD_False) = MDD_False
    | mdd_and (MDD_True, right) = right
    | mdd_and (left, MDD_True) = left
    | mdd_and (left as MDD_Node (left_level, _),
        right as MDD_Node (right_level, _)) =
        let
          val level = Int.min (left_level, right_level)
          val domain = nth clock_domains level
          val children = map (fn value => mdd_and
            (mdd_cofactor left level value, mdd_cofactor right level value))
            (0 upto (domain - 1))
        in mdd_node level children end

  fun mdd_or (MDD_True, _) = MDD_True
    | mdd_or (_, MDD_True) = MDD_True
    | mdd_or (MDD_False, right) = right
    | mdd_or (left, MDD_False) = left
    | mdd_or (left as MDD_Node (left_level, _),
        right as MDD_Node (right_level, _)) =
        let
          val level = Int.min (left_level, right_level)
          val domain = nth clock_domains level
          val children = map (fn value => mdd_or
            (mdd_cofactor left level value, mdd_cofactor right level value))
            (0 upto (domain - 1))
        in mdd_node level children end

  fun translate_mdd shift key =
    let
      fun translate MDD_False = MDD_False
        | translate MDD_True = MDD_True
        | translate (MDD_Node (level, children)) =
            let
              val period = nth character_periods level
              val domain = nth clock_domains level
              val delta = shift mod period
              val translated_children = map translate children
              fun child value =
                if value >= period then MDD_False
                else nth translated_children ((value - delta + period) mod period)
            in mdd_node level (map child (0 upto (domain - 1))) end
    in translate key end

  fun valid_character_product first last =
    if first >= last then 1
    else nth character_periods first * valid_character_product (first + 1) last

  fun mdd_cardinality key =
    let
      fun count _ MDD_False = 0
        | count level MDD_True = valid_character_product level 4
        | count level (MDD_Node (node_level, children)) =
            if node_level < level then
              error "B1 MDD cardinality moved behind its current level"
            else
              let
                val skipped = valid_character_product level node_level
                val child_count = fold (fn (value, child) => fn total =>
                  if value < nth character_periods node_level
                  then total + count (node_level + 1) child else total)
                  (map_index I children) 0
              in skipped * child_count end
    in count 0 key end

  fun cofactor_intersection key level values =
    fold (fn value => fn prior =>
      mdd_and (prior, mdd_cofactor key level value)) values MDD_True

  type component_choice = {factor: int, residue: int, values: int list}

  val component_choices =
    let
      val r4 =
        [{factor = 1, residue = 0, values = [0, 1, 2, 3]},
         {factor = 2, residue = 0, values = [0, 2]},
         {factor = 2, residue = 1, values = [1, 3]}] @
        map (fn value => {factor = 4, residue = value, values = [value]})
          (0 upto 3)
      fun prime modulus =
        {factor = 1, residue = 0, values = 0 upto (modulus - 1)} ::
        map (fn value => {factor = modulus, residue = value, values = [value]})
          (0 upto (modulus - 1))
    in [r4, prime 3, prime 7, prime 11] end

  fun choices_scope choices =
    let
      fun combine ({factor, residue, ...}: component_choice) prior =
        (case scope_meet prior (factor, residue) of
          SOME scope => scope
        | NONE => error "B1 component choices are not CRT-compatible")
    in fold combine choices (1, 0) end

  (* Enumerate maximal congruence cylinders from the reduced MDD itself.
     This canonicalizes split and overlapping scope descriptions alike.  The
     finite factor-mask lattice has 7 x 4 x 8 x 12 admissible coordinate
     choices at its widest; recursive cofactor intersections prune prefixes
     that cannot be contained in the column.  It never enumerates clock rows. *)
  fun maximal_scope_cover key =
    let
      fun implicants level suffix chosen =
        if suffix = MDD_False then []
        else if level = 4 then
          if suffix = MDD_True then [choices_scope (rev chosen)] else []
        else
          maps (fn (choice: component_choice) =>
            let val next = cofactor_intersection suffix level (#values choice)
            in implicants (level + 1) next (choice :: chosen) end)
            (nth component_choices level)
      val candidates = distinct (op =) (implicants 0 key [])
      val candidate_index = Inttab.make
        (map (fn (period, residue) =>
          (period * clock_size + residue, true)) candidates)
      fun proper_divisors value =
        let
          fun search divisor acc =
            if divisor * divisor > value then acc
            else if value mod divisor <> 0 then search (divisor + 1) acc
            else
              let
                val quotient = value div divisor
                val first = if divisor < value then divisor :: acc else acc
                val second = if quotient < value andalso quotient <> divisor
                  then quotient :: first else first
              in search (divisor + 1) second end
        in sort_distinct int_ord (search 1 []) end
      fun broader_exists (period, residue) =
        exists (fn divisor =>
          Inttab.defined candidate_index
            (divisor * clock_size + residue mod divisor))
          (proper_divisors period)
    in filter (not o broader_exists) candidates end

  (* A common rebase is occurrence data.  Its candidate anchors come from the
     representation-independent maximal cylinders above, not from whichever
     raw scope split happened to construct a column. *)
  fun partition_alignment_shifts scope_cover (keys: mdd list) global_period =
    let
      val cardinalities = map (fn key => (mdd_cardinality key, key)) keys
      val rarest = fold (fn (count, _) => fn best => if count < best then count else best)
        cardinalities clock_size
      val rare_keys = map #2 (filter (fn (count, _) => count = rarest) cardinalities)
        |> sort_distinct compare_mdd
      val scopes = maps scope_cover rare_keys
        |> sort_distinct compare_scope
      fun larger_period (period, _) best = if period > best then period else best
      val anchor_period = fold larger_period scopes 1
      val anchors = map #2 (filter (fn (period, _) => period = anchor_period) scopes)
        |> sort_distinct int_ord
      fun candidates residue =
        map (fn multiple => (anchor_period - residue) mod anchor_period +
          multiple * anchor_period)
          (0 upto (global_period div anchor_period - 1))
      val shifts = maps candidates anchors
        |> map (fn shift => shift mod global_period)
        |> sort_distinct int_ord
    in if null shifts then [0] else shifts end

  fun mdd_support_period keys =
    let
      fun levels MDD_False = []
        | levels MDD_True = []
        | levels (MDD_Node (level, children)) =
            level :: maps levels children
      val used = maps levels keys |> sort_distinct int_ord
    in fold (fn level => fn period =>
      lcm period (nth character_periods level)) used 1 end

  fun canonical_partition_rebase scope_cover translate_key (source_keys: mdd list) =
    if source_keys = [MDD_True] then (0, 1, source_keys, source_keys)
    else
      let
        val global_period = mdd_support_period source_keys
        val candidates = partition_alignment_shifts scope_cover source_keys global_period
        fun choose [] NONE = error "B1 canonical rebase has no anchor candidate"
          | choose [] (SOME (shift, key, column_keys)) = (shift, key, column_keys)
          | choose (shift :: rest) prior =
              let
                val column_keys = map (translate_key shift) source_keys
                val key = sort compare_mdd column_keys
                val better =
                  (case prior of
                    NONE => true
                  | SOME (_, best_key, _) =>
                      compare_mdd_lists_key (key, best_key) = LESS)
                val next = if better then SOME (shift, key, column_keys) else prior
              in choose rest next end
        val (shift, keys, column_keys) = choose candidates NONE
      in (shift, length candidates, keys, column_keys) end

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

  fun lift_template_slot_with translate_key period slot net_shift template_keys =
    let
      val slot_key = scope_column_key [(period, slot)]
      val negative_shift = (clock_size - (net_shift mod clock_size)) mod clock_size
    in map (fn key => mdd_and (slot_key, translate_key negative_shift key))
      template_keys end

  fun lift_template_slot period slot net_shift template_keys =
    lift_template_slot_with translate_mdd period slot net_shift template_keys

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

  fun source_action_terms ctxt source =
    let
      val action_list = @{term comma_semantic_b1_source_slot_actions} $ source
      val term_of_actions = Const (@{const_name Code_Evaluation.term_of},
        action_listT --> @{typ Code_Evaluation.term}) $ action_list
      val value = slot_actions_computation ctxt term_of_actions
    in HOLogic.dest_list value end

  fun goto_child action =
    (case strip_comb action of
      (Const (name, _), [child, shift]) =>
        if name = @{const_name Comma_Continuation_Goto}
        then SOME (child, dest_nat shift) else NONE
    | _ => NONE)

  fun action_goto_child action = Option.map #1 (goto_child action)

  (* Template discovery and its data fold share this nine-layer scheduler. *)
  fun discover_source_order roots children_of =
    let
      val visited = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
      val layers = Array.array (10, []: term list)
      fun schedule raw_source =
        let
          val source = source_base_term raw_source
          val sector = source_sector source
          val _ = if 1 <= sector andalso sector <= 9 then ()
            else error "B1 source discovery escaped sectors 1 through 9"
        in
          if Termtab.defined (!visited) source then ()
          else
            (visited := Termtab.update (source, ()) (!visited);
             Array.update (layers, sector, source :: Array.sub (layers, sector)))
        end
      val _ = List.app schedule roots
      fun visit (sector, order) =
        if sector = 10 then order
        else
          let
            val current = sort (fn (left, right) =>
              int_ord (source_order_key left, source_order_key right))
              (Array.sub (layers, sector))
            fun discover_from source =
              let
                fun add child =
                  let
                    val normalized = source_base_term child
                    val next_sector = source_sector normalized
                    val _ = if sector < next_sector andalso next_sector <= 9 then ()
                      else error "B1 Goto source violates strict sector progress"
                  in schedule normalized end
              in List.app add (children_of source) end
            val _ = List.app discover_from current
          in visit (sector + 1, current @ order) end
      val ordered = visit (1, [])
      val _ = if length ordered = Termtab.size (!visited) then ()
        else error "B1 source-order traversal lost a visited source"
    in ordered end

  fun discover_template_source_order ctxt roots =
    let
      val actions_by_source =
        Unsynchronized.ref (Termtab.empty: term list Termtab.table)
      fun actions_of source =
        (case Termtab.lookup (!actions_by_source) source of
          SOME actions => actions
        | NONE =>
            let
              val actions = source_action_terms ctxt source
              val _ = actions_by_source :=
                Termtab.update (source, actions) (!actions_by_source)
            in actions end)
      val ordered = discover_source_order roots
        (fn source => map_filter action_goto_child (actions_of source))
      val _ = if Termtab.size (!actions_by_source) = length ordered then ()
        else error "B1 template traversal did not retain each packet-action list"
    in (ordered, !actions_by_source) end

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
              | EQUAL => (prior_output, mdd_or (prior_key, key)) :: rest
              | GREATER => (prior_output, prior_key) :: insert rest)
      in insert columns end

  fun check_mdd_partition mdd_columns =
    let
      val _ = if null mdd_columns then
          error "B1 symbolic source has no terminal columns" else ()
      val keys = map #2 mdd_columns
      val cardinality = fold (fn key => fn total => total + mdd_cardinality key) keys 0
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
    in keys end

  type artifact =
    {template_keys: mdd list list, occurrence_descriptors_term: term,
     normalized_sources_term: term,
     root_occurrence_indices_term: term,
     lift_descriptors: lift_descriptor list,
     lift_refs: lift_ref list list,
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
      val (source_order, actions_by_source) =
        discover_template_source_order ctxt sources
      val _ = if length sources = 46 then ()
        else error "B1 candidate must retain all forty-six roots"
      val _ = Comma_Proof_Profile.report
        ("B1 candidate stage=template source discovery status=complete elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms started)
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
      val scope_cover_cache = Unsynchronized.ref MDDtab.empty
      val scope_cover_hits = Unsynchronized.ref 0
      val shift_cache = Unsynchronized.ref MDDShiftTab.empty
      val shift_cache_hits = Unsynchronized.ref 0
      val slot_lift_cache = Unsynchronized.ref SlotLiftTab.empty
      val slot_lift_cache_hits = Unsynchronized.ref 0
      val slot_lift_descriptors_rev = Unsynchronized.ref ([]: lift_descriptor list)
      val slot_lift_count = Unsynchronized.ref 0
      val retained_lift_columns = Unsynchronized.ref 0
      val expanded_child_ref_equivalent = Unsynchronized.ref 0
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
                val geometry = lift_template_slot_with cached_translate_key
                  period slot normalized_shift (#keys representative)
                val lift_cid = !slot_lift_count
                val entry = {lift_cid = lift_cid, geometry = geometry}: lift_entry
                val descriptor = {period = period, slot = slot,
                  template_cid = template_cid, net_shift = normalized_shift}:
                  lift_descriptor
                val _ = slot_lift_cache :=
                  SlotLiftTab.update (key, entry) (!slot_lift_cache)
                val _ = slot_lift_descriptors_rev :=
                  descriptor :: !slot_lift_descriptors_rev
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
      fun publish_source source mdd_columns pending_refs_rev =
        let
          val source_outputs = map #1 mdd_columns
          val source_keys = map #2 mdd_columns
          val (shift, checked, canonical_keys, column_keys) =
            canonical_partition_rebase cached_scope_cover cached_translate_key
              source_keys
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
            | NONE => error "B1 online fold piece has no canonical parent output column")
          fun finish_ref (Pending_Terminal (slot, output, key)) =
                if key = MDD_False then
                  error "B1 terminal online fold piece unexpectedly has empty support"
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
                  fun add_child_outputs [] [] columns = columns
                    | add_child_outputs (key :: keys) (output :: outputs) columns =
                        add_child_outputs keys outputs
                          (add_mdd_output output key columns)
                    | add_child_outputs _ _ _ =
                        error "B1 child geometry and binding lengths differ"
                  val columns = add_child_outputs geometry (#binding occurrence)
                    prior_columns
                  val _ = expanded_child_ref_equivalent :=
                    !expanded_child_ref_equivalent + length geometry
                in (columns, Pending_Goto (slot, child_index, lift_cid) :: prior_refs) end
            | NONE =>
                let
                  val slot_key = scope_column_key [(period, slot)]
                  val output = terminal_output action
                in (add_mdd_output output slot_key prior_columns,
                    Pending_Terminal (slot, output, slot_key) :: prior_refs) end)
          val (raw_columns, pending_refs_rev) = fold_index
            (fn (slot, action) => fn prior => compose_slot (slot, action) prior)
            actions ([], [])
          val _ = check_mdd_partition raw_columns
          val _ = publish_source source raw_columns pending_refs_rev
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
      val shift_cache_hits_stat = !shift_cache_hits
      val shift_cache_entries_stat = MDDShiftTab.size (!shift_cache)
      val slot_lift_cache_hits_stat = !slot_lift_cache_hits
      val slot_lift_cache_entries_stat = SlotLiftTab.size (!slot_lift_cache)
      val lift_descriptors = rev (!slot_lift_descriptors_rev)
      val retained_lift_columns_stat = !retained_lift_columns
      val expanded_child_ref_equivalent_stat = !expanded_child_ref_equivalent
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
          Int.toString compact_lift_ref_count ^
        " b1_template_expanded_child_ref_equivalent=" ^
          Int.toString expanded_child_ref_equivalent_stat
    in
      ({template_keys = template_keys,
        occurrence_descriptors_term = occurrence_descriptors_term,
        normalized_sources_term = normalized_sources_term,
        root_occurrence_indices_term = root_occurrence_indices_term,
        lift_descriptors = lift_descriptors,
        lift_refs = lift_refs,
        stats = stats}: artifact, lthy)
    end

end
