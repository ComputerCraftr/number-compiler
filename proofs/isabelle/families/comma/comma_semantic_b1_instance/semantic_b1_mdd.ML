(* Shared canonical CRT/MDD algebra for the B1 candidate constructor and
   its global ColumnCID publisher.  These values are construction data only. *)
structure Comma_Semantic_B1_MDD =
struct
  datatype mdd = MDD_False | MDD_True | MDD_Node of int * mdd list
  type scope = int * int
  type cube = int list list
  val clock_size = 924

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
  structure ScopeTab = Table(type key = scope val ord = prod_ord int_ord int_ord)

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
  fun partition_alignment_shifts_with_cardinalities scope_cover
      (cardinalities: (mdd * int) list) global_period =
    let
      val rarest = fold (fn (_, count) => fn best => if count < best then count else best)
        cardinalities clock_size
      val rare_keys = map #1 (filter (fn (_, count) => count = rarest) cardinalities)
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

  fun canonical_partition_rebase_with_cardinalities scope_cover translate_key
      (source_keys: mdd list) (cardinalities: (mdd * int) list) =
    (* The constructor supplies cardinalities from its fold-local memo.  Keep
       their MDD keys aligned here before using them to choose anchor columns. *)
    if map #1 cardinalities <> source_keys then
      error "B1 canonical rebase cardinalities lost source-column alignment"
    else if source_keys = [MDD_True] then (0, 1, source_keys, source_keys)
    else
      let
        val global_period = mdd_support_period source_keys
        val candidates = partition_alignment_shifts_with_cardinalities
          scope_cover cardinalities global_period
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

  fun canonical_partition_rebase scope_cover translate_key (source_keys: mdd list) =
    if source_keys = [MDD_True] then (0, 1, source_keys, source_keys)
    else
      let
        val cardinalities = map (fn key => (key, mdd_cardinality key)) source_keys
      in canonical_partition_rebase_with_cardinalities scope_cover translate_key
        source_keys cardinalities end

end
