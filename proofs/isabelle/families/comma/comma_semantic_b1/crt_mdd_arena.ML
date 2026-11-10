(* A single request-local arena for shared, reduced, ordered flat MDDs.
   The integer labels and node IDs are proposal data; proof authority is
   supplied only by the final-table kernel certificates. *)
signature COMMA_CRT_MDD_ARENA =
sig
  type arena
  datatype seed_node = Seed_Leaf of int | Seed_Branch of int * int list
  type action_root
  type boolean_root
  datatype view = Leaf_Value of int | Branch_At of int * int list
  type bind_key = int * int * (int * int) list
  datatype bind_step = Bind_Leaf of int | Bind_Branch of int * bind_key list
  type bind_witness =
    {key: bind_key, support: int list, result: int, step: bind_step}

  val create: int list -> arena
  val radices: arena -> int list
  val seed_prefix: arena -> seed_node list -> action_root list
  val import_action_table: arena -> seed_node list -> int -> action_root
  val import_boolean_guard_table_with_roots:
    arena -> seed_node list -> boolean_root list
  val import_boolean_table: arena -> seed_node list -> int -> boolean_root
  val action_none: arena -> action_root
  val action_some: arena -> int -> action_root
  val action_branch: arena -> int -> action_root list -> action_root
  val boolean_false: arena -> boolean_root
  val boolean_true: arena -> boolean_root
  val boolean_branch: arena -> int -> boolean_root list -> boolean_root
  val action_view: arena -> action_root -> view
  val boolean_view: arena -> boolean_root -> view
  val action_index: arena -> action_root -> int
  val boolean_index: arena -> boolean_root -> int
  val action_support: arena -> action_root -> int list
  val boolean_support: arena -> boolean_root -> int list
  val shift_action: arena -> action_root -> int -> action_root
  val shift_boolean: arena -> boolean_root -> int -> boolean_root
  val bind_action_to_boolean: arena -> action_root -> boolean_root ->
    (int * boolean_root) list -> boolean_root
  val select_boolean_action: arena -> boolean_root -> action_root -> action_root -> action_root
  val bind_witness: arena -> bind_key -> bind_witness
  val table_term: arena -> term
  val node_count: arena -> int
  val statistics: arena -> string
end

structure Comma_CRT_MDD_Arena:> COMMA_CRT_MDD_ARENA =
struct
  datatype seed_policy = Canonical_Seed | Ordered_Guard
  datatype seed_node = Seed_Leaf of int | Seed_Branch of int * int list
  datatype node = Leaf of int | Branch of int * int list
  datatype raw_root = Raw_Root of {owner: unit Unsynchronized.ref, id: int}
  datatype action_root = Action_Root of raw_root
  datatype boolean_root = Boolean_Root of raw_root
  datatype view = Leaf_Value of int | Branch_At of int * int list
  type bind_key = int * int * (int * int) list
  datatype bind_step = Bind_Leaf of int | Bind_Branch of int * bind_key list
  type bind_witness =
    {key: bind_key, support: int list, result: int, step: bind_step}

  structure Node_Table = Table(
    type key = node
    val ord = fn (Leaf x, Leaf y) => int_ord (x, y)
      | (Leaf _, Branch _) => LESS
      | (Branch _, Leaf _) => GREATER
      | (Branch (axis_x, children_x), Branch (axis_y, children_y)) =>
          prod_ord int_ord (list_ord int_ord) ((axis_x, children_x), (axis_y, children_y)))
  structure Shift_Table = Table(
    type key = int * int
    val ord = prod_ord int_ord int_ord)
  structure Bind_Table = Table(
    type key = int * int * (int * int) list
    val ord = fn ((source, fallback, mapping), (source', fallback', mapping')) =>
      prod_ord int_ord (prod_ord int_ord (list_ord (prod_ord int_ord int_ord)))
        ((source, (fallback, mapping)), (source', (fallback', mapping'))))

  type counters =
    {intern_hits: int Unsynchronized.ref, intern_misses: int Unsynchronized.ref,
     shift_requests: int Unsynchronized.ref, shift_completions: int Unsynchronized.ref,
     shift_hits: int Unsynchronized.ref, bind_requests: int Unsynchronized.ref,
     bind_completions: int Unsynchronized.ref, bind_hits: int Unsynchronized.ref}

  type arena =
    {owner: unit Unsynchronized.ref, radices: int list,
     storage: node option Array.array Unsynchronized.ref,
     size: int Unsynchronized.ref, interned: int Node_Table.table Unsynchronized.ref,
     supports: int list Inttab.table Unsynchronized.ref,
     shift_cache: int Shift_Table.table Unsynchronized.ref,
     bind_cache: bind_witness Bind_Table.table Unsynchronized.ref, counters: counters}

  fun create radices =
    let
      val _ = if not (null radices) andalso List.all (fn r => r > 0) radices
        then () else error "CRT MDD arena radices must be positive"
      val counters: counters =
        {intern_hits = Unsynchronized.ref 0,
         intern_misses = Unsynchronized.ref 0,
         shift_requests = Unsynchronized.ref 0,
         shift_completions = Unsynchronized.ref 0,
         shift_hits = Unsynchronized.ref 0,
         bind_requests = Unsynchronized.ref 0,
         bind_completions = Unsynchronized.ref 0,
         bind_hits = Unsynchronized.ref 0}
    in
      {owner = Unsynchronized.ref (), radices = radices,
       storage = Unsynchronized.ref (Array.array (128, NONE)),
       size = Unsynchronized.ref 0, interned = Unsynchronized.ref Node_Table.empty,
       supports = Unsynchronized.ref Inttab.empty,
       shift_cache = Unsynchronized.ref Shift_Table.empty,
       bind_cache = Unsynchronized.ref Bind_Table.empty,
       counters = counters}: arena
    end

  fun node_count ({size, ...}: arena) = !size
  fun radices ({radices, ...}: arena) = radices

  fun ensure_capacity storage needed =
    let
      val current = Array.length (!storage)
      val maximum = Array.maxLen
      fun grow n =
        if n >= needed then n
        else if n > maximum div 2 then needed
        else grow (2 * n)
      val capacity = if needed <= current then current else grow (Int.max (1, current))
      val _ = if capacity <= maximum andalso capacity >= needed then ()
        else error "CRT MDD arena exceeds the runtime array capacity"
    in
      if capacity = current then ()
      else
        let
          val next = Array.array (capacity, NONE: node option)
          val _ = Array.copy {src = !storage, dst = next, di = 0}
        in storage := next end
    end

  fun node_at ({storage, size, ...}: arena) id =
    if id < 0 orelse id >= !size then error "CRT MDD proposal node is out of range"
    else (case Array.sub (!storage, id) of
      SOME node => node
    | NONE => error "CRT MDD arena contains an uninitialized node")

  fun support_node (arena: arena) (Leaf label) = [label]
    | support_node (arena: arena) (Branch (_, children)) =
        fold (fn child => fn labels => union (op =) labels
          (case Inttab.lookup (!(#supports arena)) child of
            SOME support => support
          | NONE => error "CRT MDD child support is unavailable")) children []

  fun validate_branch (arena: arena) axis children =
    let
      val _ = if axis >= 0 andalso axis < length (#radices arena) then ()
        else error "CRT MDD branch axis is outside the radix vector"
      val radix = List.nth (#radices arena, axis)
      val _ = if length children = radix then ()
        else error "CRT MDD branch width disagrees with its axis radix"
      val _ = List.app (fn child =>
        if child >= 0 andalso child < node_count arena then ()
        else error "CRT MDD branch child is not an earlier node") children
      val _ = List.app (fn child =>
        case node_at arena child of
          Leaf _ => ()
        | Branch (child_axis, _) =>
            if axis < child_axis then ()
            else error "CRT MDD branch axes are not strictly ordered") children
    in () end

  fun store_node (arena as {storage, size, interned, supports, counters, ...}: arena) node =
    (case Node_Table.lookup (!interned) node of
      SOME id => (#intern_hits counters := !(#intern_hits counters) + 1; id)
    | NONE =>
        let
          val _ = (case node of Leaf _ => ()
            | Branch (axis, children) => validate_branch arena axis children)
          val id = !size
          val _ = ensure_capacity storage (id + 1)
          val _ = Array.update (!storage, id, SOME node)
          val _ = size := id + 1
          val _ = interned := Node_Table.update (node, id) (!interned)
          val _ = supports := Inttab.update (id, support_node arena node) (!supports)
          val _ = #intern_misses counters := !(#intern_misses counters) + 1
        in id end)

  fun validate_seed_nodes policy (arena: arena) nodes =
    let
      val table = Vector.fromList nodes
      val seen = Unsynchronized.ref Node_Table.empty
      fun check (index, seed_node) =
        let
          val node = (case seed_node of
            Seed_Leaf label =>
              if label >= 0 then Leaf label
              else error "CRT MDD seed contains a negative leaf label"
          | Seed_Branch (axis, children) =>
              let
                val _ = if axis >= 0 andalso axis < length (#radices arena) then ()
                  else error "CRT MDD seed axis is invalid"
                val radix = List.nth (#radices arena, axis)
                val _ = if length children = radix then ()
                  else error "CRT MDD seed width is invalid"
                val _ = List.app (fn child => if 0 <= child andalso child < index then ()
                  else error "CRT MDD seed child is not earlier than its parent") children
                val _ = List.app (fn child =>
                  case Vector.sub (table, child) of
                    Seed_Leaf _ => ()
                  | Seed_Branch (child_axis, _) =>
                      if axis < child_axis then ()
                      else error "CRT MDD seed variable order is invalid") children
                val _ = if policy = Canonical_Seed then
                    (case children of
                      [] => error "CRT MDD seed contains an empty branch"
                    | first :: rest => if List.all (fn child => child = first) rest then
                        error "CRT MDD seed branch is unreduced" else ())
                  else ()
              in Branch (axis, children) end)
          val _ = if policy = Canonical_Seed then
              if Node_Table.defined (!seen) node then
                error "CRT MDD seed table contains a duplicate node"
              else seen := Node_Table.update (node, ()) (!seen)
            else ()
        in () end
    in List.app check (map_index I nodes) end

  fun seed_prefix (arena as {storage, size, interned, supports, counters, ...}: arena) nodes =
    let
      val _ = if !size = 0 then () else error "CRT MDD seed prefix requires an empty arena"
      val _ = validate_seed_nodes Canonical_Seed arena nodes
      val _ = ensure_capacity storage (length nodes)
      fun append (index, Seed_Leaf label) =
            let val node = Leaf label
                val _ = Array.update (!storage, index, SOME node)
                val _ = size := index + 1
                val _ = interned := Node_Table.update (node, index) (!interned)
                val _ = supports := Inttab.update (index, [label]) (!supports)
                val _ = #intern_misses counters := !(#intern_misses counters) + 1
            in () end
        | append (index, Seed_Branch (axis, children)) =
            let val node = Branch (axis, children)
                val _ = validate_branch arena axis children
                val _ = Array.update (!storage, index, SOME node)
                val _ = size := index + 1
                val _ = interned := Node_Table.update (node, index) (!interned)
                val _ = supports := Inttab.update (index, support_node arena node) (!supports)
                val _ = #intern_misses counters := !(#intern_misses counters) + 1
            in () end
      val _ = List.app append (map_index I nodes)
    in map (fn id => Action_Root (Raw_Root {owner = #owner arena, id = id}))
      (0 upto (length nodes - 1)) end

  fun make_root arena id =
    if id >= 0 andalso id < node_count arena then Raw_Root {owner = #owner arena, id = id}
    else error "CRT MDD root handle is outside the proposal arena"

  fun check_root (arena: arena) (Raw_Root {owner, id}) =
    let
      val _ = if owner = #owner arena then () else error "CRT MDD root belongs to another arena"
      val _ = ignore (node_at arena id)
    in id end

  fun action_index arena (Action_Root root) = check_root arena root
  fun boolean_index arena (Boolean_Root root) = check_root arena root

  fun action_leaf arena code = Action_Root (make_root arena (store_node arena (Leaf code)))
  fun boolean_leaf arena value =
    if value = 0 orelse value = 1 then
      Boolean_Root (make_root arena (store_node arena (Leaf value)))
    else error "CRT MDD Boolean leaves are encoded by 0 and 1"

  fun action_none arena = action_leaf arena 0
  fun action_some arena target =
    if 0 <= target then action_leaf arena (target + 1)
    else error "CRT MDD Continue target is outside the supported natural range"
  fun boolean_false arena = boolean_leaf arena 0
  fun boolean_true arena = boolean_leaf arena 1

  fun intern_branch arena axis ids =
    let
      val _ = validate_branch arena axis ids
    in
      (case ids of
        [] => error "CRT MDD cannot intern an empty branch"
      | first :: rest =>
          if List.all (fn child => child = first) rest then first
          else store_node arena (Branch (axis, ids)))
    end

  fun make_branch arena id_of make_root axis children =
    let
      val ids = map id_of children
      val result = intern_branch arena axis ids
    in
      case children of
        [] => error "CRT MDD cannot intern an empty branch"
      | _ => make_root result
    end

  fun action_branch arena axis children =
    make_branch arena (fn root => check_root arena
      (case root of Action_Root action_handle => action_handle))
      (Action_Root o make_root arena) axis children

  fun boolean_branch arena axis children =
    make_branch arena (fn root => check_root arena
      (case root of Boolean_Root boolean_handle => boolean_handle))
      (Boolean_Root o make_root arena) axis children

  fun import_table policy arena leaf_builder branch_builder seeds =
    let
      val _ = validate_seed_nodes policy arena seeds
      val converted = Array.array (length seeds, NONE)
      fun import_one (index, seed) =
        let
          val result = (case seed of
            Seed_Leaf label => leaf_builder arena label
          | Seed_Branch (axis, children) =>
              branch_builder arena axis (map (fn child =>
                (case Array.sub (converted, child) of
                  SOME root_handle => root_handle
                | NONE => error "CRT MDD imported child was not converted")) children))
          val _ = Array.update (converted, index, SOME result)
        in () end
      val _ = List.app import_one (map_index I seeds)
      val roots = map (fn index =>
        (case Array.sub (converted, index) of
          SOME result => result
        | NONE => error "CRT MDD imported node was not converted"))
        (0 upto (length seeds - 1))
    in roots end

  fun validate_boolean_seed_nodes label seeds =
    List.app (fn seed => case seed of
      Seed_Leaf value => if value = 0 orelse value = 1 then ()
        else error (label ^ " contains a non-Boolean leaf")
    | Seed_Branch _ => ()) seeds

  fun import_action_table arena seeds root =
    if root >= 0 andalso root < length seeds then
      List.nth (import_table Canonical_Seed arena action_leaf action_branch seeds, root)
    else error "CRT MDD imported root is outside its local table"

  fun import_boolean_guard_table_with_roots arena seeds =
    let
      val _ = validate_boolean_seed_nodes "Boolean MDD guard import" seeds
    in import_table Ordered_Guard arena boolean_leaf boolean_branch seeds end

  fun import_boolean_table arena seeds root =
    if root >= 0 andalso root < length seeds then
      let
        val _ = validate_boolean_seed_nodes "Boolean MDD import" seeds
      in List.nth (import_table Canonical_Seed arena boolean_leaf boolean_branch seeds, root) end
    else error "CRT MDD imported root is outside its local table"

  fun action_view arena (Action_Root root) =
    (case node_at arena (check_root arena root) of
      Leaf label => Leaf_Value label
    | Branch (axis, children) => Branch_At (axis, children))

  fun boolean_view arena (Boolean_Root root) =
    (case node_at arena (check_root arena root) of
      Leaf label => Leaf_Value label
    | Branch (axis, children) => Branch_At (axis, children))

  fun support arena root =
    (case Inttab.lookup (!(#supports arena)) (check_root arena root) of
      SOME labels => labels
    | NONE => error "CRT MDD root has no payload-support certificate")

  fun action_support arena (Action_Root root) = support arena root
  fun boolean_support arena (Boolean_Root root) = support arena root

  fun top_axis arena id =
    (case node_at arena id of Leaf _ => NONE | Branch (axis, _) => SOME axis)

  fun cofactor arena axis slot id =
    (case node_at arena id of
      Leaf _ => id
    | Branch (node_axis, children) =>
        if node_axis = axis then List.nth (children, slot)
        else if axis < node_axis then id
        else error "CRT MDD cofactor skipped a decision axis")

  fun shift_id (arena as {radices, shift_cache, counters, ...}: arena) id amount =
    let
      val _ = if amount >= 0 then () else error "CRT MDD shift amount is negative"
      val _ = #shift_requests counters := !(#shift_requests counters) + 1
      fun visit node_id =
        (case Shift_Table.lookup (!shift_cache) (node_id, amount) of
          SOME target => (#shift_hits counters := !(#shift_hits counters) + 1; target)
        | NONE =>
            let
              val target = (case node_at arena node_id of
                Leaf label => store_node arena (Leaf label)
              | Branch (axis, children) =>
                  let
                    val radix = List.nth (radices, axis)
                    val shifted_children = map_index (fn (slot, _) =>
                      visit (List.nth (children, (slot + amount) mod radix))) children
                  in store_node arena (Branch (axis, shifted_children)) end)
              val _ = shift_cache := Shift_Table.update ((node_id, amount), target)
                (!shift_cache)
              val _ = #shift_completions counters := !(#shift_completions counters) + 1
            in target end)
      val result = visit id
    in make_root arena result end

  fun shift_action arena (Action_Root root) amount =
    Action_Root (shift_id arena (check_root arena root) amount)

  fun shift_boolean arena (Boolean_Root root) amount =
    Boolean_Root (shift_id arena (check_root arena root) amount)

  fun restrict_mapping (arena: arena) source mapping =
    let
      val supported = case Inttab.lookup (!(#supports arena)) source of
        SOME labels => labels | NONE => error "CRT MDD source support is missing"
    in filter (fn (payload, _) => member (op =) supported payload) mapping end

  fun bind_witness (arena: arena) (source, fallback, mapping) =
    let
      val _ = List.app (fn id => ignore (node_at arena id))
        (source :: fallback :: map #2 mapping)
      val key = (source, fallback, restrict_mapping arena source mapping)
    in case Bind_Table.lookup (!(#bind_cache arena)) key of
      SOME witness => witness
    | NONE => error "CRT MDD bind operation was not constructed in this arena"
    end

  fun bind_root (arena as {radices, bind_cache, counters, ...}: arena)
      source_root fallback_root mapping =
    let
      val source = check_root arena source_root
      val fallback = check_root arena fallback_root
      val checked_mapping = map (fn (payload, root) =>
        (if payload >= 0 then () else error "CRT MDD bind label is negative";
         (payload,check_root arena root))) mapping
      val labels = map #1 mapping
      val _ = if length (distinct (op =) labels) = length labels then ()
        else error "CRT MDD bind mapping repeats a source payload"
      val _ = #bind_requests counters := !(#bind_requests counters) + 1
      fun visit source_id default_id mapping' =
        let
          val mapping' = restrict_mapping arena source_id mapping'
          val key' = (source_id, default_id, mapping')
        in
          (case Bind_Table.lookup (!bind_cache) key' of
            SOME witness =>
              (#bind_hits counters := !(#bind_hits counters) + 1; (#result witness,key'))
          | NONE =>
              let
                val (result,step) = (case node_at arena source_id of
                  Leaf payload =>
                    ((case AList.lookup (op =) mapping' payload of
                      SOME id => id
                    | NONE => default_id), Bind_Leaf payload)
                | Branch (source_axis, _) =>
                    let
                      val roots = default_id :: map #2 mapping'
                      val axes = map_filter (top_axis arena) (source_id :: roots)
                      val axis = (case axes of
                        [] => error "CRT MDD branch has no axis"
                      | first :: rest => fold (fn next => fn current => Int.min (next,current)) rest first)
                      val _ = if axis <= source_axis then ()
                        else error "CRT MDD bind chose an axis after its source"
                      val width = List.nth (radices, axis)
                      val child_results = map (fn slot =>
                        let
                          val source_child = cofactor arena axis slot source_id
                          val default_child = cofactor arena axis slot default_id
                          val mapping_child = map (fn (label,id) =>
                            (label,cofactor arena axis slot id)) mapping'
                        in visit source_child default_child mapping_child end)
                        (0 upto (width - 1))
                    in (intern_branch arena axis (map #1 child_results),
                      Bind_Branch (axis,map #2 child_results)) end)
                val witness: bind_witness =
                  {key=key', support=the (Inttab.lookup (!(#supports arena)) source_id),
                   result=result, step=step}
                val _ = bind_cache := Bind_Table.update (key',witness) (!bind_cache)
                val _ = #bind_completions counters := !(#bind_completions counters) + 1
              in (result,key') end)
        end
      val (result,_) = visit source fallback checked_mapping
    in make_root arena result end

  fun bind_action_to_boolean arena (Action_Root source)
      (Boolean_Root fallback) mapping =
    let
      val encoded = map (fn (target, Boolean_Root root) =>
        if 0 <= target then (target + 1, root)
        else error "CRT MDD bind target label is outside the supported natural range") mapping
    in Boolean_Root (bind_root arena source fallback encoded) end

  fun select_boolean_action arena (Boolean_Root guard)
      (Action_Root if_true) (Action_Root if_false) =
    Action_Root (bind_root arena guard if_false
      [(0, if_false), (1, if_true)])

  fun table_term (arena: arena) =
    let
      fun nat n = HOLogic.mk_number @{typ nat} n
      val node_type = @{typ "nat comma_crt_mdd_node"}
      val leaf = Const (@{const_name Comma_CRT_MDD_Leaf},
        @{typ "nat => nat comma_crt_mdd_node"})
      val branch = Const (@{const_name Comma_CRT_MDD_Branch},
        @{typ "nat => nat list => nat comma_crt_mdd_node"})
      fun term_of_node (Leaf label) = leaf $ nat label
        | term_of_node (Branch (axis, children)) =
            branch $ nat axis $ HOLogic.mk_list @{typ nat} (map nat children)
      val nodes = map (fn id => term_of_node (node_at arena id))
        (0 upto (node_count arena - 1))
    in HOLogic.mk_list node_type nodes end

  fun statistics ({size, counters, ...}: arena) =
    let fun show label counter = label ^ "=" ^ Int.toString (!counter)
    in String.concatWith " "
      ["proposal_nodes=" ^ Int.toString (!size),
       show "intern_hits" (#intern_hits counters),
       show "intern_misses" (#intern_misses counters),
       show "shift_requests" (#shift_requests counters),
       show "shift_completions" (#shift_completions counters),
       show "shift_hits" (#shift_hits counters),
       show "bind_requests" (#bind_requests counters),
       show "bind_completions" (#bind_completions counters),
       show "bind_hits" (#bind_hits counters)] end
end
