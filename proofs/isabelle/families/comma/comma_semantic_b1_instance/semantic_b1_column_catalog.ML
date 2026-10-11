(* Immutable catalogue decoding and structural validation for the closed DAG. *)
structure Comma_Semantic_B1_Column_Catalog =
struct
  val natT = @{typ nat}
  val columnT = @{typ comma_crt_column}
  val dagT = @{typ comma_semantic_b1_crt_column_dag}
  val periods = Vector.fromList [4, 3, 7, 11]
  val block_size = 512
  val block_prefix = "comma_semantic_b1_crt_column_block_"

  type node = {cid: int, level: int, children: int list}
  type block = {index: int, base: int, extent: int, nodes: node list,
    constant: term, theorem: thm}
  datatype directory_shape = Directory_Empty | Directory_Block of term * term * term
    | Directory_Branch of term * term * term
  fun directory_shape term =
    case strip_comb term of
      (Const (name, _), []) =>
        if name = @{const_name Comma_B1_CRT_Column_DAG_Empty}
        then SOME Directory_Empty else NONE
    | (Const (name, _), [first, second, third]) =>
        if name = @{const_name Comma_B1_CRT_Column_DAG_Block}
        then SOME (Directory_Block (first, second, third))
        else if name = @{const_name Comma_B1_CRT_Column_DAG_Branch}
        then SOME (Directory_Branch (first, second, third)) else NONE
    | _ => NONE

  fun dest_nat term =
    (case try HOLogic.dest_number term of
      SOME (typ, value) =>
        if typ = natT andalso value >= 0 then value
        else error "B1 column DAG contains a non-natural coordinate"
    | NONE => error "B1 column DAG contains a non-literal coordinate")

  fun parse_block_index name =
    let val base_name = Long_Name.base_name name
    in
      if String.isPrefix block_prefix base_name then
        let val suffix = String.extract
          (base_name, String.size block_prefix, NONE)
        in
          (case Int.fromString suffix of
            SOME index =>
              if index >= 0 andalso suffix = Int.toString index then SOME index
              else NONE
          | NONE => NONE)
        end
      else NONE
    end

  fun canonical_block_name thy index name =
    name = Sign.intern_const thy (block_prefix ^ Int.toString index)

  fun parse_block_tree base tree_term =
    let
      val empty_name = @{const_name Comma_B1_CRT_Column_Block_Empty}
      val node_name = @{const_name Comma_B1_CRT_Column_Block_Node}
      fun parse lower upper value =
        (case strip_comb value of
          (Const (name, _), []) =>
            if name = empty_name then ([], 0)
            else error "B1 column block has an unknown empty-node shape"
        | (Const (name, _), [cid_term, level_term, children_term, left, right]) =>
            if name <> node_name then
              error "B1 column block has an unknown node shape"
            else
              let
                val cid = dest_nat cid_term
                val level = dest_nat level_term
                val children = map dest_nat (HOLogic.dest_list children_term)
                val _ = if cid >= base andalso cid < base + block_size andalso
                    (case lower of NONE => true | SOME bound => bound < cid) andalso
                    (case upper of NONE => true | SOME bound => cid < bound)
                  then () else error "B1 column block CIDs are not strictly ordered"
                val _ = if level < Vector.length periods then ()
                  else error "B1 column DAG node has an invalid level"
                val _ = if length children = Vector.sub (periods, level) then ()
                  else error "B1 column DAG node has an invalid radix shape"
                val (left_nodes, left_height) = parse lower (SOME cid) left
                val (right_nodes, right_height) = parse (SOME cid) upper right
                val _ = if Int.abs (left_height - right_height) <= 1 then ()
                  else error "B1 column block is not balanced"
              in (left_nodes @
                    (({cid = cid, level = level, children = children}: node) ::
                      right_nodes),
                  1 + Int.max (left_height, right_height)) end
        | _ => error "B1 column block has a malformed tree node")
      val (nodes, _) = parse NONE NONE tree_term
      val expected = base upto (base + length nodes - 1)
      val _ = if map #cid nodes = expected then ()
        else error "B1 column block CIDs are incomplete or out of order"
    in nodes end

  fun structure_key level children =
    Int.toString level ^ ":" ^ String.concatWith "," (map Int.toString children)

  fun validate_nodes nodes =
    let
      val cids = map #cid nodes
      val expected = 2 upto (length nodes + 1)
      val _ = if cids = expected then ()
        else error "B1 column DAG CIDs are incomplete or out of order"
      val index = fold (fn (entry: node) =>
        Inttab.update (#cid entry, entry)) nodes Inttab.empty
      fun check_child (parent: node) child =
        if child < 2 then true
        else
          (case Inttab.lookup index child of
            SOME (child_node: node) => child < #cid parent andalso
              #level parent < #level child_node
          | NONE => false)
      val _ = if forall (fn (parent: node) =>
          forall (check_child parent) (#children parent)) nodes
        then () else error "B1 column DAG has a foreign, forward, or shallow child CID"
      val structure_index = fold (fn ({cid, level, children}: node) => fn table =>
        let val key = structure_key level children
        in if Symtab.defined table key then
             error "B1 column DAG contains duplicate ordered node bodies"
           else Symtab.update (key, cid) table end) nodes Symtab.empty
    in (index, structure_index) end

  fun parse_directory (blocks: block Inttab.table) term =
    let
      fun get_block index =
        (case Inttab.lookup blocks index of
          SOME block => block
        | NONE => error "B1 column DAG directory references a foreign block")
      fun parse value =
        (case directory_shape value of
          SOME Directory_Empty => ([], 0)
        | SOME (Directory_Block (base_term, extent_term, block_term)) =>
              let
                val base = dest_nat base_term
                val extent = dest_nat extent_term
                val (block_constant, block_name_actual) =
                  (case block_term of
                    Const (block_name_actual, _) => (block_term, block_name_actual)
                  | _ => error "B1 column DAG leaf does not reference a named block")
                val block_index = (case parse_block_index block_name_actual of
                    SOME index => index
                  | NONE => error "B1 column DAG leaf names an unknown block")
                val block = get_block block_index
                val _ = if fastype_of block_constant =
                    @{typ comma_semantic_b1_crt_column_block} andalso
                    #constant block aconv block_constant then ()
                  else error "B1 column DAG leaf has a mismatched block constant"
                val _ = if base = #base block andalso extent = #extent block then ()
                  else error "B1 column DAG block range disagrees with its definition"
              in ([block_index], 1) end
        | SOME (Directory_Branch (split_term, left, right)) =>
              let
                val split = dest_nat split_term
                val (left_indices, left_height) = parse left
                val (right_indices, right_height) = parse right
                val _ = if not (null left_indices) andalso not (null right_indices)
                  then () else error "B1 column DAG directory has an empty branch"
                val right_base = #base (get_block (hd right_indices))
                val _ = if split = right_base then ()
                  else error "B1 column DAG directory split is not canonical"
                val _ = if List.last left_indices < hd right_indices then ()
                  else error "B1 column DAG directory block order is invalid"
                val _ = if Int.abs (left_height - right_height) <= 1 then ()
                  else error "B1 column DAG directory is not balanced"
              in (left_indices @ right_indices,
                  1 + Int.max (left_height, right_height)) end
        | NONE => error "B1 column DAG has a malformed directory node")
      val (indices, _) = parse term
      val expected = 0 upto (Inttab.size blocks - 1)
      val _ = if indices = expected then ()
        else error "B1 column DAG directory omits, repeats, or reorders a block"
    in indices end
end
