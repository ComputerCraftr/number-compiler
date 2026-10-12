(* Candidate-only construction for the sparse mass annotation.  The returned
   tree is data and has no authority until the invariant prover checks it. *)
structure Comma_Semantic_B1_Mass_Candidate =
struct
  type annotation_row = {cid: int, level: int, value: int}
  type node_row = {cid: int, level: int, children: int list}

  fun make_annotation node_count rows =
    let
      val natT = @{typ nat}
      val treeT = @{typ comma_semantic_b1_crt_mass_tree}
      val node = Const
        (@{const_name Comma_B1_CRT_Mass_Tree_Node},
          natT --> natT --> natT --> treeT --> treeT --> treeT)
      val empty = Const
        (@{const_name Comma_B1_CRT_Mass_Tree_Empty}, treeT)
      val nat = HOLogic.mk_number natT
      val _ = if node_count >= 2 then () else
        error "B1 annotation builder requires two terminal CIDs"
      fun cid_ord (left: annotation_row, right: annotation_row) =
        int_ord (#cid left, #cid right)
      val ordered = sort cid_ord rows
      fun check seen [] = seen
        | check seen ({cid, level, value} :: tail) =
            if cid < 2 orelse cid >= node_count then
              error "B1 annotation builder received a foreign CID"
            else if Inttab.defined seen cid then
              error "B1 annotation builder received a duplicate CID"
            else if level < 0 orelse value < 0 then
              error "B1 annotation builder received a negative annotation"
            else check (Inttab.update (cid, ()) seen) tail
      val _ = check Inttab.empty ordered
      fun balanced [] = empty
        | balanced values =
            let
              val midpoint = length values div 2
              val middle = nth values midpoint
              val left = balanced (take midpoint values)
              val right = balanced (drop (midpoint + 1) values)
            in node $ nat (#cid middle) $ nat (#level middle) $
                 nat (#value middle) $ left $ right end
    in balanced ordered end

  fun dependency_table node_count roots get_node =
    let
      fun add_node cid table =
        if cid < 0 orelse cid >= node_count then
          error "B1 annotation producer received a root or child outside the DAG extent"
        else if cid < 2 then table
        else if is_some (Inttab.lookup table cid) then table
        else
          (case get_node cid of
            NONE => error "B1 annotation producer lacks a requested node row"
          | SOME ({cid = row_cid, level, children}: node_row) =>
              let
                val _ = if row_cid = cid then () else
                  error "B1 annotation producer changed the row CID"
                val _ = if forall (fn child => child < cid andalso child >= 0) children
                  then () else error "B1 annotation producer found a non-predecessor child"
                val table' = Inttab.update (cid,
                  {cid = cid, level = level, children = children}: node_row) table
              in fold add_node children table' end)
    in fold add_node roots Inttab.empty end

  fun make_annotation_and_cids node_count period roots get_node =
    let
      val table = dependency_table node_count roots get_node
      val mass_cache = Unsynchronized.ref (Inttab.empty: int Inttab.table)
      fun candidate_mass cid =
        (case Inttab.lookup (!mass_cache) cid of
          SOME value => value
        | NONE =>
            let
              val value =
                if cid = 0 then 0
                else if cid = 1 then 924
                else
                  (case Inttab.lookup table cid of
                    NONE => error "B1 annotation producer has an open child closure"
                  | SOME ({level, children, ...}: node_row) =>
                      let
                        val radix = period level
                        val _ = if radix > 0 then () else
                          error "B1 annotation producer received a zero CRT period"
                        val total = fold (fn child => fn sum =>
                          candidate_mass child + sum) children 0
                      in total div radix end)
              val _ = mass_cache := Inttab.update (cid, value) (!mass_cache)
            in value end)
      val rows = map (fn (_, ({cid, level, ...}: node_row)) =>
        {cid = cid, level = level, value = candidate_mass cid}: annotation_row)
        (Inttab.dest table)
    in (make_annotation node_count rows, map fst (Inttab.dest table)) end

  fun make_annotation_from_nodes node_count period roots get_node =
    #1 (make_annotation_and_cids node_count period roots get_node)

  fun make_annotation_from_rows node_count period roots (rows: node_row list) =
    let
      fun add row table =
        if Inttab.defined table (#cid row) then
          error "B1 annotation producer received duplicate row CIDs"
        else Inttab.update (#cid row, row) table
      val table = fold add rows Inttab.empty
      fun get_node cid = Inttab.lookup table cid
    in make_annotation_and_cids node_count period roots get_node end

  fun tree_cids tree =
    let
      fun number term =
        (case HOLogic.dest_number term of
          (typ, value) => if typ = @{typ nat} andalso value >= 0 then value
            else error "B1 annotation tree has a non-natural CID")
      fun visit term seen =
        (case strip_comb term of
          (Const (name, _), []) =>
            if name = @{const_name Comma_B1_CRT_Mass_Tree_Empty} then seen
            else error "B1 annotation tree has an unknown leaf"
        | (Const (name, _), [cid, _, _, left, right]) =>
            if name = @{const_name Comma_B1_CRT_Mass_Tree_Node} then
              let
                val key = number cid
                val _ = if Inttab.defined seen key then
                    error "B1 annotation tree repeats a CID" else ()
                val seen_left = visit left (Inttab.update (key, ()) seen)
              in visit right seen_left end
            else error "B1 annotation tree has an unknown node"
        | _ => error "B1 annotation tree has malformed shape")
    in map fst (Inttab.dest (visit tree Inttab.empty)) end
end
