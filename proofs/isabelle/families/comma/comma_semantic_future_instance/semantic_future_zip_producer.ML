(* Untrusted structural proposal: combine two independently owned, already
   ordered action MDDs by memoizing pairs of nodes, not physical phases.
   No source binding or theorem authority is issued by this constructor. *)
signature COMMA_SEMANTIC_FUTURE_ZIP_PRODUCER =
sig
  type arena = Comma_CRT_MDD_Arena.arena
  type action_root = Comma_CRT_MDD_Arena.action_root
  val zip_roots: arena -> arena -> action_root list -> arena -> action_root list ->
    (int -> int -> int) ->
    {arena: arena, roots: action_root list, pair_states: int}
end

structure Comma_Semantic_Future_Zip_Producer:
  COMMA_SEMANTIC_FUTURE_ZIP_PRODUCER =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Pair_Table = Table
  (
    type key = int * int
    val ord = prod_ord int_ord int_ord
  )
  type arena = Arena.arena
  type action_root = Arena.action_root
  fun zip_roots out left left_roots right right_roots combine =
    let
      val radices = Arena.radices left
      val _ = if radices = Arena.radices right andalso radices = Arena.radices out then ()
        else error "Future zip input axes differ"
      val _ = if length left_roots = length right_roots then ()
        else error "Future zip root vectors have different lengths"
      val left_export = Arena.export_actions left left_roots
      val right_export = Arena.export_actions right right_roots
      val left_nodes = Vector.fromList (#seeds left_export)
      val right_nodes = Vector.fromList (#seeds right_export)
      val memo = Unsynchronized.ref Pair_Table.empty
      fun input nodes id =
        if id < 0 orelse id >= Vector.length nodes then
          error "Future zip input reference is outside its arena"
        else Vector.sub (nodes,id)
      fun axis_of (Arena.Seed_Leaf _) = NONE
        | axis_of (Arena.Seed_Branch (axis,_)) = SOME axis
      fun choose_axis (SOME a) (SOME b) = Int.min (a,b)
        | choose_axis (SOME a) NONE = a
        | choose_axis NONE (SOME b) = b
        | choose_axis NONE NONE = error "Future zip leaves have no branch axis"
      fun selected node current axis slot = (case node of
          Arena.Seed_Branch (other,children) =>
            if other=axis then List.nth (children,slot) else current
        | Arena.Seed_Leaf _ => current)
      fun build l r =
        (case Pair_Table.lookup (!memo) (l,r) of
          SOME root => root
        | NONE =>
            let
              val lnode = input left_nodes l
              val rnode = input right_nodes r
              val root = (case (lnode,rnode) of
                (Arena.Seed_Leaf x,Arena.Seed_Leaf y) =>
                  let val result = combine x y
                  in if result < 0 then error "Future zip produced a negative payload"
                     else if result=0 then Arena.action_none out
                     else Arena.action_some out (result-1)
                  end
              | _ =>
                  let
                    val axis = choose_axis (axis_of lnode) (axis_of rnode)
                    val _ = if axis >= 0 andalso axis < length radices then ()
                      else error "Future zip input has an invalid axis"
                    val width = List.nth (radices,axis)
                    val children = map (fn slot =>
                      build (selected lnode l axis slot) (selected rnode r axis slot))
                      (0 upto (width-1))
                  in Arena.action_branch out axis children end)
              val _ = memo := Pair_Table.update ((l,r),root) (!memo)
            in root end)
      val roots = ListPair.mapEq (fn (l,r) => build l r) (#roots left_export,#roots right_export)
    in {arena=out,roots=roots,pair_states=Pair_Table.size (!memo)} end
end
