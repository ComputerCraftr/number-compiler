(* Rank candidates are computed from the ordered graph's least terminating
   attractor. They are proposals until the existing kernel row checker and
   physical source morphism accept them. *)
structure Comma_Future_M204_Graph_Reachability =
struct
  type row = int * int list
  type ranked_row = int * int list * int option

  fun derive (graph: row list): ranked_row list =
    let
      val started = Time.now ()
      val rows = Vector.fromList graph
      val count = Vector.length rows
      val _ = if 0 < count then ()
        else error "Future reachability graph has an invalid size"
      val predecessors = Array.array (count, []: int list)
      val remaining = Array.array (count, 0)
      val maximum = Array.array (count, 0)
      val ranks = Array.array (count, NONE: int option)
      val queue = Array.array (count, 0)
      val back = Unsynchronized.ref 0
      fun enqueue i =
        if !back < count then (Array.update (queue, !back, i); back := !back + 1)
        else error "Future reachability graph enqueued a vertex twice"
      fun child parent target =
        if 0 <= target andalso target < count then
          Array.update (predecessors, target, parent :: Array.sub (predecessors, target))
        else error "Future reachability graph has a foreign child"
      fun admit (i, (control, children)) =
        if control = ~1 andalso null children then
          (Array.update (ranks, i, SOME 0); enqueue i)
        else if 2 <= control andalso control <= 9 andalso length children = 2 then
          (Array.update (remaining, i, 2); List.app (child i) children)
        else error "Future reachability graph has an invalid ordered action"
      val _ = Vector.appi admit rows
      fun advance i rank =
        let
          val old = Array.sub (remaining, i)
          val _ = if old > 0 then () else error "Future reachability count underflow"
          val left = old - 1
          val depth = Int.max (Array.sub (maximum, i), rank + 1)
          val _ = Array.update (remaining, i, left)
          val _ = Array.update (maximum, i, depth)
        in if left = 0 then (Array.update (ranks, i, SOME depth); enqueue i) else () end
      fun process front =
        if front = !back then ()
        else
          let
            val root = Array.sub (queue, front)
            val rank = (case Array.sub (ranks, root) of SOME value => value
              | NONE => error "Future reachability queue contains a live vertex")
            val _ = List.app (fn parent => advance parent rank)
              (Array.sub (predecessors, root))
          in process (front + 1) end
      val _ = process 0
      fun check_live (i, (control, children)) =
        if is_some (Array.sub (ranks, i)) then ()
        else
          (case (control,children) of
             (digit,[north,south]) =>
               if 2 <= digit andalso digit <= 9 andalso
                 length (filter (fn j => is_none (Array.sub (ranks,j))) [north,south]) = 1
               then () else error "Future live action lacks a unique live ordered child"
           | _ => error "Future landmine was not reached")
      val _ = Vector.appi check_live rows
      val _ = Comma_Proof_Profile.report
        ("Future ordered reachability vertices=" ^ Int.toString count ^
         " finite=" ^ Int.toString (!back) ^ " live=" ^ Int.toString (count - !back) ^
         " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started)
    in Vector.foldri (fn (i,(control,children), result) =>
      (control, children, Array.sub (ranks,i)) :: result) [] rows end
end
