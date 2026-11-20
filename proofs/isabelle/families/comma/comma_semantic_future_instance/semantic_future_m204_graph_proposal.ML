(* Untrusted quotient-graph comparison.  It visits shared MDD pairs, not
   individual physical phases.  The produced equality roots require replay. *)
structure Comma_Future_M204_Graph_Proposal =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Zip = Comma_Semantic_Future_Zip_Producer
  datatype operation = Graph_Control | Graph_N | Graph_Z | Actual_Control | Class_Bound | Equal
  type row = int * int list
  type comparison = {operation: operation, left: int, right: int, output: int}
  type result = {roots: Arena.action_root list, class_bounds: Arena.action_root list,
    comparisons: comparison list}

  fun build (join: Comma_Future_M204_Join_Proposal.result) rows : result =
    let
      val arena = #arena join
      val graph = Vector.fromList rows
      val count = Vector.length graph
      val _ = if count>0 andalso count<=65536 then ()
        else error "Future graph has an invalid class count"
      fun checked_row (control,children) =
        if control = ~1 then
          if null children then () else error "Landmine has children"
        else if 2<=control andalso control<=9 andalso length children=2 andalso
            List.all (fn child => 0<=child andalso child<count) children then ()
        else error "Future graph has an invalid fork row"
      val _ = Vector.app checked_row graph
      fun row id = if 0<=id andalso id<count then Vector.sub (graph,id)
        else error "Future class-map payload is outside the graph"
      fun graph_control id = (case row id of (~1,_) => 9 | (a,_) => a-1)
      fun graph_child side id = (case row id of (~1,_) => 0
        | (_,children) => List.nth (children,side)+1)
      fun actual_control code = if code=0 then 0 else (code-1) mod 9 + 1
      val zero = Arena.action_none arena
      val zeros = replicate 16 zero
      val _ = if length (#classes join)=16 andalso length (#outputs join)=16 andalso
          length (#children_n join)=16 andalso length (#children_z join)=16 then ()
        else error "Future graph join has wrong physical root counts"
      val records = Unsynchronized.ref ([]: comparison list)
      fun ai root = Arena.action_index arena root
      fun zip operation left right combine =
        let
          val result = Zip.zip_roots arena arena left arena right combine
          val outputs = #roots result
          val _ = if length left=length right andalso length right=length outputs then ()
            else error "Future graph comparison root counts differ"
          val _ = List.app (fn ((l,r),out) => records :=
            {operation=operation,left=ai l,right=ai r,output=ai out} :: !records)
            (ListPair.zip (ListPair.zip (left,right),outputs))
        in outputs end
      val graph_c = zip Graph_Control (#classes join) zeros (fn id => fn _ => graph_control id)
      val graph_n = zip Graph_N (#classes join) zeros (fn id => fn _ => graph_child 0 id)
      val graph_z = zip Graph_Z (#classes join) zeros (fn id => fn _ => graph_child 1 id)
      val class_bounds = zip Class_Bound (#classes join) zeros
        (fn id => fn _ => if id<count then 1 else 0)
      val actual_c = zip Actual_Control (#outputs join) zeros (fn x => fn _ => actual_control x)
      fun equal xs ys = zip Equal xs ys (fn x => fn y => if x=y then 1 else 0)
      val roots = equal actual_c graph_c @ equal (#children_n join) graph_n @
        equal (#children_z join) graph_z
      val _ = List.app (fn root =>
        if Arena.action_support arena root = [1] then ()
        else error "Future class graph does not match the source join") (roots @ class_bounds)
    in {roots=roots,class_bounds=class_bounds,comparisons=List.rev (!records)} end
end
