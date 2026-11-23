(* Small data-only check; no proposal root is proof authority. *)
local
  structure Arena = Comma_CRT_MDD_Arena
  structure Join = Comma_Future_M204_Join_Proposal
  structure Graph = Comma_Future_M204_Graph_Proposal
  val axes = [3,4,7,11]
  val source = Arena.create axes
  val weight = Arena.create axes
  val classes = Arena.create axes
  val source_roots = replicate 16 (Arena.action_some source 46)
  val weight_roots = replicate 46 (Arena.action_none weight)
  val class_roots = replicate 16 (Arena.action_none classes)
  val join = Join.build source source_roots weight weight_roots classes class_roots
  val comparison = Graph.build join [(2,[0,0])]
  val _ = if length (#roots comparison)=16 andalso length (#class_bounds comparison)=16 andalso
      List.all (fn root => Arena.action_support (#arena join) root = [1])
        (#roots comparison @ #class_bounds comparison)
    then () else error "Future M204 tiny graph did not agree"
  val _ = if null (#shifts join) then ()
    else error "Future M204 tiny graph performed an unneeded shift"
  val _ = if length (#fold_steps join)=3 then ()
    else error "Equivalent future roots repeated their semantic selection work"
  val bad = Exn.capture (fn () => Graph.build join [(2,[0,1])]) ()
  val _ = (case bad of Exn.Exn _ => ()
    | Exn.Res _ => error "Future M204 accepted an out-of-range child")
  val wrong_control = Exn.capture (fn () => Graph.build join [(3,[0,0])]) ()
  val _ = (case wrong_control of Exn.Exn _ => ()
    | Exn.Res _ => error "Future M204 accepted a mismatched control")
  val asymmetric_classes = Arena.create axes
  val class_zero = Arena.action_none asymmetric_classes
  val class_one = Arena.action_some asymmetric_classes 0
  val class_two = Arena.action_some asymmetric_classes 1
  val asymmetric_roots = map (fn i => if i=0 then class_one else
      if i=8 then class_two else class_zero) (0 upto 15)
  val asymmetric = Join.build source source_roots weight weight_roots
    asymmetric_classes asymmetric_roots
  val _ = Graph.build asymmetric (replicate 3 (2,[1,2]))
  val swapped = Exn.capture (fn () =>
    Graph.build asymmetric (replicate 3 (2,[2,1]))) ()
  val _ = (case swapped of Exn.Exn _ => ()
    | Exn.Res _ => error "Future M204 accepted swapped ordered children")
  val wrong_axes = Arena.create [4,3,7,11]
  val wrong_weights = replicate 46 (Arena.action_none wrong_axes)
  val wrong_axis_result = Exn.capture (fn () =>
    Join.build source source_roots wrong_axes wrong_weights classes class_roots) ()
  val _ = (case wrong_axis_result of Exn.Exn _ => ()
    | Exn.Res _ => error "Future M204 accepted mismatched CRT axes")
in end
