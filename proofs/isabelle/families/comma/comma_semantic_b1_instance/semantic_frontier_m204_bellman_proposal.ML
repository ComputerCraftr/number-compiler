(* Untrusted shared-DAG M204 Bellman proposal.  It retains the operation
   transcript for fresh kernel replay; no Boolean root is proof authority. *)
signature COMMA_FRONTIER_M204_BELLMAN_PROPOSAL =
sig
  type arena = Comma_CRT_MDD_Arena.arena
  type action_root = Comma_CRT_MDD_Arena.action_root
  type boolean_root = Comma_CRT_MDD_Arena.boolean_root
  type comparison = {cid:int, label:int, left:int, right:int, result:int, plus9:bool}
  type result =
    {arena:arena, roots:boolean_root list, d_roots:action_root list,
     step_roots:action_root list, shifted:action_root list,
     source_step_roots:action_root list,
     step_export:Comma_CRT_MDD_Arena.exported, step_imports:action_root list,
     comparisons:comparison list, bind_keys:Comma_CRT_MDD_Arena.bind_key list,
     equality_pair_states:int}
  val build: arena -> action_root list -> arena -> action_root list -> result
end

structure Comma_Frontier_M204_Bellman_Proposal:
  COMMA_FRONTIER_M204_BELLMAN_PROPOSAL =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Zip = Comma_Semantic_Future_Zip_Producer
  structure Pair_Table = Table
  (
    type key = int * int
    val ord = prod_ord int_ord int_ord
  )
  type arena = Arena.arena
  type action_root = Arena.action_root
  type boolean_root = Arena.boolean_root
  type comparison = {cid:int, label:int, left:int, right:int, result:int, plus9:bool}
  type result =
    {arena:arena, roots:boolean_root list, d_roots:action_root list,
     step_roots:action_root list, shifted:action_root list,
     source_step_roots:action_root list,
     step_export:Arena.exported, step_imports:action_root list,
     comparisons:comparison list, bind_keys:Arena.bind_key list,
     equality_pair_states:int}

  fun build d_arena source_d_roots step_arena source_step_roots =
    let
      val _ = if length source_d_roots=46 andalso length source_step_roots=46 then ()
        else error "M204 Bellman needs 46 ordered roots per input"
      val _ = if Arena.radices d_arena = [3,4,7,11] andalso
          Arena.radices step_arena = Arena.radices d_arena then ()
        else error "M204 Bellman input has the wrong CRT axes"
      val d_export = Arena.export_actions d_arena source_d_roots
      val step_export = Arena.export_actions step_arena source_step_roots
      val work = Arena.create (Arena.radices d_arena)
      val d_imports = Arena.import_action_table_with_roots work (#seeds d_export)
      val step_imports = Arena.import_action_table_with_roots work (#seeds step_export)
      val d_roots = map (fn i => List.nth (d_imports,i)) (#roots d_export)
      val step_roots = map (fn i => List.nth (step_imports,i)) (#roots step_export)
      val _ = List.app (fn root => List.app (fn value =>
        if 0 <= value andalso value <= 242 then ()
        else error "M204 semantic output exceeds the admitted bound")
        (Arena.action_support work root)) d_roots
      val shifted = map (fn root => Arena.shift_action work root 1) d_roots
      fun constant value = if value=0 then Arena.action_none work
        else Arena.action_some work (value-1)
      val terminals = map constant (0 upto 8)
      fun target label =
        if 1 <= label andalso label <= 46 then List.nth (shifted,label-1)
        else if 47 <= label andalso label <= 55 then List.nth (terminals,label-47)
        else error "M204 typed step has an invalid nonzero payload"
      fun labels root =
        let val values = Arena.action_support work root
            val _ = List.app (fn v => if 0 <= v andalso v <= 55 then ()
              else error "M204 typed step payload is out of range") values
        in filter (fn v => v<>0) values end
      val support = map labels step_roots
      val demands = maps I (map_index (fn (cid,values) => map
        (fn label => (cid,label,List.nth (d_roots,cid),target label)) values) support)
      val continue = filter (fn (_,label,_,_) => label<=46) demands
      val terminal = filter (fn (_,label,_,_) => label>46) demands
      fun zip rows combine = Zip.zip_roots work work (map #3 rows)
        work (map #4 rows) combine
      val continue_zip = zip continue (fn x => fn y => if x=y+9 then 1 else 0)
      val terminal_zip = zip terminal (fn x => fn y => if x=y then 1 else 0)
      val comparisons = Unsynchronized.ref Pair_Table.empty
      fun add plus9 ((cid,label,left,right),root) =
        let
          val item : comparison =
            {cid=cid,label=label,left=Arena.action_index work left,
             right=Arena.action_index work right,result=Arena.action_index work root,
             plus9=plus9}
          val _ = comparisons := Pair_Table.update ((cid,label),(root,item)) (!comparisons)
        in () end
      val _ = List.app (add true) (ListPair.zip (continue,#roots continue_zip))
      val _ = List.app (add false) (ListPair.zip (terminal,#roots terminal_zip))
      val fallback = Arena.boolean_false work
      fun one (cid,(step,values)) (completed,keys) =
        let
          fun entry label =
            (case Pair_Table.lookup (!comparisons) (cid,label) of
              SOME (root,_) => (label-1,Arena.action_as_boolean work root)
            | NONE => error "M204 comparison transcript is incomplete")
          val mapping = map entry values
          val result = Arena.bind_action_to_boolean work step fallback mapping
          val witness = Arena.bind_witness work
            (Arena.action_index work step,Arena.boolean_index work fallback,
              map (fn (label,root) => (label+1,Arena.boolean_index work root)) mapping)
        in (result::completed,#key witness::keys) end
      val (reversed,reversed_keys) = fold one
        (map_index I (ListPair.zip (step_roots,support))) ([],[])
      val roots = rev reversed
      val true_id = Arena.boolean_index work (Arena.boolean_true work)
      val _ = if List.all (fn root => Arena.boolean_index work root = true_id) roots
        then () else error "M204 candidate violates a Bellman equation"
    in {arena=work,roots=roots,d_roots=d_roots,step_roots=step_roots,shifted=shifted,
      source_step_roots=source_step_roots,
      step_export=step_export,step_imports=step_imports,
      comparisons=map (#2 o #2) (Pair_Table.dest (!comparisons)),
      bind_keys=rev reversed_keys,
      equality_pair_states= #pair_states continue_zip + #pair_states terminal_zip}:result end
end
