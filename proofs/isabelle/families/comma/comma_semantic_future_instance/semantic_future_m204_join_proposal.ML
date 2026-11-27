(* Untrusted source/weight composition.  Every import, shift, zip, guard and
   selection must subsequently be replayed in the receiving theory. *)
structure Comma_Future_M204_Join_Proposal =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Zip = Comma_Semantic_Future_Zip_Producer
  structure Pair_Table = Table
  (
    type key = int * int
    val ord = prod_ord int_ord int_ord
  )

  type selection = {guard: int, yes: int, no: int, output: int}
  type mask = {source: int, label: int, output: int}
  type shift = {source: int, amount: int, output: int}
  type zip = {left: int, right: int, output: int, add: int}
  type mapped_weight = {source: int, output: int, amount: int, add: int}
  datatype fold_stage = Source | Child_N | Child_Z
  type fold_step = {stage: fold_stage, source: int, label: int,
    guard: int, yes: int, no: int, output: int}
  type result = {arena: Arena.arena, outputs: Arena.action_root list,
    children_n: Arena.action_root list, children_z: Arena.action_root list,
    source_export: Arena.exported, weight_export: Arena.exported, class_export: Arena.exported,
    sources: Arena.action_root list, weights: Arena.action_root list, classes: Arena.action_root list,
    class_import_equalities: Arena.action_root list,
    masks: mask list, selections: selection list, shifts: shift list, zips: zip list,
    mapped_weights: mapped_weight list,
    fold_steps: fold_step list}

  fun build source_arena source_roots weight_arena weight_roots class_arena class_roots : result =
    let
      val axes = [3,4,7,11]
      val _ = if Arena.radices source_arena = axes andalso Arena.radices weight_arena = axes
          andalso Arena.radices class_arena = axes then ()
        else error "Future join inputs have incompatible CRT axes"
      val _ = if length source_roots=16 andalso length weight_roots=46 andalso
          length class_roots=16 then () else error "Future join has wrong root counts"
      val work = Arena.create_periodic axes
      fun import arena roots =
        let val export = Arena.export_actions arena roots
            val imported = Arena.import_action_table_with_roots work (#seeds export)
        in (export,map (fn i => List.nth (imported,i)) (#roots export)) end
      val (source_export,sources) = import source_arena source_roots
      val (weight_export,weights) = import weight_arena weight_roots
      val (class_export,classes) = import class_arena class_roots
      val class_import_equalities = #roots
        (Zip.zip_roots work class_arena class_roots work classes
          (fn left => fn right => if left=right then 1 else 0))
      val _ = if length class_import_equalities = 16 andalso
          List.all (fn root => Arena.action_support work root = [1]) class_import_equalities
        then () else error "Future class import proposal differs from its source"
      val masks = Unsynchronized.ref ([]: mask list)
      val selections = Unsynchronized.ref ([]: selection list)
      val shifts = Unsynchronized.ref ([]: shift list)
      val zips = Unsynchronized.ref ([]: zip list)
      val mapped_weights = Unsynchronized.ref ([]: mapped_weight list)
      (* One traversal shifts the phase and adds the Future-specific +10.
         This is deliberately not the Bellman +9 encoding. *)
      val shifted_weight_map = Arena.make_action_shift_map work (Arena.Shift_Add 10)
      val fold_steps = Unsynchronized.ref ([]: fold_step list)
      val shift_cache = Unsynchronized.ref Pair_Table.empty
      val mask_cache = Unsynchronized.ref Pair_Table.empty
      val output_cache = Unsynchronized.ref Inttab.empty
      val child_cache = Unsynchronized.ref Pair_Table.empty
      fun ai root = Arena.action_index work root
      fun bi root = Arena.boolean_index work root
      fun shift 0 root = root
        | shift amount root =
        let val key = (ai root,amount)
        in case Pair_Table.lookup (!shift_cache) key of
          SOME out => out
        | NONE =>
            let val out = Arena.shift_action work root amount
                val _ = shifts := {source=ai root,amount=amount,output=ai out} :: !shifts
                val _ = shift_cache := Pair_Table.update (key,out) (!shift_cache)
            in out end
        end
      val zero = Arena.action_none work
      val false_root = Arena.boolean_false work
      val true_root = Arena.boolean_true work
      fun constant n = if n=0 then zero else Arena.action_some work (n-1)
      fun mask root label =
        let val key = (ai root,label)
            val _ = if label>0 then () else error "Cannot select invalid source payload"
        in case Pair_Table.lookup (!mask_cache) key of
          SOME out => out
        | NONE =>
            let val out = Arena.bind_action_to_boolean work root false_root [(label-1,true_root)]
                val _ = masks := {source=ai root,label=label,output=bi out} :: !masks
                val _ = mask_cache := Pair_Table.update (key,out) (!mask_cache)
            in out end
        end
      fun select stage source label guard yes no =
        let val out = Arena.select_boolean_action work guard yes no
            val _ = selections := {guard=bi guard,yes=ai yes,no=ai no,output=ai out} :: !selections
            val _ = fold_steps := {stage=stage,source=ai source,label=label,
              guard=bi guard,yes=ai yes,no=ai no,output=ai out} :: !fold_steps
        in out end
      fun add n root =
        let
          val right = zero
          val zipped = Zip.zip_roots work work [root] work [right] (fn x => fn _ => x+n)
          val out = (case #roots zipped of [one] => one | _ => error "Future zip arity")
          val _ = zips := {left=ai root,right=ai right,output=ai out,add=n} :: !zips
        in out end
      val weight_cache = Unsynchronized.ref Inttab.empty
      val class_cache = Unsynchronized.ref Inttab.empty
      fun demanded cache make index =
        (case Inttab.lookup (!cache) index of
          SOME root => root
        | NONE => let val root = make index
            val _ = cache := Inttab.update (index,root) (!cache)
          in root end)
      fun shifted_weight index = demanded weight_cache (fn i =>
        let val source = List.nth (weights,i)
            val out = Arena.shift_map_action shifted_weight_map source 1
            val _ = mapped_weights := {source=ai source, output=ai out,
              amount=1, add=10} :: !mapped_weights
        in out end) index
      fun normalized_class index = demanded class_cache
        (fn i => add 1 (List.nth (classes,i))) index
      fun source_output root =
        (case Inttab.lookup (!output_cache) (ai root) of SOME out => out | NONE => let
          fun add_label label tail =
            if label=0 then tail
            else if label<=46 then select Source root label (mask root label)
              (shifted_weight (label-1)) tail
            else if label<=55 then select Source root label (mask root label) (constant (label-46)) tail
            else error "Future source action payload is outside its typed range"
            val out = fold add_label (Arena.action_support work root) zero
            val _ = output_cache := Inttab.update (ai root,out) (!output_cache)
        in out end)
      val outputs = map source_output sources
      fun child want_z root =
        let val key = (ai root,if want_z then 1 else 0)
        in case Pair_Table.lookup (!child_cache) key of SOME out => out | NONE => let
          fun add_label label tail =
            if label=0 then tail else
              let
                val value = label-1
                val digit = value mod 9
                val delta = value div 9
                val _ = if delta<=27 then () else error "Future exponent shift exceeds B32 bound"
              in if digit=8 then tail else
                let val family = digit + (if want_z then 8 else 0)
                    val shifted = shift delta (normalized_class family)
                in select (if want_z then Child_Z else Child_N) root label
                  (mask root label) shifted tail end end
            val out = fold add_label (Arena.action_support work root) zero
            val _ = child_cache := Pair_Table.update (key,out) (!child_cache)
        in out end end
    in {arena=work,source_export=source_export,weight_export=weight_export,
      class_export=class_export,sources=sources,weights=weights,classes=classes,
      class_import_equalities=class_import_equalities,
      outputs=outputs,children_n=map (child false) outputs,
      children_z=map (child true) outputs,masks=List.rev (!masks),
      selections=List.rev (!selections),shifts=List.rev (!shifts),zips=List.rev (!zips),
      mapped_weights=List.rev (!mapped_weights),
      fold_steps=List.rev (!fold_steps)} end
end
