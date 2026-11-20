(* Untrusted MDD applications of already-interned semantic expressions.
   The shift is application data; it is not part of the expression ID.
   Every result and operation still needs the checked producer's theorems. *)
structure Comma_Direct_MDD_Proposal =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Guard_Import = Comma_Frontier24_MDD_Import_Certificates
  val natT = @{typ nat}
  datatype application = Application of
    {expression: term, shift: int, root: Arena.action_root, step: step}
  and step = Terminal | Goto of application | Entry of entry_row list * Arena.priority_key
  withtype entry_row =
    {wanted: int, guard: Arena.boolean_root, shifted: Arena.boolean_root,
     child: application}
  type guard = {core:term, wanted:int, root:Arena.boolean_root,
    source_nodes:term, source_root:int, source_seeds:Arena.seed_node list,
    arena_roots:Arena.boolean_root list, arena_nodes:int list}
  fun dest_nat label term = Utils.dest_nat label natT term
  fun root (Application {root,...}) = root
  fun typed_terminal arena expression shift =
    let
      val (head,args) = strip_comb expression
      val name = (case head of Const (n,_) => n | _ => error "Malformed direct action")
    in
      if name = @{const_name Comma_Direct_Invalid} andalso null args then
        SOME (Arena.action_none arena)
      else if name = @{const_name Comma_Direct_Continue} then
        (case args of [target,delta] =>
          let val target = dest_nat "Continue class" target
              val delta = dest_nat "Continue delta" delta
          in SOME (if (shift+delta) mod 924 = 1 then Arena.action_some arena target
            else Arena.action_none arena) end
        | _ => error "Malformed direct Continue")
      else if name = @{const_name Comma_Direct_Fork} then
        (case args of [digit,delta] =>
          let val digit = dest_nat "Fork digit" digit
              val delta = dest_nat "Fork delta" delta
          in SOME (if 2 <= digit andalso digit <= 9 andalso shift+delta = 0 then
            Arena.action_some arena (44+digit) else Arena.action_none arena) end
        | _ => error "Malformed direct Fork")
      else if name = @{const_name Comma_Direct_Landmine} then
        (case args of [delta] => SOME (if shift + dest_nat "Landmine delta" delta = 0
          then Arena.action_some arena 54 else Arena.action_none arena)
        | _ => error "Malformed direct Landmine")
      else NONE
    end
  fun build_with (computation: Comma_Frontier24_Parametric_Compiler.computation) body
      arena terminal fallback class_expressions source_expressions =
    let
      val _ = if Arena.radices arena = [3,4,7,11] then ()
        else error "Direct MDD application has wrong CRT axes"
      val guards = Unsynchronized.ref (Termtab.empty: guard Termtab.table)
      val applications = Unsynchronized.ref (Termtab.empty: application Termtab.table)
      val application_count = Unsynchronized.ref 0
      val application_hits = Unsynchronized.ref 0
      fun guard core wanted =
        let val key = HOLogic.mk_prod (core,HOLogic.mk_number natT wanted)
        in case Termtab.lookup (!guards) key of
          SOME result => result
        | NONE =>
            let
              val (seeds,index) = #guard_table computation core wanted
              val _ = if 0 <= index andalso index < length seeds then ()
                else error "Direct guard root outside source table"
              val roots = Arena.import_boolean_guard_table_with_roots arena seeds
              val source_nodes = HOLogic.mk_list @{typ "bool comma_crt_mdd_node"}
                (map Guard_Import.source_node_term seeds)
              val result = {core=core,wanted=wanted,root=List.nth (roots,index),
                source_nodes=source_nodes,source_root=index,source_seeds=seeds,
                arena_roots=roots,arena_nodes=map (Arena.boolean_index arena) roots}
              val _ = guards := Termtab.update (key,result) (!guards)
            in result end
        end
      fun apply expression shift =
        let
          val _ = if shift >= 0 then () else error "Negative direct action shift"
          val key = HOLogic.mk_prod (expression,HOLogic.mk_number natT shift)
        in case Termtab.lookup (!applications) key of
          SOME result => (application_hits := !application_hits + 1; result)
        | NONE =>
            let
              val (head,args) = strip_comb (body expression)
              val name = (case head of Const (n,_) => n | _ => error "Malformed direct action")
              val (output,step) =
                (case terminal arena (body expression) shift of
                  SOME output => (output,Terminal)
                | NONE => if name = @{const_name Comma_Direct_Goto} then
                  (case args of [child,delta] =>
                    let val child_app = apply child (shift + dest_nat "Goto delta" delta)
                    in (root child_app,Goto child_app) end
                  | _ => error "Malformed direct Goto")
                else if name = @{const_name Comma_Direct_Entry} then
                  (case args of [core,rows] =>
                    let
                      fun one row =
                        let
                          val (wanted,child) = HOLogic.dest_prod row
                          val wanted = dest_nat "Entry wanted" wanted
                          val guard_root = #root (guard core wanted)
                          val shifted = Arena.shift_boolean arena guard_root shift
                          val child_app = apply child shift
                        in {wanted=wanted,guard=guard_root,shifted=shifted,child=child_app} end
                      val rows = map one (HOLogic.dest_list rows)
                      val labels = map (fn (row:entry_row) => #wanted row) rows
                      val _ = if length labels = length (distinct (op =) labels) then ()
                        else error "Direct Entry has duplicate wanted values"
                      val (output,key) = Arena.priority_select arena
                        (map (fn (row: entry_row) => (#shifted row,root (#child row))) rows)
                        fallback
                    in (output,Entry (rows,key)) end
                  | _ => error "Malformed direct Entry")
                else error "Unknown direct action expression")
              val result = Application {expression=expression,shift=shift,root=output,step=step}
              val _ = application_count := !application_count + 1
              val _ = applications := Termtab.update (key,result) (!applications)
            in result end
        end
      val classes = map (fn expression => apply expression 0) class_expressions
      val sources = map (fn expression => apply expression 0) source_expressions
    in {arena=arena,classes=classes,sources=sources,guards=map #2 (Termtab.dest (!guards)),
      applications= !application_count,hits= !application_hits} end
  fun build computation body class_expressions source_expressions =
    let val arena = Arena.create [3,4,7,11]
    in build_with computation body arena typed_terminal (Arena.action_none arena)
      class_expressions source_expressions end
end
