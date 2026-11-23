(* Untrusted MDD applications of already-interned semantic expressions.
   The shift is application data; it is not part of the expression ID.
   Every result and operation still needs the checked producer's theorems.
   An Entry chart is a one-hot core-value MDD; its child binding is an
   authenticated bind, never an ordered Boolean priority replay. *)
structure Comma_Direct_MDD_Proposal =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Guard_Import = Comma_Frontier24_MDD_Import_Certificates
  val natT = @{typ nat}
  type selector_step =
    {wanted: int, shifted: Arena.boolean_root, prior: Arena.action_root,
     chosen: Arena.action_root, after: Arena.action_root, key: Arena.bind_key}
  type selector_chart =
    {wanted: int list, root: Arena.action_root, steps: selector_step list,
     phase: Comma_Semantic_Phase_Selector.proposal option}
  type selector =
    {chart: selector_chart, key: Arena.bind_key,
     fallback: Arena.action_root}
  datatype application = Application of
    {expression: term, shift: int, root: Arena.action_root, step: step}
  and step = Terminal | Goto of application | Entry_One_Goto of application | Entry of entry_row list * selector
  withtype entry_row = {wanted: int, child: application}
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
      (* Only the core/shift/ordered wanted alphabet identifies the chart.
         No selected child root, source occurrence, or physical weight is
         allowed to enter this cache key. *)
      val charts = Unsynchronized.ref (Termtab.empty: selector_chart Termtab.table)
      val phase_charts = Comma_Semantic_Phase_Selector.make arena
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
      fun guard_chart core shift wanted =
        let
          val key = HOLogic.mk_prod (core,HOLogic.mk_prod
            (HOLogic.mk_number natT shift,
             HOLogic.mk_list natT (map (HOLogic.mk_number natT) wanted)))
        in case Termtab.lookup (!charts) key of
          SOME selected => selected
        | NONE =>
            let
              val empty = Arena.action_none arena
              fun one desired (prior_root,steps) =
                let
                  val selected_guard = #root (guard core desired)
                  val shifted = Arena.shift_boolean arena selected_guard shift
                  val chosen = Arena.action_some arena desired
                  (* The Boolean guard is treated as a two-label chart only
                     here; the certified bind law validates 0 and 1. *)
                  val after = Arena.select_boolean_action arena shifted chosen prior_root
                  val prior_id = Arena.action_index arena prior_root
                  val chosen_id = Arena.action_index arena chosen
                  val selected_id = Arena.boolean_index arena shifted
                  val binding = (selected_id,prior_id,
                    [(0,prior_id),(1,chosen_id)])
                  val step: selector_step =
                    {wanted=desired,shifted=shifted,prior=prior_root,chosen=chosen,
                     after=after,key=binding}
                in (after,step::steps) end
              val (root,reversed_steps) = fold_rev one wanted (empty,[])
              val selected: selector_chart =
                {wanted=wanted,root=root,steps=rev reversed_steps,phase=NONE}
              val _ = charts := Termtab.update (key,selected) (!charts)
            in selected end
        end
      fun chart core shift wanted =
        (case Comma_Semantic_Phase_Selector.propose phase_charts core shift wanted of
          NONE => guard_chart core shift wanted
        | SOME proposal =>
            {wanted=wanted,root= #root (#template proposal),steps=[],phase=SOME proposal}
              :selector_chart)

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
                          val child_app = apply child shift
                        in {wanted=wanted,child=child_app} end
                      val row_terms = HOLogic.dest_list rows
                      val labels = map (fn row =>
                        dest_nat "Entry wanted" (#1 (HOLogic.dest_prod row))) row_terms
                      val _ = if length labels = length (distinct (op =) labels) then ()
                        else error "Direct Entry has duplicate wanted values"
                      (* Chart construction and its identity precede child
                         application evaluation; children are *not* chart keys. *)
                      fun eligible () =
                        if ((core aconv @{term Comma_Core_1} andalso labels = [0]) orelse
                            (core aconv @{term Comma_Core_3} andalso labels = [1])) andalso
                            #supported_values computation core = labels then
                          (case row_terms of [row] =>
                            let
                              val (_,goto) = HOLogic.dest_prod row
                              val (head,args) = strip_comb (body goto)
                            in case (head,args) of
                              (Const (name,_),[child,delta]) =>
                                if name = @{const_name Comma_Direct_Goto} andalso
                                  dest_nat "Single Entry Goto delta" delta = 0
                                then SOME child else NONE
                            | _ => NONE end
                          | _ => NONE)
                        else NONE
                    in case eligible () of
                      SOME child => let val app = apply child shift
                        in (root app,Entry_One_Goto app) end
                    | NONE => let
                      val selected = chart core shift labels
                      val rows = map one row_terms
                      val binding = map (fn (row:entry_row) =>
                        (#wanted row + 1, Arena.action_index arena (root (#child row)))) rows
                      val key = (Arena.action_index arena (#root selected),
                        Arena.action_index arena fallback,binding)
                      val output = Arena.bind_action_to_action arena
                        (#root selected) fallback
                        (map (fn (row:entry_row) => (#wanted row + 1,root (#child row))) rows)
                      val selector: selector = {chart=selected,key=key,fallback=fallback}
                    in (output,Entry (rows,selector)) end
                    end
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
      applications= !application_count,hits= !application_hits,
      selector_charts=Termtab.size (!charts) + Termtab.size (!(#charts phase_charts)),
      phase_statistics=Comma_Semantic_Phase_Selector.statistics phase_charts} end
  fun build computation body class_expressions source_expressions =
    let val arena = Arena.create [3,4,7,11]
    in build_with computation body arena typed_terminal (Arena.action_none arena)
      class_expressions source_expressions end
end
