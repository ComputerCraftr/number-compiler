(* Named semantic expression definitions share every child before any MDD
   application or proof request is constructed. *)
structure Comma_Direct_Expression_Names =
struct
  structure Utils = Comma_CRT_MDD_Proof_Utils
  type state = {target:local_theory, expressions:term Termtab.table,
    definitions:(term * thm) Termtab.table, bodies:term Termtab.table,
    ordered:term list, next_id:int, sealed:bool}
  fun make prefix lthy =
    let
      val naming = Local_Theory.background_naming_of lthy
        |> Name_Space.transform_naming (Proof_Context.naming_of (Local_Theory.target_of lthy))
      val state = Unsynchronized.ref
        ({target=lthy,expressions=Termtab.empty,definitions=Termtab.empty,
          bodies=Termtab.empty,ordered=[],next_id=0,sealed=false}:state)
      val hits = Unsynchronized.ref 0
      val started = Time.now ()
      fun named child = Termtab.defined (#bodies (!state)) child
      fun validate expression =
        let
          val _ = if Utils.closed expression andalso
              fastype_of expression = @{typ comma_direct_action_expression} then ()
            else error "Direct expression body must be closed and well typed"
          val (head,args) = strip_comb expression
          val name = (case head of Const (n,_) => n | _ => error "Malformed direct expression body")
          fun numbers terms = List.all (fn term => fastype_of term = @{typ nat}) terms
          val valid =
            if name = @{const_name Comma_Direct_Invalid} then null args
            else if name = @{const_name Comma_Direct_Continue} orelse
                name = @{const_name Comma_Direct_Fork} then length args = 2 andalso numbers args
            else if name = @{const_name Comma_Direct_Landmine} then length args = 1 andalso numbers args
            else if name = @{const_name Comma_Direct_Goto} then
              (case args of [child,delta] => named child andalso numbers [delta] | _ => false)
            else if name = @{const_name Comma_Direct_Entry} then
              (case args of [core,rows] => fastype_of core = @{typ comma_phase_core_id} andalso
                List.all (fn row => let val (wanted,child) = HOLogic.dest_prod row
                  in numbers [wanted] andalso named child end) (HOLogic.dest_list rows)
                | _ => false)
            else false
        in if valid then () else error "Direct expression has an invalid or foreign child" end
      fun intern expression =
        (if #sealed (!state) then error "Direct expression owner is sealed" else ();
         validate expression;
         case Termtab.lookup (#expressions (!state)) expression of
          SOME name => (hits := !hits + 1; name)
        | NONE =>
            let
              val old = !state
              val id = #next_id old
              val _ = if id mod 64 = 0 then Comma_Proof_Profile.report
                ("Direct expression naming start=" ^ Int.toString id ^
                 " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started) else ()
              val base = prefix ^ "_" ^ Int.toString id
              val name = Const (Name_Space.full_name naming (Binding.name base),
                @{typ comma_direct_action_expression})
              val _ = if Termtab.defined (#bodies old) name then
                error "Direct expression name collision" else ()
              val updated = {target= #target old,
                expressions=Termtab.update (expression,name) (#expressions old),
                definitions= #definitions old,
                bodies=Termtab.update (name,expression) (#bodies old),
                ordered=name :: #ordered old,next_id=id+1,sealed=false}:state
              val _ = state := updated
              val _ = if (id+1) mod 64 = 0 then Comma_Proof_Profile.report
                ("Direct expression naming completed=" ^ Int.toString (id+1) ^
                 " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started) else ()
            in name end)
      fun definition name =
        (if #sealed (!state) then () else error "Direct expression owner is not published";
         case Termtab.lookup (#definitions (!state)) name of
          NONE => error "Unknown direct expression owner"
        | SOME (body,theorem) => Utils.exact_prop (Local_Theory.target_of (#target (!state)))
            "Direct expression definition" (Logic.mk_equals (name,body)) theorem)
      fun body name =
        let val theorem = definition name
        in Thm.term_of (Thm.rhs_of theorem) end
    in {intern=intern,body=body,definition=definition,
      expressions=fn () => rev (#ordered (!state)),hits=fn () => !hits,
      finish=fn () =>
        if #sealed (!state) then error "Direct expression owner is sealed" else
          let
            val old = !state
            val names = rev (#ordered old)
            fun publish name (facts,thy) =
              let
                val body = (case Termtab.lookup (#bodies old) name of SOME value => value
                  | NONE => error "Direct expression body is missing")
                val base = (case name of Const (full,_) => Long_Name.base_name full
                  | _ => error "Direct expression name is not a constant")
                val (declared,thy1) = Sign.declare_const_global
                  ((Binding.name base,@{typ comma_direct_action_expression}),NoSyn) thy
                val _ = if declared aconv name then () else
                  error "Direct expression background naming changed"
                val (definition,thy2) = Global_Theory.add_def
                  (Binding.name (base ^ "_def"),Logic.mk_equals (declared,body)) thy1
              in ((name,(body,definition))::facts,thy2) end
            val (facts,lthy') = Local_Theory.background_theory_result
              (fn thy => fold publish names ([],thy)) (#target old)
            val ctxt = Local_Theory.target_of lthy'
            val _ = List.app (fn (name,(body,theorem)) =>
              ignore (Utils.exact_prop ctxt "Published direct expression definition"
                (Logic.mk_equals (name,body)) theorem)) facts
            val updated = {target=lthy',expressions= #expressions old,
              definitions=fold Termtab.update facts Termtab.empty,bodies= #bodies old,
              ordered= #ordered old,next_id= #next_id old,sealed=true}:state
            val _ = state := updated
          in lthy' end} end
end

(* Untrusted structural operator proposals.  This pass creates no masks,
   MDD roots, or proof authority.  Physical sources occur only in the binding
   requests; the interned expressions contain semantic actions and guards. *)
structure Comma_Direct_Action_Proposal =
struct
  structure Compiler = Comma_Frontier24_Parametric_Compiler
  structure Runtime = Comma_Frontier24_Parametric_Runtime
  structure Utils = Comma_CRT_MDD_Proof_Utils
  val natT = @{typ nat}
  val expressionT = @{typ comma_direct_action_expression}
  val rowT = HOLogic.mk_prodT (natT,expressionT)
  fun nat n = if n < 0 then error "Negative direct action parameter"
    else HOLogic.mk_number natT n
  fun make name args = list_comb (Const (name,
    fold_rev (curry (op -->)) (map fastype_of args) expressionT),args)
  fun invalid () = @{term Comma_Direct_Invalid}
  fun build_selected prefix (computation: Compiler.computation) class_ids physical_sources lthy =
    let
      val names = Comma_Direct_Expression_Names.make prefix lthy
      val intern = #intern names
      val body = #body names
      val definition = #definition names
      val program_proposals = Unsynchronized.ref (Termtab.empty: term Termtab.table)
      val action_proposals = Unsynchronized.ref (Termtab.empty: term Termtab.table)
      val active = Unsynchronized.ref ([]: term list)
      fun exit_expression source delta =
        (case strip_comb source of
          (Const (name,_),[_,source_delta,_]) =>
            if name = @{const_name Comma_Entry} then
              let
                val total = Utils.dest_nat "Exit source delta" natT source_delta + delta
                val probe = (1 - (total mod 924) + 924) mod 924
                val code = #exit_code computation source (delta + probe)
              in if code = 0 then invalid ()
                 else if 1 <= code andalso code <= 46 then
                   make @{const_name Comma_Direct_Continue} [nat (code-1),nat total]
                 else error "Exit proposal has an invalid class code" end
            else invalid ()
        | _ => invalid ())
      fun expression_for_action action =
        (case Termtab.lookup (!action_proposals) action of
          SOME expression => expression
        | NONE => let val expression = intern (case Compiler.parse_action action of
          Compiler.Invalid => invalid ()
        | Compiler.Fork (digit,delta) =>
            make @{const_name Comma_Direct_Fork} [nat digit,nat delta]
        | Compiler.Landmine delta =>
            make @{const_name Comma_Direct_Landmine} [nat delta]
        | Compiler.Exit (source,delta) => exit_expression source delta
        | Compiler.Goto (source,delta) =>
            (case #source_program computation source of
              NONE => invalid ()
            | SOME program => make @{const_name Comma_Direct_Goto}
                [expression_for_program program,nat delta]))
            val _ = action_proposals := Termtab.update (action,expression) (!action_proposals)
          in expression end)
      and expression_for_program program =
        (case Termtab.lookup (!program_proposals) program of
          SOME expression => expression
        | NONE =>
            if exists (fn item => item aconv program) (!active) then
              error "Cyclic direct-action program proposal"
            else
              let
                val _ = if #program_admitted computation program then ()
                  else error "Direct-action program proposal is not admitted"
                val _ = active := program :: !active
                val expression = (case Compiler.parse_program program of
                    Compiler.Entry {sector,residue,core,...} =>
                      let
                        fun row wanted = HOLogic.mk_prod (nat wanted,
                          expression_for_action (#entry_action computation sector residue core wanted))
                        val rows = map row (#supported_values computation core)
                      in intern (make @{const_name Comma_Direct_Entry}
                        [core,HOLogic.mk_list rowT rows]) end
                  | _ => expression_for_action (#operator_action computation program))
                val _ = active := filter_out (fn item => item aconv program) (!active)
                val _ = program_proposals := Termtab.update (program,expression) (!program_proposals)
              in expression end)
      fun class_request cid =
        (case #class_program computation cid of
          SOME program => (cid,program,expression_for_program program)
        | NONE => error "Missing direct class program proposal")
      fun source_request source =
        (case #source_program computation source of
          SOME program => (source,program,expression_for_program program)
        | NONE => error "Missing direct physical source program proposal")
      val classes = map class_request class_ids
      val sources = map source_request physical_sources
    in ({classes=classes,sources=sources,expressions= #expressions names (),
      program_bindings=Termtab.dest (!program_proposals),
      action_bindings=Termtab.dest (!action_proposals),body=body,definition=definition,
      expression_hits= #hits names (),program_requests=Termtab.size (!program_proposals)},
      #finish names ()) end
  fun build_with_sources computation physical_sources lthy =
    build_selected "comma_direct_expression" computation (0 upto 45) physical_sources lthy
  fun build computation lthy = build_with_sources computation
    (Runtime.physical_initial_sources ()) lthy
end
