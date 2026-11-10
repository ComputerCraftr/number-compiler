(* Data-only producer for the quotient-first Frontier24
   Continue MDD.  It computes 46 top-level roots from canonical class programs;
   every table/root/reference remains untrusted until the generic HOL checker
   validates the complete guard, bind, and full-shift closure bundle. *)

signature COMMA_FRONTIER24_PARAMETRIC_COMPILER =
sig
  type arena = Comma_CRT_MDD_Arena.arena
  type computation =
    {class_program: int -> term option,
     source_program: term -> term option,
     program_admitted: term -> bool,
     supported_values: term -> int list,
     core_modulus: term -> int,
     guard_table: term -> int -> Comma_CRT_MDD_Arena.seed_node list * int,
     entry_action: int -> int -> term -> int -> term,
     operator_action: term -> term,
     exit_code: term -> int -> int}
  type selector_case =
    {wanted: int, guard_root: Comma_CRT_MDD_Arena.boolean_root,
     action_token: int}
  datatype selector_recipe =
      Near_Selector of {token: int}
    | Entry_Selector of
        {f: int, d: int, residue: int, core: term, cases: selector_case list}
  type closure_case =
    {wanted: int, guard_root: int, shifted_guard_root: int,
     action_token: int, action_output_root: int, selected_root: int,
     bind_key: Comma_CRT_MDD_Arena.bind_key,
     child_closure: int option}
  type closure =
    {program_ref: int, full_shift: int, cases: closure_case list,
     near_token: int option, near_action_output_root: int option,
     near_child_closure: int option, output_root: int}
  type guard_entry =
    {core: term, wanted: int, root: int, source_nodes: term, source_root: int,
     source_seeds: Comma_CRT_MDD_Arena.seed_node list,
     arena_roots: Comma_CRT_MDD_Arena.boolean_root list, arena_nodes: int list}
  type result
  val compile: Proof.context -> computation -> result
  val arena: result -> arena
  val programs: result -> term list
  val selectors: result -> selector_recipe list
  val action_tokens: result -> term list
  val guard_entries: result -> guard_entry list
  val closures: result -> closure list
  val class_program_refs: result -> int list
  val class_roots: result -> Comma_CRT_MDD_Arena.action_root list
  val bind_keys: result -> Comma_CRT_MDD_Arena.bind_key list
  val statistics: result -> string
end

structure Comma_Frontier24_Parametric_Compiler:
  COMMA_FRONTIER24_PARAMETRIC_COMPILER =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Proposal = Comma_Frontier24_MDD_Proposal

  type arena = Arena.arena
  type computation =
    {class_program: int -> term option,
     source_program: term -> term option,
     program_admitted: term -> bool,
     supported_values: term -> int list,
     core_modulus: term -> int,
     guard_table: term -> int -> Arena.seed_node list * int,
     entry_action: int -> int -> term -> int -> term,
     operator_action: term -> term,
     exit_code: term -> int -> int}
  type selector_case =
    {wanted: int, guard_root: Arena.boolean_root, action_token: int}
  datatype selector_recipe =
      Near_Selector of {token: int}
    | Entry_Selector of
        {f: int, d: int, residue: int, core: term, cases: selector_case list}
  type closure_case =
    {wanted: int, guard_root: int, shifted_guard_root: int,
     action_token: int, action_output_root: int, selected_root: int,
     bind_key: Arena.bind_key, child_closure: int option}
  type closure =
    {program_ref: int, full_shift: int, cases: closure_case list,
     near_token: int option, near_action_output_root: int option,
     near_child_closure: int option, output_root: int}
  type guard_entry =
    {core: term, wanted: int, root: int, source_nodes: term, source_root: int,
     source_seeds: Arena.seed_node list,
     arena_roots: Arena.boolean_root list, arena_nodes: int list}
  type result =
    {arena: arena, programs: term list, selectors: selector_recipe list,
     action_tokens: term list, guard_entries: guard_entry list,
     closures: closure list, class_program_refs: int list,
     class_roots: Arena.action_root list, bind_keys: Arena.bind_key list,
     statistics: string}

  val natT = @{typ nat}
  val programT = @{typ comma_semantic_port_program}
  val actionT = @{typ comma_source_continuation_action}
  val source_nodeT = @{typ "bool comma_crt_mdd_node"}
  val closed = Comma_CRT_MDD_Proof_Utils.closed

  fun nat n = HOLogic.mk_number natT n
  fun source_node_term (Arena.Seed_Leaf 0) =
        Const (@{const_name Comma_CRT_MDD_Leaf}, @{typ "bool => bool comma_crt_mdd_node"}) $
          @{term False}
    | source_node_term (Arena.Seed_Leaf 1) =
        Const (@{const_name Comma_CRT_MDD_Leaf}, @{typ "bool => bool comma_crt_mdd_node"}) $
          @{term True}
    | source_node_term (Arena.Seed_Leaf _) =
        error "Guard source table has a non-Boolean leaf"
    | source_node_term (Arena.Seed_Branch (axis,children)) =
        Const (@{const_name Comma_CRT_MDD_Branch},
          @{typ "nat => nat list => bool comma_crt_mdd_node"}) $
          nat axis $ HOLogic.mk_list natT (map nat children)
  fun source_nodes_term seeds =
    HOLogic.mk_list source_nodeT (map source_node_term seeds)
  fun checked_int label term =
    Comma_CRT_MDD_Proof_Utils.dest_nat label natT term

  fun dest_program label term =
    if fastype_of term = programT andalso closed term then term
    else error (label ^ " is not a closed normalized program")

  fun dest_action label term =
    if fastype_of term = actionT andalso closed term then term
    else error (label ^ " is not a closed continuation action")

  type build_state =
    {ctxt: Proof.context, computation: computation,
     arena: arena,
     programs_rev: term list Unsynchronized.ref,
     program_count: int Unsynchronized.ref,
     program_ids: int Termtab.table Unsynchronized.ref,
     program_values: term Inttab.table Unsynchronized.ref,
     selectors_rev: selector_recipe list Unsynchronized.ref,
     selector_values: selector_recipe Inttab.table Unsynchronized.ref,
     actions_rev: term list Unsynchronized.ref,
     action_count: int Unsynchronized.ref,
     action_ids: int Termtab.table Unsynchronized.ref,
     action_values: term Inttab.table Unsynchronized.ref,
     guards_rev: guard_entry list Unsynchronized.ref,
     guard_roots: Arena.boolean_root Termtab.table Unsynchronized.ref,
     source_programs: term option Termtab.table Unsynchronized.ref,
     closures_rev: closure list Unsynchronized.ref,
     closure_count: int Unsynchronized.ref,
     closure_ids: int Termtab.table Unsynchronized.ref,
     closure_roots: Arena.action_root Termtab.table Unsynchronized.ref,
     active_closures: term list Unsynchronized.ref,
     bind_keys_rev: Arena.bind_key list Unsynchronized.ref,
     bind_key_ids: unit Termtab.table Unsynchronized.ref,
     class_requests: int Unsynchronized.ref,
     source_requests: int Unsynchronized.ref,
     guard_requests: int Unsynchronized.ref,
     action_requests: int Unsynchronized.ref,
     program_requests: int Unsynchronized.ref,
     closure_requests: int Unsynchronized.ref,
     closure_hits: int Unsynchronized.ref}

  datatype program_shape =
      Entry of {sector: int, digit: int, residue: int, core: term}
    | Near_Residual of {sector: int, digit: int, residual: int}
    | Near_Boundary of {sector: int}

  fun parse_program program =
    (case Term.strip_comb program of
      (Const (name, _), [f, d, residue, core]) =>
        if name = @{const_name Comma_Entry_Core_Program} then
          Entry {sector=checked_int "Entry sector" f,
            digit=checked_int "Entry digit" d,
            residue=checked_int "Entry residue" residue, core=core}
        else error "Unknown semantic program constructor"
    | (Const (name, _), [f, d, residual]) =>
        if name = @{const_name Comma_Near_Residual_Program} then
          Near_Residual {sector=checked_int "Near sector" f,
            digit=checked_int "Near digit" d,
            residual=checked_int "Near residual" residual}
        else error "Unknown semantic program constructor"
    | (Const (name, _), [f]) =>
        if name = @{const_name Comma_Near_Boundary_Program} then
          Near_Boundary {sector=checked_int "Boundary sector" f}
        else error "Unknown semantic program constructor"
    | _ => error "Malformed semantic program")

  datatype action_shape =
      Goto of term * int
    | Exit of term * int
    | Stop

  fun parse_action action =
    (case Term.strip_comb action of
      (Const (name, _), [source, delta]) =>
        if name = @{const_name Comma_Continuation_Goto} then
          Goto (source, checked_int "Goto delta" delta)
        else if name = @{const_name Comma_Continuation_Exit} then
          Exit (source, checked_int "Exit delta" delta)
        else if name = @{const_name Comma_Continuation_Fork} then
          Stop
        else error "Unknown binary continuation constructor"
    | (Const (name, _), [_]) =>
        if name = @{const_name Comma_Continuation_Landmine} then Stop
        else error "Unknown unary continuation constructor"
    | (Const (name, _), []) =>
        if name = @{const_name Comma_Continuation_Invalid} then Stop
        else error "Unknown nullary continuation constructor"
    | _ => error "Malformed continuation action")

  fun intern_bind_key (state: build_state) key =
    let
      val keys = #bind_keys_rev state
      val key_term =
        let
          val (source, fallback, mapping) = key
          val pairT = HOLogic.mk_prodT (natT, natT)
          val mappingT = HOLogic.listT pairT
          val mapping_term = HOLogic.mk_list pairT
            (map (fn (a,b) => HOLogic.mk_prod (nat a, nat b)) mapping)
        in HOLogic.mk_prod (nat source,
          HOLogic.mk_prod (nat fallback, mapping_term)) end
      val old = Termtab.lookup (!(#bind_key_ids state)) key_term
    in
      (case old of SOME _ => ()
      | NONE => (#bind_key_ids state := Termtab.update (key_term, ())
          (!(#bind_key_ids state)); keys := key :: !keys))
    end

  fun selection_key arena guard yes no =
    let
      val source = Arena.boolean_index arena guard
      val fallback = Arena.action_index arena no
      val selected = Arena.action_index arena yes
      val witness = Arena.bind_witness arena
        (source, fallback, [(0, fallback), (1, selected)])
    in #key witness end

  fun import_guard (state: build_state) core wanted =
    let
      val {computation, arena, guards_rev, guard_roots, guard_requests, ...} = state
      val {guard_table, ...} = computation
      val key = HOLogic.mk_prod (core, nat wanted)
      val _ = guard_requests := !guard_requests + 1
    in
      (case Termtab.lookup (!guard_roots) key of
        SOME root => root
      | NONE =>
          let
            val (seeds, root_index) = guard_table core wanted
            val _ = if 0 <= root_index andalso root_index < length seeds then ()
              else error "Core guard root is outside its local node list"
            val arena_roots = Arena.import_boolean_guard_table_with_roots arena seeds
            val root = List.nth (arena_roots, root_index)
            val root_id = Arena.boolean_index arena root
            val entry: guard_entry =
              {core=core, wanted=wanted, root=root_id,
               source_nodes=source_nodes_term seeds, source_root=root_index,
               source_seeds=seeds, arena_roots=arena_roots,
               arena_nodes=map (Arena.boolean_index arena) arena_roots}
            val _ = guards_rev := entry :: !guards_rev
            val _ = guard_roots := Termtab.update (key, root) (!guard_roots)
          in root end)
    end

  fun intern_action (state: build_state) action =
    let
      val {action_ids, actions_rev, ...} = state
    in
      (case Termtab.lookup (!action_ids) action of
        SOME token => token
      | NONE =>
          let val token = !(#action_count state)
              val _ = #action_count state := token + 1
              val _ = actions_rev := action :: !actions_rev
              val _ = action_ids := Termtab.update (action, token) (!action_ids)
              val _ = #action_values state := Inttab.update
                (token, action) (!(#action_values state))
          in token end)
    end

  fun intern_program (state: build_state) program =
    let
      val {program_ids, programs_rev, selectors_rev, program_requests,
        computation, action_requests, ...} = state
      val {supported_values, core_modulus, entry_action, operator_action,
        program_admitted, ...} =
        computation
      val _ = program_requests := !program_requests + 1
    in
      (case Termtab.lookup (!program_ids) program of
        SOME reference => reference
      | NONE =>
          let
            val _ = if program_admitted program then ()
              else error "Parametric compiler rejected a structurally inadmissible program"
            val reference = !(#program_count state)
            val _ = #program_count state := reference + 1
            val _ = programs_rev := program :: !programs_rev
            val _ = program_ids := Termtab.update (program, reference) (!program_ids)
            val _ = #program_values state := Inttab.update
              (reference, program) (!(#program_values state))
            val selector = (case parse_program program of
              Entry {sector=f, digit=d, residue, core} =>
                let
                  val values = supported_values core
                  val modulus = core_modulus core
                  val _ = if distinct (op =) values = values andalso
                      forall (fn wanted => 0 <= wanted andalso wanted < modulus) values then ()
                    else error "Core supported-value domain is malformed"
                  fun one wanted : selector_case =
                    let
                      val guard = import_guard state core wanted
                      val _ = action_requests := !action_requests + 1
                      val action = dest_action "Entry selector action"
                        (entry_action f residue core wanted)
                      val token = intern_action state action
                    in {wanted=wanted, guard_root=guard, action_token=token} end
                  val cases = map one values
                in Entry_Selector {f=f,d=d,residue=residue,core=core,cases=cases} end
            | Near_Residual _ =>
                let
                  val _ = action_requests := !action_requests + 1
                  val action = dest_action "Near selector action"
                    (operator_action program)
                  val token = intern_action state action
                in Near_Selector {token=token} end
            | Near_Boundary _ =>
                let
                  val _ = action_requests := !action_requests + 1
                  val action = dest_action "Boundary selector action"
                    (operator_action program)
                  val token = intern_action state action
                in Near_Selector {token=token} end)
            val _ = selectors_rev := selector :: !selectors_rev
            val _ = #selector_values state := Inttab.update
              (reference, selector) (!(#selector_values state))
          in reference end)
    end

  fun source_program (state: build_state) source =
    let
      val {source_programs, computation, source_requests, ...} = state
      val {source_program=lookup, ...} = computation
      val _ = source_requests := !source_requests + 1
    in
      (case Termtab.lookup (!source_programs) source of
        SOME result => result
      | NONE =>
          let
            val result = Option.map (dest_program "Goto child program") (lookup source)
            val _ = source_programs := Termtab.update (source, result) (!source_programs)
          in result end)
    end

  fun exit_code (state: build_state) source full_shift =
    let
      val {computation, ...} = state
      val {exit_code=code, ...} = computation
    in code source full_shift end

  fun closure_key program_ref full_shift =
    HOLogic.mk_prod (nat program_ref, nat full_shift)

  fun build (state: build_state) =
    let
      val {arena, closures_rev, closure_ids, active_closures,
        computation, class_requests, ...} = state
      val {class_program, ...} = computation
      fun program_at reference =
        (case Inttab.lookup (!(#program_values state)) reference of
          SOME program => program
        | NONE => error "Program reference is outside the canonical table")
      fun selector_at reference =
        (case Inttab.lookup (!(#selector_values state)) reference of
          SOME selector => selector
        | NONE => error "Selector recipe is outside the canonical table")

      fun program_sector program =
        (case parse_program program of
          Entry {sector, ...} => sector
        | Near_Residual {sector, ...} => sector
        | Near_Boundary {sector} => sector)

      fun compile_token parent full_shift token =
        let
          val action = (case Inttab.lookup (!(#action_values state)) token of
            SOME value => value
          | NONE => error "Action-token reference is outside the canonical table")
        in
          (case parse_action action of
            Stop => {root=Arena.action_none arena, child=NONE}
          | Exit (source, delta) =>
              (case exit_code state source (full_shift+delta) of
                0 => {root=Arena.action_none arena, child=NONE}
              | encoded =>
                  if encoded > 0 then
                    {root=Arena.action_some arena (encoded - 1), child=NONE}
                  else error "Exit action produced a negative Continue code")
          | Goto (source, delta) =>
              (case source_program state source of
                NONE => {root=Arena.action_none arena, child=NONE}
              | SOME child_program =>
                  let
                    val child_sector = program_sector child_program
                    val parent_sector = program_sector (program_at parent)
                  in
                    if parent_sector < child_sector andalso child_sector <= 9 then
                      let
                        val child_ref = intern_program state child_program
                        val (child_closure, child_root) =
                          compile_full child_ref (full_shift+delta)
                      in {root=child_root, child=SOME child_closure} end
                    else {root=Arena.action_none arena, child=NONE}
                  end))
        end

      and compile_full program_ref full_shift =
        let
          val key = closure_key program_ref full_shift
          val _ = #closure_requests state := !(#closure_requests state) + 1
        in
          (case Termtab.lookup (!closure_ids) key of
            SOME reference =>
              let
                val _ = #closure_hits state := !(#closure_hits state) + 1
              in
                (case Termtab.lookup (!(#closure_roots state)) key of
                  SOME root => (reference, root)
                | NONE => error "Cached closure root handle is missing")
              end
          | NONE =>
              if exists (fn active => active aconv key) (!active_closures) then
                error "Semantic program/Goto closure contains a cycle"
              else
                let
                  val _ = active_closures := key :: !active_closures
                  val selector = selector_at program_ref
                  val (root, cases, near_token, near_action_output_root,
                    near_child_closure) =
                    (case selector of
                      Near_Selector {token} =>
                        let val action=compile_token program_ref full_shift token
                            val root = #root action
                        in (root, [], SOME token,
                          SOME (Arena.action_index arena root), #child action) end
                    | Entry_Selector {f,d,residue,core,cases=selector_cases} =>
                        let
                          fun add_case (selector_case: selector_case)
                              (fallback, steps_rev) =
                            let
                              val shifted_guard = Arena.shift_boolean arena
                                (#guard_root selector_case) full_shift
                              val action = compile_token program_ref full_shift
                                (#action_token selector_case)
                              val selected = Arena.select_boolean_action arena
                                shifted_guard (#root action) fallback
                              val key' = selection_key arena shifted_guard
                                (#root action) fallback
                              val _ = intern_bind_key state key'
                              val step: closure_case =
                                {wanted= #wanted selector_case,
                                 guard_root=Arena.boolean_index arena
                                   (#guard_root selector_case),
                                 shifted_guard_root=Arena.boolean_index arena shifted_guard,
                                 action_token= #action_token selector_case,
                                 action_output_root=Arena.action_index arena (#root action),
                                 selected_root=Arena.action_index arena selected,
                                 bind_key=key', child_closure= #child action}
                            in (selected, step::steps_rev) end
                          val (root, steps) = fold_rev add_case selector_cases
                            (Arena.action_none arena, [])
                        in (root, steps, NONE, NONE, NONE) end)
                  val _ = active_closures := filter (fn active => not (active aconv key))
                    (!active_closures)
                  val closure_ref = !(#closure_count state)
                  val closure: closure =
                    {program_ref=program_ref, full_shift=full_shift,
                     cases=cases, near_token=near_token,
                     near_action_output_root=near_action_output_root,
                     near_child_closure=near_child_closure,
                     output_root=Arena.action_index arena root}
                  val _ = closures_rev := closure :: !closures_rev
                  val _ = #closure_count state := closure_ref + 1
                  val _ = #closure_roots state := Termtab.update
                    (key, root) (!(#closure_roots state))
                  val _ = closure_ids := Termtab.update (key, closure_ref) (!closure_ids)
                in (closure_ref, root) end)
        end

      val class_refs = map (fn cid =>
        let
          val _ = class_requests := !class_requests + 1
          val program = (case class_program cid of
            SOME candidate => dest_program "Canonical class program" candidate
          | NONE => error "Class domain contains an unavailable program")
        in intern_program state program end) (0 upto 45)
      val class_roots = map (fn reference => #2 (compile_full reference 0)) class_refs
      val stats = Arena.statistics arena ^
        " canonical_programs=" ^ Int.toString (length (!(#programs_rev state))) ^
        " selector_cases=" ^ Int.toString (fold (fn recipe => fn n => n +
          (case recipe of Near_Selector _ => 0 | Entry_Selector {cases,...} => length cases))
          (!(#selectors_rev state)) 0) ^
        " unique_action_tokens=" ^ Int.toString (length (!(#actions_rev state))) ^
        " core_guard_roots=" ^ Int.toString (length (!(#guards_rev state))) ^
        " closure_applications=" ^ Int.toString (!(#closure_count state)) ^
        " closure_requests=" ^ Int.toString (!(#closure_requests state)) ^
        " closure_cache_hits=" ^ Int.toString (!(#closure_hits state)) ^
        " unique_bind_keys=" ^ Int.toString (length (!(#bind_keys_rev state))) ^
        " program_lookup_requests=" ^ Int.toString (!(#program_requests state)) ^
        " class_program_queries=" ^ Int.toString (!(#class_requests state)) ^
        " source_program_queries=" ^ Int.toString (!(#source_requests state)) ^
        " guard_queries=" ^ Int.toString (!(#guard_requests state)) ^
        " action_queries=" ^ Int.toString (!(#action_requests state)) ^
        " class_roots=46"
      val _ = if length class_refs = 46 andalso length class_roots = 46 then ()
        else error "Parametric compiler did not publish 46 class roots"
    in
      {class_program_refs=class_refs, class_roots=class_roots, statistics=stats}
    end

  fun compile ctxt computation : result =
    let
      val arena = Proposal.new_arena ()
      val state: build_state =
        {ctxt=ctxt, computation=computation,
         arena=arena, programs_rev=Unsynchronized.ref [], program_count=Unsynchronized.ref 0,
         program_ids=Unsynchronized.ref Termtab.empty,
         program_values=Unsynchronized.ref Inttab.empty,
         selectors_rev=Unsynchronized.ref [],
         selector_values=Unsynchronized.ref Inttab.empty,
         actions_rev=Unsynchronized.ref [], action_count=Unsynchronized.ref 0,
         action_ids=Unsynchronized.ref Termtab.empty,
         action_values=Unsynchronized.ref Inttab.empty,
         guards_rev=Unsynchronized.ref [],
        guard_roots=Unsynchronized.ref Termtab.empty,
         source_programs=Unsynchronized.ref Termtab.empty,
         closures_rev=Unsynchronized.ref [], closure_count=Unsynchronized.ref 0,
         closure_ids=Unsynchronized.ref Termtab.empty,
         closure_roots=Unsynchronized.ref Termtab.empty,
         active_closures=Unsynchronized.ref [], bind_keys_rev=Unsynchronized.ref [],
         bind_key_ids=Unsynchronized.ref Termtab.empty,
         class_requests=Unsynchronized.ref 0,
         source_requests=Unsynchronized.ref 0,
         guard_requests=Unsynchronized.ref 0,
         action_requests=Unsynchronized.ref 0,
         program_requests=Unsynchronized.ref 0,
         closure_requests=Unsynchronized.ref 0, closure_hits=Unsynchronized.ref 0}
      val {class_program_refs,class_roots,statistics} = build state
    in {arena=arena, programs=List.rev (!(#programs_rev state)),
        selectors=List.rev (!(#selectors_rev state)),
        action_tokens=List.rev (!(#actions_rev state)),
        guard_entries=List.rev (!(#guards_rev state)),
        closures=List.rev (!(#closures_rev state)),
        class_program_refs=class_program_refs, class_roots=class_roots,
        bind_keys=List.rev (!(#bind_keys_rev state)), statistics=statistics}:result end

  fun arena (r: result) = #arena r
  fun programs (r: result) = #programs r
  fun selectors (r: result) = #selectors r
  fun action_tokens (r: result) = #action_tokens r
  fun guard_entries (r: result) = #guard_entries r
  fun closures (r: result) = #closures r
  fun class_program_refs (r: result) = #class_program_refs r
  fun class_roots (r: result) = #class_roots r
  fun bind_keys (r: result) = #bind_keys r
  fun statistics (r: result) = #statistics r
end
