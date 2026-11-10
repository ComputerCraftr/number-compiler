(* Runtime adapter for the untrusted parametric compiler.  All control
   functions below come from the one-time Isabelle code_reflect module; this
   file only converts its values to the proposal arena's data representation.
   No theorem is constructed here. *)
structure Comma_Frontier24_Parametric_Runtime =
struct
  structure Data = Comma_Frontier24_Data
  structure Arena = Comma_CRT_MDD_Arena
  structure Compiler = Comma_Frontier24_Parametric_Compiler

  val natT = @{typ nat}
  val coreT = @{typ comma_phase_core_id}
  val programT = @{typ comma_semantic_port_program}
  val positionT = @{typ comma_finite_position}
  val actionT = @{typ comma_source_continuation_action}

  val integer_of_nat = Data.integer_of_nat
  val nat_of_integer = Data.nat_of_integer
  fun from_nat label value =
    let val exact = integer_of_nat value
    in
      if exact < 0 then error (label ^ " is negative")
      else (IntInf.toInt exact
        handle Overflow => error (label ^ " exceeds machine-int range"))
    end

  fun code_nat value =
    if value < 0 then error "Cannot encode a negative reflected nat"
    else nat_of_integer (IntInf.fromInt value)

  fun nat n = HOLogic.mk_number natT n
  fun app name resultT args =
    let
      val argTs = map fastype_of args
      val c = Const (name, fold_rev (curry (op -->)) argTs resultT)
    in list_comb (c,args) end

  fun core_term core =
    let
      val name = (case core of
          Data.Comma_Core_1 => @{const_name Comma_Core_1}
        | Data.Comma_Core_3 => @{const_name Comma_Core_3}
        | Data.Comma_Core_7 => @{const_name Comma_Core_7}
        | Data.Comma_Core_11 => @{const_name Comma_Core_11}
        | Data.Comma_Core_13 => @{const_name Comma_Core_13}
        | Data.Comma_Core_21 => @{const_name Comma_Core_21}
        | Data.Comma_Core_23 => @{const_name Comma_Core_23}
        | Data.Comma_Core_27 => @{const_name Comma_Core_27}
        | Data.Comma_Core_29 => @{const_name Comma_Core_29})
    in Const (name,coreT) end

  fun core_value core =
    (case Term.strip_comb core of
      (Const (name,_),[]) =>
        if name = @{const_name Comma_Core_1} then Data.Comma_Core_1
        else if name = @{const_name Comma_Core_3} then Data.Comma_Core_3
        else if name = @{const_name Comma_Core_7} then Data.Comma_Core_7
        else if name = @{const_name Comma_Core_11} then Data.Comma_Core_11
        else if name = @{const_name Comma_Core_13} then Data.Comma_Core_13
        else if name = @{const_name Comma_Core_21} then Data.Comma_Core_21
        else if name = @{const_name Comma_Core_23} then Data.Comma_Core_23
        else if name = @{const_name Comma_Core_27} then Data.Comma_Core_27
        else if name = @{const_name Comma_Core_29} then Data.Comma_Core_29
        else error "Unknown core id in Frontier24 runtime adapter"
    | _ => error "Malformed core id in Frontier24 runtime adapter")

  fun position_value source =
    let
      fun fields label xs = map (Comma_CRT_MDD_Proof_Utils.dest_nat label natT) xs
    in
      (case Term.strip_comb source of
        (Const (name,_),[f,delta,x]) =>
          let
            val (f',delta',x') =
              (case fields "Finite-position coordinate" [f,delta,x] of
                [a,b,c] => (a,b,c)
              | _ => error "Finite-position constructor has the wrong arity")
          in if name = @{const_name Comma_Entry}
             then Data.Comma_Entry (code_nat f',code_nat delta',code_nat x')
             else if name = @{const_name Comma_Near}
             then Data.Comma_Near (code_nat f',code_nat delta',code_nat x')
             else error "Unknown finite-position constructor" end
      | _ => error "Malformed finite-position term")
    end

  fun position_term source =
    let
      fun mk ctor (f,delta,x) = app ctor positionT [nat (from_nat "Position sector" f),
        nat (from_nat "Position displacement" delta),
        nat (from_nat "Position coordinate" x)]
    in
      (case source of
        Data.Comma_Entry (f,delta,x) => mk @{const_name Comma_Entry} (f,delta,x)
      | Data.Comma_Near (f,delta,x) => mk @{const_name Comma_Near} (f,delta,x))
    end

  fun action_term action =
    let
      fun unary name n = app name actionT [nat (from_nat "Action payload" n)]
      fun binary name a b = app name actionT
        [nat (from_nat "Action payload" a),nat (from_nat "Action payload" b)]
      fun with_source name source delta = app name actionT
        [position_term source,nat (from_nat "Action displacement" delta)]
    in
      (case action of
        Data.Comma_Continuation_Goto (source,delta) =>
          with_source @{const_name Comma_Continuation_Goto} source delta
      | Data.Comma_Continuation_Exit (source,delta) =>
          with_source @{const_name Comma_Continuation_Exit} source delta
      | Data.Comma_Continuation_Fork (target,delta) =>
          binary @{const_name Comma_Continuation_Fork} target delta
      | Data.Comma_Continuation_Landmine delta =>
          unary @{const_name Comma_Continuation_Landmine} delta
      | Data.Comma_Continuation_Invalid => Const (@{const_name Comma_Continuation_Invalid},actionT))
    end

  fun program_term program =
    let
      fun nat_arg label n = nat (from_nat label n)
    in
      (case program of
        Data.Comma_Entry_Core_Program (f,d,residue,core) =>
          app @{const_name Comma_Entry_Core_Program} programT
            [nat_arg "Entry sector" f,nat_arg "Entry digit" d,
             nat_arg "Entry residue" residue,core_term core]
      | Data.Comma_Near_Residual_Program (f,d,residual) =>
          app @{const_name Comma_Near_Residual_Program} programT
            [nat_arg "Near sector" f,nat_arg "Near digit" d,
             nat_arg "Near residual" residual]
      | Data.Comma_Near_Boundary_Program f =>
          app @{const_name Comma_Near_Boundary_Program} programT
            [nat_arg "Boundary sector" f])
    end

  fun program_value program =
    (case Term.strip_comb program of
      (Const (name,_),[f,d,residue,core]) =>
        if name = @{const_name Comma_Entry_Core_Program} then
          Data.Comma_Entry_Core_Program
            (code_nat (Comma_CRT_MDD_Proof_Utils.dest_nat "Entry sector" natT f),
             code_nat (Comma_CRT_MDD_Proof_Utils.dest_nat "Entry digit" natT d),
             code_nat (Comma_CRT_MDD_Proof_Utils.dest_nat "Entry residue" natT residue),
             core_value core)
        else error "Unexpected four-field Frontier24 program"
    | (Const (name,_),[f,d,residual]) =>
        if name = @{const_name Comma_Near_Residual_Program} then
          Data.Comma_Near_Residual_Program
            (code_nat (Comma_CRT_MDD_Proof_Utils.dest_nat "Near sector" natT f),
             code_nat (Comma_CRT_MDD_Proof_Utils.dest_nat "Near digit" natT d),
             code_nat (Comma_CRT_MDD_Proof_Utils.dest_nat "Near residual" natT residual))
        else error "Unexpected three-field Frontier24 program"
    | (Const (name,_),[f]) =>
        if name = @{const_name Comma_Near_Boundary_Program} then
          Data.Comma_Near_Boundary_Program
            (code_nat (Comma_CRT_MDD_Proof_Utils.dest_nat "Boundary sector" natT f))
        else error "Unexpected one-field Frontier24 program"
    | _ => error "Malformed Frontier24 program term")

  fun option_map f NONE = NONE | option_map f (SOME x) = SOME (f x)

  fun seed_node (Data.Comma_CRT_MDD_Leaf value) =
        Arena.Seed_Leaf (if value then 1 else 0)
    | seed_node (Data.Comma_CRT_MDD_Branch (axis,children)) =
        Arena.Seed_Branch
          (from_nat "Guard axis" axis,
           map (from_nat "Guard child index") children)

  val computation: Compiler.computation =
    {class_program = (fn cid =>
       option_map program_term (Data.comma_semantic_phase_program_for_class
         (code_nat cid))),
     source_program = (fn source =>
       option_map program_term (Data.comma_semantic_port_program_of_source
         (position_value source))),
     program_admitted = (fn program =>
       Data.comma_phase_program_structurally_admitted (program_value program)),
     supported_values = (fn core =>
       map (from_nat "Supported core value")
         (Data.comma_core_supported_values (core_value core))),
     core_modulus = (fn core =>
       from_nat "Core modulus" (Data.comma_phase_core_modulus (core_value core))),
     guard_table = (fn core => fn wanted =>
       let
         val c = core_value core
         val nodes = Data.comma_frontier24_core_guard_nodes c
           (code_nat wanted)
         val root_expected = from_nat "Guard root"
           (Data.comma_frontier24_core_guard_root c)
         val seeds = map seed_node nodes
         val _ = if 0 <= root_expected andalso root_expected < length seeds then ()
           else error "Reflected guard root is outside its candidate table"
       in (seeds,root_expected) end),
     entry_action = (fn f => fn residue => fn core => fn wanted =>
       action_term (Data.comma_phase_program_entry_core_value_action
         (code_nat f) (code_nat residue) (core_value core)
         (code_nat wanted))),
     operator_action = (fn program =>
       action_term (Data.comma_phase_program_operator_nf
         (program_value program) (code_nat 0))),
     exit_code = (fn source => fn full_shift =>
       from_nat "Exit Continue code"
         (Data.comma_parametric_exit_continue_code (position_value source)
           (code_nat full_shift)))}

  fun list typ terms = HOLogic.mk_list typ terms
  fun list_nat ints = list natT (map nat ints)
  fun option typ NONE = Const (@{const_name None},Type (@{type_name option},[typ]))
    | option typ (SOME value) = Const (@{const_name Some},typ -->
        Type (@{type_name option},[typ])) $ value
  fun pair left right = HOLogic.mk_prod (left,right)

  (* Parse each record schema once, then instantiate its typed abstraction
     for the candidate rows.  The resulting terms are checked again by the
     generic HOL bundle predicate; this is only serialization. *)
  fun record_builder ctxt fields =
    let
      val args = map_index (fn (i,(_,T)) =>
        ("cf24_arg" ^ Int.toString i, T)) fields
      val source = "\<lparr>" ^ space_implode ", "
        (map_index (fn (i,(field,_)) => field ^ " = cf24_arg" ^ Int.toString i)
          fields) ^ "\<rparr>"
      val template = Syntax.read_term ctxt source
      val actual_frees = Term.add_frees template []
      val typed_args = map (fn (name,_) =>
        Free (name,the (AList.lookup (op =) actual_frees name))) args
      val builder = fold_rev Term.lambda typed_args template
      val expectedT = fold_rev (curry (op -->)) (map fastype_of typed_args) (fastype_of template)
      val _ = if fastype_of builder = expectedT then ()
        else error "Frontier24 record serializer inferred an unexpected type"
    in builder end

  fun apply_builder builder values =
    Envir.beta_eta_contract (Term.list_comb (builder,values))

  type named_actions = {table: term, definition: thm}

  fun define_action_table lthy (result: Compiler.result) =
    let
      val literal = list actionT (Compiler.action_tokens result)
      val binding = Binding.name "comma_frontier24_action_tokens"
      val ((constant,(_,definition_local)),lthy') = Local_Theory.define
        ((binding,NoSyn),
         ((Binding.name "comma_frontier24_action_tokens_def",[]),literal)) lthy
      val morphism = Local_Theory.target_morphism lthy'
      val table = Morphism.term morphism constant
      val definition = Morphism.thm morphism definition_local
      val exact = Logic.mk_equals (table,literal)
      val ctxt' = Local_Theory.target_of lthy'
      val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt'
        "Frontier24 named action table definition" exact definition
      val _ = if fastype_of table = HOLogic.listT actionT andalso
          Comma_CRT_MDD_Proof_Utils.closed table andalso
          Comma_CRT_MDD_Proof_Utils.closed literal then () else
        error "Frontier24 named action table is not a closed typed value"
    in ({table=table,definition=definition}: named_actions,lthy') end

  fun serialize ctxt nodes_term (result: Compiler.result)
      ({table=action_table,...}: named_actions) =
    let
      val selector_caseT = @{typ comma_frontier24_selector_case}
      val selectorT = @{typ comma_frontier24_selector_recipe}
      val closure_caseT = @{typ comma_frontier24_closure_case}
      val closureT = @{typ comma_frontier24_closure}
      val guardT = @{typ comma_frontier24_guard_entry}
      val closure_casesT = HOLogic.listT closure_caseT
      val programs = Compiler.programs result
      val selectors = Compiler.selectors result
      val guards = Compiler.guard_entries result
      val closures = Compiler.closures result
      val arena = Compiler.arena result
      val case_builder = record_builder ctxt
        [("cf24_case_wanted",natT),("cf24_case_guard_root",natT),
         ("cf24_case_action_token",natT)]
      fun selector_case_term ({wanted,guard_root,action_token}: Compiler.selector_case) =
        apply_builder case_builder [nat wanted,
          nat (Arena.boolean_index arena guard_root),nat action_token]
      fun selector_term recipe =
        let
          val entry_name = @{const_name Comma_Frontier24_Entry_Selector}
          val near_name = @{const_name Comma_Frontier24_Near_Selector}
        in
          (case recipe of
            Compiler.Near_Selector {token} =>
              app near_name selectorT [nat token]
          | Compiler.Entry_Selector {f,d,residue,core,cases} =>
              app entry_name selectorT
                [nat f,nat d,nat residue,core,
                 list selector_caseT (map selector_case_term cases)])
        end
      val closure_case_builder = record_builder ctxt
        [("cf24_closure_case_wanted",natT),
         ("cf24_closure_case_guard_root",natT),
         ("cf24_closure_case_shifted_guard_root",natT),
         ("cf24_closure_case_action_token",natT),
         ("cf24_closure_case_action_output_root",natT),
         ("cf24_closure_case_selected_root",natT),
         ("cf24_closure_case_bind_key",HOLogic.mk_prodT (natT,
           HOLogic.mk_prodT (natT,HOLogic.listT (HOLogic.mk_prodT (natT,natT))))),
         ("cf24_closure_case_child",Type (@{type_name option},[natT]))]
      fun bind_key_term (source,fallback,mapping) =
        pair (nat source) (pair (nat fallback)
          (list (HOLogic.mk_prodT (natT,natT))
            (map (fn (label,root) => pair (nat label) (nat root)) mapping)))
      fun closure_case_term (row: Compiler.closure_case) =
        apply_builder closure_case_builder
          [nat (#wanted row),nat (#guard_root row),nat (#shifted_guard_root row),
           nat (#action_token row),nat (#action_output_root row),
           nat (#selected_root row),bind_key_term (#bind_key row),
           option natT (Option.map nat (#child_closure row))]
      val closure_builder = record_builder ctxt
        [("cf24_closure_program_ref",natT),("cf24_closure_full_shift",natT),
         ("cf24_closure_cases",closure_casesT),
         ("cf24_closure_near_token",Type (@{type_name option},[natT])),
         ("cf24_closure_near_action_output_root",Type (@{type_name option},[natT])),
         ("cf24_closure_near_child",Type (@{type_name option},[natT])),
         ("cf24_closure_output_root",natT)]
      fun closure_term (row: Compiler.closure) =
        apply_builder closure_builder
          [nat (#program_ref row),nat (#full_shift row),
           list closure_caseT (map closure_case_term (#cases row)),
           option natT (Option.map nat (#near_token row)),
           option natT (Option.map nat (#near_action_output_root row)),
           option natT (Option.map nat (#near_child_closure row)),
           nat (#output_root row)]
      val guard_builder = record_builder ctxt
        [("cf24_guard_core",coreT),("cf24_guard_wanted",natT),
         ("cf24_guard_root",natT)]
      fun guard_term (row: Compiler.guard_entry) =
        apply_builder guard_builder [#core row,nat (#wanted row),nat (#root row)]
      val bundle_builder = record_builder ctxt
        [("cf24_programs",HOLogic.listT programT),
         ("cf24_selectors",HOLogic.listT selectorT),
         ("cf24_action_tokens",HOLogic.listT actionT),
         ("cf24_guard_entries",HOLogic.listT guardT),
         ("cf24_closures",HOLogic.listT closureT),
         ("cf24_class_program_refs",HOLogic.listT natT),
         ("cf24_class_roots",HOLogic.listT natT),
         ("cf24_radices",HOLogic.listT natT),
         ("cf24_nodes",HOLogic.listT @{typ "nat comma_crt_mdd_node"}),
         ("cf24_zero_root",natT)]
      val radices = Arena.radices arena
      val roots = map (Arena.action_index arena) (Compiler.class_roots result)
      val zero_root = Arena.action_index arena (Arena.action_none arena)
      val _ = if length roots = 46 andalso length radices = 4 then ()
        else error "Frontier24 candidate has an incomplete class/radix vector"
    in
      apply_builder bundle_builder
        [list programT programs,
         list selectorT (map selector_term selectors),
         action_table,
         list guardT (map guard_term guards),
         list closureT (map closure_term closures),
         list_nat (Compiler.class_program_refs result),list_nat roots,
         list_nat radices,nodes_term,nat zero_root]
    end

  type candidate = {result: Compiler.result, bundle: term, statistics: string,
    named_actions: named_actions}

  (* Canonical interning is a producer invariant, not a premise of the
     mathematical action refinement. Exact table indices remain checked by
     the kernel certificate independently of this rejection check. *)
  fun require_distinct_terms label terms =
    let
      fun insert term seen =
        if Termtab.defined seen term then error (label ^ " contains a duplicate")
        else Termtab.update (term,()) seen
    in ignore (fold insert terms Termtab.empty) end

  fun compile_data ctxt =
    let
      val result = Compiler.compile ctxt computation
      val _ = require_distinct_terms "Frontier24 canonical programs"
        (Compiler.programs result)
      val _ = require_distinct_terms "Frontier24 canonical actions"
        (Compiler.action_tokens result)
      val _ = require_distinct_terms "Frontier24 canonical closure keys"
        (map (fn (closure: Compiler.closure) =>
          HOLogic.mk_prod (nat (#program_ref closure),nat (#full_shift closure)))
          (Compiler.closures result))
    in result end

  fun candidate ctxt nodes_term (result: Compiler.result)
      (named_actions: named_actions) : candidate =
    let
      val bundle = serialize ctxt nodes_term result named_actions
    in {result=result,bundle=bundle,statistics=Compiler.statistics result,
        named_actions=named_actions} end

  fun statistics ({statistics,...}: candidate) = statistics

  fun guard_imports ({result,...}: candidate) = Compiler.guard_entries result

  (* A bounded data-only differential used by the existing Smoke session.  It
     compares a small fixed sample of compiled roots with the reflected class
     step; it does not issue a theorem or scan the 46x924 domain. *)
  datatype candidate_node = Candidate_Leaf of int
    | Candidate_Branch of int * int vector

  fun candidate_nodes arena =
    let
      fun decode node =
        (case Term.strip_comb node of
          (Const (name,_),[label]) =>
            if name = @{const_name Comma_CRT_MDD_Leaf} then
              Candidate_Leaf (Comma_CRT_MDD_Proof_Utils.dest_nat
                "Candidate leaf" natT label)
            else error "Malformed candidate leaf"
        | (Const (name,_),[axis,children]) =>
            if name = @{const_name Comma_CRT_MDD_Branch} then
              Candidate_Branch
                (Comma_CRT_MDD_Proof_Utils.dest_nat "Candidate axis" natT axis,
                 Vector.fromList (map
                   (Comma_CRT_MDD_Proof_Utils.dest_nat "Candidate child" natT)
                   (HOLogic.dest_list children)))
            else error "Malformed candidate branch"
        | _ => error "Malformed candidate MDD node")
    in Vector.fromList (map decode (HOLogic.dest_list (Arena.table_term arena))) end

  fun evaluate_candidate arena nodes root phase =
    let
      val radices = Vector.fromList (Arena.radices arena)
      fun walk remaining index =
        if remaining = 0 then error "Candidate MDD traversal exceeded its node bound"
        else if index < 0 orelse index >= Vector.length nodes then
          error "Candidate MDD traversal reached an invalid root"
        else case Vector.sub (nodes,index) of
          Candidate_Leaf label => label
        | Candidate_Branch (axis,children) =>
            if axis < 0 orelse axis >= Vector.length radices then
              error "Candidate MDD traversal reached an invalid axis"
            else
              let
                val radix = Vector.sub (radices,axis)
                val slot = phase mod radix
              in
                if slot < 0 orelse slot >= Vector.length children then
                  error "Candidate MDD traversal reached a malformed row"
                else walk (remaining-1) (Vector.sub (children,slot))
              end
    in walk (Vector.length nodes) root end

  fun diagnostic_sample ({result,...}: candidate) =
    let
      val arena = Compiler.arena result
      val nodes = candidate_nodes arena
      val roots = Compiler.class_roots result
      val classes = [0,1,10,12,32,33,45]
      val phases = [0,1,67,299,923]

      fun compare (cid,phase) =
        let
          val root = Arena.action_index arena (List.nth (roots,cid))
          val actual = evaluate_candidate arena nodes root phase
          val expected =
            (case Data.comma_semantic_phase_program_class_step
                (code_nat phase) (code_nat cid) of
              Data.Comma_Phase_Class_Continue (_,target) =>
                from_nat "Diagnostic class target" target + 1
            | Data.Comma_Phase_Class_Invalid => 0
            | Data.Comma_Phase_Class_Fork _ => 0
            | Data.Comma_Phase_Class_Landmine _ => 0)
        in
          if actual = expected then ()
          else error ("Frontier24 bounded differential mismatch at class " ^
            Int.toString cid ^ " phase " ^ Int.toString phase ^
            ": MDD=" ^ Int.toString actual ^ " class-step=" ^ Int.toString expected)
        end
      val _ = List.app (fn cid => List.app (fn phase => compare (cid,phase)) phases)
        classes
    in "sample_comparisons=" ^ Int.toString (length classes * length phases) end
end
