structure Comma_Semantic_Continue_Observer_Contract =
struct
  type certified_column = {column:term,admitted:thm}
  type mask = certified_column
  type value =
    {column:term, admitted:thm, actual_admitted:thm, equivalent:thm}
  type stats =
    {completed_jobs:int,completed_core_folds:int,completed_applications:int,cache_hits:int,
     guard_checks:int,supported_guards:int,child_bindings:int,
     proposition_term_nodes:int,max_proposition_term_nodes:int,
     job_result_term_nodes:int,max_job_result_term_nodes:int,
     canonical_application_column_nodes:int,max_canonical_application_column_nodes:int,
     distinct_job_base_keys:int,requested_jobs:int,
     distinct_application_base_keys:int,requested_applications:int,
     completed_top_level_roots:int}
  type hooks =
    {class_program_binding:int -> term * thm,
     evaluate:string -> term -> thm,
     staged_value:string -> term -> thm list -> string list -> thm,
     validate_closed:string -> term -> unit,
     validate_native:string -> thm -> thm,
     validate_equation:string -> term -> term -> thm -> thm,
     scalar_facts:term -> thm list,
     program_catalogue:thm,
     program_representatives:(int * term) list,
     report:stats -> unit}
  type result = {image_certificate:thm, stats:stats}

  val natT = @{typ nat}
  val jobT = @{typ comma_phase_continue_job}
  val programT = @{typ comma_semantic_port_program}
  val columnT = @{typ comma_crt_column}
  val observerT = @{typ comma_continue_observer}

  fun nat n = HOLogic.mk_number natT n
  fun listT typ = Type (@{type_name list},[typ])
  fun mk_program_job program =
    Const (@{const_name Comma_Continue_Program_Job},programT --> jobT) $ program
  fun mk_core_values_job_list f residue core values =
    Const (@{const_name Comma_Continue_Core_Values_Job},
      natT --> natT --> @{typ comma_phase_core_id} --> listT natT --> jobT) $
      nat f $ nat residue $ core $ values
  fun mk_core_values_job f residue core values =
    mk_core_values_job_list f residue core (HOLogic.mk_list natT (map nat values))
  fun mk_action_job parent action =
    Const (@{const_name Comma_Continue_Action_Job},
      natT --> @{typ comma_source_continuation_action} --> jobT) $
      nat parent $ action
  fun job_observe_call observer job internal_shift clock =
    Const (@{const_name comma_continue_job_observe},
      observerT --> jobT --> natT --> natT --> columnT) $
      observer $ job $ nat internal_shift $ nat clock
  fun apply_column operation left right =
    Const (@{const_name comma_crt_apply},
      @{typ comma_crt_boolean_operation} --> columnT --> columnT --> columnT) $
      operation $ left $ right
  fun shift_column shift column =
    Const (@{const_name comma_crt_shift},natT --> columnT --> columnT) $
      nat shift $ column

  datatype job_view = Program_Job of term
      | Core_Values_Job of int * int * term * int list
      | Action_Job of int * term
  datatype program_view = Entry_Program of int * int * int * term
      | Near_Program of int * term | Boundary_Program of int

  fun decode_constructor label term =
    (case Term.strip_comb term of
      (Const (name,_),arguments) => (name,arguments)
    | _ => error (label ^ " is not a constructor application"))

  fun decode_nat label term =
    (case try HOLogic.dest_number term of
      SOME (typ,value) => if typ=natT andalso value>=0 then value
        else error (label ^ " is not a natural numeral")
    | NONE => error (label ^ " is not a natural numeral"))

  fun decode_list label term =
    (HOLogic.dest_list term
      handle TERM _ => error (label ^ " is not a literal list"))

  fun decode_option_program label term =
    (case Term.strip_comb term of
      (Const (name,_),[program]) =>
        if name = @{const_name Some} andalso fastype_of program=programT
        then SOME program
        else error (label ^ " has malformed Some payload")
    | (Const (name,_),[]) =>
        if name = @{const_name None} then NONE
        else error (label ^ " is not an option")
    | _ => error (label ^ " is not an option"))

  fun decode_job label job =
    let val (name,args)=decode_constructor label job in
      case (name,args) of
        (@{const_name Comma_Continue_Program_Job},[program]) => Program_Job program
      | (@{const_name Comma_Continue_Core_Values_Job},[f,residue,core,values]) =>
          Core_Values_Job (decode_nat (label ^ " sector") f,
            decode_nat (label ^ " residue") residue,core,
            map (decode_nat (label ^ " core value"))
              (decode_list (label ^ " core values") values))
      | (@{const_name Comma_Continue_Action_Job},[parent,action]) =>
          Action_Job (decode_nat (label ^ " parent sector") parent,action)
      | _ => error (label ^ " has an invalid Continue job shape")
    end

  fun decode_action label action =
    let val (name,args)=decode_constructor label action in
      case (name,args) of
        (@{const_name Comma_Continuation_Goto},[source,delta]) =>
          SOME (true,source,decode_nat label delta)
      | (@{const_name Comma_Continuation_Exit},[source,delta]) =>
          SOME (false,source,decode_nat label delta)
      | _ => NONE
    end

  fun decode_program label program =
    let val (name,args)=decode_constructor label program in
      case (name,args) of
        (@{const_name Comma_Entry_Core_Program},[f,d,residue,core]) =>
          Entry_Program (decode_nat "Entry sector" f,
            decode_nat "Entry digit" d,decode_nat "Entry residue" residue,core)
      | (@{const_name Comma_Near_Residual_Program},[f,_,_]) =>
          Near_Program (decode_nat "Near sector" f,program)
      | (@{const_name Comma_Near_Boundary_Program},[f]) =>
          Boundary_Program (decode_nat "Boundary sector" f)
      | _ => error (label ^ " has an unknown constructor")
    end

  datatype operator_node = Continue_1 | Continue_2 | Continue_4 |
      Continue_8 | Continue_16 | Continue_24
  datatype observer_node = Continue_Endpoint |
      Continue_Applied of operator_node * observer_node

  fun operator_code Continue_1 = 0
    | operator_code Continue_2 = 1
    | operator_code Continue_4 = 2
    | operator_code Continue_8 = 3
    | operator_code Continue_16 = 4
    | operator_code Continue_24 = 5

  fun observer_code Continue_Endpoint = 0
    | observer_code (Continue_Applied (node,observer)) =
        1 + 6 * observer_code observer + operator_code node

  fun operator_name Continue_1 = @{const_name comma_continue_operator_1}
    | operator_name Continue_2 = @{const_name comma_continue_operator_2}
    | operator_name Continue_4 = @{const_name comma_continue_operator_4}
    | operator_name Continue_8 = @{const_name comma_continue_operator_8}
    | operator_name Continue_16 = @{const_name comma_continue_operator_16}
    | operator_name Continue_24 = @{const_name comma_continue_operator_24}

  fun operator_term node = Const (operator_name node,@{typ comma_continue_operator})

  fun operator_steps Continue_1 = 1
    | operator_steps Continue_2 = 2
    | operator_steps Continue_4 = 4
    | operator_steps Continue_8 = 8
    | operator_steps Continue_16 = 16
    | operator_steps Continue_24 = 24

  fun operator_contract Continue_1 = @{thm comma_continue_operator_1_contract}
    | operator_contract Continue_2 = @{thm comma_continue_operator_2_contract}
    | operator_contract Continue_4 = @{thm comma_continue_operator_4_contract}
    | operator_contract Continue_8 = @{thm comma_continue_operator_8_contract}
    | operator_contract Continue_16 = @{thm comma_continue_operator_16_contract}
    | operator_contract Continue_24 = @{thm comma_continue_operator_24_contract}

  fun operator_parts Continue_1 = NONE
    | operator_parts Continue_2 = SOME (Continue_1,Continue_1)
    | operator_parts Continue_4 = SOME (Continue_2,Continue_2)
    | operator_parts Continue_8 = SOME (Continue_4,Continue_4)
    | operator_parts Continue_16 = SOME (Continue_8,Continue_8)
    | operator_parts Continue_24 = SOME (Continue_16,Continue_8)

  fun operator_definition Continue_1 = @{thm comma_continue_operator_1_def}
    | operator_definition Continue_2 = @{thm comma_continue_operator_2_def}
    | operator_definition Continue_4 = @{thm comma_continue_operator_4_def}
    | operator_definition Continue_8 = @{thm comma_continue_operator_8_def}
    | operator_definition Continue_16 = @{thm comma_continue_operator_16_def}
    | operator_definition Continue_24 = @{thm comma_continue_operator_24_def}

  fun lift_head_rewrite ctxt theorem term =
    let
      val (head,args)=Term.strip_comb term
      val head_eq=Conv.rewr_conv (mk_meta_eq theorem) (Thm.cterm_of ctxt head)
    in
      List.foldl (fn (argument,equation) =>
        Thm.combination equation (Thm.reflexive (Thm.cterm_of ctxt argument)))
        head_eq args
    end

  fun operator_application_conversion ctxt node term =
    let
      val head=lift_head_rewrite ctxt (operator_definition node) term
    in
      case operator_parts node of
        NONE => head
      | SOME _ =>
          let
            val body=Conv.rewr_conv
              (mk_meta_eq @{thm comma_continue_operator_compose_def})
              (Thm.rhs_of head)
          in Thm.transitive head body end
    end

  fun operator_key node observer program =
    HOLogic.mk_prod (HOLogic.mk_number @{typ nat} (operator_code node),
      HOLogic.mk_prod (HOLogic.mk_number @{typ nat} (observer_code observer),program))

  val class_count = 46

  fun guarded_column mask column =
    apply_column @{term Comma_CRT_And} mask column

  fun observer_term Continue_Endpoint =
        @{term comma_continue_bad_endpoint_observer}
    | observer_term (Continue_Applied (node,observer)) =
        let
          val target=Free ("continue_target",natT)
          val clock=Free ("continue_clock",natT)
          val child=Free ("continue_child_program",programT)
          val action=operator_term node $ observer_term observer $ child $ clock
          val no_child= @{term "Comma_CRT_Bool False"}
          val lookup= @{term comma_semantic_phase_program_for_class} $ target
          val option_case=Const (@{const_name case_option},
            fastype_of no_child --> (programT --> fastype_of no_child) -->
              fastype_of lookup --> fastype_of no_child) $ no_child $
            Term.lambda child action $ lookup
        in Term.lambda target (Term.lambda clock option_case) end

  fun observer_predicate Continue_Endpoint =
        @{term comma_continue_outside_endpoints}
    | observer_predicate (Continue_Applied (node,observer)) =
        @{term comma_continue_suffix_predicate} $
          nat (operator_steps node) $ observer_predicate observer

  fun application node observer program =
    operator_term node $ observer_term observer $ program $ nat 0

  fun job_key observer job shift (mask:mask) =
    HOLogic.mk_prod (nat (observer_code observer),
      HOLogic.mk_prod (job,HOLogic.mk_prod (nat shift,#column mask)))

  fun job_base_key observer job shift =
    HOLogic.mk_prod (nat (observer_code observer),HOLogic.mk_prod (job,nat shift))

  type state =
    {memo:value Termtab.table Unsynchronized.ref,
     active:unit Termtab.table Unsynchronized.ref,
     completed_jobs:int Unsynchronized.ref,
     completed_core_folds:int Unsynchronized.ref,
     completed_applications:int Unsynchronized.ref,
     cache_hits:int Unsynchronized.ref,
     guard_checks:int Unsynchronized.ref,supported_guards:int Unsynchronized.ref,
     child_bindings:int Unsynchronized.ref,
     proposition_term_nodes:int Unsynchronized.ref,
     max_proposition_term_nodes:int Unsynchronized.ref,
     job_result_term_nodes:int Unsynchronized.ref,
     max_job_result_term_nodes:int Unsynchronized.ref,
     canonical_application_column_nodes:int Unsynchronized.ref,
     max_canonical_application_column_nodes:int Unsynchronized.ref,
     job_base_keys:unit Termtab.table Unsynchronized.ref,
     distinct_job_base_keys:int Unsynchronized.ref,
     requested_jobs:int Unsynchronized.ref,
     application_base_keys:unit Termtab.table Unsynchronized.ref,
     distinct_application_base_keys:int Unsynchronized.ref,
     requested_applications:int Unsynchronized.ref,
     completed_top_level_roots:int Unsynchronized.ref}

  fun empty_state () : state =
    {memo=Unsynchronized.ref Termtab.empty,
     active=Unsynchronized.ref Termtab.empty,
     completed_jobs=Unsynchronized.ref 0,
     completed_core_folds=Unsynchronized.ref 0,
     completed_applications=Unsynchronized.ref 0,
     cache_hits=Unsynchronized.ref 0,
     guard_checks=Unsynchronized.ref 0,supported_guards=Unsynchronized.ref 0,
     child_bindings=Unsynchronized.ref 0,
     proposition_term_nodes=Unsynchronized.ref 0,
     max_proposition_term_nodes=Unsynchronized.ref 0,
     job_result_term_nodes=Unsynchronized.ref 0,
     max_job_result_term_nodes=Unsynchronized.ref 0,
     canonical_application_column_nodes=Unsynchronized.ref 0,
     max_canonical_application_column_nodes=Unsynchronized.ref 0,
     job_base_keys=Unsynchronized.ref Termtab.empty,
     distinct_job_base_keys=Unsynchronized.ref 0,
     requested_jobs=Unsynchronized.ref 0,
     application_base_keys=Unsynchronized.ref Termtab.empty,
     distinct_application_base_keys=Unsynchronized.ref 0,
     requested_applications=Unsynchronized.ref 0,
     completed_top_level_roots=Unsynchronized.ref 0}

  fun note_base_request keys distinct requests key =
    let
      val _=requests := !requests+1
    in
      if Termtab.defined (!keys) key then ()
      else (keys := Termtab.update (key,()) (!keys);
        distinct := !distinct+1)
    end

  fun note_job_request (current:state) key =
    note_base_request (#job_base_keys current)
      (#distinct_job_base_keys current) (#requested_jobs current) key

  fun note_application_request (current:state) key =
    note_base_request (#application_base_keys current)
      (#distinct_application_base_keys current)
      (#requested_applications current) key

  fun note_top_level_root (current:state) =
    #completed_top_level_roots current :=
      !(#completed_top_level_roots current)+1

  fun set_active (current:state) key active =
    #active current :=
      (if active then Termtab.update (key,()) (!(#active current))
       else Termtab.delete_safe key (!(#active current)))

  fun note_child_binding (current:state) =
    #child_bindings current := !(#child_bindings current)+1

  fun stats_of (current:state) : stats =
    {completed_jobs= !(#completed_jobs current),
     completed_core_folds= !(#completed_core_folds current),
     completed_applications= !(#completed_applications current),
     cache_hits= !(#cache_hits current),
     guard_checks= !(#guard_checks current),
     supported_guards= !(#supported_guards current),
     child_bindings= !(#child_bindings current),
     proposition_term_nodes= !(#proposition_term_nodes current),
     max_proposition_term_nodes= !(#max_proposition_term_nodes current),
     job_result_term_nodes= !(#job_result_term_nodes current),
     max_job_result_term_nodes= !(#max_job_result_term_nodes current),
     canonical_application_column_nodes=
       !(#canonical_application_column_nodes current),
     max_canonical_application_column_nodes=
       !(#max_canonical_application_column_nodes current),
     distinct_job_base_keys= !(#distinct_job_base_keys current),
     requested_jobs= !(#requested_jobs current),
     distinct_application_base_keys= !(#distinct_application_base_keys current),
     requested_applications= !(#requested_applications current),
     completed_top_level_roots= !(#completed_top_level_roots current)}

  type observer_proofs = {admitted:thm,matches:thm}

  fun observer_at_admitted validate_native ctxt (proofs:observer_proofs)
      observer target clock =
    let
      val actual=observer $ nat target $ nat clock
      val goal=HOLogic.mk_Trueprop (@{term comma_crt_admitted} $ nat 0 $ actual)
      val rule= @{lemma
        "comma_continue_observer_admitted observer \<Longrightarrow> target<46 \<Longrightarrow>
          comma_crt_admitted 0 (observer target clock)"
        by (auto simp: comma_continue_observer_admitted_def)} OF [#admitted proofs]
      val theorem=Goal.prove ctxt [] [] goal
        (fn {context,...} => resolve_tac context [rule] 1 THEN simp_tac context 1)
    in validate_native "Continue selected observer admission" theorem end

  fun observer_proofs validate_native ctxt
      (cache:observer_proofs Termtab.table Unsynchronized.ref)
      descriptor =
    let
      val key=nat (observer_code descriptor)
    in
      case Termtab.lookup (!cache) key of
        SOME proofs => proofs
      | NONE =>
          let
            val proofs=case descriptor of
              Continue_Endpoint =>
                {admitted = @{thm comma_continue_bad_endpoint_observer_admitted},
                 matches = @{thm comma_continue_bad_endpoint_observer_matches}}
            | Continue_Applied (node,observer) =>
                let
                  val child=observer_proofs validate_native ctxt cache observer
                  val applied=observer_term descriptor
                  val admitted_prop = @{term comma_continue_observer_admitted} $ applied
                  val admitted = @{thm comma_continue_operator_applied_observer_admitted}
                    OF [operator_contract node, #admitted child]
                  val _ = if Thm.prop_of admitted aconv
                      HOLogic.mk_Trueprop admitted_prop then ()
                    else error "Continue applied observer admission has a foreign observer"
                  val matches_prop = @{term comma_continue_observer_matches} $ applied $
                    observer_predicate descriptor
                  val matches = @{thm comma_continue_operator_applied_observer_matches}
                    OF [operator_contract node, #admitted child, #matches child]
                  val _ = if Thm.prop_of matches aconv
                      HOLogic.mk_Trueprop matches_prop then ()
                    else error "Continue applied observer semantics has a foreign observer"
                in
                  {admitted=validate_native
                     "Continue applied observer admission" admitted,
                   matches=validate_native
                     "Continue applied observer semantics" matches}
                end
            val _=cache := Termtab.update (key,proofs) (!cache)
          in proofs end
    end

  fun checked_mask (validate_closed:string -> term -> unit)
      (validate_native:string -> thm -> thm) label ({column,admitted}:mask) =
    let
      val expected=HOLogic.mk_Trueprop
        (@{term comma_crt_admitted} $ nat 0 $ column)
      val _=if Thm.prop_of admitted aconv expected then ()
        else error (label ^ " has a mismatched CRT mask admission")
      val _=if fastype_of column=columnT andalso
          Comma_Semantic_Continue_Column_Proofs.is_literal_column column then ()
        else error (label ^ " is not a canonical literal CRT mask")
      val _=validate_closed label column
    in
      {column=column,
       admitted=validate_native (label ^ " admission") admitted}:mask
    end

  fun checked_value (validate_closed:string -> term -> unit)
      (validate_native:string -> thm -> thm) node observer program
      (mask:mask) (value:value) =
    let
      val lhs=guarded_column (#column mask) (application node observer program)
      val expected=HOLogic.mk_Trueprop
        (@{term comma_crt_equiv_check} $ lhs $ #column value)
      val admitted=HOLogic.mk_Trueprop
        (@{term comma_crt_admitted} $ nat 0 $ #column value)
      val actual_admitted=HOLogic.mk_Trueprop
        (@{term comma_crt_admitted} $ nat 0 $ lhs)
      val _=if Thm.prop_of (#equivalent value) aconv expected then ()
        else error "Cached Continue result lost its exact application authority"
      val _=if Thm.prop_of (#admitted value) aconv admitted then ()
        else error "Cached Continue result has a foreign column admission"
      val _=if Thm.prop_of (#actual_admitted value) aconv actual_admitted then ()
        else error "Cached Continue result has a foreign output admission"
      val _=if fastype_of (#column value)=columnT then ()
        else error "Cached Continue result is not a CRT column"
      val _=Comma_Semantic_Continue_Column_Proofs.require_literal_column
        "Cached Continue application result" (#column value)
      val _=validate_closed "Cached Continue column" (#column value)
    in
      {column = #column value,
       admitted=validate_native "Cached Continue column admission" (#admitted value),
       actual_admitted=validate_native "Cached Continue output admission"
         (#actual_admitted value),
       equivalent=validate_native "Cached Continue semantic result"
         (#equivalent value)}:value
    end
end
