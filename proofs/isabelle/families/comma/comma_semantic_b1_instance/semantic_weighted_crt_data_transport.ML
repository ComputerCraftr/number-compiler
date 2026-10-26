(* Proof-only term transport for the shared weighted CRT data arena.
   Arena ownership, interning, proof caches, and budget accounting remain in
   semantic_weighted_crt_data.ML. *)
structure Comma_Semantic_Weighted_CRT_Data_Transport =
struct
  val natT = @{typ nat}
  val radices = [4,3,7,11]

  (* This record is created once by a single normalization publication and is
     passed only through its proof constructors.  It contains no theorem or
     cache authority.  Traces are sampled after the first 128 stages and then
     once per 64 stages; counters and elapsed times remain exact for the run. *)
  type proof_profile =
   {owner: string, stages: string list, enabled: bool,
    calls: int Unsynchronized.ref,
    active_stage: string option Unsynchronized.ref,
    totals: (int * Time.time) Symtab.table Unsynchronized.ref}

  fun make_profile owner stages: proof_profile =
    {owner=owner, stages=stages, enabled=Comma_Proof_Profile.enabled (),
     calls=Unsynchronized.ref 0,
     active_stage=Unsynchronized.ref NONE,
     totals=Unsynchronized.ref Symtab.empty}

  fun profile_stats (profile: proof_profile) =
    let
      val {owner,stages,enabled,calls,active_stage,totals} = profile
      fun fields stage =
        let
          val (count,elapsed) = (case Symtab.lookup (!totals) stage of
            SOME value => value
          | NONE => (0,Time.zeroTime))
        in owner ^ "_" ^ stage ^ "_calls=" ^ Int.toString count ^
          " " ^ owner ^ "_" ^ stage ^ "_ms=" ^
          LargeInt.toString (Time.toMilliseconds elapsed) end
    in
      if not enabled then ""
      else String.concatWith " "
        (map fields stages @ [owner ^ "_active_stage=" ^
          (case !active_stage of SOME stage => stage | NONE => "none"),
         owner ^ "_profile_calls=" ^ Int.toString (!calls)])
    end

  fun with_profile (profile: proof_profile) stage work =
    let
      val {owner,stages,enabled,calls,active_stage,totals} = profile
    in
      if not enabled then work ()
      else if not (member (op =) stages stage) then
        error ("unknown " ^ owner ^ " proof profile stage: " ^ stage)
      else
        let
          val ordinal = !calls
          val _ = calls := ordinal + 1
          val traced = ordinal < 128 orelse ordinal mod 64 = 0
          val started = Time.now ()
          val previous_stage = !active_stage
          val _ = active_stage := SOME stage
          val _ = if traced then Comma_Proof_Profile.report
            (owner ^ " stage=" ^ stage ^ "-start ordinal=" ^ Int.toString ordinal)
            else ()
          val result = Exn.capture work ()
          val elapsed = Time.- (Time.now (),started)
          val (count,prior) = (case Symtab.lookup (!totals) stage of
            SOME value => value
          | NONE => (0,Time.zeroTime))
          val _ = totals := Symtab.update
            (stage,(count+1,Time.+ (prior,elapsed))) (!totals)
          val _ = active_stage := previous_stage
          val status = (case result of Exn.Res _ => "complete" | Exn.Exn _ => "failed")
          val _ = if traced then Comma_Proof_Profile.report
            (owner ^ " stage=" ^ stage ^ "-" ^ status ^ " ordinal=" ^
              Int.toString ordinal ^ " elapsed_ms=" ^
              LargeInt.toString (Time.toMilliseconds elapsed)) else ()
        in Exn.release result end
    end

  fun prove_profiled profile stage ctxt fixes assumes proposition tactic =
    with_profile profile stage
      (fn () => Goal.prove ctxt fixes assumes proposition tactic)

  fun nat n = HOLogic.mk_number natT n

  (* Reverse a closed object equality by a theorem conversion.  The only
     accepted shape is a HOL-universal prefix ending in an object equality;
     this keeps symmetry transport structural and avoids rebuilding a proof
     with a simplifier for every normalized graph node. *)
  fun object_symmetric ctxt theorem =
    let
      val original = Thm.prop_of theorem
      val _ = if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
          andalso null (Thm.tpairs_of theorem)
          andalso not (Term.is_open original)
          andalso null (Term.add_frees original [])
          andalso null (Term.add_vars original [])
          andalso Context.subthy (Thm.theory_of_thm theorem,
            Proof_Context.theory_of ctxt) then ()
        else error "Cannot reverse an open or foreign weighted-action equality"
      val eq_commute = @{thm HOL.eq_commute} RS @{thm eq_reflection}
      fun reverse_body context current =
        (case Thm.term_of current of
          Const (name, _) $ Abs _ =>
            if name = @{const_name All} then
              Conv.arg_conv
                (Conv.abs_conv (fn (_, body_context) =>
                  reverse_body body_context) context) current
            else Conv.rewr_conv eq_commute current
        | _ => Conv.rewr_conv eq_commute current)
      val conversion = Conv.arg_conv (reverse_body ctxt)
        (Thm.cprop_of theorem)
      val reversed = Thm.equal_elim conversion theorem
      val expected = Thm.term_of (Thm.rhs_of conversion)
      val actual = Thm.prop_of reversed
      val _ = if Thm.nprems_of reversed = 0 andalso
          null (Thm.hyps_of reversed) andalso null (Thm.tpairs_of reversed) andalso
          not (Term.is_open actual) andalso
          null (Term.add_frees actual []) andalso null (Term.add_vars actual []) andalso
          actual aconv expected andalso
          Context.subthy (Thm.theory_of_thm reversed,
            Proof_Context.theory_of ctxt) then ()
        else error "Weighted-action symmetry conversion changed its theorem authority"
    in reversed end

  (* A local typed view of one checked literal vector.  Reuse its cterms for
     every selected cell so deep child payloads are not re-certified per row. *)
  datatype literal_vector = Literal_Vector of
   {rows_ct: cterm, nth_function_ct: cterm, cells: term list}

  fun make_literal_vector_cterm ctxt rows_ct =
    let
      val source_theory = Thm.theory_of_cterm rows_ct
      val current_theory = Proof_Context.theory_of ctxt
      val _ = if Context.subthy (source_theory,current_theory) then ()
        else error "Weighted CRT literal vector cterm belongs to a foreign or newer theory"
      val rows = Thm.term_of rows_ct
      val cells = HOLogic.dest_list rows
      val rowT = (case fastype_of rows of
          Type (name,[elementT]) =>
            if name = @{type_name list} then elementT
            else error "Weighted CRT selected row source is not a list"
        | _ => error "Weighted CRT selected row source has a malformed type")
      val _ = if fastype_of rows = HOLogic.listT rowT then ()
        else error "Weighted CRT literal vector has an inconsistent element type"
      val nth_function = Const (@{const_name nth},fastype_of rows --> natT --> rowT)
      val nth_function_ct = Thm.cterm_of ctxt nth_function
    in Literal_Vector {rows_ct=rows_ct,nth_function_ct=nth_function_ct,
      cells=cells} end

  fun make_literal_vector ctxt rows =
    make_literal_vector_cterm ctxt (Thm.cterm_of ctxt rows)

  fun literal_vector_rows_ct (Literal_Vector {rows_ct,...}) = rows_ct

  (* Select one cell from the validated spine without normalizing neighboring
     payloads.  The cached row cterm is applied directly to the nth function. *)
  fun literal_nth_conversion_cterm ctxt successor_equation index
      (Literal_Vector {rows_ct,nth_function_ct,cells}) =
    let
      val _ = if index >= 0 andalso index < length cells then ()
        else error "Weighted CRT selected row is outside its literal list"
      val request_ct = Thm.apply
        (Thm.apply nth_function_ct rows_ct) (Thm.cterm_of ctxt (nat index))
      val request = Thm.term_of request_ct
      val nth_zero = @{thm nth_Cons_0} RS @{thm eq_reflection}
      val nth_successor = @{thm nth_Cons_Suc} RS @{thm eq_reflection}
      fun descend remaining current =
        let
          val (function_ct,index_ct) = Thm.dest_comb current
          val (constant_ct,_) = Thm.dest_comb function_ct
          val _ = (case Thm.term_of constant_ct of
            Const (name,_) => if name = @{const_name nth} then ()
              else error "Weighted CRT literal selection changed the nth operator"
          | _ => error "Weighted CRT literal selection lost the nth operator")
          val _ = if Thm.term_of index_ct aconv nat remaining then ()
            else error "Weighted CRT literal selection exceeded its checked spine"
        in
          if remaining = 0 then Conv.rewr_conv nth_zero current
          else
            let
              val index_equation = Thm.symmetric
                (successor_equation (remaining - 1))
              val selected_index = Conv.arg_conv
                (Conv.rewr_conv index_equation) current
              val selected_head = Conv.rewr_conv nth_successor
                (Thm.rhs_of selected_index)
              val tail = descend (remaining - 1) (Thm.rhs_of selected_head)
            in Thm.transitive selected_index
              (Thm.transitive selected_head tail) end
        end
      val conversion = descend index request_ct
      val selected = List.nth (cells,index)
      val _ = if Thm.term_of (Thm.lhs_of conversion) aconv request andalso
          Thm.term_of (Thm.rhs_of conversion) aconv selected then ()
        else error "Weighted CRT literal selection returned another row"
    in conversion end

  fun check_axis axis =
    if 0 <= axis andalso axis < length radices then List.nth (radices,axis)
    else error "Weighted CRT term transport axis is outside 0..3"

  fun check_term_type label expected term =
    if fastype_of term = expected then ()
    else error (label ^ " has the wrong type")

  fun checked_closed ctxt label proposition theorem =
    if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem) andalso
        not (Term.is_open (Thm.prop_of theorem)) andalso
        null (Term.add_frees (Thm.prop_of theorem) []) andalso
        null (Term.add_vars (Thm.prop_of theorem) []) andalso
        Thm.prop_of theorem aconv proposition andalso
        null (Thm_Deps.all_oracles [theorem]) andalso
        Context.subthy (Thm.theory_of_thm theorem,
          Proof_Context.theory_of ctxt)
    then theorem
    else error (label ^ " was not a closed native theorem in this context")

  fun checked_closed_profile native_certify profile ctxt label proposition theorem =
    with_profile profile "closed_validation" (fn () =>
      if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
          null (Thm.tpairs_of theorem) andalso
          not (Term.is_open (Thm.prop_of theorem)) andalso
          null (Term.add_frees (Thm.prop_of theorem) []) andalso
          null (Term.add_vars (Thm.prop_of theorem) []) andalso
          Thm.prop_of theorem aconv proposition andalso
          Context.subthy (Thm.theory_of_thm theorem,
            Proof_Context.theory_of ctxt) then
        (ignore (native_certify theorem); theorem)
      else error (label ^ " was not a closed native theorem in this context"))

  fun specialize_hol_all ctxt argument theorem =
    let
      val quantified = HOLogic.dest_Trueprop (Thm.prop_of theorem)
      val (_,quantified_ct) = Thm.dest_comb (Thm.cprop_of theorem)
      val _ = if Thm.term_of quantified_ct aconv quantified then ()
        else error "Weighted CRT specialization changed its certified proposition"
      val _ =
        (case strip_comb quantified of
          (Const (name,_),[abstraction as Abs (_,domainT,_)]) =>
            if name = @{const_name All} andalso domainT = natT andalso
                fastype_of abstraction = natT --> HOLogic.boolT then ()
            else error "Weighted CRT specialization expects a natural HOL universal"
        | _ => error "Weighted CRT specialization expects a HOL universal")
      (* The theorem already owns this certified predicate.  Re-certifying its
         complete child trees for every scalar specialization defeats reuse. *)
      val (_,predicate_ct) = Thm.dest_comb quantified_ct
      val rule = Drule.infer_instantiate' ctxt
        [SOME predicate_ct,
         SOME (Thm.cterm_of ctxt argument)] @{thm spec}
    in Thm.implies_elim rule theorem end

  fun pointwise_reflexive native_certify profile ctxt apply_const root_offset phase action =
    let
      val _ = if fastype_of root_offset = natT andalso fastype_of phase = natT
        then () else error "Weighted CRT reflexivity variables are not natural"
      val application = apply_const $ action $ phase
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
        ("root_offset", natT, HOLogic.mk_all ("phase", natT,
          HOLogic.mk_eq (application, application))))
      val reflexivity = Thm.reflexive (Thm.cterm_of ctxt application)
      val object_equality = reflexivity RS @{thm meta_eq_to_obj_eq}
      val phase_all = Thm.forall_intr (Thm.cterm_of ctxt phase)
        object_equality COMP @{thm allI}
      val theorem = Thm.forall_intr (Thm.cterm_of ctxt root_offset)
        phase_all COMP @{thm allI}
    in checked_closed_profile native_certify profile ctxt
      "Weighted CRT leaf reflexivity theorem" proposition theorem end

  fun compose_pointwise_with check ctxt label apply_const root_offset phase
      source target facts =
    let
      val _ = if fastype_of root_offset = natT andalso fastype_of phase = natT andalso
          fastype_of source = fastype_of target then ()
        else error "Weighted CRT pointwise composition has mismatched endpoint types"
      val (source_reconstruction,canonical) =
        (case facts of
          [reconstruction,normalization] => (reconstruction,normalization)
        | _ => error "Weighted CRT pointwise transport needs two certificates")
      val source_at_offset = specialize_hol_all ctxt root_offset source_reconstruction
      val source_at_phase = specialize_hol_all ctxt phase source_at_offset
      val normalized_at_offset = specialize_hol_all ctxt root_offset canonical
      val normalized_at_phase = specialize_hol_all ctxt phase normalized_at_offset
      fun equation theorem =
        HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of theorem))
      val (source_lhs,source_rhs) = equation source_at_phase
      val (normalized_lhs,normalized_rhs) = equation normalized_at_phase
      val _ = if source_lhs aconv (apply_const $ source $ phase) andalso
          source_rhs aconv normalized_lhs andalso
          normalized_rhs aconv (apply_const $ target $ phase) then ()
        else error "Weighted CRT pointwise certificates do not compose at exact endpoints"
      val composed_meta = Thm.transitive
        (source_at_phase RS @{thm eq_reflection})
        (normalized_at_phase RS @{thm eq_reflection})
      val composed_object = composed_meta RS @{thm meta_eq_to_obj_eq}
      val phase_all = Thm.forall_intr (Thm.cterm_of ctxt phase)
        composed_object COMP @{thm allI}
      val closed = Thm.forall_intr (Thm.cterm_of ctxt root_offset)
        phase_all COMP @{thm allI}
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
        ("root_offset",natT,HOLogic.mk_all ("phase",natT,
          HOLogic.mk_eq
            (apply_const $ source $ phase,apply_const $ target $ phase))))
    in check label proposition closed end

  fun compose_pointwise ctxt label apply_const root_offset phase source target facts =
    compose_pointwise_with (fn name => fn proposition => fn theorem =>
      checked_closed ctxt name proposition theorem) ctxt label apply_const
      root_offset phase source target facts

  fun compose_pointwise_profile native_certify profile ctxt label apply_const root_offset phase
      source target facts =
    with_profile profile "branch_normalize"
      (fn () => compose_pointwise_with
        (fn name => fn proposition => fn theorem =>
          checked_closed_profile native_certify profile ctxt name proposition theorem)
        ctxt label apply_const root_offset phase source target facts)

  (* The data owner performs traversal, reservation, cache admission, and
     publication.  These proof constructors only consume its checked terms
     and already-certified child facts. *)
  fun certify_wellformed_tree ctxt payloadT tree child_wellformed =
    let
      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
      val _ = check_term_type "Weighted CRT wellformed tree" dagT tree
      val wellformed_const = Const
        (@{const_name comma_weighted_crt_wellformed},dagT --> HOLogic.boolT)
      val proposition = HOLogic.mk_Trueprop (wellformed_const $ tree)
      val theorem = Goal.prove ctxt [] [] proposition
        (fn {context,...} =>
          asm_full_simp_tac (context addsimps
            (@{thms comma_weighted_crt_wellformed.simps
              comma_crt_axis_radix_def list_all_iff prod_set_defs} @
              child_wellformed)) 1)
        |> checked_closed ctxt "Weighted CRT recursive wellformedness" proposition
    in theorem end

  fun certify_raw_cofactor ctxt payloadT axis slot source_tree result_action
      child_equations =
    let
      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
      val actionT = HOLogic.mk_prodT (natT,dagT)
      val _ = check_axis axis
      val _ = if slot >= 0 andalso slot < List.nth (radices,axis) then ()
        else error "Weighted CRT raw cofactor proof slot is outside its radix"
      val _ = check_term_type "Weighted CRT raw cofactor source" dagT source_tree
      val _ = check_term_type "Weighted CRT raw cofactor result" actionT result_action
      val raw_cofactor_const = Const
        (@{const_name comma_weighted_crt_cofactor_all_raw},
          natT --> natT --> dagT --> actionT)
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq
        (result_action,raw_cofactor_const $ nat axis $ nat slot $ source_tree))
      val theorem = Goal.prove ctxt [] [] proposition
        (fn {context,...} =>
          asm_full_simp_tac (context addsimps
            (@{thms comma_weighted_crt_cofactor_all_raw.simps
              comma_crt_axis_radix_def Let_def case_prod_unfold} @
              child_equations)) 1)
        |> checked_closed ctxt "Weighted CRT raw cofactor constructor" proposition
    in theorem end

  fun certify_cofactor_result_wellformed ctxt payloadT result_tree
      source_wellformed cofactor_equation =
    let
      val dagT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
      val _ = check_term_type "Weighted CRT cofactor wellformed result" dagT result_tree
      val wellformed_const = Const
        (@{const_name comma_weighted_crt_wellformed},dagT --> HOLogic.boolT)
      val proposition = HOLogic.mk_Trueprop (wellformed_const $ result_tree)
      val _ = if Thm.nprems_of source_wellformed = 0 andalso
          Thm.nprems_of cofactor_equation = 0 then ()
        else error "Weighted CRT cofactor wellformedness needs closed source facts"
      val theorem = Goal.prove ctxt [] [] proposition
        (fn {context,...} =>
          asm_full_simp_tac (context addsimps
            [source_wellformed,cofactor_equation,
             @{thm comma_weighted_crt_cofactor_all_raw_wellformed},
             @{thm comma_crt_axis_radix_def}]) 1)
        |> checked_closed ctxt "Weighted CRT cofactor-result wellformedness"
          proposition
    in theorem end


end
