structure Comma_Semantic_Continue_Application_Transport_Fixture =
struct
  structure Contract = Comma_Semantic_Continue_Observer_Contract
  structure Masked = Comma_Semantic_Continue_Masked_Columns
  structure Columns = Comma_Semantic_Continue_Column_Proofs
  structure Transport = Comma_Semantic_Continue_Application_Transport
  type value = Contract.value

  structure Fixture = Comma_Semantic_Continue_Apply_Memo_Fixture

  fun run ctxt =
    let
      val facts = Unsynchronized.ref (Termtab.empty:thm Termtab.table)
      val hits = Unsynchronized.ref 0
      val misses = Unsynchronized.ref 0
      val wrong_lhs_seen = Unsynchronized.ref false
      fun validate_native label theorem =
        if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
            andalso null (Thm.tpairs_of theorem) andalso Fixture.closed (Thm.prop_of theorem)
        then
          (Comma_Proof_Dependency_Audit.require_native_clean ctxt label [theorem];
           theorem)
        else error (label ^ " is not a closed native theorem")
      fun validate_equation label lhs rhs theorem =
        Comma_Semantic_Continue_Apply_Memo_Fixture.make_equation_validator ctxt
          wrong_lhs_seen label lhs rhs theorem
      val apply_proc = Columns.apply_memo_proc ctxt facts validate_equation hits misses
      val code_context = Columns.column_code_context ctxt apply_proc
      val conversion = Code_Simp.static_conv
        {ctxt=ctxt,simpset=SOME (Simplifier.simpset_of code_context),
         consts=[@{const_name comma_crt_apply_shifted_from},
           @{const_name comma_crt_apply},@{const_name comma_crt_shift}]}
      fun scalar label term =
        let
          val theorem = conversion ctxt (Thm.cterm_of ctxt term)
          val rhs = Thm.term_of (Thm.rhs_of theorem)
        in validate_equation label term rhs theorem end
      fun evaluate _ _ = error "application transport unexpectedly evaluated support"
      val callbacks:Masked.callbacks =
        {ctxt=ctxt,validate_native=validate_native,
         validate_equation=validate_equation,scalar=scalar,evaluate=evaluate}

      val true_column=Fixture.bool_column true
      val false_column=Fixture.bool_column false
      val zero_column=Fixture.node_column 0 [true_column,false_column,false_column,false_column]
      val one_column=Fixture.node_column 0 [false_column,true_column,false_column,false_column]
      val true_admitted= @{lemma
        "comma_crt_admitted 0 (Comma_CRT_Bool True)" by simp}
      val zero_admitted= @{lemma
        "comma_crt_admitted 0 (Comma_CRT_Node 0
          [Comma_CRT_Bool True, Comma_CRT_Bool False,
           Comma_CRT_Bool False, Comma_CRT_Bool False])"
        by (simp add: comma_crt_period_def)}
      val one_admitted= @{lemma
        "comma_crt_admitted 0 (Comma_CRT_Node 0
          [Comma_CRT_Bool False, Comma_CRT_Bool True,
           Comma_CRT_Bool False, Comma_CRT_Bool False])"
        by (simp add: comma_crt_period_def)}
      val true_cert={column=true_column,admitted=true_admitted}
      val zero_cert={column=zero_column,admitted=zero_admitted}
      val one_cert={column=one_column,admitted=one_admitted}

      val endpoint_proofs=Contract.observer_proofs validate_native ctxt
        (Unsynchronized.ref Termtab.empty) Contract.Continue_Endpoint
      val endpoint_observer=Contract.observer_term Contract.Continue_Endpoint
      val endpoint_admitted=Contract.observer_at_admitted validate_native ctxt
        endpoint_proofs endpoint_observer 25 1
      val _=validate_native "valid bounded endpoint observation" endpoint_admitted
      val invalid_endpoint=Exn.capture (fn () =>
        Contract.observer_at_admitted validate_native ctxt endpoint_proofs
          endpoint_observer 46 1) ()
      val _=case invalid_endpoint of Exn.Exn _ => ()
        | Exn.Res _ => error "endpoint observer admission accepted target 46"

      val full_actual=Masked.apply_and true_column zero_column
      val full_actual_admitted=Masked.apply_admitted callbacks
        "fixture full request admission" true_cert zero_cert
      val full_equivalent=Masked.true_mask_equiv callbacks
        "fixture full request equivalence" zero_cert
      val full:value={column=zero_column,admitted=zero_admitted,
        actual_admitted=full_actual_admitted,equivalent=full_equivalent}
      val _=if full_actual aconv
          (Masked.apply_and true_column (#column zero_cert)) then ()
        else error "fixture full request used the wrong True mask"

      val unmasked=Transport.unmask callbacks "fixture unmask" zero_column
        zero_admitted full
      val _=if #column unmasked aconv zero_column andalso
          Thm.prop_of (#equivalent unmasked) aconv
            (HOLogic.mk_Trueprop (@{term comma_crt_equiv_check} $
              zero_column $ zero_column)) then ()
        else error "full application did not unmask to its exact result"

      val zero_result= #1 (Masked.mask_value callbacks "fixture phase-zero mask"
        zero_cert zero_column unmasked)
      val one_result= #1 (Masked.mask_value callbacks "fixture phase-one mask"
        one_cert zero_column unmasked)
      val _=if #column zero_result aconv zero_column andalso
          #column one_result aconv false_column then ()
        else error "partial mask restriction lost the source phase"
      val _=validate_native "fixture phase-zero restricted equivalence"
        (#equivalent zero_result)
      val _=validate_native "fixture phase-one restricted equivalence"
        (#equivalent one_result)

      fun rejects label action =
        (case Exn.capture action () of
          Exn.Exn (ERROR _) => ()
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error (label ^ " accepted foreign exact authority"))
      val _=rejects "foreign source-phase actual" (fn () =>
        Transport.unmask callbacks "foreign source-phase actual" one_column
          one_admitted full)
      val _=rejects "foreign admission for exact actual" (fn () =>
        Transport.unmask callbacks "foreign admission for exact actual" zero_column
          one_admitted full)
      val _=rejects "incompatible incoming actual" (fn () =>
        Masked.mask_value callbacks "incompatible incoming actual" zero_cert
          one_column unmasked)

      val retry= #1 (Masked.mask_value callbacks "fixture retry after rejection"
        zero_cert zero_column unmasked)
      val _=if #column retry aconv zero_column then ()
        else error "rejected foreign authority corrupted later transport"
    in () end
end
