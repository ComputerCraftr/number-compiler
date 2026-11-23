(* Checked bindings of the 46 admitted classes to their existing program
   definitions. Shared by consumers; candidate program terms are not authority. *)
structure Comma_Direct_Class_Bindings =
struct
  structure Utils = Comma_CRT_MDD_Proof_Utils
  fun indexed_rows ctxt predicate facts =
    let
      val _ = if length facts = 46 then () else error "Expected 46 checked class rows"
      val natT = @{typ nat}
      fun nat n = HOLogic.mk_number natT n
      val literal = Utils.literal_list_all ctxt "Direct checked class rows" predicate
        (map nat (0 upto 45)) facts
      val upt = @{term "upt :: nat => nat => nat list"} $ nat 0 $ nat 46
      val conversion = Simplifier.rewrite
        (Comma_Entry_Arithmetic.natural_context ctxt |> Simplifier.add_simps @{thms upt_rec})
        (Thm.cterm_of ctxt upt)
      val list_all = Const (@{const_name list_all},
        (natT --> @{typ bool}) --> @{typ "nat list"} --> @{typ bool})
      val lifted = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt (list_all $ predicate))) conversion
      val proposition = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt
          (Const (@{const_name Trueprop},@{typ bool} --> @{typ prop})))) lifted
    in Thm.equal_elim (Thm.symmetric proposition) literal end

  fun make ctxt =
    let
      val evaluator = Code_Simp.static_conv
        {ctxt=ctxt,simpset=NONE,consts=Code_Thingol.read_const_exprs ctxt
          [@{const_name comma_semantic_phase_program_for_class}]} ctxt
      val codec = Comma_Selected_List_Alias.make_codec
        {ctxt=ctxt,validate_equation=Comma_Selected_List_Conversion.validate_equation}
      fun certify cid program =
        let
          val _ = if 0 <= cid andalso cid < 46 andalso Utils.closed program andalso
              fastype_of program = @{typ comma_semantic_port_program} then ()
            else error "Direct class binding requires an admitted class and closed program"
          val request = @{term comma_semantic_phase_program_for_class} $
            HOLogic.mk_number @{typ nat} cid
          val expected = @{term "Some :: comma_semantic_port_program => comma_semantic_port_program option"} $
            program
          val computed = evaluator (Thm.cterm_of ctxt request)
          val decoded = #decode codec (Thm.rhs_of computed)
          val decoded_equation = Thm.transitive computed decoded
          (* The checked code conversion can retain closed arithmetic in
             program fields. Normalize it before the exact expected-program
             check; normalization never supplies or changes authority. *)
          val normalized = Simplifier.rewrite
            (Comma_Entry_Arithmetic.natural_context ctxt)
            (Thm.rhs_of decoded_equation)
          val equation = Thm.transitive decoded_equation normalized
        in Utils.exact_prop ctxt "Direct class program binding"
          (Logic.mk_equals (request,expected)) equation RS @{thm meta_eq_to_obj_eq} end
    in certify end
end
