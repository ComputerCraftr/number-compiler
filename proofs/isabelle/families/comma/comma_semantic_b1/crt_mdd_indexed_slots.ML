(* Kernel-only transport from an already checked concrete ordered row. *)
structure Comma_CRT_MDD_Indexed_Slots =
struct
  structure Utils = Comma_CRT_MDD_Proof_Utils

  val natT = @{typ nat}
  val boolT = @{typ bool}
  val zero_nth = mk_meta_eq @{thm nth_Cons_0}
  val suc_nth = mk_meta_eq @{thm nth_Cons_Suc}

  fun nth_ct ctxt list_ct index =
    let
      val listT = Thm.typ_of_cterm list_ct
      val itemT = (case listT of
        Type (name, [typ]) => if name = @{type_name list} then typ
          else error "MDD indexed vector is not a list"
      | _ => error "MDD indexed vector is not a list")
      val nth = Thm.cterm_of ctxt (Const (@{const_name nth}, listT --> natT --> itemT))
    in Thm.apply (Thm.apply nth list_ct) index end

  fun literal_nth successor index application =
    let
      fun descend slot input =
        if slot = 0 then Conv.rewr_conv zero_nth input
        else
          let
            val index_equation = Thm.symmetric (successor (slot - 1))
            val step = Thm.combination (Thm.reflexive (Thm.dest_fun input)) index_equation
            val drop = Conv.rewr_conv suc_nth (Thm.rhs_of step)
          in Thm.transitive step (Thm.transitive drop
            (descend (slot - 1) (Thm.rhs_of drop))) end
      val _ = if index >= 0 then () else error "MDD slot index is negative"
      val theorem = descend index application
      val _ = if Thm.term_of (Thm.lhs_of theorem) aconv Thm.term_of application
        then () else error "MDD literal vector lookup changed its requested slot"
    in theorem end

  fun vector_nth ctxt successor index vector =
    let
      val slot = Thm.cterm_of ctxt (HOLogic.mk_number natT index)
      val source = nth_ct ctxt (Thm.lhs_of vector) slot
      val lifted = Thm.combination
        (Thm.combination (Thm.reflexive (Thm.dest_fun (Thm.dest_fun source))) vector)
        (Thm.reflexive slot)
    in Thm.transitive lifted (literal_nth successor index (Thm.rhs_of lifted)) end

  fun bind_conversion ctxt successor fields index input =
    let
      val expanded = Thm.beta_conversion true input
      val term = Thm.term_of (Thm.rhs_of expanded)
      val (head, args) = strip_comb term
      val _ = if length args = 6 andalso
          Term.is_Const head andalso Term.dest_Const_name head =
            @{const_name comma_crt_mdd_bind_certificate} andalso length fields = 4
        then () else error "MDD indexed bind predicate has another shape"
      val operator = Thm.cterm_of ctxt (list_comb (head, take 2 args))
      val reduced = fold (fn vector => fn eq =>
        Thm.combination eq (vector_nth ctxt successor index vector))
        fields (Thm.reflexive operator)
    in Thm.transitive expanded reduced end

  (* Restore the literal row's three coordinates without unfolding the
     selected mapping or rewriting the authenticated Store term. *)
  fun selected_conversion ctxt successor (sources, payloads, results) index input =
    let
      fun field vector = Conv.rewr_conv (vector_nth ctxt successor index vector)
      val source = field sources
      val payload = field payloads
      val result = field results
      fun binary left right = Conv.combination_conv (Conv.arg_conv left) right
      val source_cofactor = binary Conv.all_conv (Conv.arg_conv source)
      val source_bound = binary source Conv.all_conv
      val source_payload = binary (Conv.arg_conv source) (Conv.arg_conv payload)
      val target_cofactor = binary (Conv.arg_conv (Conv.arg_conv payload)) (Conv.arg_conv result)
      val row = binary source_cofactor (binary source_bound (binary source_payload target_cofactor))
      val expanded = Thm.beta_conversion true input
    in Thm.transitive expanded (row (Thm.rhs_of expanded)) end

  fun adapt ctxt predicate convert index concrete =
    let
      val slot = Thm.cterm_of ctxt (HOLogic.mk_number natT index)
      val application = Thm.apply predicate slot
      val conversion = convert index application
      val _ = if Thm.term_of (Thm.lhs_of conversion) aconv Thm.term_of application
        then () else error "MDD slot conversion changed its predicate application"
      val trueprop = Thm.cterm_of ctxt (Const (@{const_name Trueprop}, boolT --> @{typ prop}))
      val equation = Thm.combination (Thm.reflexive trueprop) conversion
      val normalized = Utils.exact_prop ctxt "Concrete MDD bind slot"
        (Thm.term_of (Thm.rhs_of equation)) concrete
      val result = Thm.equal_elim (Thm.symmetric equation) normalized
    in Utils.exact_prop ctxt "MDD indexed predicate application"
      (Thm.term_of (Thm.lhs_of equation)) result end
end
