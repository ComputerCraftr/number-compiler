(* Shared checks for proofs issued from the immutable MDD certificate store. *)
signature COMMA_CRT_MDD_PROOF_UTILS =
sig
  val mk_less: term -> term -> term
  val ball_nat: term -> term -> term
  val set_nat: int list -> term
  val closed: term -> bool
  val ensure_closed_context: Proof.context -> string -> thm -> thm
  val exact_prop: Proof.context -> string -> term -> thm -> thm
  val prove_exact: Proof.context -> string -> term -> (Proof.context -> tactic) -> thm
  val literal_list_all: Proof.context -> string -> term -> term list -> thm list -> thm
  val predicate_application: Proof.context -> string -> term -> term -> thm -> thm
  val dest_nat: string -> typ -> term -> int
end

structure Comma_CRT_MDD_Proof_Utils:> COMMA_CRT_MDD_PROOF_UTILS =
struct
  fun mk_less left right = HOLogic.mk_binrel @{const_name less} (left,right)
  fun ball_nat set predicate =
    Const (@{const_name Ball}, HOLogic.mk_setT @{typ nat} -->
      (@{typ nat} --> HOLogic.boolT) --> HOLogic.boolT) $ set $ predicate
  fun set_nat xs = Const (@{const_name set}, @{typ "nat list"} -->
    HOLogic.mk_setT @{typ nat}) $
      HOLogic.mk_list @{typ nat} (map (HOLogic.mk_number @{typ nat}) xs)

  fun closed term = not (Term.is_open term) andalso
    null (Term.add_frees term []) andalso null (Term.add_vars term [])

  fun ensure_closed_context ctxt label theorem =
    if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem) andalso closed (Thm.prop_of theorem) andalso
        Context.subthy (Thm.theory_of_thm theorem, Proof_Context.theory_of ctxt)
    then theorem else error (label ^ " is not a closed theorem in the store context")

  fun exact_prop ctxt label expected theorem =
    if Thm.prop_of theorem aconv expected
    then ensure_closed_context ctxt label theorem
    else error (label ^ " proves a different proposition\nExpected: " ^
      Syntax.string_of_term (Config.put show_types true ctxt) expected ^
      "\nActual: " ^ Syntax.string_of_term (Config.put show_types true ctxt)
        (Thm.prop_of theorem))

  fun prove_exact ctxt label expected tactic =
    Goal.prove_internal ctxt [] (Thm.cterm_of ctxt expected)
      (fn _ => tactic ctxt)
    |> exact_prop ctxt label expected

  (* Fold only already-checked literal facts; neither the predicate nor its
     items are evaluated by this generic list constructor. *)
  fun literal_list_all ctxt label predicate items facts =
    let
      val itemT = Term.domain_type (fastype_of predicate)
      val _ = if closed predicate andalso
          Term.range_type (fastype_of predicate) = HOLogic.boolT then ()
        else error (label ^ " requires a closed Boolean predicate")
      val _ = if length items = length facts then ()
        else error (label ^ " has missing or excess facts")
      fun check (item,fact) =
        if fastype_of item = itemT andalso closed item then
          exact_prop ctxt label
            (HOLogic.mk_Trueprop (Envir.beta_norm (predicate $ item))) fact
        else error (label ^ " contains an open or ill-typed item")
      val checked = map check (items ~~ facts)
      fun rule theorem = Drule.infer_instantiate ctxt
        [(("P",0),Thm.cterm_of ctxt predicate)] theorem
      val empty = @{thm iffD2} OF [rule @{thm list_all_Nil_iff},@{thm TrueI}]
      fun prepend head tail = @{thm iffD2} OF
        [rule @{thm list_all_Cons_iff},@{thm conjI} OF [head,tail]]
      val theorem = fold_rev prepend checked empty
      val list_all = Const (@{const_name list_all},
        (itemT --> HOLogic.boolT) --> HOLogic.listT itemT --> HOLogic.boolT)
      val expected = HOLogic.mk_Trueprop (list_all $ predicate $ HOLogic.mk_list itemT items)
    in exact_prop ctxt label expected theorem end

  fun predicate_application ctxt label predicate index normalized =
    let
      val _ = (case fastype_of predicate of
          Type (@{type_name fun}, [domain, range]) =>
            if domain = fastype_of index andalso range = HOLogic.boolT then ()
            else error (label ^ " has an ill-typed predicate application")
        | _ => error (label ^ " expects a function predicate"))
      val item_ct = Thm.apply (Thm.cterm_of ctxt predicate)
        (Thm.cterm_of ctxt index)
      val beta = Thm.beta_conversion false item_ct
      val trueprop_ct = Thm.cterm_of ctxt
        (Const (@{const_name Trueprop}, HOLogic.boolT --> @{typ prop}))
      val beta_trueprop = Thm.combination (Thm.reflexive trueprop_ct) beta
      val rhs = Thm.term_of (Thm.rhs_of beta)
      val normalized_prop = HOLogic.mk_Trueprop rhs
      val normalized = exact_prop ctxt (label ^ " normalized body")
        normalized_prop normalized
      val application = Thm.equal_elim (Thm.symmetric beta_trueprop) normalized
      val expected = HOLogic.mk_Trueprop
        (Thm.term_of (Thm.lhs_of beta))
    in exact_prop ctxt label expected application end

  fun dest_nat label natT term =
    (case try HOLogic.dest_number term of
      SOME (typ, value) =>
        if typ = natT andalso value >= 0 then
          (case try IntInf.toInt value of
            SOME number => number
          | NONE => error (label ^ " exceeds the local index range"))
        else error (label ^ " is not a natural numeral")
    | NONE => error (label ^ " is not a closed natural numeral"))
end
