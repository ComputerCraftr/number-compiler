(* Exact phase transport from the source-issued typed action roots into the
   M204 work table.  All row equalities are derived from checked zip certificates. *)
structure Comma_Frontier_M204_Source_Transport =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Utils = Comma_CRT_MDD_Proof_Utils
  val natT = @{typ nat}
  val listT = HOLogic.listT natT
  val nodeT = @{typ "nat comma_crt_mdd_node"}
  val nodesT = HOLogic.listT nodeT
  val optionT = @{typ "nat option"}
  fun nat n = HOLogic.mk_number natT n
  fun tp p = HOLogic.mk_Trueprop p
  fun vector xs = HOLogic.mk_list natT (map nat xs)
  fun nth xs index = Const (@{const_name nth},listT --> natT --> natT) $ xs $ index
  fun eval store phase root =
    Const (@{const_name comma_crt_mdd_eval_phase},
      listT --> nodesT --> natT --> natT --> optionT) $
      Store.radices store $ Store.table store $ phase $ root
  fun less x y = HOLogic.mk_binrel @{const_name less} (x,y)

  fun prove source source_handles work work_handles phase_facts source_exact action =
    let
      val ctxt = Store.context work
      val source_ids = map (Store.action_index source) source_handles
      val work_ids = map (Store.action_index work) work_handles
      val _ = if length source_ids=46 andalso length work_ids=46 andalso
          length phase_facts=46 andalso Store.radices source aconv Store.radices work then ()
        else error "M204 source transport requires matching 46-root stores"
      val source_roots = vector source_ids
      val work_roots = vector work_ids
      val source_phase = Free ("source_action_phase",natT)
      val source_cid = Free ("source_action_cid",natT)
      val source_result = @{term comma_frontier_m204_action_code} $ source_phase $
        (@{term comma_semantic_phase_program_class_step} $ source_phase $ source_cid)
      val source_equation = tp (HOLogic.mk_eq
        (eval source source_phase (nth source_roots source_cid),
         Const (@{const_name Some},natT --> optionT) $ source_result))
      val source_contract = Logic.all source_phase
        (Logic.mk_implies (tp (less source_phase (nat 924)),
          Logic.all source_cid
            (Logic.mk_implies (tp (less source_cid (nat 46)),source_equation))))
      val expected_action = @{term comma_frontier_m204_mdd_value} $
        Store.radices work $ Store.table work $ work_roots
      val _ = if action aconv expected_action then ()
        else error "M204 work action is not the selected frozen MDD vector"
      val source_exact = Utils.exact_prop ctxt
        "M204 universal class-action authority" source_contract source_exact
      val predicate = Abs ("cid",natT,
        HOLogic.mk_all ("phase",natT,HOLogic.mk_eq
          (eval source (Bound 0) (nth source_roots (Bound 1)),
           eval work (Bound 0) (nth work_roots (Bound 1)))))
      val scalar = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps @{thms list.simps list.size nth_Cons_0 nth_Cons_Suc nth_Cons_numeral nth_Cons'}
      fun one i =
        let
          val expected = tp (Envir.beta_norm (predicate $ nat i))
          val fact = List.nth (phase_facts,i)
        in Utils.prove_exact ctxt "M204 authenticated imported action row" expected
          (fn context => Method.insert_tac context [fact] 1 THEN auto_tac scalar) end
      val facts = map one (0 upto 45)
      val literal = Utils.literal_list_all ctxt "M204 imported action rows" predicate
        (map nat (0 upto 45)) facts
      val list_all = Const (@{const_name list_all},
        (natT --> HOLogic.boolT) --> listT --> HOLogic.boolT)
      val upt = Const (@{const_name upt},natT --> natT --> listT) $ nat 0 $ nat 46
      val upt_conversion = Simplifier.rewrite
        (Comma_Entry_Arithmetic.natural_context ctxt |> Simplifier.add_simps @{thms upt_rec})
        (Thm.cterm_of ctxt upt)
      val lifted = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt (list_all $ predicate))) upt_conversion
      val proposition_conversion = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt
          (Const (@{const_name Trueprop},HOLogic.boolT --> @{typ prop})))) lifted
      val indexed = Thm.equal_elim (Thm.symmetric proposition_conversion)
        (Utils.exact_prop ctxt "M204 literal imported rows"
          (Thm.term_of (Thm.rhs_of proposition_conversion)) literal)
      val phase = Free ("m204_source_phase",natT)
      val cid = Free ("m204_source_cid",natT)
      val phase_guard = tp (less phase (nat 924))
      val cid_guard = tp (less cid (nat 46))
      val result = HOLogic.mk_eq (action $ phase $ cid,
        @{term comma_frontier_m204_action_code} $ phase $
          (@{term comma_semantic_phase_program_class_step} $ phase $ cid))
      val proposition = Logic.all phase (Logic.all cid
        (Logic.mk_implies (phase_guard,Logic.mk_implies (cid_guard,tp result))))
      val theorem = Utils.prove_exact ctxt "M204 source-issued action transport" proposition
        (fn context => Method.insert_tac context [indexed,source_exact] 1 THEN
          auto_tac (Comma_Entry_Arithmetic.natural_context context
            |> Simplifier.add_simps [@{thm comma_frontier_m204_mdd_value_def},
                @{thm list_all_iff}, @{thm set_upt}, @{thm atLeastLessThan_iff}]))
    in theorem end
end
