(* Bind certificate state and common proof constructors. *)
structure Comma_CRT_MDD_Bind_Replay_Support =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Slots = Comma_CRT_MDD_Indexed_Slots

  structure Key_Table = Table(
    type key = Arena.bind_key
    val ord = fn ((s, f, m), (s', f', m')) =>
      prod_ord int_ord (prod_ord int_ord (list_ord (prod_ord int_ord int_ord)))
        ((s, (f, m)), (s', (f', m'))))
  structure Cover_Table = Table(
    type key = int * int list
    val ord = prod_ord int_ord (list_ord int_ord))
  structure Cofactor_Family_Table = Table(
    type key = int * int
    val ord = prod_ord int_ord int_ord)
  structure Mapping_Family_Table = Table(
    type key = int * (int * int) list
    val ord = prod_ord int_ord (list_ord (prod_ord int_ord int_ord)))
  structure Selected_Cofactor_Table = Table(
    type key = int * (int * int)
    val ord = prod_ord int_ord (prod_ord int_ord int_ord))
  structure Selected_Target_Table = Table(
    type key = int * (int * (int * int) list)
    val ord = prod_ord int_ord (prod_ord int_ord (list_ord (prod_ord int_ord int_ord))))

  val natT = @{typ nat}
  val boolT = HOLogic.boolT
  val nodeT = @{typ "nat comma_crt_mdd_node"}
  val nodesT = HOLogic.listT nodeT
  val nat_listT = HOLogic.listT natT
  val pairT = HOLogic.mk_prodT (natT, natT)
  val pair_listT = HOLogic.listT pairT
  val pair_list_listT = HOLogic.listT pair_listT
  val option_natT = Type (@{type_name option}, [natT])

  fun nat n = HOLogic.mk_number natT n
  fun optionT typ = Type (@{type_name option}, [typ])
  fun some typ value = Const (@{const_name Some}, typ --> optionT typ) $ value
  val ball = Utils.ball_nat
  fun nat_list xs = HOLogic.mk_list natT (map nat xs)
  fun pair_term (x, y) = HOLogic.mk_prod (nat x, nat y)
  fun pair_list xs = HOLogic.mk_list pairT (map pair_term xs)
  val set_nat = Utils.set_nat
  fun nth listT elementT list index =
    Const (@{const_name nth}, listT --> natT --> elementT) $ list $ index
  fun list_all predicate values =
    Const (@{const_name list_all}, fastype_of predicate -->
      fastype_of values --> boolT) $ predicate $ values

  fun mk_less (x,y) = Utils.mk_less x y
  type cofactor_family = {theorem: thm}
  type mapping_family = {theorem: thm}

  type state =
    {store: Store.store, ctxt: Proof.context, simp_ctxt: Proof.context,
     radices: int list,
     slot_successor: int -> thm,
     slot_vectors: thm Termtab.table Unsynchronized.ref,
     bind_certificates: (int * thm) Key_Table.table Unsynchronized.ref,
     public_bind_certificates: (int * thm) Key_Table.table Unsynchronized.ref,
     cover_certificates: thm Cover_Table.table Unsynchronized.ref,
     cofactor_families: cofactor_family Cofactor_Family_Table.table Unsynchronized.ref,
     mapping_families: mapping_family Mapping_Family_Table.table Unsynchronized.ref,
     selected_cofactors: (int * thm) Selected_Cofactor_Table.table Unsynchronized.ref,
     selected_targets: (int * thm) Selected_Target_Table.table Unsynchronized.ref,
     radix_facts: (thm * thm * thm) Inttab.table Unsynchronized.ref,
     support_cache: int list Inttab.table Unsynchronized.ref,
     active: unit Key_Table.table Unsynchronized.ref,
     bind_visits: int Unsynchronized.ref, cover_visits: int Unsynchronized.ref,
     cofactor_family_hits: int Unsynchronized.ref,
     cofactor_family_builds: int Unsynchronized.ref,
     mapping_family_hits: int Unsynchronized.ref,
     mapping_family_builds: int Unsynchronized.ref,
     radix_fact_hits: int Unsynchronized.ref,
     radix_fact_builds: int Unsynchronized.ref,
     identity_restrictions: int Unsynchronized.ref,
     direct_branch_shapes: int Unsynchronized.ref,
     direct_indexed_slots: int Unsynchronized.ref,
     indexed_vector_builds: int Unsynchronized.ref,
     selected_leaf_branches: int Unsynchronized.ref,
     selected_leaf_rows: int Unsynchronized.ref,
     selected_cofactor_hits: int Unsynchronized.ref,
     selected_cofactor_builds: int Unsynchronized.ref,
     selected_target_hits: int Unsynchronized.ref,
     selected_target_builds: int Unsynchronized.ref,
     first_public_checkpoint: bool Unsynchronized.ref,
     proof_timings: (string * int * Time.time) list Unsynchronized.ref}

  type replay = {state: state, certify: Arena.bind_key -> thm,
    certify_cover: int -> int list -> thm}

  fun table_size ({store, ...}: state) =
    Const (@{const_name size}, nodesT --> natT) $ Store.table store

  fun bind_term ({store, ...}: state) mapping fallback source result =
    let
      val bindT = nat_listT --> nodesT --> pair_listT --> natT --> natT --> natT --> boolT
      val bind = Const (@{const_name comma_crt_mdd_bind_certificate}, bindT)
    in bind $ Store.radices store $ Store.table store $ mapping $ fallback $ source $ result end

  fun bind_prop state mapping fallback source result =
    bind_term state (pair_list mapping) (nat fallback) (nat source) (nat result)

  fun cover_term ({store, ...}: state) labels root =
    Const (@{const_name comma_crt_mdd_payload_cover},
      nodesT --> natT --> nat_listT --> boolT) $
      Store.table store $ root $ nat_list labels

  fun cover_prop state labels root = cover_term state labels (nat root)

  fun cofactor_term ({store, ...}: state) axis slot root =
    Const (@{const_name comma_crt_mdd_cofactor},
      nat_listT --> nodesT --> natT --> natT --> natT --> option_natT) $
      Store.radices store $ Store.table store $ axis $ slot $ root

  fun mapping_cofactor_term ({store, ...}: state) axis slot mapping =
    Const (@{const_name comma_crt_mdd_cofactor_mapping},
      nat_listT --> nodesT --> natT --> natT --> pair_listT -->
        optionT pair_listT) $
      Store.radices store $ Store.table store $ axis $ slot $ mapping

  fun bind_target_term fallback mapping payload =
    Const (@{const_name comma_crt_mdd_bind_target},
      natT --> pair_listT --> natT --> natT) $ fallback $ mapping $ payload

  fun simp_context ctxt =
    Comma_Entry_Arithmetic.natural_context ctxt
    |> Simplifier.add_simps
      (@{thms comma_crt_mdd_node.simps comma_crt_mdd_cofactor_def
        comma_crt_mdd_cofactor_family_admitted_def
        comma_crt_mdd_cofactor_family_child_def
        comma_crt_mdd_cofactor_mapping.simps comma_crt_mdd_bind_target_def
        list.simps list_all_iff list.map map_of.simps fun_upd_apply
        filter.simps if_True if_False
        list.size upt_rec option.simps set_simps insert_iff empty_iff mem_Collect_eq
        nth_Cons_0 nth_Cons_Suc nth_Cons'
        ball_simps mod_simps})

  fun update_proof_timing ({proof_timings, ...}: state) label elapsed =
    let
      fun update [] = [(label, 1, elapsed)]
        | update ((name, count, total) :: rest) =
            if name = label then (name, count + 1, Time.+ (total, elapsed)) :: rest
            else (name, count, total) :: update rest
    in proof_timings := update (!proof_timings) end

  (* Inclusive aggregates are collected only when the existing proof profiler
     is enabled.  Exceptions remain observable after their cost is recorded. *)
  fun profile_stage state label operation =
    if Comma_Proof_Profile.enabled () then
      let
        val started = Time.now ()
        val result = Exn.capture operation ()
        val _ = update_proof_timing state label (Time.- (Time.now (), started))
      in Exn.release result end
    else operation ()

  fun proof_profile_summary ({bind_visits, cover_visits, cofactor_family_hits,
      cofactor_family_builds, mapping_family_hits, mapping_family_builds,
      radix_fact_hits, radix_fact_builds,
      identity_restrictions, direct_branch_shapes, selected_leaf_branches,
      direct_indexed_slots, indexed_vector_builds,
      selected_leaf_rows, selected_cofactor_hits, selected_cofactor_builds,
      selected_target_hits, selected_target_builds,
      proof_timings, ...}: state) =
    let
      fun timing (label, count, elapsed) =
        label ^ ":calls=" ^ Int.toString count ^ ",ms=" ^
          LargeInt.toString (Time.toMilliseconds elapsed)
      val timings = String.concatWith ";" (map timing (rev (!proof_timings)))
    in
      "binds=" ^ Int.toString (!bind_visits) ^
      " covers=" ^ Int.toString (!cover_visits) ^
      " cofactor_family_hits=" ^ Int.toString (!cofactor_family_hits) ^
      " cofactor_family_builds=" ^ Int.toString (!cofactor_family_builds) ^
      " mapping_family_hits=" ^ Int.toString (!mapping_family_hits) ^
      " mapping_family_builds=" ^ Int.toString (!mapping_family_builds) ^
      " radix_fact_hits=" ^ Int.toString (!radix_fact_hits) ^
      " radix_fact_builds=" ^ Int.toString (!radix_fact_builds) ^
      " identity_restrictions=" ^ Int.toString (!identity_restrictions) ^
      " direct_branch_shapes=" ^ Int.toString (!direct_branch_shapes) ^
      " direct_indexed_slots=" ^ Int.toString (!direct_indexed_slots) ^
      " indexed_vector_builds=" ^ Int.toString (!indexed_vector_builds) ^
      " selected_leaf_branches=" ^ Int.toString (!selected_leaf_branches) ^
      " selected_leaf_rows=" ^ Int.toString (!selected_leaf_rows) ^
      " selected_cofactor_hits=" ^ Int.toString (!selected_cofactor_hits) ^
      " selected_cofactor_builds=" ^ Int.toString (!selected_cofactor_builds) ^
      " selected_target_hits=" ^ Int.toString (!selected_target_hits) ^
      " selected_target_builds=" ^ Int.toString (!selected_target_builds) ^
      " prove_bool={" ^ timings ^ "}"
    end

  fun checkpoint state stage =
    if Comma_Proof_Profile.enabled () then
      Comma_Proof_Profile.report
        ("MDD Bind Replay checkpoint=" ^ stage ^ " " ^ proof_profile_summary state)
    else ()

  fun prove_bool (state as {ctxt, simp_ctxt, ...}: state) label proposition facts =
    let
      val tracing = Comma_Proof_Profile.enabled ()
      val started = if tracing then Time.now () else Time.zeroTime
      val result = Exn.capture (fn () =>
        let
          val expected = HOLogic.mk_Trueprop proposition
          val theorem = Goal.prove ctxt [] [] expected
            (fn {context = goal_ctxt, ...} =>
              Method.insert_tac goal_ctxt facts 1 THEN
              Simplifier.asm_full_simp_tac simp_ctxt 1 THEN
              TRY (Arith_Data.arith_tac simp_ctxt 1) THEN
              TRY (auto_tac simp_ctxt))
        in Utils.exact_prop ctxt label expected theorem end) ()
      val _ = if tracing then update_proof_timing state label
        (Time.- (Time.now (), started)) else ()
    in Exn.release result end

  fun prove_closed state label expected facts rule =
    profile_stage state ("prove_closed/" ^ label) (fn () => let
      val {ctxt, simp_ctxt, ...} = state
      val theorem = Goal.prove ctxt [] [] expected
        (fn {context = goal_ctxt, ...} =>
          resolve_tac goal_ctxt [rule] 1 THEN
          ALLGOALS (fn i => FIRST
            (map (fn fact =>
              (resolve_tac goal_ctxt [Thm.forall_elim_vars 0 fact]
                THEN_ALL_NEW assume_tac goal_ctxt) i) facts @
             [assume_tac goal_ctxt i,
              Simplifier.asm_full_simp_tac
                (Simplifier.add_simps facts simp_ctxt) i])))
    in Utils.exact_prop ctxt label expected theorem end)

  fun intro_closed (state as {ctxt, ...}: state) label expected intro facts =
    profile_stage state ("intro_closed/" ^ label) (fn () => let
      val (type_instantiation, term_instantiation) = Thm.match
        (Thm.cterm_of ctxt (Thm.concl_of intro), Thm.cterm_of ctxt expected)
      val intro = Thm.instantiate
        (type_instantiation, term_instantiation) intro
      val intro = Conv.fconv_rule Drule.beta_eta_conversion intro
      val facts = map (Conv.fconv_rule Drule.beta_eta_conversion) facts
      val theorem = fold
        (fn fact => fn theorem => Thm.implies_elim theorem fact) facts intro
    in Utils.exact_prop ctxt label expected theorem end)

  fun lookup_equation (state as {store, ctxt, ...}: state) index =
    profile_stage state "frozen_lookup_equation" (fn () => let
      val theorem = Store.lookup store index
      val object_theorem = theorem RS @{thm meta_eq_to_obj_eq}
      val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
        (Const (@{const_name nth}, nodesT --> natT --> nodeT) $
          Store.table store $ nat index, Store.node_term (Store.node store index)))
    in Utils.exact_prop ctxt "Frozen MDD node equation" expected object_theorem end)

  fun root_bound (state as {store, ctxt, ...}: state) root =
    profile_stage state "frozen_root_bound" (fn () =>
      let val theorem = Store.bound store root
      in Utils.exact_prop ctxt "Frozen MDD root bound" (Thm.prop_of theorem) theorem end)

  fun unique xs = length xs = length (distinct (op =) xs)
  fun same_set xs ys = unique xs andalso unique ys andalso
    List.all (fn x => member (op =) ys x) xs andalso
    List.all (fn y => member (op =) xs y) ys
  fun restrict_mapping labels mapping =
    filter (fn (payload, _) => member (op =) labels payload) mapping

  fun mk_intro state label proposition intro facts =
    prove_closed state label (HOLogic.mk_Trueprop proposition) facts intro

  fun indexed_slots (state as {ctxt, slot_successor, direct_indexed_slots, ...}: state)
      radix predicate proofs convert =
    let
      val _ = if fastype_of predicate = @{typ "nat => bool"} andalso
          length proofs = radix then ()
        else error "MDD bind slot predicate or row count is invalid"
      val pred_ct = Thm.cterm_of ctxt predicate
      val items = profile_stage state "indexed_slot_adaptation" (fn () =>
        Vector.fromList (map_index (fn (index, proof) =>
          Slots.adapt ctxt pred_ct convert index proof) proofs))
      val _ = direct_indexed_slots := !direct_indexed_slots + radix
    in profile_stage state "indexed_row_assembly" (fn () =>
      Comma_Selected_List_Conversion.prove_indexed_list_all
        {ctxt=ctxt, predicate=predicate, bound=radix,
         prove_item=fn index => Vector.sub (items, index),
         zero_fact = @{thm comma_indexed_all_zero},
         step_fact = @{thm comma_indexed_all_Suc},
         successor_equation=slot_successor}) end

  fun slot_vector (state as {ctxt, slot_vectors, indexed_vector_builds, ...}: state)
      item_context term =
    case Termtab.lookup (!slot_vectors) term of
      SOME equation => equation
    | NONE =>
        let
          val context = item_context ()
          val equation = profile_stage state "indexed_vector_preparation"
            (fn () => Simplifier.rewrite context (Thm.cterm_of ctxt term))
          val _ = ignore (HOLogic.dest_list (Thm.term_of (Thm.rhs_of equation)))
          val _ = slot_vectors := Termtab.update (term, equation) (!slot_vectors)
          val _ = indexed_vector_builds := !indexed_vector_builds + 1
        in equation end

end
