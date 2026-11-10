(* Kernel replay for Arena's memoized bind witnesses.  The arena is only a
   proposal producer: every witness is checked against the Store's exact
   node equations and the generic bind constructors before it is returned. *)
signature COMMA_CRT_MDD_BIND_REPLAY =
sig
  type replay
  val make: Comma_CRT_MDD_Certificate_Store.store -> replay
  val certify_bind: replay -> Comma_CRT_MDD_Arena.bind_key -> thm
  val bind_eval_phase: replay -> Comma_CRT_MDD_Arena.bind_key -> thm
  val statistics: replay -> string
end

structure Comma_CRT_MDD_Bind_Replay:> COMMA_CRT_MDD_BIND_REPLAY =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Utils = Comma_CRT_MDD_Proof_Utils

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
  fun ball set predicate =
    Const (@{const_name Ball}, HOLogic.mk_setT natT -->
      (natT --> boolT) --> boolT) $ set $ predicate
  fun nat_list xs = HOLogic.mk_list natT (map nat xs)
  fun pair_term (x, y) = HOLogic.mk_prod (nat x, nat y)
  fun pair_list xs = HOLogic.mk_list pairT (map pair_term xs)
  fun set_nat xs =
    Const (@{const_name set}, nat_listT --> HOLogic.mk_setT natT) $ nat_list xs
  fun nth listT elementT list index =
    Const (@{const_name nth}, listT --> natT --> elementT) $ list $ index
  fun list_all predicate values =
    Const (@{const_name list_all}, fastype_of predicate -->
      fastype_of values --> boolT) $ predicate $ values
  fun mk_less (x, y) = HOLogic.mk_binrel @{const_name less} (x, y)

  type cofactor_family = {theorem: thm}
  type mapping_family = {theorem: thm}

  type state =
    {store: Store.store, ctxt: Proof.context, simp_ctxt: Proof.context,
     radices: int list,
     bind_certificates: (int * thm) Key_Table.table Unsynchronized.ref,
     public_bind_certificates: (int * thm) Key_Table.table Unsynchronized.ref,
     cover_certificates: thm Cover_Table.table Unsynchronized.ref,
     cofactor_families: cofactor_family Cofactor_Family_Table.table Unsynchronized.ref,
     mapping_families: mapping_family Mapping_Family_Table.table Unsynchronized.ref,
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
     proof_timings: (string * int * Time.time) list Unsynchronized.ref}

  type replay = {state: state, certify: Arena.bind_key -> thm}

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

  fun proof_profile_summary ({bind_visits, cover_visits, cofactor_family_hits,
      cofactor_family_builds, mapping_family_hits, mapping_family_builds,
      radix_fact_hits, radix_fact_builds,
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
    let
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
    in Utils.exact_prop ctxt label expected theorem end

  fun intro_closed ({ctxt, ...}: state) label expected intro facts =
    let
      val (type_instantiation, term_instantiation) = Thm.match
        (Thm.cterm_of ctxt (Thm.concl_of intro), Thm.cterm_of ctxt expected)
      val intro = Thm.instantiate
        (type_instantiation, term_instantiation) intro
      val intro = Conv.fconv_rule Drule.beta_eta_conversion intro
      val facts = map (Conv.fconv_rule Drule.beta_eta_conversion) facts
      val theorem = fold
        (fn fact => fn theorem => Thm.implies_elim theorem fact) facts intro
    in Utils.exact_prop ctxt label expected theorem end

  fun lookup_equation ({store, ctxt, ...}: state) index =
    let
      val theorem = Store.lookup store index
      val object_theorem = theorem RS @{thm meta_eq_to_obj_eq}
      val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
        (Const (@{const_name nth}, nodesT --> natT --> nodeT) $
          Store.table store $ nat index, Store.node_term (Store.node store index)))
    in Utils.exact_prop ctxt "Frozen MDD node equation" expected object_theorem end

  fun root_bound ({store, ctxt, ...}: state) root =
    let val theorem = Store.bound store root
    in Utils.exact_prop ctxt "Frozen MDD root bound" (Thm.prop_of theorem) theorem end

  fun unique xs = length xs = length (distinct (op =) xs)
  fun same_set xs ys = unique xs andalso unique ys andalso
    List.all (fn x => member (op =) ys x) xs andalso
    List.all (fn y => member (op =) xs y) ys
  fun restrict_mapping labels mapping =
    filter (fn (payload, _) => member (op =) labels payload) mapping

  fun mk_intro state label proposition intro facts =
    prove_closed state label (HOLogic.mk_Trueprop proposition) facts intro

  fun indexed_slots (state as {ctxt, ...}: state)
      radix predicate proofs item_context =
    let
      val _ = if fastype_of predicate = @{typ "nat => bool"} then ()
        else error "MDD bind slot predicate has the wrong type"
      val successor_cache = Comma_Selected_List_Conversion.make_successor_cache ctxt radix
      fun proof_item index =
        let
          val index_term = nat index
          val application = Thm.apply (Thm.cterm_of ctxt predicate)
            (Thm.cterm_of ctxt index_term)
          val conversion = Simplifier.rewrite item_context application
          val trueprop_ct = Thm.cterm_of ctxt
            (Const (@{const_name Trueprop}, boolT --> @{typ prop}))
          val proposition_conversion = Thm.combination
            (Thm.reflexive trueprop_ct) conversion
          val normalized_prop = HOLogic.mk_Trueprop (Thm.term_of (Thm.rhs_of conversion))
          val normalized = Utils.exact_prop ctxt "Concrete MDD bind slot normalization"
            normalized_prop (List.nth (proofs, index))
          val item = Thm.equal_elim (Thm.symmetric proposition_conversion) normalized
          val expected = HOLogic.mk_Trueprop (predicate $ index_term)
        in Utils.exact_prop ctxt "Concrete MDD bind predicate application" expected item end
      val all = Comma_Selected_List_Conversion.prove_indexed_list_all
        {ctxt=ctxt, predicate=predicate, bound=radix, prove_item=proof_item,
         zero_fact = @{thm comma_indexed_all_zero},
         step_fact = @{thm comma_indexed_all_Suc},
         successor_equation= #equation successor_cache}
    in all end

  fun make store =
    let
      val ctxt = Store.context store
      val radices = map (Utils.dest_nat "MDD radix" natT)
        (HOLogic.dest_list (Store.radices store))
      val _ = if not (null radices) andalso List.all (fn radix => radix > 0) radices
        then () else error "Frozen MDD table has an invalid radix vector"
      val state: state =
        {store=store, ctxt=ctxt, simp_ctxt=simp_context ctxt, radices=radices,
         bind_certificates=Unsynchronized.ref Key_Table.empty,
         public_bind_certificates=Unsynchronized.ref Key_Table.empty,
         cover_certificates=Unsynchronized.ref Cover_Table.empty,
         cofactor_families=Unsynchronized.ref Cofactor_Family_Table.empty,
         mapping_families=Unsynchronized.ref Mapping_Family_Table.empty,
         radix_facts=Unsynchronized.ref Inttab.empty,
         support_cache=Unsynchronized.ref Inttab.empty,
         active=Unsynchronized.ref Key_Table.empty,
         bind_visits=Unsynchronized.ref 0, cover_visits=Unsynchronized.ref 0,
         cofactor_family_hits=Unsynchronized.ref 0,
         cofactor_family_builds=Unsynchronized.ref 0,
         mapping_family_hits=Unsynchronized.ref 0,
         mapping_family_builds=Unsynchronized.ref 0,
         radix_fact_hits=Unsynchronized.ref 0,
         radix_fact_builds=Unsynchronized.ref 0,
         proof_timings=Unsynchronized.ref []}
      val wf = Store.wellformed store
      val _ = Utils.ensure_closed_context ctxt "Frozen MDD table wellformedness" wf

      fun node_at root = Store.node store root

      fun support_of root =
        (case Inttab.lookup (!(#support_cache state)) root of
          SOME labels => labels
        | NONE =>
            let
              val labels = (case node_at root of
                Store.Leaf payload => [payload]
              | Store.Branch (_, children) =>
                  fold (fn child => fn accumulated =>
                    let
                      val _ = if child < root then ()
                        else error "Frozen MDD child is not earlier than its parent"
                    in union (op =) accumulated (support_of child) end) children [])
              val _ = #support_cache state := Inttab.update (root, labels)
                (!(#support_cache state))
            in labels end)

      fun cover root labels =
        let
          val _ = root_bound state root
          val expected = HOLogic.mk_Trueprop (cover_prop state labels root)
        in
          (case Cover_Table.lookup (!(#cover_certificates state)) (root, labels) of
            SOME theorem => Utils.exact_prop ctxt "Cached MDD payload cover" expected theorem
          | NONE =>
              let
                val actual = support_of root
                val _ = if List.all (fn payload => member (op =) labels payload) actual
                  then () else error "MDD payload cover omits a reachable leaf"
                val base =
                  (case Cover_Table.lookup (!(#cover_certificates state)) (root, actual) of
                    SOME theorem => Utils.exact_prop ctxt "Cached MDD minimal payload cover"
                      (HOLogic.mk_Trueprop (cover_prop state actual root)) theorem
                  | NONE =>
                      let
                        val _ = #cover_visits state := !(#cover_visits state) + 1
                        val bound = root_bound state root
                        val equation = lookup_equation state root
                        val theorem = (case node_at root of
                          Store.Leaf payload =>
                            let
                              val member_fact = prove_bool state "MDD leaf payload membership"
                                (HOLogic.mk_mem (nat payload, set_nat actual)) []
                            in @{thm comma_crt_mdd_payload_cover_leaf} OF
                              [bound, equation, member_fact] end
                        | Store.Branch (_, children) =>
                            let
                              val child_bounds = map (fn child =>
                                if child < root then
                                  prove_bool state "MDD payload child order"
                                    (mk_less (nat child, nat root)) []
                                else error "Frozen MDD branch child violates table order") children
                              val child_covers = map (fn child => cover child actual) children
                              val child = Free ("cover_child", natT)
                              val bound_prop = ball (set_nat children)
                                (Term.lambda child (mk_less (child, nat root)))
                              val covered_prop = ball (set_nat children)
                                (Term.lambda child (cover_term state actual child))
                              val all_bounds = prove_bool state "MDD payload branch child bounds"
                                bound_prop child_bounds
                              val all_covered = prove_bool state "MDD payload branch child coverage"
                                covered_prop child_covers
                            in @{thm comma_crt_mdd_payload_cover_branch} OF
                              [bound, equation, all_bounds, all_covered] end)
                        val theorem = Utils.exact_prop ctxt "MDD minimal payload cover"
                          (HOLogic.mk_Trueprop (cover_prop state actual root)) theorem
                        val _ = #cover_certificates state := Cover_Table.update
                          ((root, actual), theorem) (!(#cover_certificates state))
                      in theorem end)
                val theorem = if actual = labels then base
                  else
                    let
                      val setT = HOLogic.mk_setT natT
                      val subset = Const (@{const_name less_eq}, setT --> setT --> boolT)
                      val subset_fact = prove_bool state "MDD payload cover set inclusion"
                        (subset $ set_nat actual $ set_nat labels) []
                      val widened = @{thm comma_crt_mdd_payload_cover_mono} OF
                        [base, subset_fact]
                    in Utils.exact_prop ctxt "MDD widened payload cover" expected widened end
                val _ = #cover_certificates state := Cover_Table.update
                  ((root, labels), theorem) (!(#cover_certificates state))
              in Utils.exact_prop ctxt "MDD payload cover" expected theorem end)
        end

      fun radix_at axis = nth nat_listT natT (Store.radices store) (nat axis)
      fun radix_bound_conversion radix_equation slot =
        Thm.combination (Thm.reflexive (Thm.cterm_of ctxt
          (Const (@{const_name Trueprop}, boolT --> @{typ prop}))))
          (Thm.combination (Thm.reflexive (Thm.cterm_of ctxt
            (Const (@{const_name less}, natT --> natT --> boolT) $ slot)))
            (radix_equation RS @{thm eq_reflection}))
      fun axis_facts axis =
        let
          val _ = if 0 <= axis andalso axis < length radices then ()
            else error "MDD cofactor axis is outside the frozen radix vector"
          val bound_prop = mk_less (nat axis,
            Const (@{const_name size}, nat_listT --> natT) $ Store.radices store)
          val positive_prop = mk_less (nat 0, radix_at axis)
          val radix_value = nat (List.nth (radices, axis))
          val radix_equation_prop = HOLogic.mk_eq (radix_at axis, radix_value)
          val expected_bound = HOLogic.mk_Trueprop bound_prop
          val expected_positive = HOLogic.mk_Trueprop positive_prop
          val expected_radix_equation = HOLogic.mk_Trueprop radix_equation_prop
        in
          case Inttab.lookup (!(#radix_facts state)) axis of
            SOME (bound, positive, radix_equation) =>
              let
                val bound = Utils.exact_prop ctxt "Cached MDD radix axis bound"
                  expected_bound bound
                val positive = Utils.exact_prop ctxt "Cached MDD positive radix"
                  expected_positive positive
                val radix_equation = Utils.exact_prop ctxt
                  "Cached MDD axis radix equation" expected_radix_equation radix_equation
                val _ = #radix_fact_hits state := !(#radix_fact_hits state) + 1
              in (bound, positive, radix_equation) end
          | NONE =>
              let
                val bound = prove_bool state "MDD cofactor axis bound" bound_prop []
                val positive = prove_bool state "MDD cofactor radix positivity"
                  positive_prop []
                val bound = Utils.exact_prop ctxt "MDD cofactor axis bound"
                  expected_bound bound
                val positive = Utils.exact_prop ctxt "MDD cofactor radix positivity"
                  expected_positive positive
                val radix_equation = prove_bool state "MDD cofactor axis radix equation"
                  radix_equation_prop []
                val radix_equation = Utils.exact_prop ctxt
                  "MDD cofactor axis radix equation" expected_radix_equation radix_equation
                val _ = #radix_facts state := Inttab.update
                  (axis, (bound, positive, radix_equation)) (!(#radix_facts state))
                val _ = #radix_fact_builds state := !(#radix_fact_builds state) + 1
              in (bound, positive, radix_equation) end
        end

      fun family_admitted_at axis root =
        Const (@{const_name comma_crt_mdd_cofactor_family_admitted},
          nat_listT --> nodesT --> natT --> natT --> boolT) $
          Store.radices store $ Store.table store $ nat axis $ root

      fun family_admitted_term axis root = family_admitted_at axis (nat root)

      fun family_child_at axis root slot =
        Const (@{const_name comma_crt_mdd_cofactor_family_child},
          nat_listT --> nodesT --> natT --> natT --> natT --> natT) $
          Store.radices store $ Store.table store $ nat axis $ root $ slot

      fun family_child_term axis root slot = family_child_at axis (nat root) slot

      fun cofactor_family_prop axis root =
        let
          val slot = Free ("mdd_family_slot", natT)
          val width = nat (List.nth (radices, axis))
          val equation = HOLogic.mk_eq
            (cofactor_term state (nat axis) slot (nat root),
             some natT (family_child_term axis root slot))
        in Logic.all slot
          (Logic.mk_implies
            (HOLogic.mk_Trueprop (mk_less (slot, width)),
             HOLogic.mk_Trueprop equation)) end

      fun cofactor_family axis root =
        let
          val (axis_bound, positive, radix_equation) = axis_facts axis
          val bound = root_bound state root
          val equation = lookup_equation state root
          val _ = (case node_at root of
            Store.Leaf _ => ()
          | Store.Branch (node_axis, _) =>
              if axis <= node_axis then ()
              else error "MDD cofactor family selects below an operand branch")
          val expected = cofactor_family_prop axis root
        in
          case Cofactor_Family_Table.lookup (!(#cofactor_families state)) (root, axis) of
            SOME ({theorem}: cofactor_family) =>
              let
                val theorem = Utils.exact_prop ctxt "Cached MDD cofactor family" expected theorem
                val _ = #cofactor_family_hits state := !(#cofactor_family_hits state) + 1
              in {theorem=theorem}: cofactor_family end
          | NONE =>
              let
                val admission = prove_bool state "MDD cofactor family admission"
                  (family_admitted_term axis root) [axis_bound, positive, bound, equation]
                val admitted = @{thm comma_crt_mdd_cofactor_family_exact} OF
                  [Store.wellformed store, admission]
                val slot = Free ("mdd_family_slot", natT)
                val numeric_guard_ct = Thm.cterm_of ctxt
                  (HOLogic.mk_Trueprop (mk_less (slot, nat (List.nth (radices, axis)))))
                val theorem = Utils.exact_prop ctxt "MDD cofactor family" expected
                  (Thm.forall_intr (Thm.cterm_of ctxt slot)
                    (Thm.implies_intr numeric_guard_ct
                      (Thm.implies_elim
                        (Drule.infer_instantiate ctxt [(("slot",0),Thm.cterm_of ctxt slot)] admitted)
                        (Thm.equal_elim
                          (Thm.symmetric (radix_bound_conversion radix_equation slot))
                          (Thm.assume numeric_guard_ct)))))
                val family: cofactor_family = {theorem=theorem}
                val _ = #cofactor_families state := Cofactor_Family_Table.update
                  ((root, axis), family) (!(#cofactor_families state))
                val _ = #cofactor_family_builds state :=
                  !(#cofactor_family_builds state) + 1
              in family end
        end

      fun mapping_family_child_map axis mapping slot =
        let
          val payload = Free ("mdd_mapping_payload", natT)
          val root = Free ("mdd_mapping_root", natT)
          val child = family_child_at axis root slot
          val mapped_item = HOLogic.mk_prod (payload, child)
          val body = Term.lambda payload (Term.lambda root mapped_item)
          val mapper = Const (@{const_name case_prod},
            fastype_of body --> pairT --> pairT) $ body
          val map_const = Const (@{const_name map}, (pairT --> pairT) -->
            pair_listT --> pair_listT)
        in map_const $ mapper $ pair_list mapping end

      fun mapping_family_prop axis mapping =
        let
          val slot = Free ("mdd_mapping_family_slot", natT)
          val width = nat (List.nth (radices, axis))
          val equation = HOLogic.mk_eq
            (mapping_cofactor_term state (nat axis) slot (pair_list mapping),
             some pair_listT (mapping_family_child_map axis mapping slot))
        in Logic.all slot
          (Logic.mk_implies
            (HOLogic.mk_Trueprop (mk_less (slot, width)),
             HOLogic.mk_Trueprop equation)) end

      fun mapping_family axis mapping =
        let
          val roots = distinct (op =) (map #2 mapping)
          val width = nat (List.nth (radices, axis))
          val family_root = Free ("mdd_mapping_family_root", natT)
          val family_slot = Free ("mdd_mapping_family_slot", natT)
          val mapped_roots = Const (@{const_name map},
            (pairT --> natT) --> pair_listT --> nat_listT) $
              Const (@{const_name snd}, pairT --> natT) $ pair_list mapping
          val root_set = Const (@{const_name set}, nat_listT --> HOLogic.mk_setT natT) $
            mapped_roots
          val family_prop = Logic.all family_root (Logic.all family_slot
            (Logic.mk_implies
              (HOLogic.mk_Trueprop
                (HOLogic.mk_mem (family_root, root_set)),
               Logic.mk_implies
                (HOLogic.mk_Trueprop (mk_less (family_slot, width)),
                 HOLogic.mk_Trueprop (HOLogic.mk_eq
                   (cofactor_term state (nat axis) family_slot family_root,
                    some natT (family_child_at axis family_root family_slot)))))))
          val expected = mapping_family_prop axis mapping
        in
          case Mapping_Family_Table.lookup (!(#mapping_families state))
              (axis, mapping) of
            SOME ({theorem}: mapping_family) =>
              let
                val theorem = Utils.exact_prop ctxt "Cached MDD mapping cofactor family"
                  expected theorem
                val _ = #mapping_family_hits state := !(#mapping_family_hits state) + 1
              in {theorem=theorem}: mapping_family end
          | NONE =>
              let
                val families = map (cofactor_family axis) roots
                val family_theorems = map #theorem families
                val root_families = Utils.prove_exact ctxt
                  "MDD mapping-root cofactor families" family_prop
                  (fn context =>
                    let
                      val family_ctxt = put_simpset HOL_basic_ss context
                        |> Simplifier.add_simps
                          @{thms list.map list.set snd_conv insert_iff empty_iff}
                    in Method.insert_tac context family_theorems 1 THEN
                      asm_full_simp_tac family_ctxt 1 THEN
                      TRY (auto_tac family_ctxt)
                    end)
                val radix = width
                val rule = Drule.infer_instantiate ctxt
                  [( ("radices",0), Thm.cterm_of ctxt (Store.radices store)),
                   (("nodes",0), Thm.cterm_of ctxt (Store.table store)),
                   (("axis",0), Thm.cterm_of ctxt (nat axis)),
                   (("mapping",0), Thm.cterm_of ctxt (pair_list mapping)),
                   (("radix",0), Thm.cterm_of ctxt radix),
                   (("slot",0), Thm.cterm_of ctxt family_slot)]
                  @{thm comma_crt_mdd_cofactor_mapping_family_from_roots}
                val theorem = Thm.implies_elim rule root_families
                val theorem = Thm.forall_intr
                  (Thm.cterm_of ctxt family_slot) theorem
                val theorem = Utils.exact_prop ctxt "MDD mapping cofactor family"
                  expected theorem
                val family: mapping_family = {theorem=theorem}
                val _ = #mapping_families state := Mapping_Family_Table.update
                  ((axis, mapping), family) (!(#mapping_families state))
                val _ = #mapping_family_builds state :=
                  !(#mapping_family_builds state) + 1
              in family end
        end

      fun reflexive_prop label proposition_term =
        let
          val variable = (case Term.add_vars (Thm.prop_of @{thm HOL.refl}) [] of
            [item] => #1 item
          | _ => error "HOL reflexivity theorem has an unexpected schematic shape")
          val theorem = Drule.infer_instantiate ctxt
            [(variable, Thm.cterm_of ctxt proposition_term)] @{thm HOL.refl}
          val expected = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (proposition_term, proposition_term))
        in Utils.exact_prop ctxt label expected theorem end

      fun interval_term radix =
        Const (@{const_name upt}, natT --> natT --> nat_listT) $ nat 0 $ radix

      fun mapped_slots function radix =
        let
          val slot = Free ("mdd_family_slot", natT)
          val map_const = Const (@{const_name map}, (natT --> fastype_of (function slot)) -->
            nat_listT --> HOLogic.listT (fastype_of (function slot)))
        in map_const $ Term.lambda slot (function slot) $ interval_term radix end

      fun node_cofactor axis slot root =
        (case node_at root of
          Store.Leaf _ => root
        | Store.Branch (node_axis, children) =>
            if node_axis = axis then List.nth (children, slot)
            else if axis < node_axis then root
            else error "Arena bind selected an axis below an operand branch")

      fun mapping_cofactor axis slot mapping =
        map (fn (payload, root) => (payload, node_cofactor axis slot root)) mapping

      fun validate_key (source, fallback, mapping) =
        let
          val _ = ignore (root_bound state source)
          val _ = ignore (root_bound state fallback)
          val _ = List.app (fn (_, root) => ignore (root_bound state root)) mapping
          val _ = if unique (map #1 mapping) then ()
            else error "Arena bind witness has duplicate source labels"
        in () end

      fun restrict_certificate source labels full_mapping fallback result inner cover_thm =
        let
          val reduced = restrict_mapping labels full_mapping
          val expected_inner = HOLogic.mk_Trueprop
            (bind_prop state reduced fallback source result)
          val _ = if Thm.prop_of inner aconv expected_inner then ()
            else error "MDD bind restriction inner certificate has the wrong mapping"
          val proposition = bind_prop state full_mapping fallback source result
          val intro = Drule.infer_instantiate ctxt
            [(("labels",0),Thm.cterm_of ctxt (nat_list labels))]
            @{thm comma_crt_mdd_bind_certificate.bind_restrict}
        in
          if reduced = full_mapping then inner
          else mk_intro state "MDD bind support restriction" proposition intro
            [root_bound state source, cover_thm, inner]
        end

      fun certify_key (key as (source, fallback, mapping): Arena.bind_key) =
        (case Key_Table.lookup (!(#bind_certificates state)) key of
          SOME (result_root, theorem) =>
            let
              val _ = root_bound state result_root
              val expected = HOLogic.mk_Trueprop
                (bind_prop state mapping fallback source result_root)
            in Utils.exact_prop ctxt "Cached internal MDD bind certificate"
              expected theorem end
        | NONE =>
            if Key_Table.defined (!(#active state)) key then
              error "Arena bind witness contains a recursive key cycle"
            else
              let
                val _ = #active state := Key_Table.update (key, ()) (!(#active state))
                val result = Exn.capture (fn () =>
                  let
                    val _ = #bind_visits state := !(#bind_visits state) + 1
                    val visits = !(#bind_visits state)
                    val _ = if visits mod 256 = 0 then
                      checkpoint state ("cold-bind-start-" ^ Int.toString visits) else ()
                    val witness = Store.bind_witness store key
                    val _ = if #key witness = key then ()
                      else error "Arena bind witness key is not support-normalized"
                    val _ = validate_key key
                    val labels = #support witness
                    val actual_support = support_of source
                    val _ = if same_set labels actual_support then ()
                      else error "Arena bind witness support differs from frozen source leaves"
                    val _ = if List.all (fn label => label >= 0) labels then ()
                      else error "Arena bind witness contains a negative label"
                    val _ = if restrict_mapping labels mapping = mapping then ()
                      else error "Arena bind witness mapping is not support-restricted"
                    val result_root = #result witness
                    val source_bound = root_bound state source
                    val source_eq = lookup_equation state source
                    val result_bound = root_bound state result_root
                    val result_eq = lookup_equation state result_root
                    val proposition = bind_prop state mapping fallback source result_root
                    val certificate = (case #step witness of
                      Arena.Bind_Leaf payload =>
                        let
                          val _ = (case node_at source of
                            Store.Leaf actual => if actual = payload then ()
                              else error "Arena bind leaf payload differs from source node"
                          | Store.Branch _ => error "Leaf witness has a branch source")
                          val chosen = the_default fallback (AList.lookup (op =) mapping payload)
                          val _ = if chosen = result_root then ()
                            else error "Arena bind leaf selected a different output root"
                          val chosen_fact = prove_bool state "MDD bind leaf target selection"
                            (HOLogic.mk_eq (nat result_root,
                              bind_target_term (nat fallback) (pair_list mapping) (nat payload))) []
                          val fallback_bound = root_bound state fallback
                          val mapped_bounds = map (root_bound state o #2) mapping
                          val mapped = Free ("mapped_root", natT)
                          val map_snd = Const (@{const_name map},
                            (pairT --> natT) --> pair_listT --> nat_listT) $
                              Const (@{const_name snd}, pairT --> natT)
                          val all_mapped = prove_bool state "MDD bind leaf mapped-root bounds"
                            (ball
                              (Const (@{const_name set}, nat_listT --> HOLogic.mk_setT natT) $
                                (map_snd $ pair_list mapping))
                              (Term.lambda mapped (mk_less (mapped, table_size state))))
                            mapped_bounds
                          val intro = Drule.infer_instantiate ctxt
                            [( ("payload",0), Thm.cterm_of ctxt (nat payload))]
                            @{thm comma_crt_mdd_bind_certificate.bind_leaf}
                        in intro_closed state "MDD bind leaf certificate"
                          (HOLogic.mk_Trueprop proposition) intro
                          [source_bound, source_eq, chosen_fact, result_bound,
                           fallback_bound, all_mapped] end
                    | Arena.Bind_Branch (axis, child_keys) =>
                        let
                          val radix = (case try List.nth (#radices state, axis) of
                            SOME width => width
                          | NONE => error "Arena bind axis is outside the radix vector")
                          val _ = if radix > 0 andalso length child_keys = radix then ()
                            else error "Arena bind witness child count disagrees with radix"
                          val _ = (case node_at source of
                            Store.Branch (source_axis, _) => if axis <= source_axis then ()
                              else error "Arena bind axis follows its source branch"
                          | Store.Leaf _ => error "Branch witness has a leaf source")
                          val source_family = cofactor_family axis source
                          val fallback_family = cofactor_family axis fallback
                          val mapping_family_proof = mapping_family axis mapping
                          fun child_info (slot, child_key) =
                            let
                              val (child_source, child_fallback, child_mapping) = child_key
                              val source_child = node_cofactor axis slot source
                              val fallback_child = node_cofactor axis slot fallback
                              val raw_mapping_child = mapping_cofactor axis slot mapping
                              val child_witness = Store.bind_witness store child_key
                              val child_labels = #support child_witness
                              val _ = if #key child_witness = child_key andalso
                                  child_source = source_child andalso
                                  child_fallback = fallback_child andalso
                                  child_mapping = restrict_mapping child_labels raw_mapping_child
                                then () else error "Arena bind child key differs from its cofactors"
                              val inner = certify_key child_key
                              val child_cover = cover child_source child_labels
                              val child_cert = restrict_certificate child_source child_labels
                                raw_mapping_child child_fallback (#result child_witness)
                                inner child_cover
                            in {result= #result child_witness,
                                certificate=child_cert} end
                          val infos = map_index child_info child_keys
                          val results = map #result infos
                          val result_node = node_at result_root
                          val branch_matches = (case result_node of
                            Store.Branch (result_axis, children) =>
                              result_axis = axis andalso children = results
                          | Store.Leaf _ => false)
                          val alias_matches = List.all
                            (fn child => child = result_root) results
                          val _ = if branch_matches orelse alias_matches then ()
                            else error "Arena bind output is neither the witnessed branch nor its alias"
                          val results_term = nat_list results
                          val result_shape = HOLogic.mk_disj
                            (HOLogic.mk_eq
                              (Const (@{const_name nth}, nodesT --> natT --> nodeT) $
                                Store.table store $ nat result_root,
                               Const (@{const_name Comma_CRT_MDD_Branch},
                                 natT --> nat_listT --> nodeT) $ nat axis $ results_term),
                             list_all
                               (Term.lambda (Free ("bind_result_child", natT))
                                 (HOLogic.mk_eq
                                   (Free ("bind_result_child", natT), nat result_root)))
                               results_term)
                          val shape_fact = prove_bool state "MDD bind output shape"
                            result_shape [result_eq]
                          val (axis_fact, positive_fact, radix_equation) = axis_facts axis
                          val radix_axis_term = radix_at axis
                          val radix_term = nat radix
                          val width_fact = prove_bool state "MDD bind output width"
                            (HOLogic.mk_eq
                              (Const (@{const_name size}, nat_listT --> natT) $ results_term,
                               radix_axis_term)) []
                          val operands = source :: fallback :: map #2 mapping
                          val operand_bounds = map (root_bound state) operands
                          val operand = Free ("bind_operand", natT)
                          val mapped_roots = Const (@{const_name map},
                            (pairT --> natT) --> pair_listT --> nat_listT) $
                              Const (@{const_name snd}, pairT --> natT) $ pair_list mapping
                          val operand_terms = HOLogic.cons_const natT $ nat source $
                            (HOLogic.cons_const natT $ nat fallback $ mapped_roots)
                          val all_operands = prove_bool state "MDD bind operand bounds"
                            (ball (Const (@{const_name set}, nat_listT --> HOLogic.mk_setT natT) $
                              operand_terms)
                              (Term.lambda operand (mk_less (operand, table_size state))))
                            operand_bounds
                          val slot = Free ("bind_slot", natT)
                          val source_children_term = mapped_slots
                            (fn child_slot => family_child_term axis source child_slot)
                            radix_term
                          val fallback_children_term = mapped_slots
                            (fn child_slot => family_child_term axis fallback child_slot)
                            radix_term
                          val mapping_children_term = mapped_slots
                            (fn child_slot => mapping_family_child_map axis mapping child_slot)
                            radix_term
                          val slot_source = nth nat_listT natT source_children_term slot
                          val slot_fallback = nth nat_listT natT fallback_children_term slot
                          val slot_mapping = nth pair_list_listT pair_listT mapping_children_term slot
                          val slot_result = nth nat_listT natT results_term slot
                          val child_certificate = bind_term state slot_mapping slot_fallback
                            slot_source slot_result
                          val child_certificate_predicate =
                            Term.lambda slot child_certificate
                          val operand_roots = distinct (op =)
                            (source :: fallback :: map #2 mapping)
                          val item_context = Simplifier.add_simps
                            (map (lookup_equation state) operand_roots) (#simp_ctxt state)
                          val child_certificates = indexed_slots state radix
                            child_certificate_predicate (map #certificate infos) item_context
                          val source_children_exact = reflexive_prop
                            "MDD source cofactor-family vector" source_children_term
                          val fallback_children_exact = reflexive_prop
                            "MDD fallback cofactor-family vector" fallback_children_term
                          val mapping_children_exact = reflexive_prop
                            "MDD mapping cofactor-family vector" mapping_children_term
                          val row_slot = Free ("bind_row_slot", natT)
                          val row_rule = Drule.infer_instantiate ctxt
                            [(("radices",0),Thm.cterm_of ctxt (Store.radices store)),
                             (("nodes",0),Thm.cterm_of ctxt (Store.table store)),
                             (("mapping",0),Thm.cterm_of ctxt (pair_list mapping)),
                             (("axis",0),Thm.cterm_of ctxt (nat axis)),
                             (("radix",0),Thm.cterm_of ctxt radix_term),
                             (("source",0),Thm.cterm_of ctxt (nat source)),
                             (("fallback_root",0),Thm.cterm_of ctxt (nat fallback)),
                             (("source_children",0),Thm.cterm_of ctxt source_children_term),
                             (("fallback_children",0),Thm.cterm_of ctxt fallback_children_term),
                             (("result_children",0),Thm.cterm_of ctxt results_term),
                             (("mapping_children",0),Thm.cterm_of ctxt mapping_children_term),
                             (("slot",0),Thm.cterm_of ctxt row_slot)]
                            @{thm comma_crt_mdd_bind_branch_row_transport}
                          val row_theorem = Thm.implies_elim row_rule
                            (#theorem source_family)
                          val row_theorem = Thm.implies_elim row_theorem
                            (#theorem fallback_family)
                          val row_theorem = Thm.implies_elim row_theorem
                            (#theorem mapping_family_proof)
                          val row_theorem = Thm.implies_elim row_theorem
                            source_children_exact
                          val row_theorem = Thm.implies_elim row_theorem
                            fallback_children_exact
                          val row_theorem = Thm.implies_elim row_theorem
                            mapping_children_exact
                          val row_theorem = Thm.implies_elim row_theorem
                            child_certificates
                          val row_theorem = Thm.forall_intr
                            (Thm.cterm_of ctxt row_slot) row_theorem
                          val row_source = nth nat_listT natT source_children_term row_slot
                          val row_fallback = nth nat_listT natT fallback_children_term row_slot
                          val row_mapping = nth pair_list_listT pair_listT
                            mapping_children_term row_slot
                          val row_result = nth nat_listT natT results_term row_slot
                          val row_body = HOLogic.mk_conj
                            (HOLogic.mk_eq
                              (cofactor_term state (nat axis) row_slot (nat source),
                               some natT row_source),
                             HOLogic.mk_conj
                              (HOLogic.mk_eq
                                (cofactor_term state (nat axis) row_slot (nat fallback),
                                 some natT row_fallback),
                               HOLogic.mk_conj
                                (HOLogic.mk_eq
                                  (mapping_cofactor_term state (nat axis) row_slot
                                    (pair_list mapping), some pair_listT row_mapping),
                                 bind_term state row_mapping row_fallback row_source row_result)))
                          val row_expected = Logic.all row_slot
                            (Logic.mk_implies
                              (HOLogic.mk_Trueprop (mk_less (row_slot, radix_term)),
                               HOLogic.mk_Trueprop row_body))
                          val row_theorem = Utils.exact_prop ctxt
                            "MDD bind family row transport" row_expected row_theorem
                          val row_at = Drule.forall_elim_list
                            [Thm.cterm_of ctxt row_slot] row_theorem
                          val axis_guard = HOLogic.mk_Trueprop
                            (mk_less (row_slot, radix_axis_term))
                          val axis_guard_ct = Thm.cterm_of ctxt axis_guard
                          val axis_guard_fact = Thm.assume axis_guard_ct
                          val numeric_guard_fact = Thm.equal_elim
                            (radix_bound_conversion radix_equation row_slot) axis_guard_fact
                          val row_point = Thm.implies_elim row_at numeric_guard_fact
                          fun abstract_row project expected_body label =
                            let
                              val point = project row_point
                              val implication = Thm.implies_intr axis_guard_ct point
                              val universal = Thm.forall_intr
                                (Thm.cterm_of ctxt row_slot) implication
                              val expected = Logic.all row_slot
                                (Logic.mk_implies (axis_guard,
                                  HOLogic.mk_Trueprop expected_body))
                            in Utils.exact_prop ctxt label expected universal end
                          val source_rows = abstract_row
                            (fn theorem => theorem RS @{thm conjunct1})
                            (HOLogic.mk_eq
                              (cofactor_term state (nat axis) row_slot (nat source),
                               some natT row_source))
                            "MDD source cofactor row"
                          val fallback_rows = abstract_row
                            (fn theorem => (theorem RS @{thm conjunct2}) RS @{thm conjunct1})
                            (HOLogic.mk_eq
                              (cofactor_term state (nat axis) row_slot (nat fallback),
                               some natT row_fallback))
                            "MDD fallback cofactor row"
                          val mapping_rows = abstract_row
                            (fn theorem => ((theorem RS @{thm conjunct2})
                              RS @{thm conjunct2}) RS @{thm conjunct1})
                            (HOLogic.mk_eq
                              (mapping_cofactor_term state (nat axis) row_slot
                                (pair_list mapping), some pair_listT row_mapping))
                            "MDD mapping cofactor row"
                          val certificate_rows = abstract_row
                            (fn theorem => ((theorem RS @{thm conjunct2})
                              RS @{thm conjunct2}) RS @{thm conjunct2})
                            (bind_term state row_mapping row_fallback row_source row_result)
                            "MDD child bind certificate row"
                          val rule = Drule.infer_instantiate ctxt
                            [(("axis",0),Thm.cterm_of ctxt (nat axis)),
                             (("children",0),Thm.cterm_of ctxt results_term),
                             (("source_child",0),Thm.cterm_of ctxt
                               (Term.lambda row_slot row_source)),
                             (("default_child",0),Thm.cterm_of ctxt
                               (Term.lambda row_slot row_fallback)),
                             (("mapping_child",0),Thm.cterm_of ctxt
                               (Term.lambda row_slot row_mapping))]
                            @{thm comma_crt_mdd_bind_certificate.bind_branch}
                        in intro_closed state "MDD bind branch certificate"
                          (HOLogic.mk_Trueprop proposition) rule
                          [source_bound, result_bound, shape_fact, axis_fact,
                           positive_fact, width_fact, all_operands, source_rows,
                           fallback_rows, mapping_rows, certificate_rows] end)
                    val theorem = Utils.exact_prop ctxt "MDD bind certificate"
                      (HOLogic.mk_Trueprop proposition) certificate
                    val _ = #bind_certificates state :=
                      Key_Table.update (key, (result_root, theorem))
                      (!(#bind_certificates state))
                    val _ = if visits mod 256 = 0 then
                      checkpoint state ("cold-bind-complete-" ^ Int.toString visits) else ()
                  in theorem end) ()
                val _ = #active state := Key_Table.delete key (!(#active state))
              in Exn.release result end)

      fun certify_public (input_key as (source, fallback, full_mapping)) =
        (case Key_Table.lookup (!(#public_bind_certificates state)) input_key of
          SOME (result_root, theorem) =>
            Utils.exact_prop ctxt "Cached public MDD bind certificate"
              (HOLogic.mk_Trueprop (bind_prop state full_mapping fallback source result_root)) theorem
        | NONE =>
            let
              val _ = validate_key input_key
              val witness = Store.bind_witness store input_key
              val (norm_source, norm_fallback, norm_mapping) = #key witness
              val labels = #support witness
              val _ = if norm_source = source andalso norm_fallback = fallback andalso
                  same_set labels (support_of source) andalso
                  restrict_mapping labels full_mapping = norm_mapping then ()
                else error "Arena bind witness differs from requested support-normalized key"
              val inner = certify_key (#key witness)
              val support_fact = cover source labels
              val theorem = restrict_certificate source labels full_mapping fallback
                (#result witness) inner support_fact
              val expected = HOLogic.mk_Trueprop
                (bind_prop state full_mapping fallback source (#result witness))
              val theorem = Utils.exact_prop ctxt "Public MDD bind certificate" expected theorem
              val _ = #public_bind_certificates state := Key_Table.update
                (input_key, (#result witness, theorem)) (!(#public_bind_certificates state))
            in theorem end)

      val public: replay = {state=state, certify=certify_public}
    in public end

  fun certify_bind ({certify, ...}: replay) key = certify key
  fun bind_eval_phase ({state={store, ctxt, ...}, certify}: replay) key =
    let
      val certificate = certify key
      val theorem = @{thm comma_crt_mdd_bind_certificate_eval_phase} OF
        [Store.wellformed store, certificate]
      val _ = if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
          null (Thm.tpairs_of theorem) andalso
          Context.subthy (Thm.theory_of_thm theorem, Proof_Context.theory_of ctxt)
        then () else error "MDD bind phase transport is not a closed store theorem"
    in theorem end
  fun statistics ({state, ...}: replay) =
    let
      val {store, bind_visits, cover_visits, ...} = state
    in Store.statistics store ^
      " bind_certificate_nodes=" ^ Int.toString (!bind_visits) ^
      " payload_cover_nodes=" ^ Int.toString (!cover_visits) ^
      " " ^ proof_profile_summary state end
end
