(* Proof replay for finite operations over one frozen MDD table.  This module
   consumes proposal node IDs only after the certificate store has checked the
   entire table and provides indexed node equations. *)
signature COMMA_CRT_MDD_OPERATION_REPLAY =
sig
  type replay
  val make: Comma_CRT_MDD_Certificate_Store.store -> replay
  val certify_shift: replay -> int -> int -> int -> thm
  val shift_eval_phase: replay -> int -> int -> int -> thm
  val statistics: replay -> string
end

structure Comma_CRT_MDD_Operation_Replay:> COMMA_CRT_MDD_OPERATION_REPLAY =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Proof_Utils = Comma_CRT_MDD_Proof_Utils

  structure Shift_Key = Table(
    type key = int * int * int
    val ord = fn ((a,b,c),(x,y,z)) =>
      prod_ord int_ord (prod_ord int_ord int_ord)
        ((a,(b,c)),(x,(y,z))))

  type replay =
    {store: Store.store, ctxt: Proof.context, radices: int list,
     axis_facts: (thm * thm) Vector.vector,
     shifts: thm Shift_Key.table Unsynchronized.ref,
     shift_visits: int Unsynchronized.ref, slot_rows: int Unsynchronized.ref}

  val natT = @{typ nat}
  val boolT = HOLogic.boolT
  val nodeT = @{typ "nat comma_crt_mdd_node"}
  val nat_listT = @{typ "nat list"}
  val node_listT = HOLogic.listT nodeT

  fun nat n = HOLogic.mk_number natT n

  fun arithmetic_context ctxt =
    Comma_Entry_Arithmetic.natural_context ctxt
    |> Simplifier.add_simps
      (@{thms list.simps list.size nth_Cons_0 nth_Cons_Suc nth_Cons'})

  fun make store =
    let
      val ctxt = Store.context store
      val count = Store.node_count store
      val radices_term = Store.radices store
      val radices = map (Proof_Utils.dest_nat "MDD radix" natT)
        (HOLogic.dest_list radices_term)
      val _ = if count > 0 andalso not (null radices) andalso
          List.all (fn radix => radix > 0) radices
        then () else error "Frozen MDD table has an invalid extent or radix vector"
      val arithmetic = arithmetic_context ctxt
      fun scalar label proposition = Proof_Utils.prove_exact ctxt label
        (HOLogic.mk_Trueprop proposition)
        (fn _ => Simplifier.asm_full_simp_tac arithmetic 1)
      val axis_facts = Vector.tabulate (length radices, fn axis =>
        (scalar "Frozen MDD axis bound"
          (HOLogic.mk_binrel @{const_name less} (nat axis,
            Const (@{const_name size}, nat_listT --> natT) $ radices_term)),
         scalar "Frozen MDD radix positivity"
          (HOLogic.mk_binrel @{const_name less} (nat 0,
            Const (@{const_name nth}, nat_listT --> natT --> natT) $
              radices_term $ nat axis))))
      val replay = {store=store, ctxt=ctxt, radices=radices,
        axis_facts=axis_facts,
        shifts=Unsynchronized.ref Shift_Key.empty,
        shift_visits=Unsynchronized.ref 0, slot_rows=Unsynchronized.ref 0}
      val _ = Proof_Utils.ensure_closed_context ctxt "Frozen MDD wellformedness"
        (Store.wellformed store)
    in replay end

  fun node_at ({store, ...}: replay) id = Store.node store id

  fun lookup_equation ({ctxt, store, ...}: replay) id =
    let
      val theorem = Store.lookup store id
      val object_theorem = theorem RS @{thm meta_eq_to_obj_eq}
      val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
        (Const (@{const_name nth}, node_listT --> natT --> nodeT) $
          Store.table store $ nat id, Store.node_term (Store.node store id)))
    in Proof_Utils.exact_prop ctxt "Frozen MDD lookup equation" expected object_theorem end

  fun bound ({store, ctxt, ...}: replay) id =
    let
      val theorem = Store.bound store id
      val expected = Thm.prop_of theorem
    in Proof_Utils.exact_prop ctxt "Frozen MDD root bound" expected theorem end

  fun mk_less left right = HOLogic.mk_binrel @{const_name less} (left,right)

  fun prove_closed ctxt label expected tactic =
    Proof_Utils.prove_exact ctxt label expected
      (fn context => tactic {context=context, prems=[]})

  fun prove_scalar ({ctxt, ...}: replay) label proposition =
    prove_closed ctxt label (HOLogic.mk_Trueprop proposition)
      (fn {context, ...} =>
        FIRST [Simplifier.asm_full_simp_tac
          (arithmetic_context context) 1,
          Arith_Data.arith_tac context 1])

  fun mk_shift_prop ({store, ...}: replay) amount source target =
    let
      val shift_type = nat_listT --> node_listT --> natT --> natT --> natT --> boolT
      val shift = Const (@{const_name comma_crt_mdd_root_shift_certificate}, shift_type)
    in shift $ Store.radices store $ Store.table store $ nat amount $ nat source $ nat target end

  fun intro_certificate ({ctxt, ...}: replay) label intro proposition facts =
    let
      fun solve {context, ...} =
        resolve_tac context [intro] 1 THEN
        ALLGOALS (fn i =>
          FIRST (map (fn fact =>
            (resolve_tac context [Thm.forall_elim_vars 0 fact]
              THEN_ALL_NEW assume_tac context) i) facts @
            [assume_tac context i,
             Simplifier.asm_full_simp_tac
               (arithmetic_context context) i]))
    in prove_closed ctxt ("MDD root-shift " ^ label)
      (HOLogic.mk_Trueprop proposition) solve end

  fun nth_nat_list items index =
    Const (@{const_name nth}, nat_listT --> natT --> natT) $
      HOLogic.mk_list natT (map nat items) $ index

  fun radix_at store axis =
    Const (@{const_name nth}, nat_listT --> natT --> natT) $
      Store.radices store $ axis

  fun universal_slots ({ctxt, slot_rows, ...}: replay)
      radix radix_term proposition_at proofs =
    let
      val slot = Free ("mdd_slot", natT)
      val predicate = Term.lambda slot (proposition_at slot)
      val _ = if fastype_of predicate = @{typ "nat => bool"} then ()
        else error "MDD slot predicate has the wrong type"
      val successor_cache = Comma_Selected_List_Conversion.make_successor_cache ctxt radix
      val reduction_context =
        Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps
          (@{thms nth_Cons_0 nth_Cons_Suc nth_Cons' list.simps list.size
            option.simps set_simps ball_simps mod_simps})
      fun proof_item index =
        let
          val expected = HOLogic.mk_Trueprop (proposition_at (nat index))
          val child = List.nth (proofs,index)
          (* Reduce only the literal child indices.  The semantic child
             certificate is already checked; do not search for its proof
             again under a slot-specific goal. *)
          val indices = Simplifier.rewrite reduction_context
            (Thm.cterm_of ctxt expected)
          val child = Proof_Utils.exact_prop ctxt
            "MDD selected child certificate"
            (Thm.term_of (Thm.rhs_of indices)) child
          val normalized = Thm.equal_elim (Thm.symmetric indices) child
          val normalized = Proof_Utils.exact_prop ctxt
            "MDD concrete child certificate" expected normalized
        in Proof_Utils.predicate_application ctxt
          "MDD concrete child predicate application" predicate (nat index) normalized end
      val all = Comma_Selected_List_Conversion.prove_indexed_list_all
        {ctxt=ctxt, predicate=predicate, bound=radix, prove_item=proof_item,
         zero_fact = @{thm comma_indexed_all_zero},
         step_fact = @{thm comma_indexed_all_Suc},
         successor_equation= #equation successor_cache}
      val universal = Logic.all slot
        (Logic.mk_implies
          (HOLogic.mk_Trueprop (mk_less slot radix_term),
           HOLogic.mk_Trueprop (proposition_at slot)))
      val selected = @{thm comma_crt_mdd_indexed_allD} OF [all]
      val theorem = Proof_Utils.prove_exact ctxt
        "Finite MDD child certificate rows" universal
        (fn context => resolve_tac context [selected] 1 THEN
          Simplifier.asm_full_simp_tac (arithmetic_context context) 1)
      val _ = slot_rows := !slot_rows + radix
      val theorem = Proof_Utils.exact_prop ctxt "Finite MDD child certificate rows" universal theorem
    in theorem end

  fun certify_shift replay amount source target =
    let
      val {ctxt, radices, shifts, shift_visits, ...} = replay
      val _ = if amount >= 0 then () else error "MDD shift amount is negative"
      val _ = ignore (bound replay source)
      val _ = ignore (bound replay target)
      val key = (amount,source,target)
    in
      (case Shift_Key.lookup (!shifts) key of
        SOME theorem => Proof_Utils.exact_prop ctxt "Reused MDD root shift certificate"
          (HOLogic.mk_Trueprop (mk_shift_prop replay amount source target)) theorem
      | NONE =>
          let
            val _ = shift_visits := !shift_visits + 1
            val source_node = node_at replay source
            val target_node = node_at replay target
            val source_bound = bound replay source
            val target_bound = bound replay target
            val source_equation = lookup_equation replay source
            val target_equation = lookup_equation replay target
            val theorem =
              (case (source_node,target_node) of
                (Store.Leaf source_payload, Store.Leaf target_payload) =>
                  if source_payload = target_payload then
                    intro_certificate replay "leaf"
                      @{thm comma_crt_mdd_root_shift_certificate.root_shift_leaf}
                      (mk_shift_prop replay amount source target)
                      [source_bound,target_bound,source_equation,target_equation]
                  else error "MDD shift leaf payload changed"
              | (Store.Branch (axis, children), Store.Branch (target_axis, shifted_children)) =>
                  if axis <> target_axis then error "MDD shift changed a branch axis"
                  else
                    let
                      val radix = List.nth (radices,axis)
                      val _ = if length children = radix andalso
                          length shifted_children = radix then ()
                        else error "MDD shift branch width disagrees with its radix"
                      fun source_child slot = List.nth (children,(slot+amount) mod radix)
                      fun target_child slot = List.nth (shifted_children,slot)
                      val child_proofs = map (fn slot =>
                        certify_shift replay amount (source_child slot) (target_child slot))
                        (0 upto (radix - 1))
                      val slot_prop = fn slot =>
                        let
                          val source_index = HOLogic.mk_binop @{const_name modulo}
                            (HOLogic.mk_binop @{const_name plus} (slot,nat amount),
                             radix_at (#store replay) (nat axis))
                          val source_child_term = nth_nat_list children source_index
                          val target_child_term = nth_nat_list shifted_children slot
                        in Const (@{const_name comma_crt_mdd_root_shift_certificate},
                          nat_listT --> node_listT --> natT --> natT --> natT --> boolT) $
                          Store.radices (#store replay) $ Store.table (#store replay) $
                          nat amount $ source_child_term $ target_child_term end
                      val all_children = universal_slots replay radix
                        (radix_at (#store replay) (nat axis)) slot_prop child_proofs
                      val (axis_bound,positive) = Vector.sub (#axis_facts replay,axis)
                      val source_width = prove_scalar replay "MDD source branch width"
                        (HOLogic.mk_eq (Const (@{const_name size}, nat_listT --> natT) $
                          HOLogic.mk_list natT (map nat children),
                          Const (@{const_name nth}, nat_listT --> natT --> natT) $
                            Store.radices (#store replay) $ nat axis))
                      val target_width = prove_scalar replay "MDD target branch width"
                        (HOLogic.mk_eq (Const (@{const_name size}, nat_listT --> natT) $
                          HOLogic.mk_list natT (map nat shifted_children),
                          Const (@{const_name nth}, nat_listT --> natT --> natT) $
                            Store.radices (#store replay) $ nat axis))
                    in intro_certificate replay "branch"
                      @{thm comma_crt_mdd_root_shift_certificate.root_shift_branch}
                      (mk_shift_prop replay amount source target)
                      [source_bound,target_bound,source_equation,target_equation,
                       axis_bound,positive,source_width,target_width,all_children] end
              | (Store.Branch (axis,children), _) =>
                  let
                    val radix = List.nth (radices,axis)
                    val source_children = map (fn slot =>
                      List.nth (children,(slot+amount) mod radix)) (0 upto (radix - 1))
                    val child_proofs = map (fn child => certify_shift replay amount child target)
                      source_children
                    val slot_prop = fn slot =>
                      let
                        val source_index = HOLogic.mk_binop @{const_name modulo}
                          (HOLogic.mk_binop @{const_name plus} (slot,nat amount),
                           radix_at (#store replay) (nat axis))
                        val source_child_term = nth_nat_list children source_index
                      in Const (@{const_name comma_crt_mdd_root_shift_certificate},
                        nat_listT --> node_listT --> natT --> natT --> natT --> boolT) $
                        Store.radices (#store replay) $ Store.table (#store replay) $
                        nat amount $ source_child_term $ nat target end
                    val all_children = universal_slots replay radix
                      (radix_at (#store replay) (nat axis)) slot_prop child_proofs
                    val (axis_bound,positive) = Vector.sub (#axis_facts replay,axis)
                    val source_width = prove_scalar replay "MDD alias source width"
                      (HOLogic.mk_eq (Const (@{const_name size}, nat_listT --> natT) $
                          HOLogic.mk_list natT (map nat children),
                        Const (@{const_name nth}, nat_listT --> natT --> natT) $
                          Store.radices (#store replay) $ nat axis))
                  in intro_certificate replay "alias"
                    @{thm comma_crt_mdd_root_shift_certificate.root_shift_alias}
                    (mk_shift_prop replay amount source target)
                    [source_bound,target_bound,source_equation,axis_bound,positive,
                     source_width,all_children] end
              | _ => error "MDD root shift changed leaf/branch shape")
            val theorem = Proof_Utils.exact_prop ctxt "MDD root shift certificate"
              (HOLogic.mk_Trueprop (mk_shift_prop replay amount source target)) theorem
            val _ = shifts := Shift_Key.update (key,theorem) (!shifts)
          in theorem end)
    end

  fun shift_eval_phase replay amount source target =
    let
      val {ctxt, store, ...} = replay
      val cert = certify_shift replay amount source target
      val rule = @{thm comma_crt_mdd_root_shift_certificate_eval_phase} OF
        [Store.wellformed store, cert]
      val _ = if Thm.nprems_of rule = 0 andalso null (Thm.hyps_of rule) andalso
          null (Thm.tpairs_of rule) andalso
          Context.subthy (Thm.theory_of_thm rule, Proof_Context.theory_of ctxt)
        then () else error "MDD root-shift phase transport is not closed"
    in rule end

  fun statistics ({shift_visits,slot_rows,store,axis_facts,...}: replay) =
    Store.statistics store ^
    " shift_axis_fact_pairs=" ^ Int.toString (Vector.length axis_facts) ^
    " shift_certificate_nodes=" ^ Int.toString (!shift_visits) ^
    " shift_slot_rows=" ^ Int.toString (!slot_rows)
end
