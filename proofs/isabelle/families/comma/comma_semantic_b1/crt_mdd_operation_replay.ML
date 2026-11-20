(* Proof replay for finite operations over one frozen MDD table.  This module
   consumes proposal node IDs only after the certificate store has checked the
   entire table and provides indexed node equations. *)
signature COMMA_CRT_MDD_OPERATION_REPLAY =
sig
  type replay
  val make: Comma_CRT_MDD_Certificate_Store.store -> replay
  val certify_shift: replay -> int -> int -> int -> thm
  val shift_eval_phase: replay -> int -> int -> int -> thm
  type mapped_replay
  val make_mapped: Comma_CRT_MDD_Certificate_Store.store -> term ->
    (int -> int -> thm) -> mapped_replay
  val certify_mapped_shift: mapped_replay -> int -> int -> int -> thm
  val mapped_shift_eval_phase: mapped_replay -> int -> int -> int -> thm
  val mapped_statistics: mapped_replay -> string
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
     slot_templates: thm Shift_Key.table Unsynchronized.ref,
     slot_template_hits: int Unsynchronized.ref, slot_template_misses: int Unsynchronized.ref,
     shift_visits: int Unsynchronized.ref, slot_rows: int Unsynchronized.ref,
     zero_identity_hits: int Unsynchronized.ref}
  type mapped_replay = {base:replay,encode:term,leaf:int -> int -> thm,
    certificates:thm Shift_Key.table Unsynchronized.ref, visits:int Unsynchronized.ref}

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
        slot_templates=Unsynchronized.ref Shift_Key.empty,
        slot_template_hits=Unsynchronized.ref 0, slot_template_misses=Unsynchronized.ref 0,
        shift_visits=Unsynchronized.ref 0, slot_rows=Unsynchronized.ref 0,
        zero_identity_hits=Unsynchronized.ref 0}
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

  val mk_less = Proof_Utils.mk_less

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

  fun nth_nat_list items index =
    Const (@{const_name nth}, nat_listT --> natT --> natT) $
      HOLogic.mk_list natT (map nat items) $ index

  fun radix_at store axis =
    Const (@{const_name nth}, nat_listT --> natT --> natT) $
      Store.radices store $ axis

  (* The arithmetic and list selection are independent of the receiving
     node IDs and of the relation being replayed.  Prove that finite shape
     once, then instantiate it with the checked child certificates. *)
  fun mapped_slots (base as {ctxt,store,slot_templates,slot_template_hits,
        slot_template_misses,slot_rows,...}:replay)
      axis amount children target_children target proofs predicate =
    let
      val radix = length children
      val branch = is_some target_children
      val key = (axis,amount,if branch then 1 else 0)
      val source_names = map (fn i => "mdd_s" ^ Int.toString i) (0 upto (radix-1))
      val target_names = if branch then
          map (fn i => "mdd_t" ^ Int.toString i) (0 upto (radix-1))
        else ["mdd_t0"]
      val sources = map (fn n => Free (n,natT)) source_names
      val targets = map (fn n => Free (n,natT)) target_names
      val relT = natT --> natT --> boolT
      val rel = Free ("mdd_rel",relT)
      val slot = Free ("mdd_slot",natT)
      fun select terms index = Const (@{const_name nth}, nat_listT --> natT --> natT) $
        HOLogic.mk_list natT terms $ index
      fun target_at index = if branch then select targets index else hd targets
      val index = HOLogic.mk_binop @{const_name modulo}
        (HOLogic.mk_binop @{const_name plus} (slot,nat amount),radix_at store (nat axis))
      val result = rel $ select sources index $ target_at slot
      val premises = map (fn i => HOLogic.mk_Trueprop
        (rel $ List.nth (sources,(i+amount) mod radix) $
          (if branch then List.nth (targets,i) else hd targets))) (0 upto (radix-1))
      val conclusion = Logic.all slot (Logic.mk_implies
        (HOLogic.mk_Trueprop (mk_less slot (radix_at store (nat axis))),
         HOLogic.mk_Trueprop result))
      fun create () =
        let
          val alternatives = foldr1 HOLogic.mk_disj
            (map (fn i => HOLogic.mk_eq (slot,nat i)) (0 upto (radix-1)))
          val disjunction = Goal.prove ctxt ["mdd_slot"] []
            (Logic.mk_implies (HOLogic.mk_Trueprop (mk_less slot (radix_at store (nat axis))),
              HOLogic.mk_Trueprop alternatives))
            (fn {context,...} =>
              Simplifier.full_simp_tac (arithmetic_context context) 1 THEN
              TRY (Arith_Data.arith_tac context 1))
          val scalar = arithmetic_context ctxt |> Simplifier.add_simps
            (@{thms mod_simps})
          val theorem = Goal.prove ctxt ("mdd_rel" :: source_names @ target_names)
            premises conclusion (fn {context,prems} =>
              Method.insert_tac context prems 1 THEN
              dresolve_tac context [disjunction] 1 THEN
              REPEAT_DETERM (FIRSTGOAL (eresolve_tac context [@{thm disjE}])) THEN
              ALLGOALS (Simplifier.asm_full_simp_tac scalar))
          val _ = if null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
            then () else error "Mapped slot template has open assumptions"
        in theorem end
      val template = (case Shift_Key.lookup (!slot_templates) key of
          SOME th => (slot_template_hits := !slot_template_hits + 1; th)
        | NONE => let val th = create ()
            val _ = slot_template_misses := !slot_template_misses + 1
            val _ = slot_templates := Shift_Key.update (key,th) (!slot_templates)
          in th end)
      val target_values = (case target_children of SOME cs => cs | NONE => [target])
      val assignments = (("mdd_rel",predicate) ::
        (source_names ~~ map nat children) @ (target_names ~~ map nat target_values))
      val specialized = Drule.infer_instantiate ctxt
        (map (fn (name,value) => ((name,0),Thm.cterm_of ctxt value)) assignments) template
      val theorem = Thm.forall_intr_vars (specialized OF proofs)
      val expected = Logic.all slot (Logic.mk_implies
        (HOLogic.mk_Trueprop (mk_less slot (radix_at store (nat axis))),
         HOLogic.mk_Trueprop (Envir.beta_norm (predicate $
           nth_nat_list children (HOLogic.mk_binop @{const_name modulo}
             (HOLogic.mk_binop @{const_name plus} (slot,nat amount),radix_at store (nat axis))) $
           (case target_children of SOME cs => nth_nat_list cs slot | NONE => nat target)))))
      val _ = slot_rows := !slot_rows + radix
    in Proof_Utils.exact_prop ctxt "Mapped shift instantiated slot template" expected theorem end

  fun make_mapped store encode leaf : mapped_replay =
    let val ctxt = Store.context store
        val _ = if Proof_Utils.closed encode andalso fastype_of encode = @{typ "nat => nat"}
          then () else error "Mapped shift encoding must be a closed natural function"
        val _ = Thm.cterm_of ctxt encode
    in {base=make store,encode=encode,leaf=leaf,
      certificates=Unsynchronized.ref Shift_Key.empty,visits=Unsynchronized.ref 0} end

  fun mapped_prop ({base={store,...},encode,...}:mapped_replay) amount source target =
    @{term "comma_crt_mdd_root_shift_map_certificate :: nat list => nat comma_crt_mdd_node list => (nat => nat) => nat => nat => nat => bool"} $
      Store.radices store $ Store.table store $ encode $ nat amount $ nat source $ nat target

  (* Resolve a fully instantiated mapped certificate against ordered checked facts. *)
  fun mapped_intro ({ctxt,store,...}:replay) label intro encode amount source target extra facts proposition =
    let
      val bindings = [("radices", Store.radices store), ("nodes", Store.table store),
        ("encode",encode), ("amount",nat amount), ("source",nat source),
        ("target",nat target)] @ extra
      val instantiated = Drule.infer_instantiate ctxt
        (map (fn (name,term) => ((name,0),Thm.cterm_of ctxt term)) bindings) intro
      fun normalize theorem = Conv.fconv_rule Drule.beta_eta_conversion theorem
      fun discharge original theorem =
        let
          val fact = normalize original
          val (premise,_) = Logic.dest_implies (Thm.prop_of theorem)
          val _ = if premise aconv Thm.prop_of fact then ()
            else error ("Mapped shift " ^ label ^ " premise differs from checked fact")
        in Thm.implies_elim theorem fact end
      val result = fold discharge facts (normalize instantiated)
    in Proof_Utils.exact_prop ctxt ("Mapped shift " ^ label)
      (HOLogic.mk_Trueprop proposition) result end

  fun certify_mapped_shift (mapped as {base,encode,leaf,certificates,visits}:mapped_replay)
      amount source target =
    let
      val {ctxt,radices,store,...} = base
      val _ = if amount >= 0 then () else error "Mapped MDD shift amount is negative"
      val _ = ignore (bound base source)
      val _ = ignore (bound base target)
      val key = (amount,source,target)
      val proposition = mapped_prop mapped amount source target
    in case Shift_Key.lookup (!certificates) key of
      SOME theorem => Proof_Utils.exact_prop ctxt "Reused mapped shift certificate"
        (HOLogic.mk_Trueprop proposition) theorem
    | NONE =>
        let
          val _ = visits := !visits+1
          val source_node = node_at base source
          val target_node = node_at base target
          val source_bound = bound base source
          val target_bound = bound base target
          val source_eq = lookup_equation base source
          val target_eq = lookup_equation base target
          val theorem = (case (source_node,target_node) of
              (Store.Leaf input,Store.Leaf output) =>
                let
                  val equation = leaf input output |> Proof_Utils.exact_prop ctxt
                    "Mapped shift leaf encoding" (HOLogic.mk_Trueprop
                      (HOLogic.mk_eq (Envir.beta_norm (encode $ nat input),nat output)))
                  val target_expected = Envir.beta_norm (HOLogic.mk_Trueprop (HOLogic.mk_eq
                    (Const (@{const_name nth},node_listT --> natT --> nodeT) $
                      Store.table store $ nat target,
                     Const (@{const_name Comma_CRT_MDD_Leaf},natT --> nodeT) $ (encode $ nat input))))
                  val target_fact = Proof_Utils.prove_exact ctxt "Mapped shift target leaf"
                    target_expected (fn context => Method.insert_tac context [target_eq,equation] 1 THEN
                      Simplifier.asm_full_simp_tac (put_simpset HOL_basic_ss context) 1)
                in mapped_intro base "leaf"
                  @{thm comma_crt_mdd_root_shift_map_certificate.root_shift_map_leaf}
                  encode amount source target [("payload",nat input)]
                  [source_bound,target_bound,source_eq,target_fact] proposition end
            | (Store.Branch (axis,children),_) =>
                let
                  val radix = List.nth (radices,axis)
                  val _ = if length children=radix then () else error "Mapped shift source width differs"
                  val target_children = (case target_node of
                      Store.Branch (other,cs) =>
                        if other=axis then (if length cs=radix then SOME cs
                          else error "Mapped shift target width differs")
                        else if other>axis then NONE
                        else error "Mapped shift target precedes source axis"
                    | Store.Leaf _ => NONE)
                  fun source_child slot = List.nth (children,(slot+amount) mod radix)
                  fun target_child slot = (case target_children of SOME cs => List.nth (cs,slot)
                    | NONE => target)
                  val child_proofs = map (fn slot => certify_mapped_shift mapped amount
                    (source_child slot) (target_child slot)) (0 upto (radix-1))
                  val relation = @{term "comma_crt_mdd_root_shift_map_certificate :: nat list => nat comma_crt_mdd_node list => (nat => nat) => nat => nat => nat => bool"} $
                    Store.radices store $ Store.table store $ encode $ nat amount
                  val all_children = mapped_slots base axis amount children target_children target child_proofs relation
                  val (axis_bound,positive) = Vector.sub (#axis_facts base,axis)
                  fun width label items = prove_scalar base label (HOLogic.mk_eq
                    (Const (@{const_name size},nat_listT --> natT) $
                      HOLogic.mk_list natT (map nat items),radix_at store (nat axis)))
                  val source_width = width "Mapped shift source width" children
                in case target_children of
                  SOME cs => mapped_intro base "branch"
                    @{thm comma_crt_mdd_root_shift_map_certificate.root_shift_map_branch}
                    encode amount source target [("axis",nat axis),
                      ("children",HOLogic.mk_list natT (map nat children)),
                      ("shifted_children",HOLogic.mk_list natT (map nat cs))]
                    [source_bound,target_bound,source_eq,target_eq,axis_bound,positive,
                      source_width,width "Mapped shift target width" cs,all_children] proposition
                | NONE => mapped_intro base "alias"
                    @{thm comma_crt_mdd_root_shift_map_certificate.root_shift_map_alias}
                    encode amount source target [("axis",nat axis),
                      ("children",HOLogic.mk_list natT (map nat children))]
                    [source_bound,target_bound,source_eq,axis_bound,positive,
                      source_width,all_children] proposition
                end
            | _ => error "Mapped MDD shift changed leaf/branch shape")
          val theorem = Proof_Utils.exact_prop ctxt "Mapped shift certificate"
            (HOLogic.mk_Trueprop proposition) theorem
          val _ = certificates := Shift_Key.update (key,theorem) (!certificates)
        in theorem end
    end

  fun mapped_shift_eval_phase mapped amount source target =
    let val {base={store,ctxt,...},...} = mapped
        val certificate = certify_mapped_shift mapped amount source target
        val theorem = @{thm comma_crt_mdd_root_shift_map_certificate_eval_phase} OF
          [Store.wellformed store,certificate]
        val _ = if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
          null (Thm.tpairs_of theorem) andalso
          Context.subthy (Thm.theory_of_thm theorem,Proof_Context.theory_of ctxt)
          then () else error "Mapped shift phase transport is not closed"
    in theorem end

  fun mapped_statistics ({base,certificates,visits,...}:mapped_replay) =
    "mapped_shift_certificates=" ^ Int.toString (Shift_Key.size (!certificates)) ^
    " mapped_shift_visits=" ^ Int.toString (!visits) ^
    " mapped_shift_slot_rows=" ^ Int.toString (!(#slot_rows base)) ^
    " mapped_slot_template_hits=" ^ Int.toString (!(#slot_template_hits base)) ^
    " mapped_slot_template_misses=" ^ Int.toString (!(#slot_template_misses base))

  fun certify_shift (replay as {ctxt,store,shifts,shift_visits,...}:replay) amount source target =
    let
      val encode = @{term "id :: nat => nat"}
      fun identity input output =
        if input <> output then error "MDD identity shift changed leaf payload" else
          Proof_Utils.prove_exact ctxt "MDD identity shift leaf"
            (HOLogic.mk_Trueprop (HOLogic.mk_eq (encode $ nat input,nat output)))
            (fn context => Simplifier.asm_full_simp_tac
              (put_simpset HOL_basic_ss context |> Simplifier.add_simp @{thm id_apply}) 1)
      val mapped:mapped_replay = {base=replay,encode=encode,leaf=identity,
        certificates=shifts,visits=shift_visits}
      val theorem = certify_mapped_shift mapped amount source target
      val plain = Simplifier.rewrite_rule (put_simpset HOL_basic_ss ctxt)
        [Thm.symmetric (@{thm comma_crt_mdd_root_shift_certificate_def} RS @{thm eq_reflection})] theorem
    in Proof_Utils.exact_prop ctxt "MDD root shift certificate"
      (HOLogic.mk_Trueprop (mk_shift_prop replay amount source target)) plain end

  fun shift_eval_phase replay amount source target =
    let
      val {ctxt, store, zero_identity_hits, ...} = replay
      val rule = if amount=0 andalso source=target then
        let
          val _ = ignore (Store.bound store source)
          val phase = Var (("phase",0),natT)
          val eval = @{term "comma_crt_mdd_eval_phase :: nat list => nat comma_crt_mdd_node list => nat => nat => nat option"}
          fun at p = eval $ Store.radices store $ Store.table store $ p $ nat source
          val shifted = HOLogic.mk_binop @{const_name Groups.plus} (phase,nat 0)
          val conversion = Simplifier.rewrite
            (Comma_Entry_Arithmetic.natural_context ctxt) (Thm.cterm_of ctxt (at shifted))
          val _ = if Thm.term_of (Thm.rhs_of conversion) aconv at phase then ()
            else error "Zero-shift evaluation did not reduce to the same root"
          val theorem = Drule.zero_var_indexes
            (Thm.symmetric conversion RS @{thm meta_eq_to_obj_eq})
          val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq (at phase,at shifted))
          val _ = if Thm.prop_of theorem aconv expected then ()
            else error ("Zero-shift evaluation proposition mismatch: expected " ^
              Syntax.string_of_term ctxt expected ^ " actual " ^
              Syntax.string_of_term ctxt (Thm.prop_of theorem))
          val _ = zero_identity_hits := !zero_identity_hits + 1
        in theorem end
      else
        let
          val cert = certify_shift replay amount source target
        in @{thm comma_crt_mdd_root_shift_certificate_eval_phase} OF
          [Store.wellformed store, cert] end
      val _ = if Thm.nprems_of rule = 0 andalso null (Thm.hyps_of rule) andalso
          null (Thm.tpairs_of rule) andalso
          Context.subthy (Thm.theory_of_thm rule, Proof_Context.theory_of ctxt)
        then () else error "MDD root-shift phase transport is not closed"
    in rule end

  fun statistics ({shift_visits,slot_rows,store,axis_facts,zero_identity_hits,...}: replay) =
    Store.statistics store ^
    " shift_axis_fact_pairs=" ^ Int.toString (Vector.length axis_facts) ^
    " zero_shift_identity_hits=" ^ Int.toString (!zero_identity_hits) ^
    " shift_certificate_nodes=" ^ Int.toString (!shift_visits) ^
    " shift_slot_rows=" ^ Int.toString (!slot_rows)
end
