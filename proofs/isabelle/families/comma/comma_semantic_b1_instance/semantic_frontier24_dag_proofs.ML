(* Generic Frontier24 consumer.  It authenticates the finite MDD operation
   vectors once, then invokes the generic 24-step preimage induction.  The
   proposal history supplies only candidate roots; Store/Replay supplies all
   authority. *)
signature COMMA_FRONTIER24_DAG_PROOFS =
sig
  type initial_certificate = {cid: int, root: int, theorem: thm}
  type action_certificate = {roots: Comma_CRT_MDD_Arena.action_root list,
    exact: thm}
  type result = {image_certificate: thm, statistics: string}
  val action_certificate_from_exact:
    Proof.context -> Comma_CRT_MDD_Certificate_Store.store ->
    Comma_CRT_MDD_Arena.action_root list -> thm -> action_certificate
  val make:
    Proof.context -> Comma_CRT_MDD_Certificate_Store.store ->
    Comma_CRT_MDD_Arena.arena ->
    Comma_Frontier24_MDD_Proposal.history ->
    action_certificate ->
    initial_certificate list ->
    Comma_CRT_MDD_Operation_Replay.replay ->
    Comma_CRT_MDD_Bind_Replay.replay -> result
end

structure Comma_Frontier24_DAG_Proofs: COMMA_FRONTIER24_DAG_PROOFS =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Proposal = Comma_Frontier24_MDD_Proposal
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Shift = Comma_CRT_MDD_Operation_Replay
  structure Bind = Comma_CRT_MDD_Bind_Replay
  structure Utils = Comma_CRT_MDD_Proof_Utils

  type initial_certificate = {cid: int, root: int, theorem: thm}
  type action_certificate = {roots: Arena.action_root list, exact: thm}
  type result = {image_certificate: thm, statistics: string}

  val natT = @{typ nat}
  val boolT = HOLogic.boolT
  val natListT = HOLogic.listT natT
  val nodeT = @{typ "nat comma_crt_mdd_node"}
  val nodeListT = HOLogic.listT nodeT
  val layerListT = HOLogic.listT natListT
  val pairT = HOLogic.mk_prodT (natT,natT)
  val pairListT = HOLogic.listT pairT
  val natOptionT = Type (@{type_name option},[natT])
  val actionT = Type (@{type_name comma_phase_class_action},[natT])

  fun nat n = HOLogic.mk_number natT n
  fun tp p = HOLogic.mk_Trueprop p
  fun numeral_list ns = HOLogic.mk_list natT (map nat ns)
  fun vector_list rows = HOLogic.mk_list natListT (map numeral_list rows)
  fun some_nat n = Const (@{const_name Some},natT --> natOptionT) $ n
  fun list_nth xs i = Const (@{const_name nth},natListT --> natT --> natT) $ xs $ i
  fun mk_less x y = HOLogic.mk_binrel @{const_name less} (x,y)
  fun eval_phase store phase root =
    Const (@{const_name comma_crt_mdd_eval_phase},
      natListT --> nodeListT --> natT --> natT --> natOptionT) $
      Store.radices store $ Store.table store $ phase $ root
  fun phase_bound p = tp (mk_less p (nat 924))
  fun cid_bound c = tp (mk_less c (nat 46))

  fun specialize_object_all ctxt value theorem =
    let
      val rule=Drule.infer_instantiate ctxt
        [(("x",0),Thm.cterm_of ctxt value)] @{thm spec}
    in rule OF [theorem] end

  fun simp_context ctxt =
    Comma_Entry_Arithmetic.natural_context ctxt
    |> Simplifier.add_simps
      (@{thms list.simps list.size nth_Cons_0 nth_Cons_Suc nth_Cons_numeral
        upt_rec zip_Nil zip_Cons_Cons option.simps if_True if_False})

  (* Keep bounded universal checks symbolic.  This deliberately excludes
     upt_rec and recursive list equations, which belong only in selected-item
     normalization and list-all construction. *)
  fun vector_context ctxt =
    Comma_Entry_Arithmetic.natural_context ctxt
    |> Simplifier.add_simps
      @{thms list_all_iff set_upt atLeastLessThan_iff list.size
        list_all_Nil_iff list_all_Cons_iff le0}

  fun predicate_item ctxt label predicate index theorem =
    let
      val expected = tp (predicate $ nat index)
      val conv = Simplifier.rewrite (simp_context ctxt) (Thm.cterm_of ctxt expected)
      val reduced = Thm.term_of (Thm.rhs_of conv)
      val provided_conv = Simplifier.rewrite (simp_context ctxt)
        (Thm.cterm_of ctxt (Thm.prop_of theorem))
      val reduced_theorem = Utils.exact_prop ctxt (label ^ " reduced item") reduced
        (Thm.equal_elim provided_conv theorem)
      val normalized = Thm.equal_elim (Thm.symmetric conv) reduced_theorem
    in Utils.exact_prop ctxt label expected normalized end

  fun indexed_all_from_items ctxt bound predicate items =
    let
      val _ = if length items = bound then ()
        else error "Frontier indexed certificate vector has the wrong length"
      val cache = Comma_Selected_List_Conversion.make_successor_cache ctxt bound
      fun item i = predicate_item ctxt "Frontier indexed certificate item"
        predicate i (List.nth (items,i))
    in Comma_Selected_List_Conversion.prove_indexed_list_all
      {ctxt=ctxt,predicate=predicate,bound=bound,prove_item=item,
       zero_fact= @{thm comma_indexed_all_zero},
       step_fact= @{thm comma_indexed_all_Suc},
       successor_equation= #equation cache} end

  fun case_action rhs_step =
    let
      val none = some_nat (nat 0)
      val invalid = none
      val fork = Term.lambda (Free ("left_child",natT))
        (Term.lambda (Free ("right_child",natT)) none)
      val landmine = Term.lambda (Free ("landmine_child",natT)) none
      val next_phase = Free ("continue_phase",natT)
      val target = Free ("continue_target",natT)
      val continue = Term.lambda next_phase
        (Term.lambda target (some_nat (Const (@{const_name Suc},natT --> natT) $ target)))
      val caseT = natOptionT --> (natT --> natT --> natOptionT) -->
        (natT --> natOptionT) --> (natT --> natT --> natOptionT) -->
        actionT --> natOptionT
    in Const (@{const_name case_comma_phase_class_action},caseT) $
      invalid $ fork $ landmine $ continue $ rhs_step end

  fun action_certificate_exact ctxt store
      (certificate:action_certificate) =
    let
      val roots=map (Store.action_index store) (#roots certificate)
      val _=if length roots=46 then () else
        error "Universal source-action root vector must contain 46 classes"
      val root_vector=numeral_list roots
      val phase=Free ("frontier_action_phase",natT)
      val cid=Free ("frontier_action_cid",natT)
      val step = @{term comma_semantic_phase_program_class_step} $ phase $ cid
      val output=case_action step
      val equation=HOLogic.mk_eq
        (eval_phase store phase (list_nth root_vector cid),output)
      val proposition=Logic.all phase (Logic.mk_implies (phase_bound phase,
        Logic.all cid (Logic.mk_implies (cid_bound cid,tp equation))))
    in
      (roots,Utils.exact_prop ctxt "Universal source-action vector"
        proposition (#exact certificate))
    end

  fun action_certificate_from_exact ctxt store roots exact =
    let
      val certificate:action_certificate={roots=roots,exact=exact}
      val _=action_certificate_exact ctxt store certificate
    in certificate end

  fun phase_divisor ctxt store =
    let
      val radices = Store.radices store
      val vals = map (Utils.dest_nat "Frontier radix" natT) (HOLogic.dest_list radices)
      val _ = if vals=[3,4,11,7] then () else
        error "Frontier24 phase-divisor proof expects radices [3,4,11,7]"
      val axis = Free ("frontier_divisor_axis",natT)
      val radix = Const (@{const_name nth},natListT --> natT --> natT) $ radices $ axis
      val proposition = Logic.all axis (Logic.mk_implies
        (tp (mk_less axis (Const (@{const_name size},natListT --> natT) $ radices)),
         tp (Const (@{const_name dvd},natT --> natT --> boolT) $ radix $ nat 924)))
      val theorem = Drule.infer_instantiate ctxt
        [(("axis",0),Thm.cterm_of ctxt axis)] @{thm comma_frontier_radices_divide}
        |> Thm.forall_intr (Thm.cterm_of ctxt axis)
    in Utils.exact_prop ctxt "Frontier radix divisibility" proposition theorem end

  fun clock_facts ctxt =
    let
      val phase=Free ("frontier_clock_phase",natT)
      val cid=Free ("frontier_clock_cid",natT)
      val next_phase=Free ("frontier_clock_next_phase",natT)
      val target=Free ("frontier_clock_target",natT)
      val step= @{term comma_semantic_phase_program_class_step} $ phase $ cid
      val continued=HOLogic.mk_eq (step,
        Const (@{const_name Comma_Phase_Class_Continue},natT --> natT --> actionT) $
          next_phase $ target)
      val phase_ct=Thm.cterm_of ctxt phase
      val cid_ct=Thm.cterm_of ctxt cid
      val next_phase_ct=Thm.cterm_of ctxt next_phase
      val target_ct=Thm.cterm_of ctxt target
      val phase_guard_ct=Thm.cterm_of ctxt (phase_bound phase)
      val cid_guard_ct=Thm.cterm_of ctxt (cid_bound cid)
      val continued_ct=Thm.cterm_of ctxt (tp continued)
      val phase_fact=Thm.assume phase_guard_ct
      val cid_fact=Thm.assume cid_guard_ct
      val valid_definition=Drule.infer_instantiate ctxt
        [(("phase",0),phase_ct),(("class",0),cid_ct)]
        @{thm comma_semantic_phase_class_valid_def}
      val valid_fact= @{thm iffD2} OF
        [valid_definition,@{thm conjI} OF [phase_fact,cid_fact]]
      fun quantify conclusion =
        let
          val rule = Drule.infer_instantiate ctxt
            [(("phase",0),phase_ct),(("cid",0),cid_ct),
             (("next_phase",0),next_phase_ct),
             (("next_class",0),target_ct)] conclusion
          val point = rule OF [valid_fact,Thm.assume continued_ct]
          val point = Thm.implies_intr continued_ct point
          val point = Thm.forall_intr target_ct point
          val point = Thm.forall_intr next_phase_ct point
          val point = Thm.implies_intr cid_guard_ct point
          val point = Thm.forall_intr cid_ct point
          val point = Thm.implies_intr phase_guard_ct point
          val point = Thm.forall_intr phase_ct point
        in point end
      fun quant p = Logic.all phase (Logic.mk_implies (phase_bound phase,
        Logic.all cid (Logic.mk_implies (cid_bound cid,
          Logic.all next_phase (Logic.all target
            (Logic.mk_implies (tp continued,tp p)))))))
      val tick_prop=quant (HOLogic.mk_eq (next_phase,
        HOLogic.mk_binop @{const_name modulo}
          (HOLogic.mk_binop @{const_name plus} (phase,nat 1),nat 924)))
      val bound_prop=quant (mk_less target (nat 46))
      val tick=Utils.exact_prop ctxt "Frontier one-tick law" tick_prop
        (quantify @{thm comma_semantic_phase_program_class_step_continue_closed(1)})
      val next_valid_definition=Drule.infer_instantiate ctxt
        [(("phase",0),next_phase_ct),(("class",0),target_ct)]
        @{thm comma_semantic_phase_class_valid_def}
      val target_point=Drule.infer_instantiate ctxt
        [(("phase",0),phase_ct),(("cid",0),cid_ct),
         (("next_phase",0),next_phase_ct),
         (("next_class",0),target_ct)]
        @{thm comma_semantic_phase_program_class_step_continue_closed(2)}
        OF [valid_fact,Thm.assume continued_ct]
      val target_conjunction= @{thm iffD1} OF [next_valid_definition,target_point]
      val target_point= @{thm conjunct2} OF [target_conjunction]
      val target_bound=Utils.exact_prop ctxt "Frontier target bound" bound_prop
        (let
          val point=Thm.implies_intr continued_ct target_point
          val point=Thm.forall_intr target_ct point
          val point=Thm.forall_intr next_phase_ct point
          val point=Thm.implies_intr cid_guard_ct point
          val point=Thm.forall_intr cid_ct point
          val point=Thm.implies_intr phase_guard_ct point
          val point=Thm.forall_intr phase_ct point
        in point end)
    in (tick,target_bound) end

  fun initial_vector_exact ctxt store initial_roots certificates =
    let
      val roots=numeral_list initial_roots
      val predicate=Abs ("cid",natT,HOLogic.mk_all ("phase",natT,
        HOLogic.mk_imp (mk_less (Bound 0) (nat 924),
          HOLogic.mk_eq
            (eval_phase store (Bound 0) (list_nth roots (Bound 1)),
             some_nat (Const (@{const_name If},boolT --> natT --> natT --> natT) $
               HOLogic.mk_not (HOLogic.mk_mem
                 (HOLogic.mk_prod (Bound 0,Bound 1),@{term comma_continue24_endpoints})) $
               nat 1 $ nat 0)))))
      fun cert_for i =
        (case List.find (fn (c:initial_certificate) => #cid c=i) certificates of
          SOME c=>c | NONE=>error "Missing initial Frontier class theorem")
      val items=map (fn i=>
        let
          val cert=cert_for i
          val root=List.nth (initial_roots,i)
          val _=if #root cert=root then () else
            error "Initial frontier certificate refers to another root"
          val proposition=tp (HOLogic.mk_all ("phase",natT,
            HOLogic.mk_imp (mk_less (Bound 0) (nat 924),
              HOLogic.mk_eq
                (eval_phase store (Bound 0) (list_nth roots (nat i)),
                 some_nat (Const (@{const_name If},boolT --> natT --> natT --> natT) $
                   HOLogic.mk_not (HOLogic.mk_mem
                     (HOLogic.mk_prod (Bound 0,nat i),
                       @{term comma_continue24_endpoints})) $ nat 1 $ nat 0)))))
          val theorem=Utils.prove_exact ctxt "Initial vector class semantics" proposition
            (fn context=>
              Method.insert_tac context [#theorem cert] 1 THEN
              resolve_tac context [@{thm allI}] 1 THEN
              resolve_tac context [@{thm impI}] 1 THEN
              asm_full_simp_tac (simp_context context
                |> Simplifier.add_simps [@{thm comma_continue24_endpoints_def}]) 1)
        in theorem end) (0 upto 45)
      val indexed=indexed_all_from_items ctxt 46 predicate items
      val vector=Const (@{const_name comma_crt_mdd_frontier_vector_exact},
        natListT --> nodeListT --> natListT --> (pairT --> boolT) --> boolT) $
        Store.radices store $ Store.table store $ roots $
        Abs ("phase_cid",pairT,
          HOLogic.mk_not (HOLogic.mk_mem (Bound 0,@{term comma_continue24_endpoints})))
      val theorem=Utils.prove_exact ctxt "Frontier initial exact vector" (tp vector)
        (fn context=>
          Method.insert_tac context [indexed] 1 THEN
          asm_full_simp_tac (vector_context context
            |> Simplifier.add_simps [@{thm comma_crt_mdd_frontier_vector_exact_def},
              @{thm list_all_iff}]) 1 THEN
          auto_tac (vector_context context
            |> Simplifier.add_simps [@{thm comma_continue24_endpoints_def}]))
    in theorem end

  fun round_certificate ctxt store action_roots false_root future shifted preimage
      shift_replay bind_replay =
    let
      val future_term=numeral_list future
      val shifted_term=numeral_list shifted
      val preimage_term=numeral_list preimage
      val action_term=numeral_list action_roots
      val mapping_pairs=map_index (fn (i,root)=>(i+1,root)) shifted
      val zip_term=Const (@{const_name zip},natListT --> natListT --> pairListT) $
        (Const (@{const_name upt},natT --> natT --> natListT) $ nat 1 $
          (Const (@{const_name Suc},natT --> natT) $
            (Const (@{const_name size},natListT --> natT) $ shifted_term))) $ shifted_term
      val shift_pred=Abs ("target",natT,
        Const (@{const_name comma_crt_mdd_root_shift_certificate},
          natListT --> nodeListT --> natT --> natT --> natT --> boolT) $
          Store.radices store $ Store.table store $ nat 1 $
          list_nth future_term (Bound 0) $ list_nth shifted_term (Bound 0))
      val shift_facts=map_index (fn (i,source)=>
        Shift.certify_shift shift_replay 1 source (List.nth (shifted,i))) future
      val shift_all=indexed_all_from_items ctxt 46 shift_pred shift_facts
      val bind_pred=Abs ("cid",natT,
        Const (@{const_name comma_crt_mdd_bind_certificate},
          natListT --> nodeListT --> pairListT --> natT --> natT --> natT --> boolT) $
          Store.radices store $ Store.table store $ zip_term $ nat false_root $
          list_nth action_term (Bound 0) $ list_nth preimage_term (Bound 0))
      val bind_facts=map_index (fn (cid,source)=>
        let
          val key:Arena.bind_key=(source,false_root,mapping_pairs)
          val witness=Store.bind_witness store key
          val expected=List.nth (preimage,cid)
          val _=if #result witness=expected andalso #key witness=key then () else
            error "Frontier bind witness disagrees with the proposed result root"
        in Bind.certify_bind bind_replay key end) action_roots
      val bind_all=indexed_all_from_items ctxt 46 bind_pred bind_facts
      val data=Const (@{const_name comma_crt_mdd_frontier_preimage_certificates},
        natListT --> nodeListT --> natListT --> natListT --> natListT --> natListT --> natT --> boolT) $
        Store.radices store $ Store.table store $ action_term $ future_term $
        shifted_term $ preimage_term $ nat false_root
      val theorem=Utils.prove_exact ctxt "Frontier checked preimage operation vector" (tp data)
        (fn context=>
          Method.insert_tac context [shift_all,bind_all] 1 THEN
          asm_full_simp_tac (vector_context context
            |> Simplifier.add_simps [@{thm comma_crt_mdd_frontier_preimage_certificates_def},
              @{thm list_all_iff}]) 1)
    in theorem end

  fun chain_certificate ctxt store action_roots false_root layers shifted_layers edges =
    let
      val layers_term=vector_list layers
      val shifted_term=vector_list shifted_layers
      val nth_layers=Const (@{const_name nth},HOLogic.listT natListT --> natT --> natListT)
      val depth=Bound 0
      val predicate=Abs ("depth",natT,
        Const (@{const_name comma_crt_mdd_frontier_preimage_certificates},
          natListT --> nodeListT --> natListT --> natListT --> natListT --> natListT --> natT --> boolT) $
          Store.radices store $ Store.table store $ numeral_list action_roots $
          (nth_layers $ layers_term $ depth) $
          (nth_layers $ shifted_term $ depth) $
          (nth_layers $ layers_term $
            (Const (@{const_name Suc},natT --> natT) $ depth)) $ nat false_root)
      val edges_all=indexed_all_from_items ctxt 24 predicate edges
      val chain=Const (@{const_name comma_crt_mdd_frontier_chain_certificates},
        natListT --> nodeListT --> natListT --> natT -->
          layerListT --> layerListT --> boolT) $
        Store.radices store $ Store.table store $ numeral_list action_roots $
        nat false_root $ layers_term $ shifted_term
      val theorem=Utils.prove_exact ctxt "Frontier24 checked operation chain" (tp chain)
        (fn context=>
          Method.insert_tac context [edges_all] 1 THEN
          asm_full_simp_tac (vector_context context
            |> Simplifier.add_simps [@{thm comma_crt_mdd_frontier_chain_certificates_def},
              @{thm list_all_iff}]) 1 THEN
          auto_tac (vector_context context))
    in theorem end

  fun make ctxt store arena history action_cert initial_certs shift_replay bind_replay =
    let
      val _ = if Context.subthy (Proof_Context.theory_of (Store.context store),
          Proof_Context.theory_of ctxt) then () else
        error "Frontier24 consumer context does not extend its frozen store"
      val initial_roots=map (Store.boolean_index store) (#initial history)
      val rounds= #rounds history
      val round_roots=map (fn (r:Proposal.round)=>map (Store.boolean_index store) (#roots r)) rounds
      val shifted_rows=map (fn (r:Proposal.round)=>map (Store.boolean_index store) (#shifted r)) rounds
      val layers=initial_roots::round_roots
      val _=if length layers=25 andalso length shifted_rows=24 andalso
        length initial_roots=46 andalso List.all (fn x=>length x=46) layers andalso
        List.all (fn x=>length x=46) shifted_rows then () else
        error "Frontier24 DAG vectors have incorrect dimensions"
      val _=if length initial_certs=46 andalso
          sort int_ord (map #cid initial_certs)=(0 upto 45)
        then () else error "Initial certificates do not uniquely cover classes 0..45"
      val (action_roots,action_exact)=action_certificate_exact ctxt store action_cert
      val (tick,target_bound)=clock_facts ctxt
      val divisor=phase_divisor ctxt store
      val false_root=Store.boolean_index store (Arena.boolean_false arena)
      val _=if Store.node store false_root=Store.Leaf 0 then () else
        error "Frontier fallback root is not the authenticated false leaf"
      val false_phase=Free ("frontier_false_phase",natT)
      val false_fact=Store.phase_leaf store false_root
      val false_phase_ct=Thm.cterm_of ctxt false_phase
      val false_guard=Thm.cterm_of ctxt (phase_bound false_phase)
      val false_at_phase=Thm.forall_elim false_phase_ct false_fact
      val false_at_phase=Thm.implies_intr false_guard false_at_phase
      val false_exact=Thm.forall_intr false_phase_ct false_at_phase
      val false_expected=Logic.all false_phase
        (Logic.mk_implies (phase_bound false_phase,
          tp (HOLogic.mk_eq
            (eval_phase store false_phase (nat false_root),some_nat (nat 0)))))
      val false_exact=Utils.exact_prop ctxt "Frontier false-leaf phase evaluation"
        false_expected false_exact
      val edges=map_index (fn (round,_)=>
        round_certificate ctxt store action_roots false_root (List.nth (layers,round))
          (List.nth (shifted_rows,round)) (List.nth (layers,round+1))
          shift_replay bind_replay) rounds
      val chain=chain_certificate ctxt store action_roots false_root layers shifted_rows edges
      val base_exact=initial_vector_exact ctxt store initial_roots initial_certs
      val final_roots=List.nth (layers,24)
      val final_root=List.hd final_roots
      val _=if final_root=false_root andalso List.all (fn root=>root=false_root) final_roots andalso
          Store.node store final_root=Store.Leaf 0 then () else
        error "Frontier24 terminal layer is not the false leaf"
      val phase=Free ("frontier_empty_phase",natT)
      val cid=Free ("frontier_empty_cid",natT)
      val final_term=Const (@{const_name replicate},natT --> natT --> natListT) $
        nat 46 $ nat false_root
      val empty_object=tp (HOLogic.mk_all ("phase",natT,
        HOLogic.mk_imp (mk_less (Bound 0) (nat 924),
          HOLogic.mk_all ("cid",natT,
            HOLogic.mk_imp (mk_less (Bound 0) (nat 46),
              HOLogic.mk_eq (eval_phase store (Bound 1) (list_nth final_term (Bound 0)),
                some_nat (nat 0)))))))
      val empty_object_theorem=Utils.prove_exact ctxt "Frontier empty terminal object vector"
        empty_object (fn context=>
          Method.insert_tac context [false_exact] 1 THEN
          resolve_tac context [@{thm allI}] 1 THEN
          resolve_tac context [@{thm impI}] 1 THEN
          resolve_tac context [@{thm allI}] 1 THEN
          resolve_tac context [@{thm impI}] 1 THEN
          asm_full_simp_tac (simp_context context
            |> Simplifier.add_simps @{thms nth_replicate}) 1)
      val phase_ct=Thm.cterm_of ctxt phase
      val cid_ct=Thm.cterm_of ctxt cid
      val phase_guard=Thm.cterm_of ctxt (phase_bound phase)
      val cid_guard=Thm.cterm_of ctxt (cid_bound cid)
      val phase_instance=specialize_object_all ctxt phase empty_object_theorem
      val phase_fact=Thm.assume phase_guard
      val cid_universal= specialize_object_all ctxt cid
        (@{thm mp} OF [phase_instance,phase_fact])
      val cid_fact=Thm.assume cid_guard
      val point= @{thm mp} OF [cid_universal,cid_fact]
      val with_cid=Thm.implies_intr cid_guard point
      val all_cid=Thm.forall_intr cid_ct with_cid
      val with_phase=Thm.implies_intr phase_guard all_cid
      val empty_exact=Thm.forall_intr phase_ct with_phase
      val empty_expected=Logic.all phase (Logic.mk_implies (phase_bound phase,
        Logic.all cid (Logic.mk_implies (cid_bound cid,
          tp (HOLogic.mk_eq (eval_phase store phase (list_nth final_term cid),
            some_nat (nat 0)))))))
      val empty_exact=Utils.exact_prop ctxt "Frontier empty terminal layer"
        empty_expected empty_exact
      val final_row_equation=Utils.prove_exact ctxt "Frontier terminal vector shape"
        (tp (HOLogic.mk_eq (numeral_list final_roots,final_term)))
        (fn context=>simp_tac
          (Simplifier.add_simps @{thms eval_nat_numeral} context) 1)
      val rule=Drule.infer_instantiate ctxt
        [(("radices",0),Thm.cterm_of ctxt (Store.radices store)),
         (("nodes",0),Thm.cterm_of ctxt (Store.table store)),
         (("action_roots",0),Thm.cterm_of ctxt (numeral_list action_roots)),
         (("false_root",0),Thm.cterm_of ctxt (nat false_root)),
         (("layers",0),Thm.cterm_of ctxt (vector_list layers)),
         (("shifted_layers",0),Thm.cterm_of ctxt (vector_list shifted_rows))]
        @{thm comma_crt_mdd_frontier_dag_direct_image}
      val result=Utils.prove_exact ctxt "Frontier24 DAG direct image certificate"
        (tp @{term comma_continue24_direct_image_certificate})
        (fn context=>
          resolve_tac context [rule] 1 THEN
          ALLGOALS (Method.insert_tac context
            [Store.wellformed store,divisor,action_exact,target_bound,tick,false_exact,
             base_exact,chain,empty_exact] THEN'
            asm_full_simp_tac (simp_context context
              |> Simplifier.add_simps [final_row_equation])))
      val stats="frontier_dag_rounds=24 classes=46 structural_rounds=" ^
        Int.toString (length edges) ^ " one_step_actions=" ^
        Int.toString (length action_roots) ^ "; " ^
        Shift.statistics shift_replay ^ "; " ^ Bind.statistics bind_replay
    in {image_certificate=result,statistics=stats}:result end
end
