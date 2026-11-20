(* Replay priority-selection witnesses within one immutable Store. *)
structure Comma_CRT_MDD_Multiway_Replay =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Key = Table(type key = Arena.priority_key
    val ord = prod_ord (list_ord (prod_ord int_ord int_ord)) int_ord)
  structure Family_Key = Table(type key = int * int
    val ord = prod_ord int_ord int_ord)
  structure Cofactor_Key = Table(type key = int * int * int
    val ord = prod_ord int_ord (prod_ord int_ord int_ord) o
      apply2 (fn (a,b,c) => (a,(b,c))))
  val natT = @{typ nat}
  val pairT = @{typ "nat * nat"}
  fun nat n = HOLogic.mk_number natT n
  fun pairs rows = HOLogic.mk_list pairT
    (map (fn (g,a) => HOLogic.mk_prod (nat g,nat a)) rows)
  type replay = {store:Store.store, memo:(int * thm) Key.table Unsynchronized.ref,
    active:unit Key.table Unsynchronized.ref, normalization_proofs:int Unsynchronized.ref,
    memo_hits:int Unsynchronized.ref, cold_misses:int Unsynchronized.ref,
    cofactors:thm Cofactor_Key.table Unsynchronized.ref, families:thm Family_Key.table Unsynchronized.ref, ranges:thm Inttab.table Unsynchronized.ref,
    cofactor_hits:int Unsynchronized.ref, cofactor_misses:int Unsynchronized.ref,
    normalization_time:Time.time Unsynchronized.ref, cofactor_time:Time.time Unsynchronized.ref,
    slot_time:Time.time Unsynchronized.ref, split_time:Time.time Unsynchronized.ref,
    arithmetic:Proof.context}
  fun make store : replay = {store=store,memo=Unsynchronized.ref Key.empty,
    active=Unsynchronized.ref Key.empty,normalization_proofs=Unsynchronized.ref 0,
    memo_hits=Unsynchronized.ref 0,cold_misses=Unsynchronized.ref 0,
    cofactors=Unsynchronized.ref Cofactor_Key.empty,families=Unsynchronized.ref Family_Key.empty,ranges=Unsynchronized.ref Inttab.empty,
    cofactor_hits=Unsynchronized.ref 0,cofactor_misses=Unsynchronized.ref 0,
    normalization_time=Unsynchronized.ref Time.zeroTime, cofactor_time=Unsynchronized.ref Time.zeroTime,
    slot_time=Unsynchronized.ref Time.zeroTime, split_time=Unsynchronized.ref Time.zeroTime,
    arithmetic=Comma_Entry_Arithmetic.natural_context (Store.context store)}

  fun certify ({store,memo,active,normalization_proofs,memo_hits,cold_misses,
      cofactors,families,ranges,cofactor_hits,cofactor_misses,normalization_time,cofactor_time,
      slot_time,split_time,arithmetic}:replay) key =
    let
      val ctxt = Store.context store
      val radices = Store.radices store
      val nodes = Store.table store
      val widths = map (Utils.dest_nat "priority radix" natT) (HOLogic.dest_list radices)
      val certificate = @{term comma_crt_mdd_multiway_certificate} $ radices $ nodes
      fun proposition (rows,fallback) output = HOLogic.mk_Trueprop
        (certificate $ pairs rows $ nat fallback $ nat output)
      fun stage ordinal label f =
        let
          val report = ordinal <= 3 orelse ordinal mod 256 = 0
          val started = Time.now ()
          val _ = if report then Comma_Proof_Profile.report
            ("Priority cold=" ^ Int.toString ordinal ^ " " ^ label ^ " start") else ()
          val outcome = Exn.capture f ()
          val elapsed = Time.- (Time.now (),started)
          val metric = (case label of "normalization lookup" => SOME normalization_time
            | "normalization proof" => SOME normalization_time
            | "cofactor facts" => SOME cofactor_time | "slot proofs" => SOME slot_time
            | "split assembly" => SOME split_time | _ => NONE)
          val _ = Option.app (fn cell => cell := Time.+ (!cell,elapsed)) metric
          val _ = if label = "normalization lookup" andalso ordinal mod 256 = 0 then
            Comma_Proof_Profile.report
              ("Priority totals cold=" ^ Int.toString ordinal ^
                " cofactor_hits=" ^ Int.toString (!cofactor_hits) ^
                " cofactor_misses=" ^ Int.toString (!cofactor_misses) ^
                " normalization_ms=" ^ LargeInt.toString (Time.toMilliseconds (!normalization_time)) ^
                " cofactor_ms=" ^ LargeInt.toString (Time.toMilliseconds (!cofactor_time)) ^
                " slot_ms=" ^ LargeInt.toString (Time.toMilliseconds (!slot_time)) ^
                " split_ms=" ^ LargeInt.toString (Time.toMilliseconds (!split_time)))
            else ()
          val _ = if report then Comma_Proof_Profile.report
            ("Priority cold=" ^ Int.toString ordinal ^ " " ^ label ^ " elapsed_ms=" ^
              Comma_Proof_Profile.elapsed_ms started) else ()
        in Exn.release outcome end
      fun cofactor axis slot id = (case Store.node store id of
          Store.Leaf _ => id
        | Store.Branch (other,children) =>
            if other<axis then error "Priority split did not choose the least axis"
            else if axis=other then List.nth (children,slot) else id)
      val child_term = @{term "comma_crt_mdd_zip_child :: nat comma_crt_mdd_node list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"} $ nodes
      val nth_context = arithmetic |> Simplifier.add_simps
        @{thms nth_Cons_0 nth_Cons_Suc nth_Cons' list.simps}
      fun cofactor_fact axis slot id =
        let
          val node = Store.node store id
          val value = cofactor axis slot id
          val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (child_term $ nat id $ nat axis $ nat slot,nat value))
          val concrete_key = (axis,slot,id)
          val theorem = (case Cofactor_Key.lookup (!cofactors) concrete_key of
              SOME th => (cofactor_hits := !cofactor_hits + 1; th)
            | NONE => let
                val _ = cofactor_misses := !cofactor_misses + 1
              val key = (axis,id)
              val variable = Free ("priority_cofactor_slot",natT)
              val rhs = (case node of
                  Store.Branch (other,children) =>
                    if other = axis then Const (@{const_name nth},
                        HOLogic.listT natT --> natT --> natT) $
                      HOLogic.mk_list natT (map nat children) $ variable
                    else nat id
                | Store.Leaf _ => nat id)
              val family_expected = Logic.all variable (HOLogic.mk_Trueprop
                (HOLogic.mk_eq (child_term $ nat id $ nat axis $ variable,rhs)))
              val family = (case Family_Key.lookup (!families) key of
                  SOME th => (th)
                | NONE => let
                    val lookup = Store.lookup store id
                    val context = arithmetic |> Simplifier.add_simps
                      (lookup :: @{thms comma_crt_mdd_zip_child_def comma_crt_mdd_node.case})
                    val th = Utils.prove_exact ctxt "Priority cofactor family" family_expected
                      (fn _ => Simplifier.asm_full_simp_tac context 1)
                    val _ = families := Family_Key.update (key,th) (!families)
                  in th end)
              val family = Utils.exact_prop ctxt "Priority cofactor family" family_expected family
              val specialized = Thm.forall_elim (Thm.cterm_of ctxt (nat slot)) family
              val specialized_result = (case node of
                  Store.Branch (other,_) => if other = axis then
                    Conv.fconv_rule (Conv.arg_conv (Conv.arg_conv (Simplifier.rewrite nth_context))) specialized
                    else specialized
                | Store.Leaf _ => specialized)
                val result = Utils.exact_prop ctxt "Priority cofactor" expected specialized_result
                val _ = cofactors := Cofactor_Key.update (concrete_key,result) (!cofactors)
              in result end)
        in Utils.exact_prop ctxt "Priority cofactor" expected theorem end
      fun normalize raw =
        let
          val (rows,fallback) = raw
          val {key=expected,steps} = Store.priority_normalize_trace store raw
          val listT = HOLogic.listT pairT
          val cons = Const (@{const_name Cons},pairT --> listT --> listT)
          fun pair (g,a) = HOLogic.mk_prod (nat g,nat a)
          fun goal original final_rows final_fallback = HOLogic.mk_Trueprop
            (@{term comma_crt_mdd_multiway_normalize} $ nodes $ original $ nat fallback $
              final_rows $ nat final_fallback)
          fun build [] [] =
                let val empty = HOLogic.mk_list pairT []
                    val target = goal empty empty fallback
                    val rule = @{thm comma_crt_mdd_multiway_normalize.empty}
                    val theorem = Thm.instantiate
                      (Thm.match (Thm.cconcl_of rule,Thm.cterm_of ctxt target)) rule
                      |> Utils.exact_prop ctxt "Priority empty normalization" target
                in (empty,empty,([],fallback),theorem) end
            | build ((g,a)::rest) (((g',a'),kind)::tail) =
                let
                  val _ = if (g,a)=(g',a') then () else error "Priority normalization transcript changed order"
                  val entry = pair (g,a)
                  fun apply rule target extra =
                    (Thm.instantiate (Thm.match (Thm.cconcl_of rule,Thm.cterm_of ctxt target)) rule OF extra)
                    |> Utils.exact_prop ctxt "Priority normalization step" target
                  fun guard_facts expected_leaf =
                    if Store.node store g=Store.Leaf expected_leaf then
                      [Store.bound store g,Store.lookup store g RS @{thm meta_eq_to_obj_eq}]
                    else error "Priority normalization guard classification differs"
                in (case kind of
                    Arena.Guard_True =>
                      let val _ = if null tail then () else error "Priority true guard has later transcript steps"
                          val original = cons $ entry $ pairs rest
                          val target = goal original (HOLogic.mk_list pairT []) a
                          val theorem = apply @{thm comma_crt_mdd_multiway_normalize.stop} target (guard_facts 1)
                      in (original,HOLogic.mk_list pairT [],([],a),theorem) end
                  | Arena.Guard_False =>
                      let val (rest_term,normalized,(out,final),child) = build rest tail
                          val original = cons $ entry $ rest_term
                          val target = goal original normalized final
                          val theorem = apply @{thm comma_crt_mdd_multiway_normalize.drop} target (guard_facts 0 @ [child])
                      in (original,normalized,(out,final),theorem) end
                  | Arena.Guard_Keep =>
                      let val _ = (case Store.node store g of Store.Leaf 0 => error "False guard retained"
                              | Store.Leaf 1 => error "True guard retained" | _ => ())
                          val (rest_term,normalized,(out,final),child) = build rest tail
                          val original = cons $ entry $ rest_term
                          val kept = cons $ entry $ normalized
                          val target = goal original kept final
                          val theorem = apply @{thm comma_crt_mdd_multiway_normalize.keep} target [child]
                      in (original,kept,((g,a)::out,final),theorem) end)
                end
            | build _ _ = error "Priority normalization transcript is incomplete"
          val (_,_,actual,theorem) = build rows steps
          val _ = if actual=expected then () else error "Priority normalization result differs"
          val target = goal (pairs rows) (pairs (#1 expected)) (#2 expected)
        in Utils.exact_prop ctxt "Priority normalization" target theorem end
      fun prove raw =
        (case Key.lookup (!memo) raw of
          SOME (output,theorem) =>
            (memo_hits := !memo_hits+1;
             Utils.exact_prop ctxt "Reused priority certificate" (proposition raw output) theorem)
        | NONE =>
          let val _ = cold_misses := !cold_misses+1
              val ordinal = !cold_misses
              val key = stage ordinal "normalization lookup" (fn () => Store.priority_normalize store raw)
          in if raw<>key then
            let val witness = stage ordinal "witness lookup" (fn () => Store.priority_witness store raw)
                val norm = stage ordinal "normalization proof" (fn () => normalize raw)
                val canonical = prove key
                val output = #result witness
                val target = proposition raw output
                val theorem = (@{thm comma_crt_mdd_multiway_certificate.normalize} OF [norm,canonical])
                  |> Utils.exact_prop ctxt "Priority normalized certificate" target
                val _ = normalization_proofs := !normalization_proofs+1
                val _ = memo := Key.update (raw,(output,theorem)) (!memo)
            in theorem end
          else
          let
            val _ = if Key.defined (!active) key then error "Cyclic priority witness" else ()
            val _ = active := Key.update (key,()) (!active)
            fun run () =
              let
                val witness = stage ordinal "witness lookup" (fn () => Store.priority_witness store key)
                val _ = if #key witness=key then () else error "Priority witness changed key"
                val (rows,fallback) = key
                val output = #result witness
                val ids = distinct (op =) (fallback :: output :: maps (fn (g,a) => [g,a]) rows)
                val node_facts = stage ordinal "node facts" (fn () =>
                  maps (fn id => [Store.bound store id,Store.lookup store id]) ids)
                val base = arithmetic
                  |> Simplifier.add_simps (node_facts @
                    @{thms comma_crt_mdd_multiway_leaf_value_def list_all_Nil_iff list_all_Cons_iff list.simps prod.case})
                fun direct rule extra = Goal.prove ctxt [] [] (proposition key output)
                  (fn _ => resolve_tac base [rule] 1 THEN
                    ALLGOALS (asm_full_simp_tac (Simplifier.add_simps extra base)))
                val theorem = (case #step witness of
                    Arena.Priority_Fallback => direct @{thm comma_crt_mdd_multiway_certificate.fallback} []
                  | Arena.Priority_Take => direct @{thm comma_crt_mdd_multiway_certificate.take} []
                  | Arena.Priority_Skip child => direct @{thm comma_crt_mdd_multiway_certificate.skip} [prove child]
                  | Arena.Priority_Leaf _ => direct @{thm comma_crt_mdd_multiway_certificate.leaf} []
                  | Arena.Priority_Branch (axis,children) =>
                    let
                      val _ = if 0<=axis andalso axis<length widths then () else error "Priority axis invalid"
                      val width = List.nth (widths,axis)
                      val _ = if width>0 andalso length children=width then () else error "Priority branch width invalid"
                      fun selected slot =
                        (map (fn (g,a) => (cofactor axis slot g,cofactor axis slot a)) rows,
                         cofactor axis slot fallback)
                      val _ = List.app (fn (slot,child) =>
                        if child=selected slot andalso #result (Store.priority_witness store child)=cofactor axis slot output
                        then () else error "Priority child is not the exact cofactor")
                        ((0 upto (width-1)) ~~ children)
                      val slot = Free ("priority_slot",natT)
                      (* Construct the indexed predicate with exact cofactor terms. *)
                      val map_pair = @{term "\<lambda>(nodes::nat comma_crt_mdd_node list) axis slot (g,a). (comma_crt_mdd_zip_child nodes g axis slot, comma_crt_mdd_zip_child nodes a axis slot)"}
                      val mapped = Const (@{const_name map},(pairT --> pairT) --> HOLogic.listT pairT --> HOLogic.listT pairT) $
                        (map_pair $ nodes $ nat axis $ slot) $ pairs rows
                      val predicate = Envir.beta_norm (Term.lambda slot (certificate $ mapped $
                        (child_term $ nat fallback $ nat axis $ slot) $
                        (child_term $ nat output $ nat axis $ slot)))
                      fun slot_fact (i,child) =
                        let val body = Envir.beta_norm (predicate $ nat i)
                            val target = HOLogic.mk_Trueprop body
                            val theorem = prove child
                            val facts = stage ordinal "cofactor facts" (fn () =>
                              map (cofactor_fact axis i) ids)
                        in stage ordinal "slot proofs" (fn () =>
                          let val context = arithmetic |> Simplifier.add_simps
                                (facts @ @{thms list.simps prod.case fst_conv snd_conv})
                              val conversion = Simplifier.rewrite context (Thm.cterm_of ctxt target)
                              val checked = Utils.exact_prop ctxt "Priority reduced cofactor slot"
                                (Thm.term_of (Thm.rhs_of conversion)) theorem
                          in Thm.equal_elim (Thm.symmetric conversion) checked
                            |> Utils.exact_prop ctxt "Priority cofactor slot" target end) end
                      val slot_facts = stage ordinal "slot subtree" (fn () =>
                        map slot_fact ((0 upto (width-1)) ~~ children))
                      val all_slots = Utils.literal_list_all ctxt "Priority split slots" predicate
                        (map nat (0 upto (width-1))) slot_facts
                      val listT = HOLogic.listT natT
                      val nth = Const (@{const_name nth}, listT --> natT --> natT)
                      val upt = Const (@{const_name upt},natT --> natT --> listT) $
                        nat 0 $ (nth $ radices $ nat axis)
                      val range_conversion = (case Inttab.lookup (!ranges) axis of
                          SOME th => th
                        | NONE => let
                            val th = Simplifier.rewrite
                              (arithmetic |> Simplifier.add_simps
                                @{thms upt_rec nth_Cons_0 nth_Cons_Suc nth_Cons' list.size})
                              (Thm.cterm_of ctxt upt)
                            val _ = Utils.ensure_closed_context ctxt "Priority slot range" th
                            val _ = ranges := Inttab.update (axis,th) (!ranges)
                          in th end)
                      val list_all = Const (@{const_name list_all},
                        (natT --> HOLogic.boolT) --> listT --> HOLogic.boolT)
                      val lifted = Thm.combination
                        (Thm.reflexive (Thm.cterm_of ctxt (list_all $ predicate))) range_conversion
                      val conversion = Thm.combination
                        (Thm.reflexive (Thm.cterm_of ctxt
                          (Const (@{const_name Trueprop},HOLogic.boolT --> @{typ prop})))) lifted
                      val indexed_slots = Thm.equal_elim (Thm.symmetric conversion)
                        (Utils.exact_prop ctxt "Priority literal split slots"
                          (Thm.term_of (Thm.rhs_of conversion)) all_slots)
                      val axis_ct = Thm.cterm_of ctxt (nat axis)
                      val rule = Drule.infer_instantiate ctxt [(("axis",0),axis_ct)]
                        @{thm comma_crt_mdd_multiway_split_list}
                    in stage ordinal "split assembly" (fn () => Goal.prove ctxt [] [] (proposition key output) (fn _ =>
                      resolve_tac base [rule] 1 THEN
                      EVERY (replicate 5 (asm_full_simp_tac
                        (Simplifier.add_simps @{thms nth_Cons_0 nth_Cons_Suc nth_Cons' list.size} base) 1)) THEN
                      resolve_tac base [indexed_slots] 1)) end)
              in (output,Utils.exact_prop ctxt "Priority selector certificate"
                (proposition key output) theorem) end
            val outcome = Exn.capture run ()
            val _ = active := Key.delete key (!active)
            val (output,theorem) = Exn.release outcome
            val _ = memo := Key.update (key,(output,theorem)) (!memo)
          in theorem end
        end)
    in prove key end

  fun statistics ({memo,normalization_proofs,memo_hits,cold_misses,cofactor_hits,
      cofactor_misses,cofactors,families,ranges,normalization_time,cofactor_time,slot_time,split_time,...}: replay) =
    "priority_certificates=" ^ Int.toString (Key.size (!memo)) ^
    " priority_normalization_proofs=" ^ Int.toString (!normalization_proofs) ^
    " priority_certificate_hits=" ^ Int.toString (!memo_hits) ^
    " priority_cold_misses=" ^ Int.toString (!cold_misses) ^
    " priority_cofactor_hits=" ^ Int.toString (!cofactor_hits) ^
    " priority_cofactor_misses=" ^ Int.toString (!cofactor_misses) ^
    " priority_cofactor_entries=" ^ Int.toString (Cofactor_Key.size (!cofactors)) ^
    " priority_cofactor_family_entries=" ^ Int.toString (Family_Key.size (!families)) ^
    " priority_range_entries=" ^ Int.toString (Inttab.size (!ranges)) ^
    " priority_normalization_ms=" ^ LargeInt.toString (Time.toMilliseconds (!normalization_time)) ^
    " priority_cofactor_ms=" ^ LargeInt.toString (Time.toMilliseconds (!cofactor_time)) ^
    " priority_slot_ms=" ^ LargeInt.toString (Time.toMilliseconds (!slot_time)) ^
    " priority_split_ms=" ^ LargeInt.toString (Time.toMilliseconds (!split_time))
end
