(* Construct the finite structural M204 checker proposition from individually
   kernel-replayed Store facts, then derive the universal Bellman theorem.
   No physical phase is enumerated here. *)
structure Comma_Frontier_M204_Bulk_Publisher =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Proposal = Comma_Frontier_M204_Bellman_Proposal
  structure Certificates = Comma_Frontier_M204_Bellman_Certificates
  structure Comparison_Table = Table
  (
    type key = int * int
    val ord = prod_ord int_ord int_ord
  )
  val natT = @{typ nat}
  val natListT = @{typ "nat list"}
  val boolT = HOLogic.boolT
  fun nat n = HOLogic.mk_number natT n
  fun list_nat xs = HOLogic.mk_list natT (map nat xs)
  fun app f xs = Envir.beta_norm (list_comb (f,xs))
  fun tp t = HOLogic.mk_Trueprop t

  fun certify ctxt store (candidate: Proposal.result) (proofs: Certificates.result) =
    let
      val arena = #arena candidate
      val radices = Store.radices store
      val nodes = Store.table store
      val d_ids = map (Store.action_index store) (#d_roots candidate)
      val step_ids = map (Store.action_index store) (#step_roots candidate)
      val shift_ids = map (Store.action_index store) (#shifted candidate)
      val result_ids = map (Store.boolean_index store) (#roots candidate)
      val keys = #bind_keys candidate
      val _ = if length d_ids=46 andalso length step_ids=46 andalso
          length shift_ids=46 andalso length result_ids=46 andalso length keys=46
        then () else error "M204 bulk publisher requires 46 structural rows"
      val fallback = #2 (hd keys)
      val _ = if List.all (fn (_,f,_) => f=fallback) keys then ()
        else error "M204 bulk bind rows have different fallback roots"
      val _ = (case Store.node store fallback of Store.Leaf 0 => ()
        | _ => error "M204 bulk fallback is not the checked false leaf")
      val _ = List.app (fn id => case Store.node store id of Store.Leaf 1 => ()
        | _ => error "M204 bulk result is not the checked true leaf") result_ids
      val roots = list_nat d_ids
      val steps = list_nat step_ids
      val shifted = list_nat shift_ids
      val labels = list_nat (#d_labels proofs)
      val compT = @{typ comma_frontier_m204_comparison}
      val rowT = @{typ comma_frontier_m204_row}
      val comp_builder = @{term "\<lambda>code right out. \<lparr>m204_code=code,m204_right=right,m204_output=out\<rparr>"}
      val row_builder = @{term "\<lambda>step out comparisons. \<lparr>m204_step_root=step,m204_result_root=out,m204_comparisons=comparisons\<rparr>"}
      fun comp_term ({label,right,result,...}: Proposal.comparison) =
        app comp_builder [nat label,nat right,nat result]
      val _ = if length (#comparisons candidate) = length (#comparisons proofs) then ()
        else error "M204 comparison proof transcript has the wrong length"
      val all_comparisons = #comparisons candidate ~~ #comparisons proofs
      fun insert_comparison (item as (row: Proposal.comparison,_)) table =
        let val key = (#cid row,#label row)
        in if Comparison_Table.defined table key then
             error "M204 comparison transcript repeats a class/label pair"
           else Comparison_Table.update (key,item) table end
      val comparison_index = fold insert_comparison all_comparisons Comparison_Table.empty
      fun entry cid droot (label,output) =
        (case Comparison_Table.lookup comparison_index (cid,label) of
          SOME (item as (row,_)) =>
            if #left row=droot andalso #result row=output then item
            else error "M204 comparison differs from its checked bind mapping"
        | NONE => error "M204 bind mapping lacks a checked comparison")
      (* Keep already-certified predicates opaque at higher assembly layers. *)
      val scalar_rules = @{thms Let_def list.simps list.size nth_Cons_0 nth_Cons_Suc nth_Cons'
        comma_frontier_m204_comparison.select_convs comma_frontier_m204_row.select_convs}
      fun simp_context rules facts =
        Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps (scalar_rules @ rules @ facts)
      fun proof label rules proposition facts =
        Utils.prove_exact ctxt label (tp (Envir.beta_norm proposition))
          (fn _ => simp_tac (simp_context rules facts) 1)
      fun comp_pred droot = @{term comma_frontier_m204_comparison_checked} $
        radices $ nodes $ shifted $ nat droot
      fun row_pred cid = @{term comma_frontier_m204_row_checked} $
        radices $ nodes $ roots $ shifted $ nat fallback $ nat cid
      fun row_at (cid,(step,f,mapping)) =
        let
          val _ = if step=List.nth (step_ids,cid) andalso f=fallback then ()
            else error "M204 bind transcript disagrees with its typed-step row"
          val droot = List.nth (d_ids,cid)
          val selected = map (entry cid droot) mapping
          val comp_terms = map (comp_term o #1) selected
          fun comp_proof (record as ({right,result,...}: Proposal.comparison),zip_theorem) =
            let
              val goal = comp_pred droot $ comp_term record
              val terminal_fact = if #plus9 record then [] else [Store.lookup store right]
              val bounds = map (Store.bound store) [droot,right,result]
            in proof "M204 structural comparison"
              @{thms comma_frontier_m204_comparison_checked_def} goal (zip_theorem :: (terminal_fact @ bounds)) end
          val facts = map comp_proof selected
          val checked = Utils.literal_list_all ctxt "M204 checked comparisons"
            (comp_pred droot) comp_terms facts
          val row = app row_builder [nat step,nat (List.nth (result_ids,cid)),
            HOLogic.mk_list compT comp_terms]
          val bind = List.nth (#bind_certificates proofs,cid)
          val row_facts = [checked,bind,Store.bound store droot,Store.bound store step,
            Store.bound store (List.nth (result_ids,cid)),
            Store.lookup store (List.nth (result_ids,cid))]
          val row_theorem = proof "M204 checked structural row"
            @{thms comma_frontier_m204_row_checked_def comma_frontier_m204_row_mapping_def}
            (row_pred cid $ row) row_facts
        in (row,row_theorem) end
      val rows_and_facts = map_index row_at keys
      val rows = HOLogic.mk_list rowT (map #1 rows_and_facts)
      val row_proofs = map #2 rows_and_facts
      val wf = Store.wellformed store
      val periodic = @{thm comma_frontier_radices_divide}
      (* Bound the 46 rows with one list_all proof over certified row facts;
         all unfolding below is of short structural vectors, not phase data. *)
      val indexed_builder = @{term "\<lambda>radices nodes roots steps shifted fallback labels rows i.
        roots!i<length (nodes::nat comma_crt_mdd_node list) \<and>
        steps!i<length nodes \<and>
        comma_crt_mdd_payload_cover nodes (roots!i) labels \<and>
        comma_crt_mdd_root_shift_certificate radices nodes 1 (roots!i) (shifted!i) \<and>
        m204_step_root (rows!i)=steps!i \<and>
        comma_frontier_m204_row_checked radices nodes roots shifted fallback i (rows!i)"}
      val indexed_predicate = app indexed_builder
        [radices,nodes,roots,steps,shifted,nat fallback,labels,rows]
      fun indexed_fact i =
        let val evidence = [List.nth (row_proofs,i),
              List.nth (#d_covers proofs,i),List.nth (#shifts proofs,i),
              Store.bound store (List.nth (d_ids,i)),
              Store.bound store (List.nth (step_ids,i))]
        in proof "M204 indexed structural row" [] (indexed_predicate $ nat i) evidence end
      val indices = 0 upto 45
      val indexed = Utils.literal_list_all ctxt "M204 46 checked rows" indexed_predicate
        (map nat indices) (map indexed_fact indices)
      val bulk = @{term comma_frontier_m204_bulk_checked} $ radices $ nodes $
        roots $ steps $ shifted $ nat fallback $ labels $ rows
      (* Convert the finite index range once, then compose the checked bulk
         conjuncts directly.  Do not simplify inside the indexed predicate. *)
      val upt = @{term "[0..<46::nat]"}
      val upt_eq = Simplifier.rewrite
        (Comma_Entry_Arithmetic.natural_context ctxt |> Simplifier.add_simps @{thms upt_rec})
        (Thm.cterm_of ctxt upt)
      val list_all = Const (@{const_name list_all},
        (natT --> @{typ bool}) --> HOLogic.listT natT --> @{typ bool})
      val lifted = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt (list_all $ indexed_predicate))) upt_eq
      val prop_conversion = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt
          (Const (@{const_name Trueprop},@{typ bool} --> @{typ prop})))) lifted
      val indexed_upt = Thm.equal_elim (Thm.symmetric prop_conversion) indexed
      val definition = Conv.rewr_conv (@{thm comma_frontier_m204_bulk_checked_def} RS @{thm eq_reflection})
        (Thm.cterm_of ctxt bulk)
      val expanded = Thm.term_of (Thm.rhs_of definition)
      val clauses = HOLogic.dest_conj expanded
      val _ = if length clauses=10 then () else error "M204 bulk conjunct shape changed"
      val periodic_clause = List.nth (clauses,1)
      val periodic_fact = Utils.prove_exact ctxt "M204 radix period bound" (tp periodic_clause)
        (fn context => resolve_tac context [@{thm allI}] 1 THEN
          resolve_tac context [@{thm impI}] 1 THEN
          resolve_tac context [periodic] 1 THEN assume_tac context 1)
      val exact_facts = [wf,periodic_fact,Store.bound store fallback,
        Store.lookup store fallback,indexed_upt]
      val scalar = simp_context @{thms list_all_Cons_iff list_all_Nil_iff} exact_facts
      fun clause (index,term) =
        if index=9 then Utils.exact_prop ctxt "M204 indexed bulk rows" (tp term) indexed_upt
        else (case List.find (fn theorem => Thm.prop_of theorem aconv tp term) exact_facts of
          SOME theorem => Utils.exact_prop ctxt "M204 bulk component" (tp term) theorem
        | NONE => Utils.prove_exact ctxt "M204 scalar bulk component" (tp term)
            (fn _ => simp_tac scalar 1))
      val pieces = map_index clause clauses
      val conjunction = fold_rev (fn fact => fn tail => @{thm conjI} OF [fact,tail])
        (take (length pieces-1) pieces) (List.last pieces)
      val proposition_definition = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt
          (Const (@{const_name Trueprop},@{typ bool} --> @{typ prop})))) definition
      val _ = Utils.exact_prop ctxt "M204 expanded bulk conjunction"
        (Thm.term_of (Thm.rhs_of proposition_definition)) conjunction
      val bulk_theorem = Thm.equal_elim (Thm.symmetric proposition_definition) conjunction
        |> Utils.exact_prop ctxt "M204 bulk structural certificate" (tp bulk)
      val bellman = @{thm comma_frontier_m204_bulk_checked_bellman} OF [bulk_theorem]
      val D = @{term comma_frontier_m204_mdd_value} $ radices $ nodes $ roots
      val action = @{term comma_frontier_m204_mdd_value} $ radices $ nodes $ steps
      val expected = tp (@{term comma_frontier_m204_code_bellman} $ D $ action)
      val bellman = Utils.exact_prop ctxt "M204 checked Bellman theorem" expected bellman
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 bulk Bellman publisher" [bulk_theorem,bellman]
    in {code_bellman=bellman,D=D,action=action} end
end
