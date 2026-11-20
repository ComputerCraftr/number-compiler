(* Single-Store candidate publication with request-local preparation. *)
structure Comma_M204_Direct_Candidate_Publication =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Data = Comma_Frontier_M204_Candidate_Data
  fun publish prepare certify lthy =
  let
    val arena = Arena.create Data.radices
    val _ = Comma_Proof_Profile.report "Direct Bellman candidate seed start"
    val nodes = Vector.fromList (Arena.seed_prefix arena (Data.seeds ()))
    val _ = Comma_Proof_Profile.report "Direct Bellman candidate seed complete"
    val _ = if Vector.length nodes = 4804 andalso length Data.roots = 46 then ()
      else error "Direct Bellman candidate has an unexpected extent"
    val roots = map (fn index =>
      let val root = Vector.sub (nodes,index)
          val _ = if Arena.action_index arena root = index then ()
            else error "Direct Bellman candidate root changed during import"
      in root end) Data.roots
    val _ = Comma_Proof_Profile.report "Direct Bellman candidate prepare start"
    val (prepared,lthy0) = prepare {arena=arena,roots=roots} lthy
    val _ = Comma_Proof_Profile.report "Direct Bellman candidate prepare complete"
    val _ = Comma_Proof_Profile.report "Direct Bellman Store freeze start"
    val (store,lthy1) = Store.make "comma_m204_direct_nodes" arena lthy0
    val _ = Comma_Proof_Profile.report "Direct Bellman Store freeze complete"
    val root_terms = HOLogic.mk_list @{typ nat}
      (map (HOLogic.mk_number @{typ nat} o Store.action_index store) roots)
    val ((local_roots,(_,local_roots_definition)),lthy2) = Local_Theory.define
      ((Binding.name "comma_m204_direct_roots",NoSyn),
       ((Binding.name "comma_m204_direct_roots_def",[]),root_terms)) lthy1
    val roots_morphism = Local_Theory.target_morphism lthy2
    val roots_term = Morphism.term roots_morphism local_roots
    val roots_definition = Morphism.thm roots_morphism local_roots_definition
    val d_rhs = @{term comma_frontier_m204_mdd_value} $
      Store.radices store $ Store.table store $ roots_term
    val ((local_D,(_,local_D_definition)),lthy3) = Local_Theory.define
      ((Binding.name "comma_m204_direct_D",NoSyn),
       ((Binding.name "comma_m204_direct_D_def",[]),d_rhs)) lthy2
    val d_morphism = Local_Theory.target_morphism lthy3
    val D = Morphism.term d_morphism local_D
    val D_definition = Morphism.thm d_morphism local_D_definition
    val (_,lthy4) = Local_Theory.note
      ((Binding.name "comma_m204_direct_nodes_wellformed_native",[]),
       [Store.wellformed store]) lthy3
    val (_,lthy5) = Local_Theory.note
      ((Binding.name "comma_m204_direct_root_bounds_native",[]),
       map (Store.bound store o Store.action_index store) roots) lthy4
  in certify {arena=arena,store=store,roots=roots,roots_term=roots_term,
      roots_definition=roots_definition,D=D,D_definition=D_definition,prepared=prepared} lthy5 end
end
