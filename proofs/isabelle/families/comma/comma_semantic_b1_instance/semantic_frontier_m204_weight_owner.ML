(* Theory-scoped retention of the already-issued, checked M204 weight Store.
   The owner retains handles and kernel theorems; it issues no new action. *)
signature COMMA_FRONTIER_M204_WEIGHT_OWNER =
sig
  type publication =
    {store: Comma_CRT_MDD_Certificate_Store.store,
     arena: Comma_CRT_MDD_Arena.arena,
     roots: Comma_CRT_MDD_Arena.action_root list,
     weight: term, definition: thm, bellman: thm}
  val publish: Comma_CRT_MDD_Certificate_Store.store -> Comma_CRT_MDD_Arena.arena ->
    Comma_CRT_MDD_Arena.action_root list -> term -> thm -> thm ->
    local_theory -> local_theory
  val retrieve: Proof.context -> term -> publication
end

structure Comma_Frontier_M204_Weight_Owner:> COMMA_FRONTIER_M204_WEIGHT_OWNER =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Arena = Comma_CRT_MDD_Arena
  structure Utils = Comma_CRT_MDD_Proof_Utils
  type publication =
    {store: Store.store, arena: Arena.arena, roots: Arena.action_root list,
     weight: term, definition: thm, bellman: thm}
  type owned = {publication: publication, issuer: theory}
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n
  fun indices ({store,roots,...}: publication) = map (Store.action_index store) roots
  fun same ((left:owned),(right:owned)) =
    let
      val a = #publication left
      val b = #publication right
    in Context.eq_thy (#issuer left,#issuer right) andalso
      Store.table (#store a) aconv Store.table (#store b) andalso
      Store.radices (#store a) aconv Store.radices (#store b) andalso
      #weight a aconv #weight b andalso indices a = indices b andalso
      Thm.eq_thm (#definition a,#definition b) andalso Thm.eq_thm (#bellman a,#bellman b)
    end
  structure Data = Theory_Data
  (
    type T = owned option
    val empty = NONE
    fun merge (NONE,value) = value
      | merge (value,NONE) = value
      | merge (SOME left,SOME right) =
          if same (left,right) then SOME left
          else error "Conflicting M204 weight issuers cannot be merged"
  )

  fun validate ctxt expected_weight ({store,arena,roots,weight,definition,bellman}:publication) =
    let
      val issuer_context = Store.context store
      val _ = if Context.subthy (Proof_Context.theory_of issuer_context,
          Proof_Context.theory_of ctxt) then ()
        else error "M204 weight Store is foreign to the receiving theory"
      val ids = map (Store.action_index store) roots
      val arena_ids = map (Arena.action_index arena) roots
      val _ = if length ids = 46 andalso ids = arena_ids andalso
          Arena.radices arena = [3,4,7,11] andalso weight aconv expected_weight andalso
          Store.radices store aconv HOLogic.mk_list natT (map nat [3,4,7,11]) then ()
        else error "M204 weight roots, radix or consumer identity differ"
      val decoder = @{term comma_frontier_m204_mdd_value} $
        Store.radices store $ Store.table store $ HOLogic.mk_list natT (map nat ids)
      val _ = Utils.exact_prop ctxt "M204 issued weight definition"
        (Logic.mk_equals (weight,decoder)) definition
      val _ = Utils.exact_prop ctxt "M204 issued Bellman theorem"
        (HOLogic.mk_Trueprop (@{term comma_frontier_m204_bellman} $ weight)) bellman
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 retained weight authority" [definition,bellman]
    in () end

  fun publish store arena roots weight definition bellman lthy =
    let
      val ctxt = Local_Theory.target_of lthy
      val publication: publication =
        {store=store,arena=arena,roots=roots,weight=weight,definition=definition,
         bellman=bellman}
      val _ = validate ctxt weight publication
      val owned:owned = {publication=publication,issuer=Proof_Context.theory_of ctxt}
      fun install thy =
        (case Data.get thy of
          NONE => Data.put (SOME owned) thy
        | SOME prior => if same (prior,owned) then thy
            else error "M204 weight authority was already issued by another owner")
    in Local_Theory.background_theory install lthy end

  fun retrieve ctxt expected_weight =
    (case Data.get (Proof_Context.theory_of ctxt) of
      NONE => error "No M204 weight authority exists in the receiving theory"
    | SOME (owned:owned) =>
        let
          val _ = if Context.subthy (#issuer owned,Proof_Context.theory_of ctxt) then ()
            else error "M204 weight issuer is not an ancestor of the receiving theory"
          val publication = #publication owned
          val _ = validate ctxt expected_weight publication
        in publication end)
end
