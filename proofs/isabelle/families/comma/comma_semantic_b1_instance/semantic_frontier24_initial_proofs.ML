(* Kernel certificates for the initial bad-state MDD roots.  The five
   exceptional roots are proved as complements of one CRT point by walking
   their four ordered branch levels; phases are never enumerated. *)
signature COMMA_FRONTIER24_INITIAL_PROOFS =
sig
  type certificate = {cid: int, root: int, theorem: thm}
  val certify_initial:
    Proof.context -> Comma_CRT_MDD_Certificate_Store.store ->
    Comma_CRT_MDD_Arena.arena -> int list -> certificate list
end

structure Comma_Frontier24_Initial_Proofs:> COMMA_FRONTIER24_INITIAL_PROOFS =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Arena = Comma_CRT_MDD_Arena
  structure Utils = Comma_CRT_MDD_Proof_Utils

  type certificate = {cid: int, root: int, theorem: thm}

  val natT = @{typ nat}
  val boolT = HOLogic.boolT
  val natOptionT = Type (@{type_name option}, [natT])
  val natListT = HOLogic.listT natT
  val nodeT = @{typ "nat comma_crt_mdd_node"}
  val nodeListT = HOLogic.listT nodeT

  fun nat n = HOLogic.mk_number natT n
  fun some value = Const (@{const_name Some}, natT --> natOptionT) $ value
  fun mk_if typ condition yes no =
    Const (@{const_name If}, boolT --> typ --> typ --> typ) $
      condition $ yes $ no
  fun raw_eval_term store coordinate root =
    Const (@{const_name comma_crt_mdd_eval_raw},
      natListT --> nodeListT --> (natT --> natT) --> natT --> natOptionT) $
      Store.radices store $ Store.table store $ coordinate $ root
  fun raw_eval store coordinate root = raw_eval_term store coordinate (nat root)
  fun phase_eval store phase root =
    Const (@{const_name comma_crt_mdd_eval_phase},
      natListT --> nodeListT --> natT --> natT --> natOptionT) $
      Store.radices store $ Store.table store $ phase $ nat root
  fun nth_list items index =
    Const (@{const_name nth}, natListT --> natT --> natT) $
      HOLogic.mk_list natT (map nat items) $ index
  fun less left right = HOLogic.mk_binrel @{const_name less} (left,right)
  fun numeral_list xs = HOLogic.mk_list natT (map nat xs)

  fun arithmetic_context ctxt =
    Comma_Entry_Arithmetic.natural_context ctxt
    |> Simplifier.add_simps
      (@{thms list.simps list.size nth_Cons_0 nth_Cons_Suc nth_Cons'
        if_True if_False mod_simps comma_crt_mdd_node.simps})

  fun prove ctxt label proposition facts =
    let
      val expected = HOLogic.mk_Trueprop proposition
      val theorem = Goal.prove ctxt [] [] expected
        (fn {context,...} =>
          Method.insert_tac context facts 1 THEN
          Simplifier.asm_full_simp_tac (arithmetic_context context) 1 THEN
          TRY (auto_tac (arithmetic_context context)))
    in Utils.exact_prop ctxt label expected theorem end

  fun exact_open ctxt label expected theorem =
    if Thm.prop_of theorem aconv expected andalso Thm.nprems_of theorem=0 andalso
        null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
        Context.subthy (Thm.theory_of_thm theorem,Proof_Context.theory_of ctxt)
    then theorem else error (label ^ " is not the requested pointwise theorem")

  fun prove_raw_leaf ctxt store root payload =
    let
      val phase = Free ("phase",natT)
      val axis = Free ("frontier_axis", natT)
      val coordinate = Term.lambda axis phase
      val body = HOLogic.mk_Trueprop (HOLogic.mk_eq
        (raw_eval store coordinate root, some (nat payload)))
      val expected = Logic.all phase body
      val bound = Store.bound store root
      val lookup = Store.lookup store root RS @{thm meta_eq_to_obj_eq}
      val pointwise = Goal.prove ctxt [] [] body
        (fn {context,...} =>
          resolve_tac context [@{thm comma_crt_mdd_eval_raw_leaf}] 1 THEN
          resolve_tac context [bound] 1 THEN
          resolve_tac context [lookup] 1)
      val pointwise = exact_open ctxt "Initial frontier pointwise leaf evaluation" body pointwise
      val theorem = Thm.forall_intr (Thm.cterm_of ctxt phase) pointwise
    in Utils.exact_prop ctxt "Initial frontier MDD leaf evaluation" expected theorem end

  fun raw_true_all ctxt store true_root =
    prove_raw_leaf ctxt store true_root 1

  fun off_path_fact ctxt store phase true_eval true_root axis selected radix children =
    let
      val slot = Free ("frontier_slot",natT)
      val children_term = numeral_list children
      val phase_in_predicate = Free ("frontier_predicate_phase",natT)
      val phase_coordinate = Term.lambda (Free ("frontier_axis",natT)) phase_in_predicate
      val proposition_at = fn slot_term =>
        HOLogic.mk_all ("frontier_predicate_phase",natT,
          HOLogic.mk_imp
            (HOLogic.mk_not (HOLogic.mk_eq (slot_term,nat selected)),
             HOLogic.mk_eq
               (raw_eval_term store phase_coordinate (nth_list children slot_term),
                some (nat 1))))
      val predicate = Term.lambda slot (proposition_at slot)
      val successor_cache = Comma_Selected_List_Conversion.make_successor_cache ctxt radix
      val reduction_context = arithmetic_context ctxt
      fun prove_item index =
        let
          val index_term = nat index
          val child = List.nth (children,index)
          val _ = if index=selected orelse child=true_root then ()
            else error "Initial off-path MDD child is not the certified true root"
          val normalized_expected = HOLogic.mk_Trueprop (proposition_at index_term)
          val normalized = Goal.prove ctxt [] [] normalized_expected
            (fn {context,...} =>
              resolve_tac context [@{thm allI}] 1 THEN
              resolve_tac context [@{thm impI}] 1 THEN
              Simplifier.asm_full_simp_tac
                (reduction_context |> Simplifier.add_simps [true_eval]) 1)
          val normalized = exact_open ctxt "Initial off-path concrete item"
            normalized_expected normalized
        in Utils.predicate_application ctxt "Initial off-path predicate item"
          predicate index_term normalized end
      val all = Comma_Selected_List_Conversion.prove_indexed_list_all
        {ctxt=ctxt,predicate=predicate,bound=radix,prove_item=prove_item,
         zero_fact = @{thm comma_indexed_all_zero},
         step_fact = @{thm comma_indexed_all_Suc},
         successor_equation= #equation successor_cache}
      val selected_rule =
        ((@{thm comma_crt_mdd_indexed_allD} OF [all]) RS @{thm spec}) RS @{thm mp}
      val body = Logic.mk_implies
        (HOLogic.mk_Trueprop (less slot
          (Const (@{const_name size},natListT --> natT) $ children_term)),
         Logic.mk_implies
           (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (slot,nat selected))),
            HOLogic.mk_Trueprop (HOLogic.mk_eq
              (raw_eval_term store
                (Term.lambda (Free ("frontier_axis",natT)) phase)
                (nth_list children slot),some (nat 1)))))
      val pointwise_proposition = Logic.all slot body
      val width_prop = HOLogic.mk_eq
        (Const (@{const_name size},natListT --> natT) $ children_term,nat radix)
      val width = prove ctxt "Initial branch width" width_prop []
      val pointwise = Goal.prove_internal ctxt []
        (Thm.cterm_of ctxt pointwise_proposition)
        (fn _ =>
          resolve_tac ctxt [selected_rule] 1 THEN
          asm_full_simp_tac
            (arithmetic_context ctxt |> Simplifier.add_simps [width]) 1 THEN
          assume_tac ctxt 1)
      val pointwise = exact_open ctxt "Initial indexed off-path leaf facts"
        pointwise_proposition pointwise
      val theorem = Thm.forall_intr (Thm.cterm_of ctxt phase) pointwise
      val proposition = Logic.all phase pointwise_proposition
    in Utils.exact_prop ctxt ("Initial frontier off-path leaf facts at axis " ^
      Int.toString axis) proposition theorem end

  fun prove_complement ctxt store true_root false_root true_eval point root =
    let
      val phase = Free ("phase",natT)
      val coordinate = Term.lambda (Free ("frontier_axis",natT)) phase
      val radices = map (Utils.dest_nat "Initial frontier radix" natT)
        (HOLogic.dest_list (Store.radices store))
      val _ = if radices = [3,4,11,7] then ()
        else error "Initial frontier proof expects CRT radices [3,4,11,7]"
      val wellformed = Store.wellformed store
      val phase_match = fn axis => HOLogic.mk_eq
        (HOLogic.mk_binop @{const_name modulo} (phase,nat (List.nth (radices,axis))),
         nat (point mod List.nth (radices,axis)))
      fun matches [] = @{term True}
        | matches (axis::rest) = HOLogic.mk_conj (phase_match axis,matches rest)

      fun walk [] node =
            (case Store.node store node of
              Store.Leaf 0 =>
                if node = false_root then
                  (prove_raw_leaf ctxt store node 0, @{term True})
                else error "Initial exception path ended at a noncanonical False leaf"
            | _ => error "Initial exception path does not terminate at False")
        | walk (axis::rest) node =
            (case Store.node store node of
              Store.Branch (actual_axis,children) =>
                let
                  val _ = if actual_axis=axis then ()
                    else error "Initial exception branch axes are not ordered"
                  val radix = List.nth (radices,axis)
                  val selected = point mod radix
                  val _ = if length children=radix then ()
                    else error "Initial exception branch has the wrong radix width"
                  val child = List.nth (children,selected)
                  val _ = List.app (fn (slot,child_id) =>
                    if slot=selected then ()
                    else if child_id=true_root then ()
                    else error "Initial exception branch has a non-true off-path child")
                    (map_index I children)
                  val (child_theorem,tail_match) = walk rest child
                  val children_term = numeral_list children
                  val selected_term = nat selected
                  val branch_term = Store.node_term (Store.node store node)
                  val node_lookup = Store.lookup store node RS @{thm meta_eq_to_obj_eq}
                  val branch_expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
                    (Const (@{const_name nth},nodeListT --> natT --> nodeT) $
                       Store.table store $ nat node,
                     branch_term))
                  val branch_lookup = Utils.exact_prop ctxt
                    "Initial exception branch lookup" branch_expected node_lookup
                  val axis_radix = nth_list
                    (map (Utils.dest_nat "Initial frontier radix" natT)
                      (HOLogic.dest_list (Store.radices store))) (nat axis)
                  val selected_bound = prove ctxt "Initial exception selected slot bound"
                    (less selected_term axis_radix) []
                  val special = prove ctxt "Initial exception selected child equation"
                    (HOLogic.mk_eq (nat child,nth_list children selected_term)) []
                  val off_path_all = off_path_fact ctxt store phase true_eval true_root
                    axis selected radix children
                  val off_path = Thm.forall_elim
                    (Thm.cterm_of ctxt phase) off_path_all
                  val branch_rule = @{thm comma_crt_mdd_eval_raw_branch_except} OF
                    [wellformed,Store.bound store node,branch_lookup,selected_bound,
                     special,off_path]
                  val head_match = phase_match axis
                  val branch_formula = HOLogic.mk_eq
                    (raw_eval store coordinate node,
                     mk_if natOptionT head_match
                       (raw_eval store coordinate child) (some (nat 1)))
                  val branch_equation = Goal.prove ctxt [] []
                    (HOLogic.mk_Trueprop branch_formula)
                    (fn {context,...} => resolve_tac context [branch_rule] 1)
                  val branch_equation = exact_open ctxt
                    "Initial exception branch reduction"
                    (HOLogic.mk_Trueprop branch_formula) branch_equation
                  val full_match = HOLogic.mk_conj (head_match,tail_match)
                  val value = mk_if natT full_match (nat 0) (nat 1)
                  val body = HOLogic.mk_eq (raw_eval store coordinate node,some value)
                  val child_at_phase = Thm.forall_elim
                    (Thm.cterm_of ctxt phase) child_theorem
                  val pointwise = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop body)
                    (fn {context,...} =>
                      Method.insert_tac context [branch_equation,child_at_phase] 1 THEN
                      auto_tac (arithmetic_context context))
                  val pointwise = exact_open ctxt
                    "Initial exception recursive branch evaluation"
                    (HOLogic.mk_Trueprop body) pointwise
                  val theorem = Thm.forall_intr (Thm.cterm_of ctxt phase) pointwise
                  val proposition = Logic.all phase (HOLogic.mk_Trueprop body)
                  val theorem = Utils.exact_prop ctxt
                    "Initial exception branch phase evaluation" proposition theorem
                in (theorem,full_match) end
            | _ => error "Initial exception path is missing a branch")

      val (raw_theorem,axis_match) = walk [0,1,2,3] root
      val _ = if axis_match aconv matches [0,1,2,3] then ()
        else error "Initial exception proof assembled another CRT point"
      val point_bound = prove ctxt "Initial exception phase point bound"
        (less (nat point) (nat 924)) []
      val point_iff = @{thm comma_crt_phase_point_iff_axis_residues}
        OF [point_bound]
      val phase_eval = phase_eval store phase root
      val wanted = HOLogic.mk_eq
        (phase_eval,some (mk_if natT
          (HOLogic.mk_eq
            (HOLogic.mk_binop @{const_name modulo} (phase,nat 924),nat point))
          (nat 0) (nat 1)))
      val body = HOLogic.mk_Trueprop wanted
      val pointwise = Goal.prove ctxt [] [] body
        (fn {context,...} =>
          Method.insert_tac context [Store.wellformed store,
            Thm.forall_elim (Thm.cterm_of ctxt phase) raw_theorem,point_iff] 1 THEN
          simp_tac (arithmetic_context context
            |> Simplifier.add_simps [@{thm comma_crt_mdd_eval_phase_def},
                 @{thm comma_crt_mdd_eval_def}]) 1 THEN
          TRY (auto_tac (arithmetic_context context)))
      val pointwise = exact_open ctxt
        "Initial exception CRT point evaluation" body pointwise
      val proposition = Logic.all phase body
      val theorem = Thm.forall_intr (Thm.cterm_of ctxt phase) pointwise
    in Utils.exact_prop ctxt "Initial exception phase evaluation" proposition theorem end

  fun certify_initial ctxt store arena roots =
    let
      val _ = if length roots=46 then ()
        else error "Initial frontier needs exactly 46 class roots"
      val true_id = Store.boolean_index store (Arena.boolean_true arena)
      val false_id = Store.boolean_index store (Arena.boolean_false arena)
      val true_raw = raw_true_all ctxt store true_id
      val phase = Free ("phase",natT)
      val true_at_phase = Thm.forall_elim (Thm.cterm_of ctxt phase) true_raw
      val true_body = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (phase_eval store phase true_id,some (nat 1)))
      val true_pointwise = Goal.prove ctxt [] [] true_body
        (fn {context,...} =>
          Method.insert_tac context [Store.wellformed store,true_at_phase] 1 THEN
          simp_tac (arithmetic_context context
            |> Simplifier.add_simps [@{thm comma_crt_mdd_eval_phase_def},
                 @{thm comma_crt_mdd_eval_def}]) 1)
      val true_pointwise = exact_open ctxt "Initial shared true-leaf evaluation"
        true_body true_pointwise
      val true_phase_eval = Thm.forall_intr (Thm.cterm_of ctxt phase) true_pointwise
      val true_phase_eval = Utils.exact_prop ctxt "Initial shared true-root phase evaluation"
        (Logic.all phase true_body) true_phase_eval
      val exceptions = Inttab.make [(33,299),(10,66),(12,298),(32,67),(1,68)]
      fun one (cid,root) =
        let
          val _ = ignore (Store.bound store root)
          val theorem = (case Inttab.lookup exceptions cid of
            SOME point =>
              let
                val _ = if root <> true_id andalso root <> false_id then ()
                  else error "Initial exceptional state collapsed to a constant root"
              in prove_complement ctxt store true_id false_id true_raw point root end
          | NONE =>
              if root = true_id then true_phase_eval
              else error "Nonexceptional initial state is not the canonical true leaf")
        in {cid=cid,root=root,theorem=theorem}: certificate end
    in map_index (fn (cid,root) => one (cid,root)) roots end
end
