(* Context-owned authority for concrete split B32 root diagrams.  Control
   geometry and terminal weights stay separate; point queries do not rebuild
   return rows or replay the powered fold. *)
signature COMMA_SEMANTIC_B1_B32_PROJECTION =
sig
  type root_action =
    {root: int, action: term, equation: thm, stop_weights: thm}
  type projection = {query: thm, semantic_value: thm, stop_value: term}
  type projector = int -> int -> projection
  val publish: root_action list -> theory -> theory
  val publish_local: root_action list -> local_theory -> local_theory
  val lookup: Proof.context -> int -> root_action
  val make_projector: Proof.context -> projector
  val action_constructor_normal: Proof.context -> term -> bool
end

structure Comma_Semantic_B1_B32_Projection: COMMA_SEMANTIC_B1_B32_PROJECTION =
struct
  type root_action =
    {root: int, action: term, equation: thm, stop_weights: thm}
  type projection = {query: thm, semantic_value: thm, stop_value: term}
  type projector = int -> int -> projection

  fun same_theorem left right = Thm.prop_of left aconv Thm.prop_of right

  fun same_root_action (left: root_action, right: root_action) =
    #root left = #root right andalso #action left aconv #action right andalso
    same_theorem (#equation left) (#equation right) andalso
    same_theorem (#stop_weights left) (#stop_weights right)

  structure Data = Theory_Data
  (
    type T = root_action Inttab.table
    val empty = Inttab.empty
    fun merge (left, right) = Inttab.merge same_root_action (left, right)
  )

  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n

  fun equation_request root =
    @{term comma_semantic_b1_crt_power_split_action} $ nat 5 $ nat root

  fun stop_weights_claim action = HOLogic.mk_Trueprop
    (@{term comma_crt_mdd_stop_weights_bounded242} $
      (@{term comma_crt_split_weight} $ action))

  fun standalone theorem =
    Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
      null (Thm.tpairs_of theorem)

  fun natural_numeral term =
    (case try HOLogic.dest_number term of
      SOME (typ, value) => if typ = natT andalso value >= 0 then SOME value else NONE
    | NONE => NONE)

  fun mdd_constructor_normal_from lower_level leaf term =
    (case strip_comb term of
      (Const (name, _), [payload])
        => name = @{const_name Comma_CRT_MDD_Leaf} andalso leaf payload
    | (Const (name, _), [level_term, children_term])
        => if name = @{const_name Comma_CRT_MDD_Node} then
          (case natural_numeral level_term of
            SOME level =>
              let
                val periods = [4, 3, 7, 11]
                val children = try HOLogic.dest_list children_term
              in lower_level <= level andalso level < length periods andalso
                 Option.map length children = SOME (nth periods level) andalso
                 (case children of SOME values =>
                    List.all (mdd_constructor_normal_from (level + 1) leaf) values
                  | NONE => false)
              end
          | NONE => false)
          else false
    | _ => false)

  fun mdd_constructor_normal leaf term =
    mdd_constructor_normal_from 0 leaf term

  fun control_leaf term =
    (case strip_comb term of
      (Const (name, _), [root]) =>
        name = @{const_name Comma_CRT_Control_Live} andalso
          (case natural_numeral root of SOME value => value < 46 | NONE => false)
    | (Const (name, _), []) => name = @{const_name Comma_CRT_Control_Stop} orelse
        name = @{const_name Comma_CRT_Control_Invalid}
    | _ => false)

  fun weight_leaf term =
    (case strip_comb term of
      (Const (name, _), []) => name = @{const_name None}
    | (Const (name, _), [weight]) => name = @{const_name Some} andalso
        Option.isSome (natural_numeral weight)
    | _ => false)

  fun action_constructor_normal ctxt action =
    let
      val actionT = @{typ comma_crt_split_action}
      val controlT = @{typ comma_crt_control_mdd}
      val weightT = @{typ comma_crt_weight_mdd}
      val selector_context = put_simpset HOL_basic_ss ctxt addsimps
        @{thms comma_crt_split_action.select_convs}
      fun select name resultT =
        let
          val selector = Const (name, actionT --> resultT) $ action
          val equation = Simplifier.rewrite selector_context
            (Thm.cterm_of ctxt selector)
        in Thm.term_of (Thm.rhs_of equation) end
      val controls = select @{const_name comma_crt_split_control} controlT
      val weights = select @{const_name comma_crt_split_weight} weightT
    in mdd_constructor_normal control_leaf controls andalso
       mdd_constructor_normal weight_leaf weights end

  (* A local shape fixture pins both sides of the level-order boundary.  The
     outer level-0 node may contain level-1 children, but a repeated level-0
     child is malformed even when both nodes have their individually correct
     CRT widths. *)
  val _ =
    let
      val leaf = @{term "Comma_CRT_MDD_Leaf Comma_CRT_Control_Invalid"}
      val control_mddT = fastype_of leaf
      val listT = Type (@{type_name list}, [control_mddT])
      val node = Const (@{const_name Comma_CRT_MDD_Node},
        natT --> listT --> control_mddT)
      val zero = nat 0
      val one = nat 1
      val good_child = node $ one $ HOLogic.mk_list control_mddT [leaf, leaf, leaf]
      val good = node $ zero $ HOLogic.mk_list control_mddT
        [good_child, good_child, good_child, good_child]
      val bad_child = node $ zero $ HOLogic.mk_list control_mddT
        [leaf, leaf, leaf, leaf]
      val bad = node $ zero $ HOLogic.mk_list control_mddT
        [bad_child, leaf, leaf, leaf]
    in
      if mdd_constructor_normal control_leaf good andalso
          not (mdd_constructor_normal control_leaf bad) then ()
      else error "B32 MDD shape checker level-order regression"
    end

  fun validate_entry ctxt (entry: root_action) =
    let
      val root = #root entry
      val action = #action entry
      val equation = #equation entry
      val stop_weights = #stop_weights entry
    in
      if root < 0 orelse root >= 46 then
        error "B32 projection root index is outside the published boundary"
      else if not (Comma_Selected_List_Conversion.closed action) then
        error "B32 projection split action is not closed"
      else if fastype_of action <> @{typ comma_crt_split_action} then
        error "B32 projection action has the wrong type"
      else if not (action_constructor_normal ctxt action) then
        error "B32 projection action is not a constructor-normal split MDD"
      else if not (Thm.term_of (Thm.lhs_of equation) aconv equation_request root andalso
          Thm.term_of (Thm.rhs_of equation) aconv action andalso standalone equation)
      then error "B32 projection action equation does not bind its root and action"
      else if not (Thm.prop_of stop_weights aconv stop_weights_claim action andalso
          standalone stop_weights)
      then error "B32 Stop-weight theorem does not certify its root action"
      else ()
    end

  fun transfer_entry thy (entry: root_action) : root_action =
    {root = #root entry,
     action = #action entry,
     equation = Thm.transfer thy (#equation entry),
     stop_weights = Thm.transfer thy (#stop_weights entry)}

  fun publish entries thy =
    let
      val ctxt = Proof_Context.init_global thy
      val transferred = map (transfer_entry thy) entries
      val _ = List.app (validate_entry ctxt) transferred
      val roots = map #root transferred
      val expected = 0 upto 45
      val _ = if sort int_ord roots = expected andalso length roots = length expected
        then () else error "B32 split publication must contain roots 0 through 45 once"
      val table = fold (fn entry => Inttab.update (#root entry, entry))
        transferred Inttab.empty
      val _ = if Inttab.size table = 46 then ()
        else error "B32 split publication contains duplicate root indices"
    in Data.put table thy end

  fun publish_local entries = Local_Theory.background_theory (publish entries)

  fun lookup ctxt root =
    if root < 0 orelse root >= 46 then
      error "B32 projection root index is outside the published boundary"
    else
      (case Inttab.lookup (Data.get (Proof_Context.theory_of ctxt)) root of
        SOME entry =>
          if #root entry = root then entry
          else error "B32 projection context entry has a mismatched root index"
      | NONE => error "B32 root split action is not published in this theory")

  fun bound ctxt value upper =
    let
      val proposition = HOLogic.mk_Trueprop
        (@{term "less :: nat => nat => bool"} $ nat value $ nat upper)
    in Goal.prove ctxt [] [] proposition
      (fn {context, ...} => simp_tac
        (Comma_Entry_Arithmetic.natural_context context) 1)
    end

  fun stop_weight result =
    (case strip_comb result of
      (Const (constructor, _), [weight]) =>
        if constructor <> @{const_name Comma_Semantic_B1_Stop} then
          error "B32 phase projection did not select a Stop label"
        else
          (case try HOLogic.dest_number weight of
            SOME (typ, value) =>
              if typ = natT andalso value >= 0 andalso value <= 242 then weight
              else error "B32 phase projection selected an invalid Stop weight"
          | NONE => error "B32 phase projection Stop weight is not a numeral")
    | _ => error "B32 phase projection result is not a constructor")

  fun make_projector ctxt =
    let
      val result_conversion = Code_Simp.static_conv
        {ctxt = ctxt, simpset = SOME (Simplifier.simpset_of ctxt),
         consts = [@{const_name comma_crt_split_mdd_result_at}]}
      fun normalize request = result_conversion ctxt (Thm.cterm_of ctxt request)
      val memo = Unsynchronized.ref (Termtab.empty: projection Termtab.table)
      val memo_capacity = 8192

      fun project root phase =
        if root < 0 orelse root >= 46 then
          error "B32 projection root index is outside the published boundary"
        else if phase < 0 orelse phase >= 924 then
          error "B32 projection phase is outside the published clock"
        else
          let val key = HOLogic.mk_prod (nat root, nat phase)
          in
            (case Termtab.lookup (!memo) key of
              SOME value => value
            | NONE =>
              let
                val entry = lookup ctxt root
                val root_bound = bound ctxt root 46
                val phase_bound = bound ctxt phase 924
                val result_request = @{term comma_crt_split_mdd_result_at} $
                  nat phase $
                  (@{term comma_crt_split_control} $ #action entry) $
                  (@{term comma_crt_split_weight} $ #action entry)
                val result_equation = normalize result_request
                val _ = if Thm.term_of (Thm.lhs_of result_equation) aconv result_request andalso
                    Comma_Selected_List_Conversion.closed
                      (Thm.term_of (Thm.rhs_of result_equation)) andalso
                    standalone result_equation
                  then () else error "B32 split phase conversion returned an invalid equation"
                val selected = Thm.term_of (Thm.rhs_of result_equation)
                val stop_value =
                  (case strip_comb selected of
                    (Const (some, _), [value]) =>
                      if some = @{const_name Some} then value
                      else error "B32 split phase result is not Some Stop"
                  | _ => error "B32 split phase result is not an option constructor")
                val _ = stop_weight stop_value
                val depth_rule = Drule.infer_instantiate ctxt
                  [( ("k", 0), Thm.cterm_of ctxt (nat 5))]
                  @{thm comma_semantic_b1_crt_power_split_action_exact}
                val exact_rule = depth_rule OF [root_bound, phase_bound]
                val result_exact = Simplifier.rewrite_rule ctxt [#equation entry] exact_rule
                val semantic_option = Thm.transitive
                  (Thm.symmetric (mk_meta_eq result_exact)) result_equation
                val semantic_option_object = semantic_option RS @{thm meta_eq_to_obj_eq}
                val option_inject = @{thm option.inject} RS @{thm iffD1}
                val semantic_goal = HOLogic.mk_Trueprop (HOLogic.mk_eq
                  (@{term comma_semantic_b1_of_word} $
                    (@{term comma_orbit_word} $ nat 5 $ nat phase $ nat root), stop_value))
                val semantic_value = Goal.prove ctxt [] [] semantic_goal
                  (fn {context, ...} =>
                    resolve_tac context [option_inject] 1 THEN
                    resolve_tac context [semantic_option_object] 1)
                val optionT = @{typ "comma_semantic_b1_result option"}
                val some = Const (@{const_name Some},
                  @{typ comma_semantic_b1_result} --> optionT)
                val power_query = @{term comma_semantic_b1_crt_power_result} $
                  nat 5 $ nat root $ nat phase
                val query_goal = HOLogic.mk_Trueprop (HOLogic.mk_eq
                  (power_query, some $ stop_value))
                val query = Goal.prove ctxt [] [] query_goal
                  (fn {context, ...} => simp_tac
                    (put_simpset HOL_basic_ss context addsimps
                      [@{thm comma_semantic_b1_crt_power_result_def},
                       #equation entry, result_equation, root_bound, phase_bound]) 1)
                val _ = if standalone query andalso standalone semantic_value then ()
                  else error "B32 split phase projection theorem has unresolved assumptions"
                val value = {query = query, semantic_value = semantic_value,
                  stop_value = stop_value}: projection
                val _ = if Termtab.size (!memo) < memo_capacity then
                  memo := Termtab.update (key, value) (!memo) else ()
              in value end)
          end
    in project end
end
