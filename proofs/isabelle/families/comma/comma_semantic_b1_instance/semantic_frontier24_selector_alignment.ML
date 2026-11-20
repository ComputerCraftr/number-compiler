(* Structural assembly of authenticated selector constructors. No arithmetic
   evaluator participates here: exact head propositions and literal order are
   checked before the generic list induction is instantiated. *)
structure Comma_Frontier24_Selector_Alignment =
struct
  structure Utils = Comma_CRT_MDD_Proof_Utils

  val programT = @{typ comma_semantic_port_program}
  val selectorT = @{typ comma_frontier24_selector_recipe}
  val actionT = @{typ comma_source_continuation_action}
  val bundleT = @{typ comma_frontier24_parametric_bundle}

  fun projection ctxt bundle projections name elementT =
    let
      val request = Const (name,bundleT --> HOLogic.listT elementT) $ bundle
      val equation = (case AList.lookup (op =) projections name of
          SOME theorem => theorem | NONE => error "Selector field projection is missing")
      val value = Thm.term_of (Thm.rhs_of equation)
      val _ = Utils.exact_prop ctxt "Selector field projection"
        (Logic.mk_equals (request,value)) equation
    in (value,equation) end

  fun fields ctxt bundle projections =
    let
      val _ = if fastype_of bundle = bundleT andalso Utils.closed bundle then ()
        else error "Selector alignment requires a closed typed bundle"
      val (programs, program_equation) = projection ctxt bundle projections
        @{const_name cf24_programs} programT
      val (selectors, selector_equation) = projection ctxt bundle projections
        @{const_name cf24_selectors} selectorT
      val (actions, action_equation) = projection ctxt bundle projections
        @{const_name cf24_action_tokens} actionT
      val program_items = HOLogic.dest_list programs
      val selector_items = HOLogic.dest_list selectors
      val _ = if length program_items = length selector_items then ()
        else error "Selector alignment has unequal program and recipe extents"
    in {programs=program_items, selectors=selector_items, actions=actions,
      equations=[program_equation,selector_equation,action_equation]} end

  fun rows ctxt bundle projections =
    let val {programs,selectors,actions,...} = fields ctxt bundle projections
    in {programs=programs,selectors=selectors,actions=actions} end

  fun certify ctxt bundle projections facts =
    let
      val {programs,selectors,actions,equations} = fields ctxt bundle projections
      val _ = if length facts = length programs then ()
        else error "Selector alignment has missing or excess constructor proofs"
      val predicate = @{term comma_frontier24_selector_recipe_matches}
      fun check ((program,selector),fact) =
        Utils.exact_prop ctxt "Selector constructor binding"
          (HOLogic.mk_Trueprop (predicate $ program $ selector $ actions)) fact
      val checked = map check ((programs ~~ selectors) ~~ facts)
      val empty = Drule.infer_instantiate ctxt
        [(("actions",0),Thm.cterm_of ctxt actions)]
        @{thm comma_frontier24_selector_rows_nil}
      val paired = fold_rev (fn head => fn tail =>
        @{thm comma_frontier24_selector_rows_cons} OF [head,tail]) checked empty
      val intro = Drule.infer_instantiate ctxt
        [(("bundle",0),Thm.cterm_of ctxt bundle)]
        @{thm comma_frontier24_selector_rows_intro}
      val literal_intro = Simplifier.rewrite_rule
        (put_simpset HOL_basic_ss ctxt) equations intro
      val theorem = literal_intro OF [paired]
      val expected = HOLogic.mk_Trueprop
        (@{term comma_frontier24_selector_rows_checked} $ bundle)
    in Utils.exact_prop ctxt "Selector constructor alignment" expected theorem end
  (* Production consumes exact indexed selections from the named owners;
     proposed rows alone are never used as selector authority. *)
  fun certify_indexed ctxt bundle projections programs
      (program_owner: Comma_Frontier24_Parametric_Runtime.named_table)
      (selector_owner: Comma_Frontier24_Parametric_Runtime.named_table)
      (program_plan: Comma_Frontier24_Selected_Table_Plan.plan)
      (selector_plan: Comma_Frontier24_Selected_Table_Plan.plan) facts =
    let
      val selectors = #rows selector_owner
      val count = length programs
      val _ = if count > 0 andalso length selectors=count andalso length facts=count then ()
        else error "Indexed selector alignment has unequal extents"
      val (program_table,program_projection) = projection ctxt bundle projections
        @{const_name cf24_programs} programT
      val (selector_table,selector_projection) = projection ctxt bundle projections
        @{const_name cf24_selectors} selectorT
      val (actions,action_projection) = projection ctxt bundle projections
        @{const_name cf24_action_tokens} actionT
      val _ = if program_table aconv #table program_owner andalso
          ListPair.allEq (op aconv) (programs,#rows program_owner) then ()
        else error "Indexed program owner differs from the bundle program field or proposals"
      val _ = if selector_table aconv #table selector_owner then ()
        else error "Indexed selector owner differs from the bundle selector field"
      val program_field = Thm.term_of (Thm.lhs_of program_projection)
      val selector_field = Thm.term_of (Thm.lhs_of selector_projection)
      val action_field = Thm.term_of (Thm.lhs_of action_projection)
      val natT = @{typ nat}
      fun nat n = HOLogic.mk_number natT n
      fun nth table elementT index = Const (@{const_name nth},
        HOLogic.listT elementT --> natT --> elementT) $ table $ index
      fun size table = Const (@{const_name size},fastype_of table --> natT) $ table
      val program_size_goal = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (size program_field,nat count))
      val program_length_const = Const (@{const_name size},fastype_of program_field --> natT)
      val program_length_projection = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt program_length_const)) program_projection
      val program_size = (Thm.transitive program_length_projection
        (#size program_owner RS @{thm eq_reflection}) RS @{thm meta_eq_to_obj_eq})
        |> Utils.exact_prop ctxt "Program selector extent" program_size_goal
      val selector_size_goal = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (size selector_field,nat count))
      val selector_length_const = Const (@{const_name size},fastype_of selector_field --> natT)
      val selector_length_projection = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt selector_length_const)) selector_projection
      val selector_size = (Thm.transitive selector_length_projection
        (#size selector_owner RS @{thm eq_reflection}) RS @{thm meta_eq_to_obj_eq})
        |> Utils.exact_prop ctxt "Named selector extent" selector_size_goal
      val extent = @{thm trans} OF [program_size,@{thm sym} OF [selector_size]]
      val predicate = @{term comma_frontier24_selector_recipe_matches}
      val trueprop = Const (@{const_name Trueprop},@{typ bool} --> @{typ prop})
      fun selected (i,((program,selector),fact)) =
        let
          val request = HOLogic.mk_Trueprop (predicate $ program $ selector $ actions)
          val checked = Utils.exact_prop ctxt "Indexed selector constructor" request fact
          val program_eq = #lookup program_plan i
          val selector_eq = #lookup selector_plan i
          val _ = Utils.exact_prop ctxt "Indexed program selection"
            (Logic.mk_equals (nth program_field programT (nat i),program)) program_eq
          val _ = Utils.exact_prop ctxt "Indexed selector selection"
            (Logic.mk_equals (nth selector_field selectorT (nat i),selector)) selector_eq
          val head = Thm.reflexive (Thm.cterm_of ctxt predicate)
          val equal = fold (fn equation => fn function => Thm.combination function equation)
            [program_eq,selector_eq,action_projection] head
          val prop_eq = Thm.combination (Thm.reflexive (Thm.cterm_of ctxt trueprop)) equal
          val goal = HOLogic.mk_Trueprop (predicate $ nth program_field programT (nat i) $
            nth selector_field selectorT (nat i) $ action_field)
          val theorem = Thm.equal_elim (Thm.symmetric prop_eq) checked
        in Utils.exact_prop ctxt "Indexed selector binding" goal theorem end
      val row_facts = map_index selected ((programs ~~ selectors) ~~ facts)
      val i = Free ("selector_index",natT)
      val row = Term.lambda i (predicate $ nth program_field programT i $
        nth selector_field selectorT i $ action_field)
      val indexed_literal = Utils.literal_list_all ctxt "Indexed selector recipes" row
        (map nat (0 upto (count-1))) row_facts
      val range = Const (@{const_name upt},natT --> natT --> HOLogic.listT natT) $
        nat 0 $ size program_field
      val range_eq = Simplifier.rewrite
        (Comma_Entry_Arithmetic.natural_context ctxt |> Simplifier.add_simp program_size
          |> Simplifier.add_simps @{thms upt_rec}) (Thm.cterm_of ctxt range)
      val expected_range = HOLogic.mk_list natT (map nat (0 upto (count-1)))
      val _ = Utils.exact_prop ctxt "Indexed selector range"
        (Logic.mk_equals (range,expected_range)) range_eq
      val list_all = Const (@{const_name list_all},
        (natT --> @{typ bool}) --> HOLogic.listT natT --> @{typ bool})
      val lifted = Thm.combination (Thm.reflexive (Thm.cterm_of ctxt (list_all $ row))) range_eq
      val prop_eq = Thm.combination (Thm.reflexive (Thm.cterm_of ctxt trueprop)) lifted
      val indexed = Thm.equal_elim (Thm.symmetric prop_eq) indexed_literal
      val intro = Drule.infer_instantiate ctxt
        [(("bundle",0),Thm.cterm_of ctxt bundle)]
        @{thm comma_frontier24_selector_rows_indexed_intro}
      val theorem = intro OF [extent,indexed]
      val expected = HOLogic.mk_Trueprop (@{term comma_frontier24_selector_rows_checked} $ bundle)
    in Utils.exact_prop ctxt "Indexed selector alignment" expected theorem end

end
