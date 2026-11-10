(* Postorder source certification for one semantic program state at a time.
   The compiler owns only transient cofactor states; this module returns one
   closed universal theorem for each completed state. *)
structure Comma_Semantic_Phase_Action_State_Certificate =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data
  structure Compiler = Comma_Semantic_Phase_Action_Program_Compiler
  structure Source_Certificate = Comma_Semantic_Phase_Action_Program_Certificate
  structure Shallow = Comma_Semantic_Weighted_CRT_Shallow_Certificate
  structure Transport = Comma_Semantic_Weighted_CRT_Data_Transport
  structure Clock = Comma_Semantic_Phase_Action_Clock_Refinement
  structure Candidate = Comma_Semantic_Phase_Class_Rank_Candidate

  val natT = @{typ nat}
  val actionT = @{typ comma_phase_rank_mask_action}
  val treeT = Type (@{type_name comma_semantic_weighted_crt_dag}, [actionT])
  val outputPairT = HOLogic.mk_prodT (actionT,natT)
  val optionOutputT = Type (@{type_name option}, [outputPairT])

  fun nat n = HOLogic.mk_number natT n
  fun mod_nat (left,right) = Clock.mod_nat (left,right)
  fun mk_eq (left,right) = HOLogic.mk_eq (left,right)
  fun mk_imp (left,right) = HOLogic.mk_imp (left,right)
  fun mk_conj (left,right) = HOLogic.mk_conj (left,right)
  fun mk_less (left,right) = HOLogic.mk_binrel @{const_name less} (left,right)
  fun mk_trueprop proposition = HOLogic.mk_Trueprop proposition

  fun applied tree phase =
    Const (@{const_name comma_weighted_crt_apply},
      HOLogic.mk_prodT (natT,treeT) --> natT --> optionOutputT) $
      HOLogic.mk_prod (nat 0,tree) $ phase

  fun applied_some value =
    Const (@{const_name Some}, outputPairT --> optionOutputT) $
      HOLogic.mk_prod (value,nat 0)

  fun round_output source phase =
    @{term comma_semantic_b1_round_output} $ phase $ source

  fun ranked_output source phase =
    @{term comma_rank_mask_action_of_b1_result} $ round_output source phase

  fun expected_from_fields (source: term) (period: int)
      (environment: Compiler.clock_env) named_term =
    let
      val phase = Free ("phase",natT)
      val guard = Clock.period_env_condition phase period environment
    in
      HOLogic.mk_all ("phase",natT,
        mk_imp (mk_conj (mk_less (phase,nat 924),guard),
          mk_eq (applied named_term phase,
            applied_some (ranked_output source phase))))
    end

  fun expected_exactness (action: Compiler.program_action) named_term =
    expected_from_fields (#source action) (#period action)
      (#environment action) named_term

  fun expected_state_exactness (state: Compiler.certified_state) named_term =
    expected_from_fields (#source state) (#period state)
      (#environment state) named_term

  fun child_exactness_check check (child: Compiler.certified_state) named_term =
    check "Postorder child state exactness"
      (mk_trueprop (expected_state_exactness child named_term)) (#exactness child)

  type source_proof_scope =
    {token: Compiler.scope_token, reservation: Data.reservation,
     bundle: Source_Certificate.source_proof_bundle option Unsynchronized.ref}

  fun make_state_certifier (initial_ctxt: Proof.context)
      (arena: Candidate.arena)
      (transaction: Candidate.shallow_transaction)
      (publisher: Candidate.shallow_publisher):
      Compiler.state_certifier =
    let
      val checker = Transport.make_scoped_checker initial_ctxt
        "comma_semantic_phase_action_state_certificate"
      val check = #check checker
      fun action_lookup diagram =
        Candidate.shallow_publisher_lookup publisher diagram
      fun receiving_context () =
        let
          val target_ctxt = Local_Theory.target_of
            (Candidate.current_local_theory transaction)
          val receiving = Transport.install_scoped_checker target_ctxt checker
          val _ = #set_context checker receiving
        in receiving end
      fun ensure_named roots =
        (ignore (Candidate.publish_shallow_roots publisher roots);
         receiving_context ())
      val shallow = Shallow.make
        (Transport.install_scoped_checker initial_ctxt checker)
        arena actionT {lookup=action_lookup,ensure_named=SOME ensure_named}
      val source_proof_scopes = Unsynchronized.ref ([]: source_proof_scope list)
      fun begin_scope reservation =
        let
          val token = #begin_scope shallow reservation
          val scope: source_proof_scope =
            {token=token,reservation=reservation,bundle=Unsynchronized.ref NONE}
          val _ = source_proof_scopes := scope :: !source_proof_scopes
        in token end
      fun end_scope token =
        (case !source_proof_scopes of
          [] => error "Source proof scope stack is empty"
        | scope :: rest =>
            if #token scope = token then
              let
                val outcome = Exn.capture (fn () => #end_scope shallow token) ()
                val _ = source_proof_scopes := rest
              in Exn.release outcome end
            else error "Source proof scope closed out of order")
      fun source_proof_bundle_for ctxt source_program action =
        (case !source_proof_scopes of
          [] => Source_Certificate.make_source_proof_bundle
            check ctxt source_program action
        | scope :: _ =>
            let
              val _ = Data.check_reservation arena (#reservation scope)
            in case !(#bundle scope) of
              SOME bundle => Source_Certificate.validate_source_proof_bundle
                check source_program action bundle
            | NONE =>
                let
                  val _ = Data.reserve_external arena (#reservation scope)
                  val bundle = Source_Certificate.make_source_proof_bundle
                    check ctxt source_program action
                  val _ = #bundle scope := SOME bundle
                in bundle end end)
      fun context () =
        let
          val receiving = receiving_context ()
          val _ = #set_context shallow receiving
        in receiving end

      fun check_action_context
          (context_record: Compiler.action_context) =
        let
          val action = #action context_record
          val source_binding = #source_binding context_record
          val _ = if #source source_binding aconv #source action andalso
              #program source_binding aconv #program action andalso
              Compiler.key_of_program (#program source_binding) = #key action
            then ()
            else error "State source binding does not match its semantic program"
        in action end

      fun validate_child_source (parent: Compiler.program_action)
          (child: Compiler.certified_state) =
        if #key parent = #key child andalso
            #program parent aconv #program child andalso
            #source parent aconv #source child then ()
        else error "Branch child changed its semantic source key"

      fun branch_guard_transport check ctxt (parent: Compiler.program_action)
          (child: Compiler.certified_state) (axis: int) (slot: int) =
        let
          val phase = Free ("phase",natT)
          val period = #period parent
          val radix = Data.axis_radix axis
          val component = Compiler.period_component period axis
          val {divisor,...} = Clock.gcd_component_divisor check ctxt period axis
          val parent_guard = Clock.period_env_condition phase period
            (#environment parent)
          val selected = mk_eq (mod_nat (phase,nat radix),nat slot)
          val child_guard = Clock.period_env_condition phase period
            (#environment child)
          val selected_prop = HOLogic.mk_all ("phase",natT,
            mk_imp (selected,
              mk_eq (mod_nat (phase,nat component),
                mod_nat (nat slot,nat component))))
          val slot_rule = Drule.infer_instantiate ctxt
            [(("radix",0),Thm.cterm_of ctxt (nat radix)),
             (("gcd_residue",0),Thm.cterm_of ctxt (nat component)),
             (("slot",0),Thm.cterm_of ctxt (nat slot))]
            @{thm comma_crt_slot_gcd_residue_transport} OF [divisor]
          val selected_fact = Goal.prove ctxt [] []
            (mk_trueprop selected_prop)
            (fn {context,...} =>
              REPEAT_DETERM (resolve_tac context
                [@{thm allI},@{thm impI}] 1) THEN
              resolve_tac context [slot_rule] 1 THEN
              assume_tac context 1)
            |> check "A raw CRT slot selects its canonical GCD residue"
              (mk_trueprop selected_prop)
          val child_slot = (case Compiler.env_slot (#environment child) axis of
              SOME value => value
            | NONE => error "Branch child is missing its selected CRT coordinate")
          val slot_remainder_prop = mk_eq
            (mod_nat (nat slot,nat component),nat child_slot)
          val slot_remainder = Clock.prove_simp check ctxt
            "Raw branch slot agrees with its canonical child coordinate"
            slot_remainder_prop @{thms numeral_mod_numeral}
          val selected_child_prop = HOLogic.mk_all ("phase",natT,
            mk_imp (selected,
              mk_eq (mod_nat (phase,nat component),nat child_slot)))
          val selected_child_conversion = Simplifier.rewrite
            (put_simpset HOL_basic_ss ctxt
              |> Simplifier.add_simps [slot_remainder])
            (Thm.cprop_of selected_fact)
          val selected_child_fact = Thm.equal_elim
            selected_child_conversion selected_fact
            |> check "A raw CRT slot selects its canonical child coordinate"
              (mk_trueprop selected_child_prop)
          val proposition = HOLogic.mk_all ("phase",natT,
            mk_imp (mk_conj (mk_less (phase,nat 924),
              mk_conj (parent_guard,selected)),child_guard))
          val selected_child_rule =
            selected_child_fact RS @{thm spec} RS @{thm mp}
        in
          Goal.prove ctxt [] [] (mk_trueprop proposition)
            (fn {context,...} =>
              REPEAT_DETERM (resolve_tac context
                [@{thm allI},@{thm impI}] 1) THEN
              REPEAT_DETERM (eresolve_tac context [@{thm conjE}] 1) THEN
              TRY (REPEAT_ALL_NEW (resolve_tac context [@{thm conjI}]) 1) THEN
              ALLGOALS (fn i =>
                assume_tac context i ORELSE
                  (resolve_tac context [selected_child_rule] i THEN
                   assume_tac context i)))
            |> check
              "Parent state guard and raw slot establish the child GCD guard"
              (mk_trueprop proposition)
        end

      fun validate_child_exactness check (child: Compiler.certified_state)
          named_term =
        child_exactness_check check child named_term

      fun exactness_for_terminal check ctxt
          (context_record: Compiler.action_context)
          (action: Compiler.program_action)
          (named: Shallow.named_node) =
        let
          val terminal = (case #terminal_reduction context_record of
              SOME reduction => reduction
            | NONE => error "Terminal state is missing its checked result reduction")
          val action_label = (case #node action of
              Compiler.Terminal_Node {action,...} => action
            | _ => error "Terminal exactness received a nonterminal state")
          val _ = if #action terminal aconv action_label then ()
            else error "Terminal result reduction belongs to another action"
          val view = Data.view arena (#diagram action)
          val leaf_payload = (case view of
              Data.View_Leaf {offset=0,payload} => payload
            | Data.View_Leaf _ =>
                error "Terminal state diagram has a nonzero leaf offset"
            | Data.View_Branch _ =>
                error "Terminal state diagram unexpectedly has a branch")
          val _ = if #value leaf_payload aconv #result terminal then ()
            else error "Terminal state diagram has the wrong checked result payload"
          val source_bundle = source_proof_bundle_for ctxt
            (#source_binding context_record) action
          val action_uniform = Source_Certificate.local_action_template
            check ctxt (#source_binding context_record) action source_bundle
          val output = Source_Certificate.local_output_template
            check ctxt (#source_binding context_record) action
            (SOME terminal) action_uniform source_bundle
          val phase = Free ("phase",natT)
          val named_eval_prop = HOLogic.mk_all ("phase",natT,
            mk_eq (applied (#term named) phase,
              applied_some (#result terminal)))
          val named_eval = Clock.prove_simp check ctxt
            "Named terminal node applies to its checked zero-weight result"
            named_eval_prop
            ([#definition named] @
              @{thms comma_weighted_crt_eval.simps
                comma_weighted_crt_apply_def option.map})
          val expected = expected_exactness action (#term named)
        in
          Clock.prove_simp check ctxt "Terminal state output exactness" expected
            [named_eval,output]
        end

      fun exactness_for_goto check ctxt
          (context_record: Compiler.action_context)
          (action: Compiler.program_action)
          (named: Shallow.named_node)
          (children: Compiler.certified_state list) =
        let
          val goto_action = (case #node action of
              Compiler.Goto_Node {action,...} => action
            | _ => error "Goto exactness received a non-Goto state")
          val (child_source,shift) = (case Compiler.goto_parts goto_action of
              SOME pair => pair
            | NONE => error "Goto state action is not a checked Goto")
          val _ = if shift=0 then ()
            else error "Goto state cannot transport a nonzero phase shift"
          val child = (case children of
              [state] => state
            | _ => error "Goto state requires exactly one universal child state")
          val child_key = (case #node action of
              Compiler.Goto_Node {child,...} => child
            | _ => error "Goto state lost its child key")
          val _ = if #1 child_key= #key child andalso
              #2 child_key=Compiler.empty_env then ()
            else error "Goto child is not the semantic key's empty-env root"
          val _ = if #environment child=Compiler.empty_env then ()
            else error "Goto child certificate is not for an empty-env root state"
          val actual_child_binding = (case #goto_child_binding context_record of
              SOME binding => binding
            | NONE => error "Goto state is missing its checked child source binding")
          val _ = if #source actual_child_binding aconv child_source then ()
            else error "Goto child binding belongs to another source occurrence"
          val _ = if Compiler.key_of_program (#program actual_child_binding) =
              #key child andalso #program actual_child_binding aconv #program child
            then ()
            else error "Goto child occurrence does not normalize to its certified key"
          val child_diagram = #diagram child
          val _ = if Data.same_action arena (#diagram action) child_diagram then ()
            else error "Goto parent target differs from the full child root diagram"
          val child_named = #named shallow child_diagram
          val _ = if #term named aconv #term child_named then ()
            else error "Goto target and child root lack a shared named definition"
          val child_exact = validate_child_exactness check child
            (#term child_named)
          val source_same = Source_Certificate.source_program_same check ctxt
            actual_child_binding (#source_binding child) child_source (#source child)
          val source_bundle = source_proof_bundle_for ctxt
            (#source_binding context_record) action
          val action_uniform = Source_Certificate.local_action_template
            check ctxt (#source_binding context_record) action source_bundle
          val goto_output = Source_Certificate.local_output_template
            check ctxt (#source_binding context_record) action NONE
            action_uniform source_bundle
          val expected = expected_exactness action (#term named)
        in
          Clock.prove_simp check ctxt "Zero-shift Goto state exactness" expected
            [child_exact,source_same,goto_output]
        end

      fun exactness_for_branch check ctxt
          (context_record: Compiler.action_context)
          (action: Compiler.program_action)
          (named: Shallow.named_node)
          (children: Compiler.certified_state list) =
        let
          val (axis,child_rows) = (case #node action of
              Compiler.Branch_Node {axis,children} => (axis,children)
            | _ => error "Branch exactness received a nonbranch state")
          val radix = Data.axis_radix axis
          val _ = if length children=radix andalso length child_rows=radix then ()
            else error "Branch state does not carry every raw CRT slot"
          val _ = List.app (fn (slot,_) =>
            if slot>=0 andalso slot<radix then ()
            else error "Branch state contains an out-of-range raw slot") child_rows
          val _ = List.app (fn (slot,child) =>
            let
              val (expected_slot,expected_key) = List.nth (child_rows,slot)
              val expected_env = Compiler.env_update (#period action)
                (#environment action) axis slot
              val _ = validate_child_source action child
              val _ = if expected_slot=slot andalso
                  expected_key=(#key child,#environment child) andalso
                  #environment child=expected_env andalso
                  #period child= #period action then ()
                else error "Branch slot child does not match its checked quotient key"
              val _ = if #source (#source_binding child) aconv
                    #source (#source_binding context_record) andalso
                    #program (#source_binding child) aconv
                    #program (#source_binding context_record) then ()
                else error "Branch child changed its representative source binding"
            in () end) (ListPair.zip (0 upto (radix-1),children))
          val child_diagrams = map #diagram children
          val parent_named = #named shallow (#diagram action)
          val child_named = map (#named shallow) child_diagrams
          val composed = #named_bind shallow axis child_diagrams (#diagram action)
          val ctxt = context ()
          val _ = if length (#apply_slots composed)=radix andalso
              length child_named=radix then ()
            else error "Shallow branch bind lost a raw slot apply theorem"
          val phase = Free ("phase",natT)
          val parent_guard = Clock.period_env_condition phase (#period action)
            (#environment action)
          val slots = 0 upto (radix-1)
          val slot_list = HOLogic.mk_list natT (map nat slots)
          val slot_range = Const (@{const_name upt},
            natT --> natT --> HOLogic.listT natT) $ nat 0 $ nat radix
          val slot_range_bridge = Clock.prove_simp check ctxt
            "Bounded CRT range is exactly its ordered raw-slot list"
            (mk_eq (slot_range,slot_list)) @{thms upt_rec}
          val child_terms = map #term child_named
          val children_term = HOLogic.mk_list treeT child_terms
          val nth_tree = Const (@{const_name nth},
            HOLogic.listT treeT --> natT --> treeT)
          val child_output_rows =
            Const (@{const_name list_all},
              (natT --> HOLogic.boolT) --> HOLogic.listT natT --> HOLogic.boolT) $
              Abs ("slot",natT,
                mk_imp (mk_eq
                  (mod_nat (phase,nat radix),Bound 0),
                  mk_eq (applied (nth_tree $ children_term $ Bound 0) phase,
                    applied_some (ranked_output (#source action) phase)))) $
              slot_range
          val branch_output_prop = HOLogic.mk_all ("phase",natT,
            mk_imp (mk_conj (mk_less (phase,nat 924),parent_guard),
              child_output_rows))
          val child_output_facts = map_index (fn (slot,child) =>
            let
              val named_child = List.nth (child_named,slot)
              val child_exact = validate_child_exactness check child
                (#term named_child)
              val selected_guard = branch_guard_transport check ctxt action
                child axis slot
              val proposition = HOLogic.mk_all ("phase",natT,
                mk_imp (mk_conj (mk_less (phase,nat 924),
                  mk_conj (parent_guard,
                    mk_eq (mod_nat (phase,nat radix),nat slot))),
                  mk_eq (applied (#term named_child) phase,
                    applied_some (ranked_output (#source action) phase))))
            in Goal.prove ctxt [] [] (mk_trueprop proposition)
              (fn {context,...} =>
                REPEAT_DETERM (resolve_tac context
                  [@{thm allI},@{thm impI}] 1) THEN
                eresolve_tac context [@{thm conjE}] 1 THEN
                resolve_tac context
                  [child_exact RS @{thm spec} RS @{thm mp}] 1 THEN
                resolve_tac context [@{thm conjI}] 1 THEN
                assume_tac context 1 THEN
                resolve_tac context
                  [selected_guard RS @{thm spec} RS @{thm mp}] 1 THEN
                resolve_tac context [@{thm conjI}] 1 THEN
                assume_tac context 1 THEN
                assume_tac context 1)
              |> check
                "Raw branch slot and gcd guard select its universal child theorem"
                (mk_trueprop proposition) end) children
          val output_rows = Clock.prove_simp check ctxt
            "Every raw branch slot has its checked selected output"
            branch_output_prop (child_output_facts @
              [slot_range_bridge] @
              @{thms list_all_Cons_iff list_all_Nil_iff nth_Cons' list.size
                upt_rec comma_crt_axis_radix_def})
          val bind_rows_prop = HOLogic.mk_all ("phase",natT,
            Const (@{const_name list_all},
              (natT --> HOLogic.boolT) --> HOLogic.listT natT --> HOLogic.boolT) $
              Abs ("slot",natT,
                mk_imp (mk_eq
                  (mod_nat (phase,nat radix),Bound 0),
                  mk_eq (applied (#term parent_named) phase,
                    applied (nth_tree $ children_term $ Bound 0) phase))) $
                slot_list)
          val bind_rows = Clock.prove_simp check ctxt
            "Named bind full-apply covers all raw branch slots" bind_rows_prop
            (#apply_slots composed @
              @{thms list_all_Cons_iff list_all_Nil_iff nth_Cons' list.size})
          val axis_bound = Clock.prove_simp check ctxt
            "Branch axis is a checked CRT coordinate"
            (mk_less (nat axis,nat 4)) []
          val axis_radix_term = @{term comma_crt_axis_radix} $ nat axis
          val radix_fact = Clock.prove_simp check ctxt
            "Branch radix agrees with the checked raw-slot extent"
            (mk_eq (axis_radix_term,nat radix))
            @{thms comma_crt_axis_radix_def}
          val selected_bind_prop = HOLogic.mk_all ("phase",natT,
            mk_eq (applied (#term parent_named) phase,
              applied (nth_tree $ children_term $
                mod_nat (phase,axis_radix_term)) phase))
          val selected_bind = Goal.prove ctxt [] []
            (mk_trueprop selected_bind_prop)
            (fn {context,...} =>
              resolve_tac context [@{thm allI}] 1 THEN
              resolve_tac context [@{thm comma_weighted_crt_apply_bind_slot_cover}] 1 THEN
              ALLGOALS (asm_full_simp_tac
                (put_simpset HOL_basic_ss context
                  |> Simplifier.add_simps
                    [axis_bound,radix_fact,slot_range_bridge,bind_rows])))
            |> check "Named bind selects the checked child at each raw slot"
              (mk_trueprop selected_bind_prop)
          val selected_residue = mod_nat (phase,nat radix)
          val set_slot_range = Const (@{const_name set},
            HOLogic.listT natT --> HOLogic.mk_setT natT) $ slot_range
          val selected_member_prop = HOLogic.mk_all ("phase",natT,
            HOLogic.mk_mem (selected_residue,set_slot_range))
          val radix_positive = Clock.prove_simp check ctxt
            "Branch raw-slot radix is positive"
            (mk_less (nat 0,nat radix)) []
          val selected_member = Clock.prove_simp check ctxt
            "Every selected branch residue belongs to the raw slot range"
            selected_member_prop
            (radix_positive :: @{thms mod_less_divisor set_upt
              atLeastLessThan_iff zero_le})
          val selected_output_prop = HOLogic.mk_all ("phase",natT,
            mk_imp (mk_conj (mk_less (phase,nat 924),parent_guard),
              mk_eq (applied (nth_tree $ children_term $ selected_residue) phase,
                applied_some (ranked_output (#source action) phase))))
          val selected_row_from_rows =
            (output_rows RS @{thm spec} RS @{thm mp}) RS
              (@{thm list_all_iff} RS @{thm iffD1}) RS
              @{thm bspec} RS @{thm mp}
          val selected_output = Goal.prove ctxt [] []
            (mk_trueprop selected_output_prop)
            (fn {context,...} =>
              REPEAT_DETERM (resolve_tac context
                [@{thm allI},@{thm impI}] 1) THEN
              resolve_tac context [selected_row_from_rows] 1 THEN
              assume_tac context 1 THEN
              resolve_tac context [selected_member RS @{thm spec}] 1 THEN
              resolve_tac context [@{thm refl}] 1)
            |> check "The selected raw slot satisfies its checked source output"
              (mk_trueprop selected_output_prop)
          val exact_prop = expected_exactness action (#term parent_named)
        in
          Clock.prove_simp check ctxt "Branch state exactness after normalized bind"
            exact_prop [selected_bind,selected_output,radix_fact]
        end

      fun certify (context_record: Compiler.action_context)
          (children: Compiler.certified_state list) =
        let
          val action = check_action_context context_record
          val _ = (case !source_proof_scopes of
              [] => ()
            | scope :: _ => Data.check_reservation arena (#reservation scope))
          val _ = Candidate.publish_shallow_roots publisher [#diagram action]
          val ctxt = context ()
          val named = #named shallow (#diagram action)
          val _ = if Data.offset (#diagram action)=0 then ()
            else error "State certificate action root has a physical offset"
          val theorem = (case #node action of
              Compiler.Terminal_Node _ =>
                if null children then
                  exactness_for_terminal check ctxt context_record action named
                else error "Terminal state cannot have child states"
            | Compiler.Goto_Node _ =>
                exactness_for_goto check ctxt context_record action named children
            | Compiler.Branch_Node _ =>
                exactness_for_branch check ctxt context_record action named children)
          val expected = expected_exactness action (#term named)
        in check "Completed universal semantic program state"
          (mk_trueprop expected) theorem end
    in
      {certify=certify,begin_scope=begin_scope,
       end_scope=end_scope,current_context=context}: Compiler.state_certifier
    end
end
