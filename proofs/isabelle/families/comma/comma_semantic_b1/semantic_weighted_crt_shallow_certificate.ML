(* Checked shallow-node facts.  Mathematical identity is the issued diagram,
   not a printed source address; publication never quotes a recursive tree. *)
structure Comma_Semantic_Weighted_CRT_Shallow_Certificate =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data
  structure Transport = Comma_Semantic_Weighted_CRT_Data_Transport
  structure Id_Table = Table
  (
    type key = Data.identity
    val ord = Data.identity_ord
  )
  type named_node = {term: term, definition: thm}
  type cofactor_result = {result: Data.diagram, equation: thm, shape: thm}
  type named_bind_result =
    {axis: int, diagram: Data.diagram, node: named_node,
     inputs: Data.diagram list, children: named_node list, apply_slots: thm list}
  type proof_caches =
    {shapes: thm Inttab.table Id_Table.table Unsynchronized.ref,
     cofactors: cofactor_result Inttab.table Inttab.table Id_Table.table Unsynchronized.ref,
     zero_weight_nodes: unit Id_Table.table Unsynchronized.ref,
     named_binds: named_bind_result list Id_Table.table Unsynchronized.ref}
  type scope_token = unit Unsynchronized.ref
  type scope_frame =
    {token: scope_token, reservation: Data.reservation, caches: proof_caches}

  val natT = @{typ nat}
  val mod_nat = @{term "(mod)::nat \<Rightarrow> nat \<Rightarrow> nat"}
  fun nat n = HOLogic.mk_number natT n

  type named_owner =
    {lookup: Data.diagram -> named_node option,
     ensure_named: (Data.diagram list -> Proof.context) option}

  fun make initial_ctxt arena payloadT
      ({lookup,ensure_named}: named_owner) =
    let
      val receiving_ctxt = Unsynchronized.ref initial_ctxt
      fun current_context () = !receiving_ctxt
      fun empty_caches (): proof_caches =
        {shapes=Unsynchronized.ref Id_Table.empty,
         cofactors=Unsynchronized.ref Id_Table.empty,
         zero_weight_nodes=Unsynchronized.ref Id_Table.empty,
         named_binds=Unsynchronized.ref Id_Table.empty}
      val default_caches = empty_caches ()
      val scope_stack = Unsynchronized.ref ([]: scope_frame list)
      fun current_caches () =
        (case !scope_stack of
          [] => default_caches
        | frame :: _ =>
            (Data.check_reservation arena (#reservation frame);
             #caches frame))
      fun reserve_cache_entries reservation count =
        let
          val owner = (case !scope_stack of [] => reservation
            | frame :: _ => #reservation frame)
        in List.app (fn _ => Data.reserve_external arena owner)
          (0 upto (count-1)) end
      fun retain_cache_entries reservation count =
        (case !scope_stack of [] => Data.retain_external arena reservation count
        | _ => ())
      fun begin_scope reservation =
        let
          val _ = Data.reserve_external arena reservation
          val token = Unsynchronized.ref ()
          val frame: scope_frame =
            {token=token,reservation=reservation,caches=empty_caches ()}
        in scope_stack := frame :: !scope_stack; token end
      fun end_scope token =
        (case !scope_stack of
          frame :: rest => if #token frame = token then scope_stack := rest
            else error "Shallow CRT cache scopes must close in stack order"
        | [] => error "Shallow CRT cache scope is not active")
      val treeT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
      val edgeT = HOLogic.mk_prodT (natT,treeT)
      val pairT = HOLogic.mk_prodT (natT,treeT)
      val leaf = Const (@{const_name Comma_Weighted_CRT_Leaf},payloadT --> treeT)
      val branch = Const (@{const_name Comma_Weighted_CRT_Branch},
        natT --> HOLogic.listT edgeT --> treeT)
      val shape_const = Const (@{const_name comma_weighted_crt_shape},
        natT --> treeT --> HOLogic.boolT)
      val raw = Const (@{const_name comma_weighted_crt_cofactor_all_raw},
        natT --> natT --> treeT --> pairT)
      val apply_resultT = Type (@{type_name option},
        [HOLogic.mk_prodT (payloadT,natT)])
      val apply_const = Const (@{const_name comma_weighted_crt_apply},
        HOLogic.mk_prodT (natT,treeT) --> natT --> apply_resultT)
      fun apply_action action phase = apply_const $ action $ phase
      fun apply_tree tree phase = apply_action (HOLogic.mk_prod (nat 0,tree)) phase
      val named_checks = Unsynchronized.ref 0
      val shape_builds = Unsynchronized.ref 0
      val cofactor_builds = Unsynchronized.ref 0
      val named_bind_builds = Unsynchronized.ref 0
      val named_bind_hits = Unsynchronized.ref 0
      val zero_weight_hits = Unsynchronized.ref 0
      val zero_weight_checks = Unsynchronized.ref 0
      val scoped = Transport.make_scoped_checker initial_ctxt "shallow_crt"
      val normalization_profile = Transport.make_normalization_profile
        "shallow_named_normalization"
      fun certify_native theorem =
        #check scoped "Shallow named normalization proof"
          (Thm.prop_of theorem) theorem
      fun set_context next =
        (#set_context scoped next;
         receiving_ctxt := next)

      fun checked label proposition theorem =
        #check scoped label proposition theorem

      fun prove label proposition facts =
        let
          val context = Transport.arithmetic_context (current_context ())
            |> Simplifier.add_simps (Comma_Proof_Rewrite_Rules.nonreflexive_rules facts)
          val _ = Comma_Proof_Profile.report ("Shallow proof stage=start label=" ^ label)
          val theorem = Goal.prove (current_context ()) [] [] proposition
            (fn _ => HEADGOAL (simp_tac context))
          val _ = Comma_Proof_Profile.report ("Shallow proof stage=proved label=" ^ label)
          val result = checked label proposition theorem
          val _ = Comma_Proof_Profile.report ("Shallow proof stage=checked label=" ^ label)
        in result end

      fun published diagram =
        (case lookup diagram of
          SOME entry => entry
        | NONE =>
            (case ensure_named of
              NONE => error "Shallow CRT proof refers to an unpublished node"
            | SOME publish =>
                let
                  val next_context = publish [diagram]
                  val _ = set_context next_context
                in case lookup diagram of
                  SOME entry => entry
                | NONE => error "Shallow CRT publisher omitted its requested node" end))

      fun zero_view diagram =
        (case Data.view arena diagram of
          view as Data.View_Leaf {offset,...} =>
            if offset=0 then view
            else error "Shallow CRT payload proof retains a root weight"
        | view as Data.View_Branch {offset,children,...} =>
            if offset=0 andalso List.all (fn (weight,_) => weight=0) children
            then view
            else error "Shallow CRT payload proof retains an edge weight")

      (* Weight validation is memoized by immutable arena identity.  A node is
         entered only after its full reachable DAG has passed validation, so a
         failed parent cannot poison the cache with a partial success. *)
      fun require_zero diagram =
        let
          val identity = Data.identity arena diagram
          val cache = #zero_weight_nodes (current_caches ())
        in if Id_Table.defined (!cache) identity then
            (zero_weight_hits := !zero_weight_hits+1; ())
          else Data.with_reservation arena (fn reservation =>
            let
              val _ = reserve_cache_entries reservation 1
              val _ = (case Data.view arena diagram of
                Data.View_Leaf {offset,...} =>
                  if offset=0 then ()
                  else error "Named CRT bind rejects a nonzero leaf root weight"
              | Data.View_Branch {offset,children,...} =>
                  if offset<>0 orelse
                      not (List.all (fn (weight,_) => weight=0) children)
                  then error "Named CRT bind rejects nonzero root or edge weights"
                  else List.app (fn (_,child) => require_zero child) children)
              val _ = retain_cache_entries reservation 1
              val _ = cache := Id_Table.update (identity,()) (!cache)
              val _ = zero_weight_checks := !zero_weight_checks+1
            in () end)
        end

      fun named diagram =
        Data.with_reservation arena (fn reservation =>
          let
            val _ = Data.reserve_external arena reservation
            val tree = Data.tree_part arena diagram
            val view = zero_view tree
            val entry = published tree
            val _ = if fastype_of (#term entry)=treeT then ()
              else error "Shallow CRT node has the wrong payload type"
            val rhs = (case view of
                Data.View_Leaf {payload={value,...},...} =>
                  if fastype_of value=payloadT then leaf $ value
                  else error "Shallow CRT leaf changed its payload type"
              | Data.View_Branch {axis,children,...} =>
                  let
                    val _ = List.app (fn _ =>
                      Data.reserve_external arena reservation) children
                    val rows = map (fn (weight,child) =>
                      HOLogic.mk_prod (nat weight,#term (published child))) children
                  in branch $ nat axis $ HOLogic.mk_list edgeT rows end)
            val definition = checked "Shallow CRT node definition"
              (Logic.mk_equals (#term entry,rhs)) (#definition entry)
            (* The publisher already owns and accounts for this exact named
               definition. Keep no second theorem cache for the same authority. *)
            val result = {term= #term entry,definition=definition}: named_node
            val _ = named_checks := !named_checks+1
          in result end)

      fun shape diagram lower =
        let
          val tree = Data.tree_part arena diagram
          val identity = Data.identity arena tree
          val _ = if 0<=lower andalso lower<=4 then ()
            else error "Shallow CRT shape bound is outside 0..4"
          val cache = #shapes (current_caches ())
          val prior = the_default Inttab.empty (Id_Table.lookup (!cache) identity)
        in
          (case Inttab.lookup prior lower of
            SOME theorem => theorem
          | NONE => Data.with_reservation arena (fn reservation =>
              let
                val _ = reserve_cache_entries reservation 1
                val entry = named tree
                val proposition = HOLogic.mk_Trueprop
                  (shape_const $ nat lower $ #term entry)
                val view = zero_view tree
                val facts = (case view of
                    Data.View_Leaf _ => [#definition entry]
                  | Data.View_Branch {axis,children,...} =>
                      if lower>axis then
                        error "Shallow CRT shape contradicts its canonical axis"
                      else if lower<axis then [shape diagram axis]
                      else #definition entry ::
                        map (fn (_,child) => shape child (axis+1)) children)
                val theorem =
                  (case view of
                    Data.View_Branch {axis,...} =>
                      if lower<axis then
                        let
                          val base = hd facts
                          val rule = Drule.infer_instantiate (current_context ())
                            [(("upper",0),Thm.cterm_of (current_context ()) (nat axis))]
                            @{thm comma_weighted_crt_shape_lower_mono}
                          val theorem = Goal.prove (current_context ()) [] [] proposition
                            (fn {context,...} =>
                              HEADGOAL (resolve_tac context [rule]) THEN
                              ALLGOALS (simp_tac
                                (Transport.arithmetic_context context
                                  |> Simplifier.add_simps [base])))
                        in checked "Shallow CRT shape transport" proposition theorem end
                      else prove "Shallow CRT node shape" proposition
                        (facts @ @{thms comma_weighted_crt_shape.simps
                          comma_crt_axis_radix_def list_all_Cons_iff list_all_Nil_iff
                          list.size})
                  | Data.View_Leaf _ =>
                      let
                        val conversion = Conv.arg_conv
                          (Conv.arg_conv (Conv.rewr_conv (#definition entry)))
                          (Thm.cterm_of (current_context ()) proposition)
                        val leaf_intro =
                          (@{thm comma_weighted_crt_shape.simps(1)} RS
                            @{thm iffD2}) OF [@{thm TrueI}]
                        val body = Goal.prove (current_context ()) [] []
                          (Thm.term_of (Thm.rhs_of conversion))
                          (fn {context,...} =>
                            HEADGOAL (resolve_tac context [leaf_intro]))
                        val theorem = Thm.equal_elim
                          (Thm.symmetric conversion) body
                      in checked "Shallow CRT leaf shape" proposition theorem end)
                val current = the_default Inttab.empty
                  (Id_Table.lookup (!cache) identity)
                val _ = retain_cache_entries reservation 1
                val _ = cache := Id_Table.update
                  (identity,Inttab.update (lower,theorem) current) (!cache)
                val _ = shape_builds := !shape_builds+1
              in theorem end))
        end

      fun cofactor diagram axis slot =
        let
          val identity = Data.identity arena diagram
          val radix = Data.axis_radix axis
          val _ = if 0<=slot andalso slot<radix then ()
            else error "Shallow CRT cofactor slot is outside its character"
          val cache = #cofactors (current_caches ())
          val rows = the_default Inttab.empty
            (Id_Table.lookup (!cache) identity)
          val slots = the_default Inttab.empty (Inttab.lookup rows axis)
        in
          (case Inttab.lookup slots slot of
            SOME result => result
          | NONE => Data.with_reservation arena (fn reservation =>
              let
                val _ = reserve_cache_entries reservation 1
                val entry = named diagram
                val view = zero_view diagram
                val result = Data.first_port arena axis slot diagram
                val selected = named result
                val selected_shape = shape result 0
                val proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq
                  (raw $ nat axis $ nat slot $ #term entry,
                   HOLogic.mk_prod (nat 0,#term selected)))
                val equation = (case view of
                    Data.View_Leaf _ => prove "Shallow CRT leaf cofactor" proposition
                      [#definition entry,
                       @{thm comma_weighted_crt_cofactor_all_raw.simps(1)}]
                  | Data.View_Branch {axis=minimum,children,...} =>
                      if axis<minimum then
                        let
                          val base = shape diagram minimum
                          val rule = Drule.infer_instantiate (current_context ())
                            [(("lower",0),Thm.cterm_of (current_context ()) (nat minimum))]
                            @{thm comma_weighted_crt_cofactor_all_raw_axis_below}
                          val theorem = Goal.prove (current_context ()) [] [] proposition
                            (fn {context,...} =>
                              HEADGOAL (resolve_tac context [rule]) THEN
                              ALLGOALS (simp_tac
                                (Transport.arithmetic_context context
                                  |> Simplifier.add_simps [base])))
                        in checked "Shallow CRT absent cofactor" proposition theorem end
                      else if axis=minimum then
                        let
                          val child_shape = shape result (axis+1)
                          val selected_identity = Drule.infer_instantiate (current_context ())
                            [(("lower",0),Thm.cterm_of (current_context ()) (nat (axis+1)))]
                            @{thm comma_weighted_crt_cofactor_all_raw_axis_below}
                          val identity_prop = HOLogic.mk_Trueprop (HOLogic.mk_eq
                            (raw $ nat axis $ nat slot $ #term selected,
                             HOLogic.mk_prod (nat 0,#term selected)))
                          val child_identity = Goal.prove (current_context ()) [] [] identity_prop
                            (fn {context,...} =>
                              HEADGOAL (resolve_tac context [selected_identity]) THEN
                              ALLGOALS (simp_tac
                                (Transport.arithmetic_context context
                                  |> Simplifier.add_simps [child_shape])))
                          val _ = List.app (fn _ =>
                            Data.reserve_external arena reservation) children
                          val raw_root = raw $ nat axis $ nat slot $ #term entry
                          val definition_lhs = Thm.term_of
                            (Thm.lhs_of (#definition entry))
                          val definition_rhs = Thm.term_of
                            (Thm.rhs_of (#definition entry))
                          val raw_cterm = Thm.cterm_of (current_context ()) raw_root
                          val definition_step =
                            if definition_lhs aconv definition_rhs then
                              Thm.reflexive raw_cterm
                            else Conv.arg_conv
                              (Conv.rewr_conv (#definition entry)) raw_cterm
                          val root_step = Conv.rewr_conv
                            (@{thm comma_weighted_crt_cofactor_all_raw.simps(2)} RS
                              @{thm eq_reflection})
                            (Thm.rhs_of definition_step)
                          val unfolded = Thm.transitive definition_step root_step
                          val reduction_ctxt =
                            Transport.arithmetic_context (current_context ())
                            |> Simplifier.del_simps
                              @{thms comma_weighted_crt_cofactor_all_raw.simps}
                            |> Simplifier.add_simps (Comma_Proof_Rewrite_Rules.nonreflexive_rules
                              [child_identity,@{thm if_True},@{thm if_False},
                               @{thm nth_Cons'},@{thm list.size(3)},
                               @{thm list.size(4)},@{thm case_prod_beta},
                               @{thm Let_def},@{thm fst_conv},@{thm snd_conv},
                               @{thm add_0_left}])
                          val reduced = Simplifier.rewrite reduction_ctxt
                            (Thm.rhs_of unfolded)
                          val expected = #2 (HOLogic.dest_eq
                            (HOLogic.dest_Trueprop proposition))
                          val actual = Thm.term_of (Thm.rhs_of reduced)
                          val _ = if actual aconv expected then ()
                            else error ("Shallow selected cofactor reduced to " ^
                              Transport.diagnostic_term_in (current_context ()) actual ^
                              " instead of its checked child")
                          val selected_meta = Thm.transitive unfolded reduced
                          val selected_object = selected_meta RS
                            @{thm meta_eq_to_obj_eq}
                          val theorem = Goal.prove (current_context ()) [] [] proposition
                            (fn {context,...} =>
                              resolve_tac context [selected_object] 1)
                        in checked "Shallow CRT selected cofactor" proposition theorem
                        end
                      else error "Shallow CRT cofactor skipped an unresolved earlier axis")
                val result_record = {result=result,equation=equation,
                  shape=selected_shape}: cofactor_result
                val current_rows = the_default Inttab.empty
                  (Id_Table.lookup (!cache) identity)
                val current_slots = the_default Inttab.empty
                  (Inttab.lookup current_rows axis)
                val _ = retain_cache_entries reservation 1
                val _ = cache := Id_Table.update (identity,
                  Inttab.update (axis,Inttab.update (slot,result_record)
                    current_slots) current_rows) (!cache)
                val _ = cofactor_builds := !cofactor_builds+1
              in result_record end))
        end

      fun action_term diagram =
        let val tree = Data.tree_part arena diagram
        in HOLogic.mk_prod (nat (Data.offset diagram),#term (named tree)) end

      fun action_rhs diagram =
        let
          val entry = named (Data.tree_part arena diagram)
          val lhs = Thm.term_of (Thm.lhs_of (#definition entry))
          val rhs = Thm.term_of (Thm.rhs_of (#definition entry))
          val _ = if lhs aconv #term entry then ()
            else error "Shallow root definition changed its exact named term"
        in HOLogic.mk_prod (nat (Data.offset diagram),rhs) end

      fun pointwise_tree_equation_at label offset left_tree right_tree tree_equation =
        let
          val context = current_context ()
          val lhs = Thm.term_of (Thm.lhs_of tree_equation)
          val rhs = Thm.term_of (Thm.rhs_of tree_equation)
          val _ = if lhs aconv left_tree andalso rhs aconv right_tree then ()
            else error "Shallow tree equation has foreign exact endpoints"
          val root_offset = Free ("root_offset",natT)
          val phase = Free ("phase",natT)
          val pair_const = Const (@{const_name Pair},natT --> treeT --> pairT)
          val offset_term = offset root_offset
          val pair_at_root = pair_const $ offset_term
          val pair_equation = Thm.combination
            (Thm.combination
              (Thm.reflexive (Thm.cterm_of context pair_const))
              (Thm.reflexive (Thm.cterm_of context offset_term))) tree_equation
          val apply_equation = Thm.combination
            (Thm.reflexive (Thm.cterm_of context apply_const)) pair_equation
          val phase_equation = Thm.combination apply_equation
            (Thm.reflexive (Thm.cterm_of context phase))
          val object_equality = phase_equation RS @{thm meta_eq_to_obj_eq}
          val phase_all = Thm.forall_intr (Thm.cterm_of context phase)
            object_equality COMP @{thm allI}
          val theorem = Thm.forall_intr (Thm.cterm_of context root_offset)
            phase_all COMP @{thm allI}
          val source = pair_at_root $ left_tree
          val target = pair_at_root $ right_tree
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
            ("root_offset",natT,HOLogic.mk_all ("phase",natT,
              HOLogic.mk_eq (apply_action source phase,apply_action target phase))))
        in checked label proposition theorem end

      fun pointwise_tree_equation label left_tree right_tree tree_equation =
        pointwise_tree_equation_at label I left_tree right_tree tree_equation

      fun zero_delta_pointwise label tree =
        let
          val context = current_context ()
          val root_offset = Free ("root_offset",natT)
          val phase = Free ("phase",natT)
          val root_plus_zero = HOLogic.mk_binop @{const_name plus}
            (root_offset,nat 0)
          val source = HOLogic.mk_prod (root_offset,tree)
          val target = HOLogic.mk_prod (root_plus_zero,tree)
          val offset_equation = Thm.symmetric (Simplifier.rewrite
            (Simplifier.add_simps [@{thm add_0_right}]
              (put_simpset HOL_basic_ss context))
            (Thm.cterm_of context root_plus_zero))
          val _ = if Thm.term_of (Thm.lhs_of offset_equation) aconv root_offset andalso
              Thm.term_of (Thm.rhs_of offset_equation) aconv root_plus_zero then ()
            else error "Shallow zero-delta conversion changed its exact scalar endpoints"
          val pair_const = Const (@{const_name Pair},natT --> treeT --> pairT)
          val pair_function_equation = Thm.combination
            (Thm.reflexive (Thm.cterm_of context pair_const)) offset_equation
          val pair_equation = Thm.combination pair_function_equation
            (Thm.reflexive (Thm.cterm_of context tree))
          val apply_equation = Thm.combination
            (Thm.combination
              (Thm.reflexive (Thm.cterm_of context apply_const)) pair_equation)
            (Thm.reflexive (Thm.cterm_of context phase))
          val object_equality = apply_equation RS @{thm meta_eq_to_obj_eq}
          val phase_all = Thm.forall_intr (Thm.cterm_of context phase)
            object_equality COMP @{thm allI}
          val theorem = Thm.forall_intr (Thm.cterm_of context root_offset)
            phase_all COMP @{thm allI}
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
            ("root_offset",natT,HOLogic.mk_all ("phase",natT,
              HOLogic.mk_eq (apply_action source phase,apply_action target phase))))
        in checked label proposition theorem end

      fun inverse_pointwise label theorem source target =
        let
          val context = current_context ()
          val root_offset = Free ("root_offset",natT)
          val phase = Free ("phase",natT)
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
            ("root_offset",natT,HOLogic.mk_all ("phase",natT,
              HOLogic.mk_eq (apply_action source phase,apply_action target phase))))
          val reversed = Transport.object_symmetric context theorem
        in checked label proposition reversed end

      fun compose_pointwise label source target first second =
        let
          val root_offset = Free ("root_offset",natT)
          val phase = Free ("phase",natT)
        in Transport.compose_pointwise_profile certify_native normalization_profile
          (current_context ()) label apply_const root_offset phase source target
          [first,second] end

      fun raw_branch_tree axis rows =
        branch $ nat axis $ HOLogic.mk_list edgeT rows

      fun certify_selector reservation selector =
        Data.with_selector_view arena selector (fn view =>
          let
            val axis = #axis view
            val split_axis = #split_axis view
            val input_rows = #input_rows view
            val result = #result view
            val _ = Data.reserve_external arena reservation
            val input_nodes = map (fn row => named (Data.tree_part arena row)) input_rows
            val root_nodes = Unsynchronized.ref input_nodes
            fun remember_named diagram =
              let
                val entry = named (Data.tree_part arena diagram)
                val _ = if List.exists (fn prior => #term prior aconv #term entry)
                    (!root_nodes) then ()
                  else root_nodes := entry :: !root_nodes
              in entry end
            fun root_definition tree =
              (case List.find (fn entry => #term entry aconv tree) (!root_nodes) of
                SOME entry => SOME (#definition entry)
              | NONE => NONE)
            fun certify_piece piece =
              (case piece of
                Data.Same_Axis_Port {slot,selected} =>
                  let
                    val selected_named = remember_named selected
                    val selected_action = HOLogic.mk_prod
                      (nat (Data.offset selected),#term selected_named)
                  in Comma_Semantic_Weighted_CRT_Selector_Transport.Same_Axis_Port
                    {slot=slot,selected=selected_action} end
              | Data.Lower_Axis_Port
                  {slot,restricted_rows,child,child_common,child_result} =>
                  let
                    val child_equation = certify_selector reservation child
                    val recorded_common = Data.selector_common arena child
                    val _ = if child_common=recorded_common then ()
                      else error "Shallow nested selector common weight changed"
                    val relative_rows = map
                      (Data.reduce_offset arena child_common) restricted_rows
                    val relative_result = Data.reduce_offset arena child_common child_result
                    val _ = List.app (fn row => ignore (remember_named row))
                      relative_rows
                    val child_named = remember_named relative_result
                    val child_body = #2 (Logic.dest_equals
                      (Thm.prop_of (#definition child_named)))
                    val relative_offset = Data.offset relative_result
                    val rename = pointwise_tree_equation_at
                      "Shallow selected child name transport"
                      (fn root => HOLogic.mk_binop @{const_name plus}
                        (root,nat relative_offset))
                      child_body (#term child_named)
                      (Thm.symmetric (#definition child_named))
                    val root_offset = Free ("root_offset",natT)
                    val source = HOLogic.mk_prod (root_offset,
                      raw_branch_tree axis (map action_term relative_rows))
                    val target = HOLogic.mk_prod
                      (HOLogic.mk_binop @{const_name plus}
                        (root_offset,nat relative_offset),#term child_named)
                    val named_equation = compose_pointwise
                      "Shallow selected child completed action"
                      source target child_equation rename
                  in Comma_Semantic_Weighted_CRT_Selector_Transport.Lower_Axis_Port
                    {slot=slot,
                     restricted_rows=map action_term relative_rows,
                     child_common=child_common,
                     child_result=action_term relative_result,
                     child_equation=named_equation} end)
            val pieces = map certify_piece (#pieces view)
            val input_terms = map action_term input_rows
            val result_action = action_rhs result
            val theorem =
              Comma_Semantic_Weighted_CRT_Selector_Transport.certify_completed_select
                certify_native normalization_profile (current_context ()) root_definition
                payloadT axis split_axis input_terms pieces result_action
          in theorem end)

      fun certify_normalization initial source_override =
        Data.with_reservation arena (fn reservation => let
          val tree = Data.tree_part arena initial
          val root_identity = Data.identity arena tree
          val _ = (case source_override of
            NONE => ()
          | SOME override =>
              (case zero_view tree of
                Data.View_Leaf _ => error "Shallow literal override is not a branch"
              | Data.View_Branch {axis,children,...} =>
                  let
                    val rows = map (fn (weight,child) =>
                      HOLogic.mk_prod (nat weight,#term (named child))) children
                    val expected = raw_branch_tree axis rows
                  in if override aconv expected then ()
                    else error "Shallow literal source is not its exact ordered branch" end))
          val plan_facts = Unsynchronized.ref Id_Table.empty
          fun certify_plan plan =
            let
              val source = Data.plan_source arena plan
              val identity = Data.identity arena source
            in case Id_Table.lookup (!plan_facts) identity of
              SOME theorem => theorem
            | NONE =>
                let
                  val _ = Data.reserve_external arena reservation
                  val completed = Data.plan_completed arena plan
                  val result = Data.plan_result arena plan
                  val delta = Data.offset result - Data.offset source
                  val _ = if delta>=0 then ()
                    else error "Shallow normalization decreased its root weight"
                  val override = if identity=root_identity then source_override else NONE
                  val source_named = (case override of
                    NONE => SOME (named source)
                  | SOME _ => NONE)
                  val result_named = named result
                  val source_term = (case (override,source_named) of
                    (SOME term,NONE) => term
                  | (NONE,SOME entry) => #term entry
                  | _ => error "Shallow normalization source override is inconsistent")
                  val source_rhs = (case (override,source_named) of
                    (SOME term,NONE) => term
                  | (NONE,SOME entry) => Thm.term_of (Thm.rhs_of (#definition entry))
                  | _ => error "Shallow normalization source definition is unavailable")
                  val result_rhs = Thm.term_of (Thm.rhs_of (#definition result_named))
                  val root_offset = Free ("root_offset",natT)
                  val phase = Free ("phase",natT)
                  val source_action = HOLogic.mk_prod (root_offset,source_term)
                  val result_action = HOLogic.mk_prod
                    (HOLogic.mk_binop @{const_name plus} (root_offset,nat delta),
                     #term result_named)
                  val theorem =
                    if Data.same_action arena source result then
                      if delta<>0 then
                        error "Shallow identity normalization has nonzero delta"
                      else (case source_named of
                        SOME entry =>
                          let
                            val _ = if #term entry aconv #term result_named then ()
                              else error "Shallow identity normalization changed its named root"
                          in zero_delta_pointwise "Shallow unchanged named action"
                            (#term entry) end
                      | NONE =>
                          let
                            val _ = if source_term aconv result_rhs then ()
                              else error "Shallow literal source disagrees with its issued node"
                            val literal_to_named = pointwise_tree_equation
                              "Shallow unchanged literal source definition"
                              result_rhs (#term result_named)
                              (Thm.symmetric (#definition result_named))
                            val endpoint_shift = zero_delta_pointwise
                              "Shallow unchanged literal endpoint shift"
                              (#term result_named)
                          in compose_pointwise "Shallow unchanged literal normalization"
                            (HOLogic.mk_prod (root_offset,source_term))
                            (HOLogic.mk_prod
                              (HOLogic.mk_binop @{const_name plus} (root_offset,nat 0),
                               #term result_named)) literal_to_named endpoint_shift end)
                    else (case zero_view source of
                      Data.View_Branch {axis,...} =>
                        let
                          val child_rows = Data.plan_children arena plan
                          val _ = if length child_rows=Data.axis_radix axis then ()
                            else error "Shallow normalization plan lost an ordered branch row"
                          val raw_rows = map (fn (raw_row,_,_) => action_term raw_row)
                            child_rows
                          val completed_rows = map
                            (fn (_,_,completed_row) => action_term completed_row) child_rows
                          val child_equations = map
                            (fn (_,child_plan,_) => certify_plan child_plan) child_rows
                          val source_tree = raw_branch_tree axis raw_rows
                          val completed_tree = raw_branch_tree axis completed_rows
                          val _ = if source_rhs aconv source_tree then ()
                            else error "Shallow source name does not expose its exact ordered rows"
                          val completed_named = named completed
                          val completed_definition_rhs =
                            Thm.term_of (Thm.rhs_of (#definition completed_named))
                          val _ = if completed_definition_rhs aconv completed_tree then ()
                            else error "Shallow completed name does not expose its exact ordered rows"
                          val source_definition = (case source_named of
                            SOME entry => pointwise_tree_equation
                              "Shallow source definition application"
                              (#term entry) source_rhs (#definition entry)
                          | NONE => Transport.pointwise_reflexive certify_native
                              normalization_profile (current_context ()) apply_const
                              root_offset phase source_action)
                          val canonical_fact =
                            (case zero_view completed of
                              Data.View_Leaf _ =>
                                let
                                  val _ = if delta=0 andalso completed_tree aconv result_rhs then ()
                                    else error "Shallow leaf selector changed its action"
                                in zero_delta_pointwise "Shallow completed leaf identity"
                                  completed_tree end
                            | Data.View_Branch _ =>
                                let
                                  val selector = Data.plan_selector arena plan
                                  val common = Data.selector_common arena selector
                                  val selector_fact = certify_selector reservation selector
                                  val selector_view = Data.with_selector_view arena selector
                                    (fn selector_data => selector_data)
                                  val relative_rows = map action_term
                                    (#input_rows selector_view)
                                  val relative_result = action_rhs (#result selector_view)
                                  val lifted =
                                    Comma_Semantic_Weighted_CRT_Selector_Transport.lift_selector_common
                                      certify_native normalization_profile (current_context ())
                                      payloadT axis common relative_rows relative_result selector_fact
                                  val lifted_prop = Thm.prop_of lifted
                                  val actual_tree = raw_branch_tree axis completed_rows
                                  val expected_offset = common +
                                    Data.offset (#result selector_view)
                                  val _ = if expected_offset=delta andalso
                                      Thm.prop_of lifted aconv
                                        (HOLogic.mk_Trueprop (HOLogic.mk_all
                                          ("root_offset",natT,HOLogic.mk_all ("phase",natT,
                                            HOLogic.mk_eq
                                              (apply_action
                                                (HOLogic.mk_prod (root_offset,actual_tree)) phase,
                                               apply_action
                                                (HOLogic.mk_prod
                                                  (HOLogic.mk_binop @{const_name plus}
                                                    (root_offset,nat delta),result_rhs)) phase)))))
                                    then ()
                                    else error "Shallow selector theorem changed its plan endpoints"
                                in lifted end)
                          val canonical_action = HOLogic.mk_prod
                            (HOLogic.mk_binop @{const_name plus}
                              (root_offset,nat delta),result_rhs)
                          val branch_to_result =
                            Comma_Semantic_Weighted_CRT_Branch_Transport.certify_bottom_up_normalization
                              certify_native normalization_profile (current_context ()) payloadT axis
                              source_tree completed_tree (nat delta) result_rhs
                              raw_rows completed_rows child_equations canonical_fact
                          val named_to_result = compose_pointwise
                            "Shallow named normalization composition"
                            source_action canonical_action source_definition branch_to_result
                          val result_back = pointwise_tree_equation_at
                            "Shallow result definition at normalized weight"
                            (fn root => HOLogic.mk_binop @{const_name plus}
                              (root,nat delta))
                            result_rhs (#term result_named)
                            (Thm.symmetric (#definition result_named))
                        in compose_pointwise "Shallow normalized action endpoint"
                          source_action result_action named_to_result result_back end
                    | Data.View_Leaf _ =>
                        error "Shallow canonical normalization changed a leaf")
                  val _ = checked "Shallow normalization plan theorem"
                    (Thm.prop_of theorem) theorem
                  val _ = plan_facts := Id_Table.update
                    (identity,theorem) (!plan_facts)
                in theorem end
            end
          val result = Data.with_normalization_plan arena tree (fn plan =>
            let
              val theorem = certify_plan plan
              val normalized = Data.plan_result arena plan
            in (normalized,theorem) end)
        in result end)

      fun bind_slot_equation axis slot parent child whole raw_tree row_terms
          row_vector successor_equation =
        let
          val context = current_context ()
          val radix = Data.axis_radix axis
          val phase = Free ("phase",natT)
          val guard = HOLogic.mk_eq
            (mod_nat $ phase $ nat radix,nat slot)
          val free_proposition = HOLogic.mk_Trueprop (HOLogic.mk_imp
            (guard,HOLogic.mk_eq (apply_tree parent phase,apply_tree child phase)))
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
            ("phase",natT,HOLogic.dest_Trueprop free_proposition))
          val rows_term = HOLogic.mk_list edgeT row_terms
          val axis_fact = prove "Named bind axis bound"
            (HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less}
              (nat axis,nat 4))) []
          val size_term = Const
            (@{const_name size},HOLogic.listT edgeT --> natT) $ rows_term
          val size_conversion =
            Comma_Semantic_Weighted_CRT_Selector_Transport.literal_size_conversion
              context rows_term
          val radix_term = @{term comma_crt_axis_radix} $ nat axis
          val radix_conversion = Simplifier.rewrite
            (Simplifier.add_simps [@{thm comma_crt_axis_radix_def}]
              (Transport.arithmetic_context context))
            (Thm.cterm_of context radix_term)
          val _ = if Thm.term_of (Thm.lhs_of size_conversion) aconv size_term andalso
              Thm.term_of (Thm.rhs_of size_conversion) aconv nat radix andalso
              Thm.term_of (Thm.lhs_of radix_conversion) aconv radix_term andalso
              Thm.term_of (Thm.rhs_of radix_conversion) aconv nat radix then ()
            else error "Named bind literal extent conversion changed its checked rows"
          val extent_fact = Thm.transitive size_conversion
            (Thm.symmetric radix_conversion) RS @{thm meta_eq_to_obj_eq}
          val _ = checked "Named bind raw row extent"
            (HOLogic.mk_Trueprop (HOLogic.mk_eq (size_term,radix_term))) extent_fact
          val branch_rule = Drule.infer_instantiate context
            [(("axis",0),Thm.cterm_of context (nat axis)),
             (("offset",0),Thm.cterm_of context (nat 0)),
             (("rows",0),Thm.cterm_of context rows_term),
             (("phase",0),Thm.cterm_of context phase)]
            @{thm comma_weighted_crt_branch_apply_offset}
            OF [axis_fact,extent_fact]
          val selected_row = Transport.literal_nth_conversion_cterm context
            successor_equation slot row_vector
          val branch_selected_prop = HOLogic.mk_Trueprop (HOLogic.mk_imp
            (guard,HOLogic.mk_eq (apply_tree raw_tree phase,apply_tree child phase)))
          val branch_selected = Goal.prove context [] [] branch_selected_prop
            (fn {context,...} =>
              resolve_tac context [@{thm impI}] 1 THEN
              asm_full_simp_tac
                (put_simpset HOL_basic_ss context
                  |> Simplifier.add_simps
                    [branch_rule,selected_row,radix_conversion,
                     @{thm add_0_left},@{thm add_0_right},@{thm case_prod_beta},
                     @{thm fst_conv},@{thm snd_conv}]) 1)
          val branch_selected_rule = Object_Logic.rulify context branch_selected
          val parent_at = Transport.specialize_hol_all context (nat 0) whole
            |> Transport.specialize_hol_all context phase
          val free_theorem = Goal.prove context [] [] free_proposition
            (fn {context,...} =>
              resolve_tac context [@{thm impI}] 1 THEN
              resolve_tac context [@{thm trans}] 1 THEN
              resolve_tac context [parent_at] 1 THEN
              resolve_tac context [branch_selected_rule] 1 THEN assume_tac context 1)
          val theorem = Thm.forall_intr (Thm.cterm_of context phase) free_theorem
            COMP @{thm allI}
        in checked "Named multi-axis weighted row" proposition theorem end

      fun named_bind axis ordered_children target =
        let
          val radix = Data.axis_radix axis
          val _ = if 0<=axis andalso axis<4 then ()
            else error "Named multi-axis bind axis is outside 0..3"
          val _ = if length ordered_children=radix then ()
            else error "Named multi-axis bind child order has the wrong radix"
          val identity = Data.identity arena target
          val cache = #named_binds (current_caches ())
          val cached = the_default [] (Id_Table.lookup (!cache) identity)
          fun same_children left right =
            length left=length right andalso ListPair.allEq
              (fn (a,b) => Data.same_action arena a b) (left,right)
          val hit = List.find (fn result => #axis result=axis andalso
            same_children (#inputs result) ordered_children)
            cached
        in
          (case hit of
            SOME result => (named_bind_hits := !named_bind_hits+1; result)
          | NONE => Data.with_reservation arena (fn reservation =>
              let
                val retained = 2+radix
                val _ = reserve_cache_entries reservation retained
                val _ = require_zero target
                val _ = List.app require_zero ordered_children
                val target_named = named target
                val child_named = map named ordered_children
                val raw_rows = map (fn child =>
                  HOLogic.mk_prod (nat 0,#term (named (Data.tree_part arena child))))
                  ordered_children
                val raw_rows_term = HOLogic.mk_list edgeT raw_rows
                val row_vector = Transport.make_literal_vector
                  (current_context ()) raw_rows_term
                val successor_equation =
                  Comma_Selected_List_Conversion.make_successor_equation
                    (current_context ())
                val raw_tree = raw_branch_tree axis raw_rows
                val raw_parent_matches =
                  (case Data.view arena target of
                    Data.View_Branch {offset,axis=target_axis,children} =>
                      offset=0 andalso target_axis=axis andalso
                      length children=length ordered_children andalso
                      ListPair.allEq (fn ((weight,actual),expected) =>
                        weight=0 andalso Data.same_action arena actual expected)
                        (children,ordered_children)
                  | Data.View_Leaf _ => false)
                val whole =
                  if raw_parent_matches then
                    let
                      val target_rhs = Thm.term_of
                        (Thm.rhs_of (#definition target_named))
                      val _ = if target_rhs aconv raw_tree then ()
                        else error "Named bind target does not have its exact ordered child rows"
                    in pointwise_tree_equation "Named bind identity branch"
                      (#term target_named) raw_tree (#definition target_named) end
                  else
                    let
                      val root_offset = Free ("root_offset",natT)
                      val phase = Free ("phase",natT)
                      val completed_diagrams = ordered_children
                      val completed_rows = raw_rows
                      val completed_tree = raw_tree
                      val child_equations = map (fn entry =>
                        Transport.pointwise_reflexive certify_native normalization_profile
                          (current_context ()) apply_const root_offset phase
                          (HOLogic.mk_prod (root_offset,#term entry))) child_named
                      val (raw_result,result_named,raw_equation) =
                        Data.with_normalized_branch arena axis completed_diagrams
                          (fn (result,selector) =>
                            let
                              val selector_fact = certify_selector reservation selector
                              val selector_view = Data.with_selector_view arena selector
                                (fn value => value)
                              val common = Data.selector_common arena selector
                              val relative_rows = map action_term
                                (#input_rows selector_view)
                              val relative_result = action_rhs (#result selector_view)
                              val canonical_fact =
                                Comma_Semantic_Weighted_CRT_Selector_Transport.lift_selector_common
                                  certify_native normalization_profile (current_context ())
                                  payloadT axis common relative_rows relative_result selector_fact
                              val result_named = named result
                              val result_rhs = Thm.term_of
                                (Thm.rhs_of (#definition result_named))
                              val delta = Data.offset result
                              val expected_result_offset = common +
                                Data.offset (#result selector_view)
                              val canonical_proposition = HOLogic.mk_Trueprop (HOLogic.mk_all
                                ("root_offset",natT,HOLogic.mk_all ("phase",natT,
                                  HOLogic.mk_eq
                                    (apply_action
                                      (HOLogic.mk_prod (root_offset,completed_tree)) phase,
                                     apply_action
                                      (HOLogic.mk_prod
                                        (HOLogic.mk_binop @{const_name plus}
                                          (root_offset,nat delta),result_rhs)) phase))))
                              val _ = if expected_result_offset=delta andalso
                                  Thm.prop_of canonical_fact aconv canonical_proposition then ()
                                else error "Named bind selector changed its normalized endpoint"
                              val branch_equation =
                                Comma_Semantic_Weighted_CRT_Branch_Transport.certify_bottom_up_normalization
                                  certify_native normalization_profile (current_context ())
                                  payloadT axis raw_tree completed_tree (nat delta) result_rhs
                                  raw_rows completed_rows child_equations canonical_fact
                              val result_back = pointwise_tree_equation_at
                                "Named bind result definition at normalized weight"
                                (fn root => HOLogic.mk_binop @{const_name plus}
                                  (root,nat delta))
                                result_rhs (#term result_named)
                                (Thm.symmetric (#definition result_named))
                              val normalized_action = HOLogic.mk_prod
                                (HOLogic.mk_binop @{const_name plus}
                                  (root_offset,nat delta),#term result_named)
                              val raw_action = HOLogic.mk_prod (root_offset,raw_tree)
                              val raw_to_named = compose_pointwise
                                "Named bind source normalization"
                                raw_action normalized_action branch_equation result_back
                            in (result,result_named,raw_to_named) end)
                      val target_equation =
                        if Data.same_action arena target raw_result then
                          let
                            val _ = if Data.offset target=0 andalso
                                Data.offset raw_result=0 andalso
                                #term target_named aconv #term result_named then ()
                              else error "Named bind canonical target changed its exact normalized root"
                          in zero_delta_pointwise "Named bind canonical target identity"
                            (#term target_named) end
                        else
                          let
                            val (target_result,equation) = certify_normalization target NONE
                            val _ = if Data.same_action arena target_result raw_result then ()
                              else error "Named bind target and ordered source rows normalize differently"
                            val _ = if #term (named target_result) aconv
                                #term result_named then ()
                              else error "Named bind normalization changed its canonical name"
                          in equation end
                      val normalized_action = HOLogic.mk_prod
                        (HOLogic.mk_binop @{const_name plus}
                          (root_offset,nat (Data.offset raw_result)),#term result_named)
                      val target_action = HOLogic.mk_prod
                        (root_offset,#term target_named)
                      val raw_action = HOLogic.mk_prod (root_offset,raw_tree)
                      val raw_back = inverse_pointwise
                        "Named bind ordered branch reversal" raw_equation
                        normalized_action raw_action
                    in compose_pointwise "Named bind normalized ordered branch"
                      target_action raw_action target_equation raw_back end
                val apply_slots = map (fn slot => bind_slot_equation axis slot
                  (#term target_named) (#term (List.nth (child_named,slot)))
                  whole raw_tree raw_rows row_vector successor_equation)
                  (0 upto (radix-1))
                val result: named_bind_result =
                  {axis=axis,diagram=target,node=target_named,
                   inputs=ordered_children,children=child_named,
                   apply_slots=apply_slots}
                val entries = the_default []
                  (Id_Table.lookup (!cache) identity)
                val _ = cache := Id_Table.update
                  (identity,result::entries) (!cache)
                val _ = retain_cache_entries reservation retained
                val _ = named_bind_builds := !named_bind_builds+1
              in result end))
        end

    in {named=named,shape=shape,cofactor=cofactor,set_context=set_context,
      named_bind=named_bind,begin_scope=begin_scope,end_scope=end_scope,
      audit= #audit scoped,proof_stats= #stats scoped,
      (* Counters span scopes; this field reports only the live frame size. *)
      stats=fn () => {named_checks= !named_checks,shape_builds= !shape_builds,
        cofactor_builds= !cofactor_builds,
        named_bind_builds= !named_bind_builds,
        named_bind_hits= !named_bind_hits,
        zero_weight_nodes=Id_Table.size
          (!(#zero_weight_nodes (current_caches ()))),
        zero_weight_checks= !zero_weight_checks,
        zero_weight_hits= !zero_weight_hits}} end
end
