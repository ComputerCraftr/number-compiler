(* Checked Entry relation assembly over factored action-row transports. *)
functor Comma_Direct_Entry_Bindings (
  val fixed_entry_port_conversion_plan: Proof.context ->
    {procedure: Simplifier.simproc, plain_procedure: Simplifier.simproc,
     statistics: unit -> string}
  val core_parameter_conversion_plan: Proof.context ->
    {procedure: Simplifier.simproc, plain_procedure: Simplifier.simproc,
     hits: unit -> int, seed_hits: unit -> int}
) =
struct
  structure Compiler = Comma_Frontier24_Parametric_Compiler
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Rows = Comma_Direct_Row_Bindings (
    val fixed_entry_port_conversion_plan = fixed_entry_port_conversion_plan
    val core_parameter_conversion_plan = core_parameter_conversion_plan)
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n
  fun fold_expression ctxt label relation left expression definition theorem =
    let
      val body = Thm.term_of (Thm.rhs_of definition)
      val _ = Utils.exact_prop ctxt (label ^ " expression definition")
        (Logic.mk_equals (expression,body)) definition
      val body_prop = HOLogic.mk_Trueprop (relation $ left $ body)
      val theorem = Utils.exact_prop ctxt (label ^ " shallow proof") body_prop theorem
      val conversion = Conv.arg_conv (Conv.arg_conv
        (Conv.rewr_conv (Thm.symmetric definition))) (Thm.cprop_of theorem)
      val result = Thm.equal_elim conversion theorem
    in Utils.exact_prop ctxt label (HOLogic.mk_Trueprop (relation $ left $ expression)) result end
  fun make ctxt (computation: Compiler.computation) program_bindings body definition =
    let
      val rows = Rows.make ctxt computation program_bindings
      val issued = Unsynchronized.ref 0
      val support_evaluator = Code_Simp.static_conv
        {ctxt=ctxt,simpset=NONE,
         consts=Code_Thingol.read_const_exprs ctxt
           [@{const_name comma_core_supported_values}]} ctxt
      val support_cache = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val product_context = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_simps @{thms prod.case}
      val support_context = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps @{thms list.simps list.map prod.case fst_conv}
      val uniqueness_context = support_context |> Simplifier.add_simps
        @{thms distinct.simps set_simps insert_iff empty_iff}
      val admission_context = support_context |> Simplifier.add_simps
        @{thms comma_phase_program_structurally_admitted_def
          comma_semantic_port_program.simps comma_entry_core_common_rules
          comma_phase_core_of_modulus_def comma_sector_entry_bound_def}
      fun support core wanted =
        (case Termtab.lookup (!support_cache) core of
          SOME theorem => Utils.exact_prop ctxt "Direct Entry support"
            (Logic.mk_equals (@{term comma_core_supported_values} $ core,
              HOLogic.mk_list natT (map nat wanted))) theorem
        | NONE =>
            let
              val request = @{term comma_core_supported_values} $ core
              val raw = support_evaluator (Thm.cterm_of ctxt request)
              val normalized = Simplifier.rewrite
                (Comma_Entry_Arithmetic.natural_context ctxt) (Thm.rhs_of raw)
              val theorem = Thm.transitive raw normalized
                |> Utils.exact_prop ctxt "Direct Entry support"
                  (Logic.mk_equals (request,HOLogic.mk_list natT (map nat wanted)))
              val _ = support_cache := Termtab.update (core,theorem) (!support_cache)
            in theorem end)
      fun certify chart program expression representatives =
        let
          val {sector,digit,residue,core} = (case Compiler.parse_program program of
              Compiler.Entry data => data | _ => error "Expected a direct Entry program")
          val expression_body = body expression
          val expression_definition = definition expression
          val _ = Utils.exact_prop ctxt "Direct Entry expression definition"
            (Logic.mk_equals (expression,expression_body)) expression_definition
          val (expression_core,row_terms) = (case Term.strip_comb expression_body of
              (Const (name,_),[c,items]) =>
                if name = @{const_name Comma_Direct_Entry} then (c,HOLogic.dest_list items)
                else error "Entry binding has a different expression constructor"
            | _ => error "Malformed direct Entry expression")
          val _ = if expression_core aconv core then () else error "Entry core changed"
          fun dest item = let val (w,child) = HOLogic.dest_prod item
            in (Utils.dest_nat "Entry supported value" natT w,child) end
          val fields = map dest row_terms
          val wanted = map #1 fields
          val _ = if wanted = #supported_values computation core andalso
              length fields = length representatives then ()
            else error "Entry rows differ from proposed ordered support"
          fun bind ((w,child),(representative,certificate)) =
            let val _ = #register rows representative child certificate
            in #entry rows chart sector residue core w child end
          val children_facts = map bind (fields ~~ representatives)
          val checked_support = support core wanted
          val rowT = HOLogic.mk_prodT (natT, @{typ comma_direct_action_expression})
          val rows_term = HOLogic.mk_list rowT row_terms
          val row_pred = Envir.beta_norm
            (@{term "\<lambda>f residue core (wanted,child). comma_direct_source_relation
              (comma_phase_program_entry_core_value_action f residue core wanted) child"} $
              nat sector $ nat residue $ core)
          fun row_fact (item,fact) =
            let
              val expected = HOLogic.mk_Trueprop (Envir.beta_norm (row_pred $ item))
              val conversion = Simplifier.rewrite product_context (Thm.cterm_of ctxt expected)
              val normalized = Utils.exact_prop ctxt "Direct Entry child row"
                (Thm.term_of (Thm.rhs_of conversion)) fact
            in Thm.equal_elim (Thm.symmetric conversion) normalized end
          val row_facts = map row_fact (row_terms ~~ children_facts)
          val children_list = Utils.literal_list_all ctxt "Direct Entry child rows"
            row_pred row_terms row_facts
          val fst_map = @{term "map (fst :: nat \<times> comma_direct_action_expression \<Rightarrow> nat)"} $ rows_term
          val shape_goal = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (fst_map, @{term comma_core_supported_values} $ core))
          val simple = support_context |> Simplifier.add_simp checked_support
          val shape = Utils.prove_exact ctxt "Direct Entry row support" shape_goal
            (fn _ => simp_tac simple 1)
          val unique_goal = HOLogic.mk_Trueprop (@{term "distinct :: nat list \<Rightarrow> bool"} $ fst_map)
          val unique = Utils.prove_exact ctxt "Direct Entry row uniqueness" unique_goal
            (fn _ => simp_tac (uniqueness_context |> Simplifier.add_simp checked_support) 1)
          val admission_goal = HOLogic.mk_Trueprop
            (@{term comma_phase_program_structurally_admitted} $ program)
          val admission = Utils.prove_exact ctxt "Direct Entry admission" admission_goal
            (fn _ => simp_tac (admission_context |> Simplifier.add_simp checked_support) 1)
          val expected = HOLogic.mk_Trueprop
            (@{term comma_direct_program_relation} $ program $ expression_body)
          val rule = Drule.infer_instantiate ctxt
            [(("f",0),Thm.cterm_of ctxt (nat sector)),
             (("d",0),Thm.cterm_of ctxt (nat digit)),
             (("residue",0),Thm.cterm_of ctxt (nat residue)),
             (("core",0),Thm.cterm_of ctxt core),
             (("rows",0),Thm.cterm_of ctxt rows_term)]
            @{thm comma_direct_program_entry_rows}
          val theorem = (rule OF [admission,shape,unique,children_list])
            |> Utils.exact_prop ctxt "Direct Entry program binding" expected
          val theorem = fold_expression ctxt "Direct Entry program binding"
            @{term comma_direct_program_relation} program expression expression_definition theorem
          val _ = issued := !issued+1
        in theorem end
      fun statistics () = "direct_entry_bindings=" ^ Int.toString (!issued) ^ " " ^
        #statistics rows ()
    in {certify=certify,prepare= #prepare rows,representative= #representative rows,
      support=support,statistics=statistics} end
end
