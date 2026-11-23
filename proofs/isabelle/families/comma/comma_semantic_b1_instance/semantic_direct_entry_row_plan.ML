(* Checked factored Entry row equations shared by selector and direct owners. *)
functor Comma_Direct_Entry_Row_Plan (
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
  val natT = @{typ nat}
  val actionT = @{typ comma_source_continuation_action}
  fun nat n = HOLogic.mk_number natT n
  fun const name T args =
    list_comb (Const (name,fold_rev (curry (op -->)) (map fastype_of args) T),args)
  (* Each candidate key is a proposed (sector,digit,port-row) action class.
     Its representative equation is admitted by the kernel before it can be
     transported to another source.  The proposed key itself is not evidence. *)
  fun make ctxt (computation: Compiler.computation)
      (proposed: (term * Compiler.entry_representative) list) =
    let
      val representatives = fold Termtab.update
        proposed Termtab.empty
      val proofs = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val misses = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val representative_elapsed = Unsynchronized.ref Time.zeroTime
      fun timed elapsed f =
        let val start = Time.now ()
            val outcome = Exn.capture f ()
            val _ = elapsed := Time.+ (!elapsed,Time.- (Time.now (),start))
        in Exn.release outcome end
      val ports = fixed_entry_port_conversion_plan ctxt
      val parameters = core_parameter_conversion_plan ctxt
      val row_context = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_proc (#plain_procedure ports)
        |> Simplifier.add_proc (#plain_procedure parameters)
        |> Simplifier.add_simps @{thms comma_entry_row_action_simp_rules}
      val evaluator = Simplifier.rewrite row_context
      val product_context = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_simps @{thms prod.case}
      val sector_facts = Unsynchronized.ref (Inttab.empty: thm list Inttab.table)
      fun sector f =
        (case Inttab.lookup (!sector_facts) f of
          SOME facts => facts
        | NONE =>
            let
              fun prove proposition = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop proposition)
                (fn {context,...} => simp_tac
                  (Comma_Entry_Arithmetic.natural_context context) 1)
              val facts = [prove (HOLogic.mk_binrel @{const_name less_eq} (nat 1,nat f)),
                prove (HOLogic.mk_binrel @{const_name less_eq} (nat f,nat 9))]
              val _ = sector_facts := Inttab.update (f,facts) (!sector_facts)
            in facts end)
      (* Ordered lift charts are source-independent.  Each exact source gets
         one checked offset and one ordered key theorem before its rows. *)
      val period_cache = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val lift_cache = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val chart_builds = Unsynchronized.ref 0
      val source_builds = Unsynchronized.ref 0
      val row_requests = Unsynchronized.ref 0
      val chart_elapsed = Unsynchronized.ref Time.zeroTime
      val period_context = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simp @{thm comma_finite_period_fast_def}
        |> Simplifier.add_simps @{thms list.simps nth_Cons_0 nth_Cons_Suc nth_Cons_numeral nth_Cons'}
      val vector_context = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_proc (#plain_procedure parameters)
        |> Simplifier.add_simp @{thm comma_entry_lift_chart_def}
        |> Simplifier.add_simps @{thms comma_phase_core_modulus.simps list.simps list.map}
      val source_context = Comma_Entry_Arithmetic.signed_context ctxt
        |> Simplifier.add_proc (#plain_procedure ports)
        |> Simplifier.add_simp @{thm comma_entry_source_chart_def}
      val chart_context = Comma_Entry_Arithmetic.signed_context ctxt
        |> Simplifier.add_simps @{thms list.simps list.map prod.case fst_conv snd_conv}
      val nth_context = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_simps @{thms list.map nth_Cons_0 nth_Cons_Suc}
      fun unary_index 0 = nat 0
        | unary_index n = HOLogic.mk_Suc (unary_index (n-1))
      val keyT = @{typ "nat \<times> nat \<times> nat"}
      fun certified cache label context term =
        (case Termtab.lookup (!cache) term of
          SOME theorem => Utils.exact_prop ctxt label
            (Logic.mk_equals (term,Thm.term_of (Thm.rhs_of theorem))) theorem
        | NONE =>
            let val theorem = Simplifier.rewrite context (Thm.cterm_of context term)
                  |> Utils.ensure_closed_context ctxt label
                val _ = cache := Termtab.update (term,theorem) (!cache)
            in theorem end)
      fun lift_chart f digit core wanted_term =
        let
          val period_term = @{term comma_finite_period_fast} $ nat f $ digit
          val period_eq = certified period_cache "Entry chart period" period_context period_term
          val P = Thm.term_of (Thm.rhs_of period_eq)
          val _ = Utils.dest_nat "Entry chart period" natT P
          val lift_term = @{term comma_entry_lift_chart} $ P $ core $ wanted_term
          val prior = Termtab.defined (!lift_cache) lift_term
          val lift_eq = certified lift_cache "Entry lift chart" vector_context lift_term
          val _ = if prior then () else chart_builds := !chart_builds + 1
        in (period_eq,P,lift_eq) end
      fun prewarm f residue core = timed chart_elapsed (fn () =>
        let
          val wanted = #supported_values computation core
          val wanted_term = HOLogic.mk_list natT (map nat wanted)
          val _ = lift_chart f (nat (residue mod 10)) core wanted_term
        in () end)
      fun prepare f residue core = timed chart_elapsed (fn () =>
          let
            val wanted = #supported_values computation core
            val _ = if length wanted = length (distinct (op =) wanted) then () else error "Entry chart support is not distinct"
            val wanted_term = HOLogic.mk_list natT (map nat wanted)
            val digit_term = HOLogic.mk_binop @{const_name modulo} (nat residue,nat 10)
            val digit_eq = Simplifier.rewrite period_context (Thm.cterm_of period_context digit_term)
            val digit = Thm.term_of (Thm.rhs_of digit_eq)
            val _ = Utils.dest_nat "Entry chart digit" natT digit
            val source_period = @{term comma_finite_period_fast} $ nat f $ digit_term
            val (period_eq,P,lift_eq) = lift_chart f digit core wanted_term
            val lift_values = HOLogic.dest_list (Thm.term_of (Thm.rhs_of lift_eq))
            val _ = if length lift_values = length wanted then ()
              else error "Entry lift chart changed its ordered length"
            val source_term = @{term comma_entry_source_chart} $ nat f $ nat residue $ P
            val source_eq = Simplifier.rewrite source_context (Thm.cterm_of source_context source_term)
              |> Utils.ensure_closed_context ctxt "Entry source chart"
            val _ = Utils.dest_nat "Entry normalized source" natT (Thm.term_of (Thm.rhs_of source_eq))
            val positive_goal = HOLogic.mk_Trueprop
              (@{term "\<lambda>p::nat. 0 < p div 10"} $ source_period |> Envir.beta_norm)
            val positive = Utils.prove_exact ctxt "Entry positive chart period" positive_goal
              (fn _ => simp_tac (period_context |> Simplifier.add_simps [digit_eq,period_eq]) 1)
            val rule = Drule.infer_instantiate ctxt
              [(("f",0),Thm.cterm_of ctxt (nat f)),
               (("residue",0),Thm.cterm_of ctxt (nat residue)),
               (("core",0),Thm.cterm_of ctxt core),
               (("wanted",0),Thm.cterm_of ctxt wanted_term)]
              @{thm comma_entry_key_chart_exact} OF (sector f @ [positive])
            val initial = rule RS @{thm eq_reflection}
            val compact = chart_context |> Simplifier.add_simps [digit_eq,period_eq,lift_eq,source_eq]
            val evaluated = Simplifier.rewrite compact (Thm.rhs_of initial)
            val combined = Thm.transitive initial evaluated
            val key_fn = @{term comma_entry_core_action_key} $ nat f $ nat residue $ core
            val proposed = map (#entry_action_key computation f residue core) wanted
            val key_list = HOLogic.mk_list keyT proposed
            val key_map = @{term "map :: (nat \<Rightarrow> (nat \<times> nat \<times> nat)) \<Rightarrow> nat list \<Rightarrow> (nat \<times> nat \<times> nat) list"} $ key_fn $ wanted_term
            val chart = Utils.exact_prop ctxt "Ordered Entry key chart"
              (Logic.mk_equals (key_map,key_list)) combined
            val nth = @{term "nth :: (nat \<times> nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat)"}
            fun one (index,(value,key)) table =
              let
                val selected = Thm.combination
                  (Thm.combination (Thm.reflexive (Thm.cterm_of ctxt nth)) chart)
                  (Thm.reflexive (Thm.cterm_of ctxt (unary_index index)))
                val lhs = Simplifier.rewrite nth_context (Thm.lhs_of selected)
                val rhs = Simplifier.rewrite nth_context (Thm.rhs_of selected)
                val fact = Thm.transitive (Thm.symmetric lhs) (Thm.transitive selected rhs)
                val request = key_fn $ nat value
                val exact = Utils.exact_prop ctxt "Entry chart row"
                  (Logic.mk_equals (request,key)) fact
              in Inttab.update (value,exact) table end
            val rows = fold one (map_index I (wanted ~~ proposed)) Inttab.empty
            val _ = source_builds := !source_builds + 1
          in rows end)
      fun prove key =
        (case Termtab.lookup (!proofs) key of
          SOME theorem => (hits := !hits + 1; theorem)
        | NONE =>
            let
              val _ = if !misses mod 64=0 then Comma_Proof_Profile.report
                ("Frontier24 representative start count=" ^ Int.toString (!misses+1)) else ()
              val rep = (case Termtab.lookup representatives key of
                SOME value => value
              | NONE => error "Missing canonical Entry action representative")
              val (f,rest) = HOLogic.dest_prod key
              val (digit,row) = HOLogic.dest_prod rest
              val request = const @{const_name comma_entry_row_action} actionT [f,digit,row]
              val raw = timed representative_elapsed
                (fn () => evaluator (Thm.cterm_of row_context request))
              val theorem = raw
              val exact = Utils.exact_prop ctxt "Entry action representative"
                (Logic.mk_equals (request,#action rep)) theorem
              val _ = misses := !misses + 1
              val _ = proofs := Termtab.update (key,exact) (!proofs)
              val _ = if !misses mod 64=0 then Comma_Proof_Profile.report
                ("Frontier24 representative complete count=" ^ Int.toString (!misses)) else ()
            in exact end)
      fun statistics () = "entry_representative_proofs=" ^ Int.toString (!misses) ^
        " entry_representative_hits=" ^ Int.toString (!hits) ^
        " entry_representative_ms=" ^ LargeInt.toString
          (Time.toMilliseconds (!representative_elapsed)) ^
        " entry_chart_ms=" ^ LargeInt.toString (Time.toMilliseconds (!chart_elapsed)) ^
        " entry_lift_charts=" ^ Int.toString (!chart_builds) ^
        " entry_source_charts=" ^ Int.toString (!source_builds) ^
        " entry_chart_row_requests=" ^ Int.toString (!row_requests) ^
        " core_seed_hits=" ^ Int.toString (#seed_hits parameters ())
      val transports = Unsynchronized.ref 0
      fun transport_prepared rows f residue core wanted =
        let
          val key = #entry_action_key computation f residue core wanted
          val rep = (case Termtab.lookup representatives key of
            SOME value => value
          | NONE => error "Missing canonical Entry action transport")
          val request = const @{const_name comma_phase_program_entry_core_value_action}
            actionT [nat f,nat residue,core,nat wanted]
          val key_request = const @{const_name comma_entry_core_action_key}
            (fastype_of key) [nat f,nat residue,core,nat wanted]
          val _ = row_requests := !row_requests + 1
          val key_equation = (case Inttab.lookup rows wanted of
              SOME theorem => theorem | NONE => error "Entry wanted value is not in the ordered chart")
          val _ = Utils.exact_prop ctxt "Entry action key"
            (Logic.mk_equals (key_request,key)) key_equation
          val factor = Drule.infer_instantiate ctxt
            [(("f",0),Thm.cterm_of ctxt (nat f)),
             (("residue",0),Thm.cterm_of ctxt (nat residue)),
             (("core",0),Thm.cterm_of ctxt core),
             (("wanted",0),Thm.cterm_of ctxt (nat wanted))]
            @{thm comma_entry_core_action_row_factor} OF (sector f)
          val factor = factor RS @{thm eq_reflection}
          val key_rewrite = Conv.arg_conv (Conv.rewr_conv key_equation) (Thm.rhs_of factor)
          val case_rewrite = Simplifier.rewrite product_context (Thm.rhs_of key_rewrite)
          val factor = Thm.transitive factor (Thm.transitive key_rewrite case_rewrite)
          val (sector,rest) = HOLogic.dest_prod key
          val (digit,row) = HOLogic.dest_prod rest
          val row_action = const @{const_name comma_entry_row_action} actionT
            [sector,digit,row]
          val _ = Utils.exact_prop ctxt "Entry action row factor"
            (Logic.mk_equals (request,row_action)) factor
          val theorem = Thm.transitive factor (prove key)
          val _ = transports := !transports + 1
          val _ = if !transports mod 128=0 then Comma_Proof_Profile.report
            ("Frontier24 row transports=" ^ Int.toString (!transports)) else ()
        in Utils.exact_prop ctxt "Entry action row transport"
          (Logic.mk_equals (request,#action rep)) theorem end
      fun transport_statistics () = statistics () ^
        " entry_row_transports=" ^ Int.toString (!transports)
    in {prove=prove,prewarm=prewarm,prepare=prepare,transport_prepared=transport_prepared,
      statistics=transport_statistics} end

end
