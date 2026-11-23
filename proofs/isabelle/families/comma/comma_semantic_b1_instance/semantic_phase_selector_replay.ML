(* Checked replay of shared CRT phase charts and their sparse slot bindings. *)
structure Comma_Semantic_Phase_Selector_Replay =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Bind = Comma_CRT_MDD_Bind_Replay
  structure Operation = Comma_CRT_MDD_Operation_Replay
  structure Point = Comma_CRT_MDD_Point_Eval
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Candidate = Comma_Semantic_Phase_Selector
  val natT = @{typ nat}
  val boolT = @{typ bool}
  fun nat n = HOLogic.mk_number natT n
  fun tp t = HOLogic.mk_Trueprop t
  fun instantiate ctxt bindings theorem = Drule.infer_instantiate ctxt
    (map (fn (name,term) => ((name,0),Thm.cterm_of ctxt term)) bindings) theorem
  fun reachable period =
    (case period of 1 => 1 | 2 => 4 | 3 => 3 | 6 => 12
      | 22 => 44 | 28 => 28 | _ => error "Unsupported phase period")

  fun make ctxt store arena bind_replay shift_replay =
    let
      val wf = Store.wellformed store
      val phase = Free ("phase_selector_phase",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      val point = Free ("phase_selector_point",natT)
      val base_cache = Unsynchronized.ref (Inttab.empty:thm Inttab.table)
      val table_cache = Unsynchronized.ref
        (Termtab.empty:(thm * int list) Termtab.table)
      val base_builds = Unsynchronized.ref 0
      val base_hits = Unsynchronized.ref 0
      val point_proofs = Unsynchronized.ref 0
      val chart_proofs = Unsynchronized.ref 0
      val scalar = Comma_Entry_Arithmetic.natural_context ctxt
      val eval_const = @{term "comma_crt_mdd_eval_phase :: nat list => nat comma_crt_mdd_node list => nat => nat => nat option"}
      fun eval_term root p = eval_const $ Store.radices store $ Store.table store $ p $ root
      fun eval root p = eval_term (nat root) p
      fun some t = @{term "Some :: nat => nat option"} $ t
      fun suc t = @{term Suc} $ t
      fun mod_nat x y = HOLogic.mk_binop @{const_name modulo} (x,y)
      fun eq (x,y) = HOLogic.mk_eq (x,y)
      fun checked label expected theorem = Utils.exact_prop ctxt label expected theorem
      fun close label goal theorem =
        checked label (Logic.all phase goal) (Thm.forall_intr phase_ct theorem)
      fun prove label proposition facts extra =
        let
          val goal = tp proposition
          val context = scalar |> Simplifier.add_simps facts |> Simplifier.add_simps extra
          val theorem = Goal.prove ctxt [] [] goal (fn _ => simp_tac context 1)
        in checked label goal theorem end
      fun interval_list_all label bound predicate literal =
        let
          val upt = Const (@{const_name upt},natT --> natT --> @{typ "nat list"}) $
            nat 0 $ nat bound
          val interval_conversion = Simplifier.rewrite
            (scalar |> Simplifier.add_simp @{thm upt_rec}) (Thm.cterm_of ctxt upt)
          val expected = HOLogic.mk_list natT (map nat (0 upto (bound-1)))
          val _ = if Thm.term_of (Thm.rhs_of interval_conversion) aconv expected
            then () else error (label ^ " interval did not normalize to its literal rows")
          val all_head = Const (@{const_name list_all},
            (natT --> boolT) --> @{typ "nat list"} --> boolT) $ predicate
          val all_conversion = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt all_head)) interval_conversion
          val prop_conversion = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt
              (Const (@{const_name Trueprop},boolT --> @{typ prop})))) all_conversion
        in Thm.equal_elim (Thm.symmetric prop_conversion) literal end
      fun base_certificate period root =
        let
          val root_id = Store.action_index store root
          val goal = tp (eq (eval root_id phase,some (suc (mod_nat phase (nat period)))))
          val expected = Logic.all phase goal
        in case Inttab.lookup (!base_cache) period of
          SOME theorem => (base_hits := !base_hits+1;
            checked "Cached phase-selector base" expected theorem)
        | NONE =>
            let
              val whole = reachable period
              val shift_fact = Operation.shift_eval_phase shift_replay whole root_id root_id
              val periodic_point = instantiate ctxt [("phase",point)] shift_fact RS @{thm sym}
              val periodic = Thm.forall_intr (Thm.cterm_of ctxt point) periodic_point
              val predicate = Term.lambda point
                (eq (eval root_id point,some (suc (mod_nat point (nat period)))))
              fun row i =
                let
                  val result = Point.prove store i root_id
                  val _ = if #payload result = i mod period + 1 then ()
                    else error "Phase-selector base has an incorrect point value"
                  val proposition = Envir.beta_norm (predicate $ nat i)
                  val theorem = prove "Phase-selector base point" proposition
                    [#theorem result] []
                  val _ = point_proofs := !point_proofs+1
                in theorem end
              val all = Utils.literal_list_all ctxt "Phase-selector base points" predicate
                (map nat (0 upto (whole-1))) (map row (0 upto (whole-1)))
              val rows = interval_list_all "Phase-selector base point interval"
                whole predicate all
              val positive = prove "Phase-selector reachable period positive"
                (HOLogic.mk_binrel @{const_name less} (nat 0,nat whole)) [] []
              val divisor = prove "Phase-selector period divides reachable period"
                (HOLogic.mk_binrel @{const_name dvd} (nat period,nat whole)) []
                  @{thms dvd_eq_mod_eq_0}
              val rule = instantiate ctxt
                [("evaluate",Term.lambda point (eval root_id point)),("P",nat whole),
                 ("T",nat period),("phase",phase)] @{thm comma_phase_selector_finite_period}
                |> Conv.fconv_rule Drule.beta_eta_conversion
              val proof = fold (fn fact => fn theorem => Thm.implies_elim theorem fact)
                [positive,divisor,periodic,rows] rule
              val theorem = close "Phase-selector base" goal proof
              val _ = base_cache := Inttab.update (period,theorem) (!base_cache)
              val _ = base_builds := !base_builds+1
            in theorem end
        end

      fun certify core shift labels ({shift=issued,template}:Candidate.proposal) =
        let
          val {period,offset,base,shifted,root,fallback,rows}:Candidate.template = template
          val _ = if shift=issued then () else error "Phase selector shift authority changed"
          val base_id = Store.action_index store base
          val shifted_id = Store.action_index store shifted
          val result_id = Store.action_index store root
          val fallback_id = Store.action_index store fallback
          val indexed_rows = map (fn (label,target) =>
            (label,Store.action_index store target)) rows
          val bind = Bind.certify_bind bind_replay (shifted_id,fallback_id,indexed_rows)
          val base_proof = base_certificate period base
          val shift_fact = instantiate ctxt [("phase",phase)]
            (Operation.shift_eval_phase shift_replay offset base_id shifted_id)
          val at_shift = Thm.forall_elim (Thm.cterm_of ctxt
            (HOLogic.mk_binop @{const_name Groups.plus} (phase,nat offset))) base_proof
          val shifted_proof = @{thm trans} OF [shift_fact,at_shift]
          val slot = mod_nat
            (HOLogic.mk_binop @{const_name Groups.plus}
              (HOLogic.mk_binop @{const_name Groups.plus} (phase,nat shift),nat 919))
            (nat period)
          val source_goal = tp (eq (eval shifted_id phase,some (suc slot)))
          val offset_value = mod_nat
            (HOLogic.mk_binop @{const_name Groups.plus} (nat shift,nat 919)) (nat period)
          val offset_fact = prove "Phase selector normalized offset"
            (eq (nat offset,offset_value)) [] []
          val offset_rule = instantiate ctxt
            [("offset",nat offset),("shift",nat shift),("T",nat period),("phase",phase)]
            @{thm comma_phase_selector_offset}
          val offset_theorem = Thm.implies_elim offset_rule offset_fact
          val source = Goal.prove ctxt [] [] source_goal (fn _ =>
            simp_tac (put_simpset HOL_basic_ss ctxt |>
              Simplifier.add_simps [shifted_proof,offset_theorem]) 1)
          val _ = checked "Phase selector shifted slot" (Logic.all phase source_goal)
            (Thm.forall_intr phase_ct source)
          val pairT = HOLogic.mk_prodT (natT,natT)
          val mapping = HOLogic.mk_list pairT
            (map (fn (a,b) => HOLogic.mk_prod (nat a,nat b)) indexed_rows)
          val label_term = HOLogic.mk_list natT (map nat labels)
          val index = Free ("phase_selector_index",natT)
          val selected_term = @{term "map_of :: (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat option"} $
            mapping $ suc index
          val item = Free ("phase_selector_target",natT)
          val target = @{term "case_option :: nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat option \<Rightarrow> nat"} $
            nat fallback_id $ Term.lambda item item $ selected_term
          val table = @{term comma_phase_selector_table} $ core $ label_term
          val table_key = HOLogic.mk_prod (core,label_term)
          val (table_fact,table_values) =
            (case Termtab.lookup (!table_cache) table_key of
              SOME cached => cached
            | NONE =>
                let
                  val table_context = scalar |> Simplifier.add_simps
                    @{thms comma_phase_selector_table_def comma_phase_core_modulus.simps
                      comma_core_period_def list.simps list.size list.map set_simps
                      insert_iff empty_iff if_True if_False
                      Let_def upt_rec nth_map nth_upt power_numeral_even
                      power_numeral_odd power_0 power_one_right power_Suc0_right}
                  val conversion = Simplifier.rewrite table_context (Thm.cterm_of ctxt table)
                  val terms = HOLogic.dest_list (Thm.term_of (Thm.rhs_of conversion))
                  fun dest_value term =
                    (Utils.dest_nat "Phase selector table value" natT term
                      handle ERROR message =>
                        error (message ^ ": " ^ Syntax.string_of_term
                          (Config.put show_types true ctxt) term))
                  val values = map dest_value terms
                  val _ = if length values = period then ()
                    else error "Phase selector output table has the wrong period"
                  val equation = conversion RS @{thm meta_eq_to_obj_eq}
                  val _ = Utils.ensure_closed_context ctxt "Phase selector output table" equation
                  val cached = (equation,values)
                  val _ = table_cache := Termtab.update (table_key,cached) (!table_cache)
                in cached end)
          val _ = if length table_values = period then ()
            else error "Cached phase selector output table has a different period"
          val table_goal = tp (eq
            (table,HOLogic.mk_list natT (map nat table_values)))
          val _ = Utils.exact_prop ctxt "Phase selector output table"
            table_goal table_fact
          val nth = Const (@{const_name nth}, @{typ "nat list"} --> natT --> natT)
          val slot_body = eq (eval_term target phase,some (nth $ table $ index))
          val every_phase = Const (@{const_name All},(natT --> boolT) --> boolT) $
            Term.lambda phase slot_body
          val predicate = Term.lambda index every_phase
          val rules = @{thms comma_phase_selector_table_def
            comma_phase_core_modulus.simps comma_core_period_def
            list.simps list.size list.map set_simps map_of.simps map_of_Cons_code
            option.simps Let_def upt_rec nth_map nth_upt
            nth_Cons_0 nth_Cons_Suc nth_Cons_numeral nth_Cons'}
          fun output_row i =
            let
              val target_id = the_default fallback_id (AList.lookup (op =) indexed_rows (i+1))
              val expected_value = List.nth (table_values,i)
              val _ = (case Store.node store target_id of
                Store.Leaf value => if value=expected_value then ()
                  else error "Phase selector slot target has an incorrect value"
              | Store.Branch _ => error "Phase selector slot target is not a leaf")
              val leaf = Store.phase_leaf store target_id
              val proposition = tp (Envir.beta_norm (predicate $ nat i))
              val context = scalar |> Simplifier.add_simps [leaf,table_fact] |>
                Simplifier.add_simps @{thms map_of_Cons_code option.simps
                  nth_Cons_0 nth_Cons_Suc nth_Cons_numeral nth_Cons'}
              val theorem = Goal.prove ctxt [] [] proposition (fn {context=goal,...} =>
                resolve_tac goal [@{thm allI}] 1 THEN simp_tac context 1)
            in checked "Phase selector slot output" proposition theorem end
          val slots = 0 upto (period-1)
          val literal_rows = Utils.literal_list_all ctxt "Phase selector slot outputs"
            predicate (map nat slots) (map output_row slots)
          val interval_rows = interval_list_all "Phase selector slot output interval"
            period predicate literal_rows
          val output_rule = instantiate ctxt
            [("Q",Term.lambda index (Term.lambda phase slot_body)),
             ("T",nat period),("phase",phase)]
            @{thm comma_phase_selector_slot_rows}
          val output_rule = (output_rule OF [interval_rows])
            |> Conv.fconv_rule Drule.beta_eta_conversion
          val output_rule = instantiate ctxt [("i",index)] output_rule
            |> Thm.forall_intr (Thm.cterm_of ctxt index)
          val rule = instantiate ctxt
            [("radices",Store.radices store),("nodes",Store.table store),
             ("core",core),("wanteds",label_term),("phase",phase),("shift",nat shift),
             ("source",nat shifted_id),("result",nat result_id),
             ("fallback",nat fallback_id),("mapping",mapping)]
            @{thm comma_phase_selector_bind_exact_expanded}
          val output_premise = List.nth (Thm.prems_of rule,3)
          val period_expression = @{term comma_core_period} $
            (@{term comma_phase_core_modulus} $ core)
          val period_fact = prove "Phase selector core period"
            (eq (period_expression,nat period)) []
            @{thms comma_phase_core_modulus.simps comma_core_period_def}
          val output_conversion = Conv.top_sweep_conv
            (K (Conv.rewr_conv (period_fact RS @{thm eq_reflection}))) ctxt
            (Thm.cterm_of ctxt output_premise)
          val normalized_output = Thm.term_of (Thm.rhs_of output_conversion)
          val _ = if Thm.prop_of output_rule aconv normalized_output then ()
            else error ("Phase selector output premise differs: " ^
              Syntax.string_of_term ctxt (Thm.prop_of output_rule) ^ " versus " ^
              Syntax.string_of_term ctxt normalized_output)
          val output_fact = Thm.equal_elim (Thm.symmetric output_conversion) output_rule
          val source_premise = List.nth (Thm.prems_of rule,2)
          val source_fact = Goal.prove ctxt [] [] source_premise (fn _ =>
            simp_tac (scalar |> Simplifier.add_simp source |> Simplifier.add_simps rules) 1)
          val facts = [wf,bind,source_fact,output_fact]
          val _ = ListPair.appEq (fn (prem,fact) =>
            if prem aconv Thm.prop_of fact then ()
            else error ("Phase selector binding premise differs: " ^
              Syntax.string_of_term ctxt prem ^ " versus " ^
              Syntax.string_of_term ctxt (Thm.prop_of fact)))
            (Thm.prems_of rule,facts)
          val theorem = fold (fn fact => fn current => Thm.implies_elim current fact)
            facts rule
          val goal = tp (eq (eval result_id phase,
            some (@{term comma_direct_entry_selector_code} $ core $ label_term $
              phase $ nat shift)))
          val theorem = close "Checked phase selector chart" goal theorem
          val _ = chart_proofs := !chart_proofs+1
        in theorem end
      fun statistics () =
        "phase_base_proofs=" ^ Int.toString (!base_builds) ^
        " phase_base_hits=" ^ Int.toString (!base_hits) ^
        " phase_point_proofs=" ^ Int.toString (!point_proofs) ^
        " phase_chart_proofs=" ^ Int.toString (!chart_proofs)
    in {certify=certify,statistics=statistics} end
end
