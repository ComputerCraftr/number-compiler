structure Comma_Phase_134_Certificate =
struct
  structure Candidate = Comma_Phase_134_Proposals
  fun nat n = HOLogic.mk_number @{typ nat} n
  fun prove ctxt proposition tactic = Goal.prove ctxt [] [] proposition (fn _ => tactic)
  fun report phase stage start =
    Comma_Proof_Profile.report
      ("Continue phase " ^ Int.toString phase ^ " " ^ stage ^ " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms start)
  fun run lthy =
    let
      val started = Time.now ()
      val ctxt = Local_Theory.target_of lthy
      val certify_step = Comma_Semantic_Program_Arithmetic.class_step_store ctxt
      val action_type = @{typ "nat comma_phase_class_action"}
      fun action (p, Candidate.Continue c) =
            @{term "Comma_Phase_Class_Continue :: nat => nat => nat comma_phase_class_action"} $
              nat ((p+1) mod 924) $ nat c
        | action (_, Candidate.Fork a) =
            Const (@{const_name Comma_Phase_Class_Fork}, @{typ nat} --> @{typ nat} --> action_type) $
              nat a $ nat 0
        | action (_, Candidate.Landmine j) =
            Const (@{const_name Comma_Phase_Class_Landmine}, @{typ nat} --> action_type) $ nat j
      fun certificate (key as (p,_),result) = certify_step key (action (p,result))
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
      val basis = put_simpset HOL_basic_ss ctxt
      val power = @{term "comma_phase_class_continue_power
        comma_semantic_phase_program_class_step"}
      val none = @{term "None :: (nat \<times> nat) option"}
      val roots = 0 upto 45
      val root_list = HOLogic.mk_list @{typ nat} (map nat roots)
      val range = prove ctxt
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (@{term "[0..<46::nat]"},root_list)))
        (simp_tac (arithmetic |> Simplifier.add_simp @{thm upt_rec}) 1)
      fun unary n = if n=0 then nat 0
        else @{term Suc} $ unary (n-1)
      fun inst cxt key value rule =
        Drule.infer_instantiate cxt [((key,0), Thm.cterm_of cxt value)] rule
      fun batch (phase,depth,proposals) lthy =
        let
          val first_visit = Time.now ()
          val _ = report phase ("class steps=" ^ Int.toString (length proposals) ^ " start") started
          fun verify (index,row) =
            let
              val fact = certificate row
              val _ = if (index+1) mod 16 = 0 then
                report phase ("verified=" ^ Int.toString (index+1)) first_visit else ()
            in fact end
          val facts = map_index verify proposals
          val _ = report phase ("step facts=" ^ Int.toString (length facts)) first_visit
          val compose = Time.now ()
          val closure_context = basis
            |> Simplifier.add_simps @{thms
              comma_phase_class_continue_power_Suc comma_phase_class_continue_power_0
              comma_phase_class_continue_option_step_def prod.case
              comma_phase_class_action.case Option.bind.simps}
            |> Simplifier.add_simps facts
          val depth_equation = prove ctxt
            (HOLogic.mk_Trueprop (HOLogic.mk_eq (unary depth,nat depth)))
            (simp_tac arithmetic 1)
          fun check_root cid =
            let
              val point = HOLogic.mk_prod (nat phase,nat cid)
              val goal = HOLogic.mk_Trueprop (HOLogic.mk_eq (power $ unary depth $ point,none))
              val fact = prove ctxt goal (simp_tac closure_context 1)
            in Simplifier.rewrite_rule basis [mk_meta_eq depth_equation] fact end
          val root_facts = map check_root roots
          val _ = report phase "proved 46 point powers" compose
          val free = Free ("cid",@{typ nat})
          val predicate = Term.lambda free
            (HOLogic.mk_eq (power $ nat depth $ HOLogic.mk_prod (nat phase,free),none))
          val nil_rule = inst ctxt "P" predicate @{thm comma_phase_134_list_nil}
          val cons_rule = inst ctxt "P" predicate @{thm comma_phase_134_list_cons}
          val all_roots = fold_rev (fn fact => fn tail => cons_rule OF [fact,tail]) root_facts nil_rule
          val ranged = Simplifier.rewrite_rule basis [Thm.symmetric (mk_meta_eq range)] all_roots
          val result = @{thm comma_phase_134_intro} OF [ranged]
          val _ = report phase "assembled all 46 roots" compose
          val _ = (case Exn.capture certificate ((phase,0),Candidate.Fork 0) of
              Exn.Exn (ERROR _) => ()
            | Exn.Exn exn => Exn.reraise exn
            | Exn.Res _ => error "Continue phase probe admitted a false terminal")
          val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
            "Single phase Continue barrier" [result]
          val name = "comma_continue_phase_" ^ Int.toString phase ^ "_checked"
          val (_, lthy') = Local_Theory.note ((Binding.name name, []), [result]) lthy
          val _ = report phase "total" started
        in lthy' end
    in fold batch Candidate.batches lthy end
end
