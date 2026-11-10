theory Comma_Semantic_Predecessor_Certificate
  imports Comma_Semantic_Predecessor_Action
begin

lemma comma_semantic_b1_crt_compose_action_eval:
  assumes child_count: "length children=46"
    and left_wf: "comma_weighted_crt_wellformed (snd left)"
    and children_wf: "\<And>child. child<46 \<Longrightarrow>
      comma_weighted_crt_wellformed (snd (children!child))"
    and left_zero:
      "comma_semantic_b1_crt_action_nonterminal_zero left"
    and children_zero: "\<And>child. child<46 \<Longrightarrow>
      comma_semantic_b1_crt_action_nonterminal_zero (children!child)"
  shows "comma_semantic_b1_crt_action_eval
      (comma_semantic_b1_crt_compose span left children) phase =
    comma_semantic_b1_weighted_word_then span
      (\<lambda>p i. comma_semantic_b1_crt_action_eval left p)
      (\<lambda>p i. comma_semantic_b1_crt_action_eval (children!i) p)
      phase root"
proof -
  obtain control elapsed where left_applied:
      "comma_weighted_crt_apply left phase=Some (control,elapsed)"
    using comma_semantic_b1_crt_action_eval_total[OF left_wf] by blast
  have left_observation:
      "comma_semantic_b1_crt_action_eval left phase=
        comma_semantic_b1_crt_decode control elapsed"
    using comma_semantic_b1_crt_action_eval_decode[OF left_applied] .
  have compose_binding:
      "comma_weighted_crt_apply
        (comma_semantic_b1_crt_compose span left children) phase =
        Option.bind (comma_weighted_crt_eval (snd left) phase)
          (\<lambda>(selected,spent). map_option
            (\<lambda>(result,more). (result,spent+more))
            (comma_weighted_crt_apply
              (case selected of
                Comma_Semantic_B1_CRT_Continue next_child \<Rightarrow>
                  if next_child<length children then
                    comma_semantic_b1_crt_add_stop span
                      (fst (children!next_child),
                        comma_weighted_crt_shift span
                          (snd (children!next_child)))
                  else comma_semantic_b1_crt_invalid_action
              | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow>
                  (fst left,comma_semantic_b1_crt_leaf selected)
              | Comma_Semantic_B1_CRT_Invalid \<Rightarrow>
                  (fst left,comma_semantic_b1_crt_leaf selected)) phase))"
    using child_count
    by (simp only: comma_semantic_b1_crt_compose_def if_P
      comma_weighted_crt_bind_exact)
  show ?thesis
  proof (cases control)
    case (Comma_Semantic_B1_CRT_Continue child)
    have zero_case:
      "case control of
          Comma_Semantic_B1_CRT_Continue root \<Rightarrow> elapsed=0
        | Comma_Semantic_B1_CRT_Invalid \<Rightarrow> elapsed=0
        | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow> True"
      using left_zero[unfolded
          comma_semantic_b1_crt_action_nonterminal_zero_def,
          rule_format, of phase control elapsed]
        left_applied by blast
    have zero: "elapsed=0"
      using zero_case Comma_Semantic_B1_CRT_Continue by simp
    obtain local_height where local_eval:
        "comma_weighted_crt_eval (snd left) phase=
          Some (Comma_Semantic_B1_CRT_Continue child,local_height)"
      and local_total: "fst left+local_height=elapsed"
      using left_applied Comma_Semantic_B1_CRT_Continue
      by (auto simp: comma_weighted_crt_apply_def split: option.splits prod.splits)
    have local_height_zero: "local_height=0"
      using local_total zero by simp
    have left_tree_result:
      "comma_weighted_crt_eval (snd left) phase=
        Some (Comma_Semantic_B1_CRT_Continue child,0)"
      using local_eval local_height_zero by simp
    show ?thesis
    proof (cases "child<46")
      case False
      have invalid_applied:
        "comma_weighted_crt_apply comma_semantic_b1_crt_invalid_action phase=
          Some (Comma_Semantic_B1_CRT_Invalid,0)"
        by (simp only: comma_semantic_b1_crt_invalid_action_def
          comma_semantic_b1_crt_leaf_apply)
      have compose_invalid:
        "comma_weighted_crt_apply
          (comma_semantic_b1_crt_compose span left children) phase=
            Some (Comma_Semantic_B1_CRT_Invalid,0)"
        using compose_binding left_tree_result child_count False invalid_applied
        by (simp only: Option.bind_lunit prod.case case_prod_Pair
          comma_semantic_b1_crt_control.case if_False option.map add_0_left)
      show ?thesis using left_observation compose_invalid
        Comma_Semantic_B1_CRT_Continue False
        by (simp add: comma_semantic_b1_crt_action_eval_def
          comma_semantic_b1_crt_decode.simps
          comma_semantic_b1_weighted_word_then.simps)
    next
      case True
      let ?right = "children!child"
      have right_wf: "comma_weighted_crt_wellformed (snd ?right)"
        by (rule children_wf[OF True])
      obtain next_control next_height where right_applied:
          "comma_weighted_crt_apply ?right (phase+span)=
            Some (next_control,next_height)"
        using comma_semantic_b1_crt_action_eval_total[OF right_wf] by blast
      have shifted_applied:
          "comma_weighted_crt_apply
            (fst ?right,comma_weighted_crt_shift span (snd ?right)) phase=
              Some (next_control,next_height)"
        using right_applied comma_weighted_crt_shift_exact[OF right_wf, of span phase]
        by (simp add: comma_weighted_crt_apply_def)
      have shifted_zero:
          "comma_semantic_b1_crt_action_nonterminal_zero
            (fst ?right,comma_weighted_crt_shift span (snd ?right))"
        using children_zero[OF True] right_wf
        unfolding comma_semantic_b1_crt_action_nonterminal_zero_def
        by (auto simp: comma_weighted_crt_apply_def
            comma_weighted_crt_shift_exact)
      have shifted_zero_nonterminal:
          "(\<exists>root. next_control=Comma_Semantic_B1_CRT_Continue root) \<or>
            next_control=Comma_Semantic_B1_CRT_Invalid
            \<Longrightarrow> next_height=0"
      proof -
        assume next_control_nonterminal:
            "(\<exists>root. next_control=Comma_Semantic_B1_CRT_Continue root) \<or>
              next_control=Comma_Semantic_B1_CRT_Invalid"
        have pointwise:
            "case next_control of
               Comma_Semantic_B1_CRT_Continue root \<Rightarrow> next_height=0
             | Comma_Semantic_B1_CRT_Invalid \<Rightarrow> next_height=0
             | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow> True"
          using shifted_zero shifted_applied
          unfolding comma_semantic_b1_crt_action_nonterminal_zero_def
          by blast
        show "next_height=0"
          using pointwise next_control_nonterminal by (cases next_control) auto
      qed
      have add_stop:
          "comma_weighted_crt_apply
            (comma_semantic_b1_crt_add_stop span
              (fst ?right,comma_weighted_crt_shift span (snd ?right))) phase=
             Some (next_control,
               (case next_control of
                  Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow> next_height+span
                | _ \<Rightarrow> 0))"
        by (rule comma_semantic_b1_crt_add_stop_exact
          [OF shifted_applied shifted_zero_nonterminal])
      have compose_apply:
          "comma_weighted_crt_apply
            (comma_semantic_b1_crt_compose span left children) phase=
             Some (next_control,
               (case next_control of
                  Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow> next_height+span
                | _ \<Rightarrow> 0))"
        using compose_binding left_tree_result add_stop True child_count
        by (simp only: Option.bind_lunit prod.case case_prod_Pair
          comma_semantic_b1_crt_control.case if_True option.map option.map_id
          add_0_left add_stop child_count)
      have right_periodic:
          "comma_weighted_crt_apply ?right ((phase+span) mod 924)=
            comma_weighted_crt_apply ?right (phase+span)"
        using comma_weighted_crt_eval_mod_924[OF right_wf, of "phase+span"]
        by (simp add: comma_weighted_crt_apply_def)
      have right_observation:
          "comma_semantic_b1_crt_action_eval ?right
              ((phase+span) mod 924)=
            comma_semantic_b1_crt_decode next_control next_height"
        using right_applied right_periodic
        by (simp add: comma_semantic_b1_crt_action_eval_def)
      show ?thesis
        using left_observation compose_apply right_observation
          Comma_Semantic_B1_CRT_Continue True zero shifted_zero_nonterminal
        by (cases next_control)
          (auto simp: comma_semantic_b1_crt_action_eval_def
            comma_semantic_b1_crt_decode.simps
            comma_semantic_b1_weighted_word_then.simps algebra_simps)
    qed
  next
    case (Comma_Semantic_B1_CRT_Stop terminal)
    obtain local_height where local_eval:
        "comma_weighted_crt_eval (snd left) phase=
          Some (Comma_Semantic_B1_CRT_Stop terminal,local_height)"
      and local_total: "fst left+local_height=elapsed"
      using left_applied Comma_Semantic_B1_CRT_Stop
      by (auto simp: comma_weighted_crt_apply_def
        split: option.splits prod.splits)
    have stop_leaf_applied:
        "comma_weighted_crt_apply
          (fst left,comma_semantic_b1_crt_leaf
            (Comma_Semantic_B1_CRT_Stop terminal)) phase=
          Some (Comma_Semantic_B1_CRT_Stop terminal,fst left)"
      by (simp add: comma_weighted_crt_apply_def
        comma_semantic_b1_crt_leaf_def)
    have composed_stop_height:
        "comma_weighted_crt_apply
          (comma_semantic_b1_crt_compose span left children) phase=
          Some (Comma_Semantic_B1_CRT_Stop terminal,local_height+fst left)"
      using compose_binding local_eval stop_leaf_applied
      by (simp only: Option.bind_lunit prod.case case_prod_Pair
        comma_semantic_b1_crt_control.case option.map)
    have composed_stop_applied:
        "comma_weighted_crt_apply
          (comma_semantic_b1_crt_compose span left children) phase=
          Some (Comma_Semantic_B1_CRT_Stop terminal,elapsed)"
      using composed_stop_height local_total by (simp add: algebra_simps)
    have compose_stop:
      "comma_semantic_b1_crt_action_eval
         (comma_semantic_b1_crt_compose span left children) phase =
       comma_semantic_b1_crt_action_eval left phase"
      using composed_stop_applied left_applied Comma_Semantic_B1_CRT_Stop
      by (simp add: comma_semantic_b1_crt_action_eval_def)
    show ?thesis using compose_stop left_observation
      Comma_Semantic_B1_CRT_Stop
      by (simp add: comma_semantic_b1_weighted_word_then.simps)
  next
    case Comma_Semantic_B1_CRT_Invalid
    have zero_case:
      "case control of
          Comma_Semantic_B1_CRT_Continue root \<Rightarrow> elapsed=0
        | Comma_Semantic_B1_CRT_Invalid \<Rightarrow> elapsed=0
        | Comma_Semantic_B1_CRT_Stop terminal \<Rightarrow> True"
      using left_zero[unfolded
          comma_semantic_b1_crt_action_nonterminal_zero_def,
          rule_format, of phase control elapsed]
        left_applied by blast
    have elapsed_zero: "elapsed=0"
      using zero_case Comma_Semantic_B1_CRT_Invalid by simp
    obtain local_height where local_eval:
        "comma_weighted_crt_eval (snd left) phase=
          Some (Comma_Semantic_B1_CRT_Invalid,local_height)"
      and local_total: "fst left+local_height=elapsed"
      using left_applied Comma_Semantic_B1_CRT_Invalid
      by (auto simp: comma_weighted_crt_apply_def
        split: option.splits prod.splits)
    have zero_total: "fst left+local_height=0"
      using local_total elapsed_zero by simp
    have root_zero: "fst left=0" and local_zero: "local_height=0"
      using zero_total by arith+
    have invalid_leaf_applied:
        "comma_weighted_crt_apply
          (fst left,comma_semantic_b1_crt_leaf
            Comma_Semantic_B1_CRT_Invalid) phase=
          Some (Comma_Semantic_B1_CRT_Invalid,0)"
      using root_zero
      by (simp add: comma_weighted_crt_apply_def
        comma_semantic_b1_crt_leaf_def)
    have composed_invalid_applied:
        "comma_weighted_crt_apply
          (comma_semantic_b1_crt_compose span left children) phase=
          Some (Comma_Semantic_B1_CRT_Invalid,0)"
      using compose_binding local_eval invalid_leaf_applied local_zero
      by (simp only: Option.bind_lunit prod.case case_prod_Pair
        comma_semantic_b1_crt_control.case option.map add_0_left)
    have compose_invalid:
      "comma_semantic_b1_crt_action_eval
        (comma_semantic_b1_crt_compose span left children) phase=
       Comma_Semantic_B1_Weighted_Invalid"
      using composed_invalid_applied
      by (simp add: comma_semantic_b1_crt_action_eval_def)
    show ?thesis using compose_invalid left_observation
      Comma_Semantic_B1_CRT_Invalid
      by (simp add: comma_semantic_b1_weighted_word_then.simps)
  qed
qed

ML \<open>
  val checked = @{thms comma_semantic_b1_crt_compose_action_eval};
  Thm.consolidate checked;
  Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Weighted CRT chronological composition refinement" checked;
  if null (Thm_Deps.all_oracles checked) then ()
  else error "Weighted CRT composition refinement depends on an oracle"
\<close>

lemma comma_semantic_b1_crt_power_action_eval:
  assumes roots_wf: "comma_semantic_b1_crt_roots_wellformed roots"
    and base_exact: "\<And>phase root. phase<924 \<Longrightarrow> root<46 \<Longrightarrow>
      comma_semantic_b1_crt_roots_action roots phase root = action phase root"
    and base_admitted: "\<And>phase root. phase<924 \<Longrightarrow> root<46 \<Longrightarrow>
      comma_semantic_b1_weighted_result_admitted (action phase root)"
  shows "phase<924 \<Longrightarrow> root<46 \<Longrightarrow>
    comma_semantic_b1_crt_roots_action
      (comma_semantic_b1_crt_power k roots) phase root =
    comma_semantic_b1_weighted_action_power k action phase root"
  using roots_wf
proof (induction k arbitrary: phase root)
  case 0
  assume phase: "phase<924" and root: "root<46"
  have length_roots: "length roots=46"
    using roots_wf by (simp add: comma_semantic_b1_crt_roots_wellformed_def)
  show ?case
    using base_exact[OF phase root] root length_roots phase
    by (simp add: comma_semantic_b1_crt_roots_action_def)
next
  case (Suc k)
  let ?current = "comma_semantic_b1_crt_power k roots"
  assume phase_bound: "phase<924" and root: "root<46"
  have current_wf: "comma_semantic_b1_crt_roots_wellformed ?current"
    by (rule comma_semantic_b1_crt_power_wellformed[OF roots_wf])
  have current_length: "length ?current=46"
    using current_wf by (simp add: comma_semantic_b1_crt_roots_wellformed_def)
  have current_exact:
      "\<And>p i. p<924 \<Longrightarrow> i<46 \<Longrightarrow>
        comma_semantic_b1_crt_roots_action ?current p i =
          comma_semantic_b1_weighted_action_power k action p i"
  proof -
    fix p i :: nat assume p: "p<924" and i: "i<46"
    show "comma_semantic_b1_crt_roots_action ?current p i =
        comma_semantic_b1_weighted_action_power k action p i"
      by (rule Suc.IH[OF p i roots_wf])
  qed
  have current_admitted:
      "\<And>p i. p<924 \<Longrightarrow> i<46 \<Longrightarrow>
        comma_semantic_b1_weighted_result_admitted
          (comma_semantic_b1_weighted_action_power k action p i)"
  proof -
    fix p i :: nat assume p: "p<924" and i: "i<46"
    show "comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_weighted_action_power k action p i)"
      by (rule comma_semantic_b1_weighted_action_power_admitted
        [OF base_admitted p i])
  qed
  have left_wf: "comma_weighted_crt_wellformed (snd (?current!root))"
    using current_wf root
    by (auto simp: comma_semantic_b1_crt_roots_wellformed_def)
  have left_admitted:
      "\<forall>p<924. comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_crt_action_eval (?current!root) p)"
  proof (intro allI impI)
    fix p :: nat assume p: "p<924"
    have exact:
        "comma_semantic_b1_crt_action_eval (?current!root) p =
          comma_semantic_b1_crt_roots_action ?current p root"
      using current_length root p
      by (simp add: comma_semantic_b1_crt_roots_action_def)
    show "comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_crt_action_eval (?current!root) p)"
      using exact current_exact[of p root] current_admitted[of p root] root p by simp
  qed
  have left_zero: "comma_semantic_b1_crt_action_nonterminal_zero (?current!root)"
    by (rule comma_semantic_b1_crt_action_admitted_zero[OF left_wf left_admitted])
  have children_wf: "\<And>child. child<46 \<Longrightarrow>
      comma_weighted_crt_wellformed (snd (?current!child))"
    using current_wf by (auto simp: comma_semantic_b1_crt_roots_wellformed_def)
  have children_zero: "\<And>child. child<46 \<Longrightarrow>
      comma_semantic_b1_crt_action_nonterminal_zero (?current!child)"
  proof -
    fix child :: nat assume child: "child<46"
    have admitted:
        "\<forall>p<924. comma_semantic_b1_weighted_result_admitted
          (comma_semantic_b1_crt_action_eval (?current!child) p)"
    proof (intro allI impI)
      fix p :: nat assume p: "p<924"
      have exact:
          "comma_semantic_b1_crt_action_eval (?current!child) p =
            comma_semantic_b1_crt_roots_action ?current p child"
        using current_length child p
        by (simp add: comma_semantic_b1_crt_roots_action_def)
      show "comma_semantic_b1_weighted_result_admitted
          (comma_semantic_b1_crt_action_eval (?current!child) p)"
        using exact current_exact[of p child] current_admitted[of p child] child p by simp
    qed
    show "comma_semantic_b1_crt_action_nonterminal_zero (?current!child)"
      by (rule comma_semantic_b1_crt_action_admitted_zero
        [OF children_wf[OF child] admitted])
  qed
  have compose_exact:
      "comma_semantic_b1_crt_action_eval
          (comma_semantic_b1_crt_compose (2^k) (?current!root) ?current) phase =
        comma_semantic_b1_weighted_word_then (2^k)
          (\<lambda>p i. comma_semantic_b1_crt_action_eval (?current!root) p)
          (\<lambda>p i. comma_semantic_b1_crt_action_eval (?current!i) p)
          phase root"
    by (rule comma_semantic_b1_crt_compose_action_eval
      [OF current_length left_wf children_wf left_zero children_zero])
  have left:
      "comma_semantic_b1_crt_action_eval (?current!root) phase =
        comma_semantic_b1_weighted_action_power k action phase root"
    using current_length root phase_bound current_exact[of phase root]
    by (simp add: comma_semantic_b1_crt_roots_action_def)
  have right:
      "\<And>i. i<46 \<Longrightarrow>
        comma_semantic_b1_crt_action_eval (?current!i)
            ((phase+2^k) mod 924) =
          comma_semantic_b1_weighted_action_power k action
            ((phase+2^k) mod 924) i"
  proof -
    fix i :: nat assume i: "i<46"
    have next_phase: "(phase+2^k) mod 924<924" by simp
    show "comma_semantic_b1_crt_action_eval (?current!i)
          ((phase+2^k) mod 924) =
        comma_semantic_b1_weighted_action_power k action
          ((phase+2^k) mod 924) i"
      using current_length i next_phase
        current_exact[of "(phase+2^k) mod 924" i]
      by (simp add: comma_semantic_b1_crt_roots_action_def)
  qed
  have length_power: "length (comma_semantic_b1_crt_power (Suc k) roots)=46"
    using current_length by simp
  have left_admitted_phase:
      "comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_crt_action_eval (?current!root) phase)"
    using left_admitted phase_bound by blast
  show ?case
  proof (cases "comma_semantic_b1_crt_action_eval (?current!root) phase")
    case (Comma_Semantic_B1_Continue next_root)
    have next_root_bound: "next_root<46"
      using left_admitted_phase Comma_Semantic_B1_Continue by simp
    have power_left_case:
        "comma_semantic_b1_weighted_action_power k action phase root =
          Comma_Semantic_B1_Continue next_root"
      by (rule trans[OF left[symmetric] Comma_Semantic_B1_Continue])
    show ?thesis
      using compose_exact right[OF next_root_bound] root current_length
        power_left_case Comma_Semantic_B1_Continue
      by (simp add: comma_semantic_b1_crt_roots_action_def
        comma_semantic_b1_crt_power.simps
        comma_semantic_b1_weighted_action_power.simps
        comma_semantic_b1_weighted_word_then.simps)
  next
    case (Comma_Semantic_B1_Stop_At J H)
    have power_left_case:
        "comma_semantic_b1_weighted_action_power k action phase root =
          Comma_Semantic_B1_Stop_At J H"
      by (rule trans[OF left[symmetric] Comma_Semantic_B1_Stop_At])
    show ?thesis
      using compose_exact root current_length power_left_case
        Comma_Semantic_B1_Stop_At
      by (simp add: comma_semantic_b1_crt_roots_action_def
        comma_semantic_b1_crt_power.simps
        comma_semantic_b1_weighted_action_power.simps
        comma_semantic_b1_weighted_word_then.simps)
  next
    case Comma_Semantic_B1_Weighted_Invalid
    have power_left_case:
        "comma_semantic_b1_weighted_action_power k action phase root =
          Comma_Semantic_B1_Weighted_Invalid"
      by (rule trans[OF left[symmetric] Comma_Semantic_B1_Weighted_Invalid])
    show ?thesis
      using compose_exact root current_length power_left_case
        Comma_Semantic_B1_Weighted_Invalid
      by (simp add: comma_semantic_b1_crt_roots_action_def
        comma_semantic_b1_crt_power.simps
        comma_semantic_b1_weighted_action_power.simps
        comma_semantic_b1_weighted_word_then.simps)
  qed
qed

lemma comma_semantic_graph_stop242_from_weighted_crt_power:
  assumes roots_wf: "comma_semantic_b1_crt_roots_wellformed roots"
    and base_exact: "\<And>phase root. phase<924 \<Longrightarrow> root<46 \<Longrightarrow>
      comma_semantic_b1_crt_roots_action roots phase root =
        comma_semantic_graph_root_weighted_action phase root"
    and base_admitted: "\<And>phase root. phase<924 \<Longrightarrow> root<46 \<Longrightarrow>
      comma_semantic_b1_weighted_result_admitted
        (comma_semantic_graph_root_weighted_action phase root)"
    and phase: "phase<924" and root: "root<46"
    and stop: "comma_weighted_crt_apply
      (comma_semantic_b1_crt_power 5 roots!root) phase=
        Some (Comma_Semantic_B1_CRT_Stop J,H)"
    and terminal: "J<9" and height: "H\<le>26"
  shows "\<exists>D. comma_semantic_graph_action_power 5 phase root=
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
proof -
  have root_count: "length (comma_semantic_b1_crt_power 5 roots)=46"
    using roots_wf by (simp add: comma_semantic_b1_crt_power_length
      comma_semantic_b1_crt_roots_wellformed_def)
  have action_exact:
      "comma_semantic_b1_crt_roots_action
          (comma_semantic_b1_crt_power 5 roots) phase root =
        comma_semantic_b1_weighted_action_power 5
          comma_semantic_graph_root_weighted_action phase root"
    by (rule comma_semantic_b1_crt_power_action_eval
      [OF roots_wf base_exact base_admitted phase root])
  have selected_action:
      "comma_semantic_b1_crt_roots_action
          (comma_semantic_b1_crt_power 5 roots) phase root=
        Comma_Semantic_B1_Stop_At J H"
    using stop terminal root_count root
    by (simp add: comma_semantic_b1_crt_roots_action_def
      comma_semantic_b1_crt_action_eval_def comma_semantic_b1_crt_decode.simps)
  have weighted:
      "comma_semantic_b1_weighted_action_power 5
          comma_semantic_graph_root_weighted_action phase root=
        Comma_Semantic_B1_Stop_At J H"
    using action_exact selected_action by simp
  have graph_exact:
      "comma_semantic_b1_weighted_encode
          (comma_semantic_b1_weighted_action_power 5
            comma_semantic_graph_root_weighted_action phase root)=
        comma_semantic_graph_action_power 5 phase root"
    by (rule comma_semantic_graph_weighted_power_exact)
  have result:
      "comma_semantic_graph_action_power 5 phase root=
        Comma_Semantic_B1_Stop (9*H+J)"
    using graph_exact weighted by simp
  have bound: "9*H+J\<le>242"
    using height terminal by arith
  show ?thesis using result bound by blast
qed

lemma comma_semantic_graph_stop242_from_weighted_crt_power_all:
  assumes roots_wf: "comma_semantic_b1_crt_roots_wellformed roots"
    and base_exact: "\<And>phase root. phase<924 \<Longrightarrow> root<46 \<Longrightarrow>
      comma_semantic_b1_crt_roots_action roots phase root =
        comma_semantic_graph_root_weighted_action phase root"
    and base_admitted: "\<And>phase root. phase<924 \<Longrightarrow> root<46 \<Longrightarrow>
      comma_semantic_b1_weighted_result_admitted
        (comma_semantic_graph_root_weighted_action phase root)"
    and final_exact:
      "\<forall>root<46. \<forall>phase.
        comma_weighted_crt_apply (final_actions!root) phase =
          comma_weighted_crt_apply
            (comma_semantic_b1_crt_power 5 roots!root) phase"
    and final_bounded:
      "\<forall>root<46. \<forall>phase. \<exists>J H.
        comma_weighted_crt_apply (final_actions!root) phase =
          Some (Comma_Semantic_B1_CRT_Stop J,H) \<and> J<9 \<and> H\<le>26"
  shows "\<forall>root<46. \<forall>phase<924. \<exists>D.
      comma_semantic_graph_action_power 5 phase root =
        Comma_Semantic_B1_Stop D \<and> D\<le>242"
proof (intro allI impI)
  fix root phase :: nat
  assume root: "root<46" and phase: "phase<924"
  have final_bounded_root:
    "\<forall>phase. \<exists>J H.
      comma_weighted_crt_apply (final_actions!root) phase =
        Some (Comma_Semantic_B1_CRT_Stop J,H) \<and> J<9 \<and> H\<le>26"
  proof -
    have root_imp:
      "root<46 \<longrightarrow> (\<forall>phase. \<exists>J H.
        comma_weighted_crt_apply (final_actions!root) phase =
          Some (Comma_Semantic_B1_CRT_Stop J,H) \<and> J<9 \<and> H\<le>26)"
      by (rule spec[OF final_bounded])
    show ?thesis by (rule mp[OF root_imp root])
  qed
  have final_bounded_phase:
    "\<exists>J H. comma_weighted_crt_apply (final_actions!root) phase =
      Some (Comma_Semantic_B1_CRT_Stop J,H) \<and> J<9 \<and> H\<le>26"
    using final_bounded_root by (rule spec)
  obtain J H where final_stop:
      "comma_weighted_crt_apply (final_actions!root) phase =
          Some (Comma_Semantic_B1_CRT_Stop J,H)"
    and terminal: "J<9" and height: "H\<le>26"
    using final_bounded_phase by blast
  have powered_stop:
      "comma_weighted_crt_apply
        (comma_semantic_b1_crt_power 5 roots!root) phase =
          Some (Comma_Semantic_B1_CRT_Stop J,H)"
  proof -
    have root_exact:
      "\<forall>phase. comma_weighted_crt_apply (final_actions!root) phase =
        comma_weighted_crt_apply
          (comma_semantic_b1_crt_power 5 roots!root) phase"
    proof -
      have root_imp:
        "root<46 \<longrightarrow> (\<forall>phase.
          comma_weighted_crt_apply (final_actions!root) phase =
            comma_weighted_crt_apply
              (comma_semantic_b1_crt_power 5 roots!root) phase)"
        by (rule spec[OF final_exact])
      show ?thesis by (rule mp[OF root_imp root])
    qed
    have phase_exact:
      "comma_weighted_crt_apply (final_actions!root) phase =
        comma_weighted_crt_apply
          (comma_semantic_b1_crt_power 5 roots!root) phase"
      using spec[OF root_exact] .
    show ?thesis using final_stop phase_exact by simp
  qed
  show "\<exists>D. comma_semantic_graph_action_power 5 phase root =
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
    by (rule comma_semantic_graph_stop242_from_weighted_crt_power
      [OF roots_wf base_exact base_admitted phase root powered_stop terminal height])
qed

fun comma_semantic_b1_crt_terminal_bound ::
    "nat \<Rightarrow> nat \<times> comma_semantic_b1_crt_dag \<Rightarrow> bool" where
  "comma_semantic_b1_crt_terminal_bound limit (accumulated_weight,
      Comma_Weighted_CRT_Leaf (Comma_Semantic_B1_CRT_Stop J)) =
    (J<9 \<and> accumulated_weight\<le>limit)"
| "comma_semantic_b1_crt_terminal_bound limit (accumulated_weight,
      Comma_Weighted_CRT_Leaf control) = False"
| "comma_semantic_b1_crt_terminal_bound limit (accumulated_weight,
      Comma_Weighted_CRT_Branch axis rows) =
    (axis<4 \<and> length rows=comma_crt_axis_radix axis \<and>
      list_all (\<lambda>(weight,child).
        comma_semantic_b1_crt_terminal_bound limit
          (accumulated_weight+weight,child)) rows)"

lemma comma_semantic_b1_crt_terminal_bound_sound:
  assumes bound: "comma_semantic_b1_crt_terminal_bound limit action"
  shows "\<exists>J H. comma_weighted_crt_apply action phase=Some
      (Comma_Semantic_B1_CRT_Stop J,H) \<and> J<9 \<and> H\<le>limit"
  using bound
proof (induction action arbitrary: limit phase)
  case (Pair offset tree)
  then show ?case
  proof (induction tree arbitrary: offset limit phase)
    case (Comma_Weighted_CRT_Leaf control)
    then show ?case
      by (cases control) (auto simp: comma_weighted_crt_apply_def)
  next
    case (Comma_Weighted_CRT_Branch axis rows)
    have axis: "axis<4" and extent: "length rows=comma_crt_axis_radix axis"
      and children:
        "list_all (\<lambda>(weight,child).
          comma_semantic_b1_crt_terminal_bound limit (offset+weight,child)) rows"
      using Comma_Weighted_CRT_Branch.prems by simp_all
    have index: "phase mod comma_crt_axis_radix axis<length rows"
      using comma_weighted_crt_axis_positive[OF axis] extent by simp
    obtain weight child where selected:
        "rows!(phase mod comma_crt_axis_radix axis)=(weight,child)"
      by (cases "rows!(phase mod comma_crt_axis_radix axis)") auto
    have member: "(weight,child)\<in>set rows"
      using nth_mem[OF index] selected by simp
    have child_member: "child\<in>Basic_BNFs.snds (weight,child)"
      by (simp add: prod_set_defs)
    have child_bound:
        "comma_semantic_b1_crt_terminal_bound limit (offset+weight,child)"
      using children member by (auto simp: list_all_iff prod_set_defs)
    have child_exists:
      "\<exists>J H. comma_weighted_crt_apply (offset+weight,child) phase=
          Some (Comma_Semantic_B1_CRT_Stop J,H) \<and> J<9 \<and> H\<le>limit"
      by (rule Comma_Weighted_CRT_Branch.IH
        [OF member child_member child_bound])
    then obtain J H where child_result:
        "comma_weighted_crt_apply (offset+weight,child) phase=
            Some (Comma_Semantic_B1_CRT_Stop J,H)"
      and terminal: "J<9" and height: "H\<le>limit"
      by blast
    obtain child_height where child_eval:
        "comma_weighted_crt_eval child phase=
          Some (Comma_Semantic_B1_CRT_Stop J,child_height)"
      and accumulated: "offset+weight+child_height=H"
      using child_result
      by (auto simp: comma_weighted_crt_apply_def
        split: option.splits prod.splits)
    have branch_eval:
        "comma_weighted_crt_eval
            (Comma_Weighted_CRT_Branch axis rows) phase=
          Some (Comma_Semantic_B1_CRT_Stop J,weight+child_height)"
      using axis extent selected child_eval
      by (simp add: comma_weighted_crt_eval_branch)
    have branch_result:
        "comma_weighted_crt_apply
            (offset,Comma_Weighted_CRT_Branch axis rows) phase=
          Some (Comma_Semantic_B1_CRT_Stop J,H)"
      using branch_eval accumulated
      by (simp add: comma_weighted_crt_apply_def algebra_simps)
    show ?case using branch_result terminal height by blast
  qed
qed

text \<open>
The checked source graph is compiled only at its authenticated 16 source roots.
Graph-node actions are normalized in postorder before parent compilation.
The separate rank owner supplies the B32 action, so this publisher does not
recompute or recertify the five-square graph action.
\<close>

ML_file "semantic_weighted_crt_local_node_compiler.ML"
ML_file "semantic_weighted_crt_dag.ML"
ML_file "semantic_predecessor_certificate.ML"

local_setup \<open>Comma_Semantic_Predecessor_Certificate.publish\<close>

ML \<open>
  Thm.consolidate @{thms comma_semantic_graph_initial_source_actions_refine};
  Thm.consolidate @{thms comma_semantic_graph_initial_source_actions_length
    comma_semantic_graph_initial_source_actions_wellformed
    comma_semantic_graph_initial_source_actions_nonterminal_zero};
  Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Authenticated 16-source weighted action vector"
    @{thms comma_semantic_graph_initial_source_binding_exact
      comma_semantic_graph_initial_source_actions_refine
      comma_semantic_graph_initial_source_actions_length
      comma_semantic_graph_initial_source_actions_wellformed
      comma_semantic_graph_initial_source_actions_nonterminal_zero};
  Comma_Proof_Dependency_Audit.require_native_closed_expected_paths @{context}
    "Source selected action DAGs refine the checked graph"
    ["comma_semantic_graph_valid_checked",
     "comma_semantic_b1_crt_compile_node_from_children_refines_graph_eval"]
    @{thms comma_semantic_graph_initial_source_actions_refine};
\<close>

end
