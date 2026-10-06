theory Comma_Semantic_Path
  imports Comma_Semantic_Future Comma_Literal_Bridge.Comma_Unique_Path
begin

text \<open>
This layer upgrades the provider-neutral occurrence contract with the
unique-path witness itself.  Keeping that witness at the same control,
endpoint, and weight lets arbitrary infinite paths be compared at every
literal index, including indices before the certified occurrence ends.
\<close>

definition comma_semantic_strong_occurrence_bridge ::
  "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> nat) \<Rightarrow>
   ('s \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
   ('s \<Rightarrow> comma_future_control \<Rightarrow> nat) \<Rightarrow>
   ('s \<Rightarrow> comma_future_control \<Rightarrow> 's list) \<Rightarrow>
   ('s \<Rightarrow> comma_future_control option) \<Rightarrow> bool" where
  "comma_semantic_strong_occurrence_bridge valid phase value exponent_delta children control_step
    \<longleftrightarrow> (\<forall>q p. valid q \<longrightarrow> 5 \<le> p \<longrightarrow>
      p mod 924 = phase q \<longrightarrow>
      (\<exists>control endpoint weight.
        control_step q = Some control \<and>
        comma_unique_literal_path weight (value q p) endpoint \<and>
        distinct (children q control) \<and>
        (\<forall>child\<in>set (children q control).
          valid child \<and> 5 \<le> p + exponent_delta q control \<and>
          (p + exponent_delta q control) mod 924 = phase child) \<and>
        (case control of Comma_Future_Fork a \<Rightarrow>
          length (children q control) = 2
          | Comma_Future_Landmine \<Rightarrow> children q control = []) \<and>
        (\<forall>v. comma_child endpoint v \<longleftrightarrow>
          (\<exists>child\<in>set (children q control).
            v = value child (p + exponent_delta q control)))))"

lemma comma_semantic_strong_occurrence_bridgeD:
  assumes bridge: "comma_semantic_strong_occurrence_bridge valid phase value
      exponent_delta children control_step"
    and state_valid: "valid q"
    and exponent: "5 \<le> p"
    and phase_match: "p mod 924 = phase q"
  obtains control endpoint weight where
    "control_step q = Some control"
    "comma_unique_literal_path weight (value q p) endpoint"
    "distinct (children q control)"
    "\<forall>child\<in>set (children q control).
      valid child \<and> 5 \<le> p + exponent_delta q control \<and>
      (p + exponent_delta q control) mod 924 = phase child"
    "case control of Comma_Future_Fork a \<Rightarrow>
        length (children q control) = 2
      | Comma_Future_Landmine \<Rightarrow> children q control = []"
    "\<forall>v. comma_child endpoint v \<longleftrightarrow>
      (\<exists>child\<in>set (children q control).
        v = value child (p + exponent_delta q control))"
  using bridge state_valid exponent phase_match
  unfolding comma_semantic_strong_occurrence_bridge_def
  by blast

lemma comma_semantic_strong_occurrence_bridge_implies:
  assumes bridge: "comma_semantic_strong_occurrence_bridge valid phase value
      exponent_delta children control_step"
  shows "comma_semantic_occurrence_bridge valid phase value
      exponent_delta children control_step"
  unfolding comma_semantic_occurrence_bridge_def
proof (intro allI impI)
  fix q p
  assume state_valid: "valid q"
    and exponent: "5 \<le> p"
    and phase_match: "p mod 924 = phase q"
  obtain control endpoint weight where step:
      "control_step q = Some control"
    and unique_path:
      "comma_unique_literal_path weight (value q p) endpoint"
    and alternatives: "distinct (children q control)"
    and children_admitted:
      "\<forall>child\<in>set (children q control).
        valid child \<and> 5 \<le> p + exponent_delta q control \<and>
        (p + exponent_delta q control) mod 924 = phase child"
    and complete_control:
      "(case control of Comma_Future_Fork a \<Rightarrow>
          length (children q control) = 2
        | Comma_Future_Landmine \<Rightarrow> children q control = [])"
    and child_relation:
      "\<forall>v. comma_child endpoint v \<longleftrightarrow>
        (\<exists>child\<in>set (children q control).
          v = value child (p + exponent_delta q control))"
    by (rule comma_semantic_strong_occurrence_bridgeD
      [OF bridge state_valid exponent phase_match])
  have literal: "comma_literal_path weight (value q p) endpoint"
    by (rule comma_unique_literal_path_literal[OF unique_path])
  have unique_endpoint:
    "\<forall>other. comma_literal_path weight (value q p) other \<longrightarrow>
      other = endpoint"
  proof (intro allI impI)
    fix other
    assume other_path: "comma_literal_path weight (value q p) other"
    show "other = endpoint"
      by (rule comma_unique_literal_path_endpoint[OF unique_path other_path])
  qed
  show "\<exists>control endpoint weight.
      control_step q = Some control \<and>
      comma_literal_path weight (value q p) endpoint \<and>
      (\<forall>other. comma_literal_path weight (value q p) other \<longrightarrow>
        other = endpoint) \<and>
      distinct (children q control) \<and>
      (\<forall>child\<in>set (children q control).
        valid child \<and> 5 \<le> p + exponent_delta q control \<and>
        (p + exponent_delta q control) mod 924 = phase child) \<and>
      (case control of Comma_Future_Fork a \<Rightarrow>
          length (children q control) = 2
        | Comma_Future_Landmine \<Rightarrow> children q control = []) \<and>
      (\<forall>v. comma_child endpoint v \<longleftrightarrow>
        (\<exists>child\<in>set (children q control).
          v = value child (p + exponent_delta q control)))"
  proof (rule exI[of _ control], rule exI[of _ endpoint],
      rule exI[of _ weight], intro conjI)
    show "control_step q = Some control" by (rule step)
    show "comma_literal_path weight (value q p) endpoint" by (rule literal)
    show "\<forall>other. comma_literal_path weight (value q p) other \<longrightarrow>
        other = endpoint" by (rule unique_endpoint)
    show "distinct (children q control)" by (rule alternatives)
    show "\<forall>child\<in>set (children q control).
        valid child \<and> 5 \<le> p + exponent_delta q control \<and>
        (p + exponent_delta q control) mod 924 = phase child"
      by (rule children_admitted)
    show "(case control of Comma_Future_Fork a \<Rightarrow>
          length (children q control) = 2
        | Comma_Future_Landmine \<Rightarrow> children q control = [])"
      by (rule complete_control)
    show "\<forall>v. comma_child endpoint v \<longleftrightarrow>
        (\<exists>child\<in>set (children q control).
          v = value child (p + exponent_delta q control))"
      by (rule child_relation)
  qed
qed

theorem comma_semantic_infinite_paths_agree:
  assumes bridge: "comma_semantic_strong_occurrence_bridge valid phase value
      exponent_delta children control_step"
    and checked: "comma_semantic_rank_check valid rank children control_step"
  shows "\<forall>q p left right. valid q \<longrightarrow> 5 \<le> p \<longrightarrow>
    p mod 924 = phase q \<longrightarrow>
    comma_semantic_infinite_path value q p left \<longrightarrow>
    comma_semantic_infinite_path value q p right \<longrightarrow>
    (\<forall>n. left n = right n)"
proof -
  have weak_bridge:
    "comma_semantic_occurrence_bridge valid phase value exponent_delta children control_step"
    by (rule comma_semantic_strong_occurrence_bridge_implies[OF bridge])
  let ?P = "\<lambda>n. \<forall>q p left right. valid q \<longrightarrow> 5 \<le> p \<longrightarrow>
      p mod 924 = phase q \<longrightarrow>
      comma_semantic_infinite_path value q p left \<longrightarrow>
      comma_semantic_infinite_path value q p right \<longrightarrow> left n = right n"
  have all_indices: "?P n" for n
  proof (induction n rule: less_induct)
    case (less n)
    show ?case
    proof (intro allI impI)
      fix q p left right
      assume state_valid: "valid q"
        and exponent: "5 \<le> p"
        and phase_match: "p mod 924 = phase q"
        and left_path: "comma_semantic_infinite_path value q p left"
        and right_path: "comma_semantic_infinite_path value q p right"
      have left_start: "left 0 = value q p"
        using left_path by (simp add: comma_semantic_infinite_path_def)
      have right_start: "right 0 = value q p"
        using right_path by (simp add: comma_semantic_infinite_path_def)
      have left_edges: "comma_child (left j) (left (Suc j))" for j
        using left_path by (simp add: comma_semantic_infinite_path_def)
      have right_edges: "comma_child (right j) (right (Suc j))" for j
        using right_path by (simp add: comma_semantic_infinite_path_def)
      obtain control endpoint weight where control_step:
          "control_step q = Some control"
        and unique_path:
          "comma_unique_literal_path weight (value q p) endpoint"
        and distinct_children: "distinct (children q control)"
        and children_admitted:
          "\<forall>child\<in>set (children q control).
            valid child \<and> 5 \<le> p + exponent_delta q control \<and>
            (p + exponent_delta q control) mod 924 = phase child"
        and complete_control:
          "(case control of Comma_Future_Fork a \<Rightarrow>
              length (children q control) = 2
            | Comma_Future_Landmine \<Rightarrow> children q control = [])"
        and child_relation:
          "\<forall>v. comma_child endpoint v \<longleftrightarrow>
            (\<exists>child\<in>set (children q control).
              v = value child (p + exponent_delta q control))"
        by (rule comma_semantic_strong_occurrence_bridgeD
          [OF bridge state_valid exponent phase_match])
      have left_prefix:
        "comma_literal_path weight (value q p) (left weight)"
        using comma_infinite_literal_prefix[where path=left and n=weight,
          OF left_edges] left_start by simp
      have right_prefix:
        "comma_literal_path weight (value q p) (right weight)"
        using comma_infinite_literal_prefix[where path=right and n=weight,
          OF right_edges] right_start by simp
      have left_endpoint: "left weight = endpoint"
        by (rule comma_unique_literal_path_endpoint[OF unique_path left_prefix])
      have right_endpoint: "right weight = endpoint"
        by (rule comma_unique_literal_path_endpoint[OF unique_path right_prefix])
      show "left n = right n"
      proof (cases "n \<le> weight")
        case True
        obtain middle where unique_n:
            "comma_unique_literal_path n (value q p) middle"
          using comma_unique_literal_path_prefix[OF unique_path True] by blast
        have left_n: "comma_literal_path n (value q p) (left n)"
          using comma_infinite_literal_prefix[where path=left and n=n,
            OF left_edges] left_start by simp
        have right_n: "comma_literal_path n (value q p) (right n)"
          using comma_infinite_literal_prefix[where path=right and n=n,
            OF right_edges] right_start by simp
        have left_eq: "left n = middle"
          by (rule comma_unique_literal_path_endpoint[OF unique_n left_n])
        have right_eq: "right n = middle"
          by (rule comma_unique_literal_path_endpoint[OF unique_n right_n])
        show ?thesis using left_eq right_eq by simp
      next
        case False
        have weight_before: "Suc weight \<le> n" using False by arith
        let ?m = "n - Suc weight"
        have n_split: "n = Suc weight + ?m" using weight_before by arith
        have m_less: "?m < n" using weight_before by arith
        obtain forced_control forced_endpoint forced_weight forced_child forced_tail where
          forced_step: "control_step q = Some forced_control"
          and forced_occurrence:
            "comma_literal_path forced_weight (value q p) forced_endpoint"
          and forced_member: "forced_child \<in> set (children q forced_control)"
          and forced_value:
            "left (Suc forced_weight) = value forced_child
              (p + exponent_delta q forced_control)"
          and forced_child_valid: "valid forced_child"
          and forced_exponent: "5 \<le> p + exponent_delta q forced_control"
          and forced_phase:
            "(p + exponent_delta q forced_control) mod 924 = phase forced_child"
          and forced_tail_path:
            "comma_semantic_infinite_path value forced_child
              (p + exponent_delta q forced_control) forced_tail"
          and source_unranked: "rank q = None"
          and forced_child_unranked: "rank forced_child = None"
          and forced_siblings_ranked:
            "\<forall>other\<in>set (children q forced_control).
              other \<noteq> forced_child \<longrightarrow> rank other \<noteq> None"
          by (rule comma_semantic_infinite_path_forces_unique_unranked_child
            [OF weak_bridge checked state_valid exponent phase_match left_path])
        have left_edge_after_prefix: "comma_child endpoint (left (Suc weight))"
          using left_edges[of weight] left_endpoint by simp
        have right_edge_after_prefix: "comma_child endpoint (right (Suc weight))"
          using right_edges[of weight] right_endpoint by simp
        have left_child_exists:
          "\<exists>child\<in>set (children q control).
            left (Suc weight) = value child (p + exponent_delta q control)"
          using child_relation left_edge_after_prefix by blast
        have right_child_exists:
          "\<exists>child\<in>set (children q control).
            right (Suc weight) = value child (p + exponent_delta q control)"
          using child_relation right_edge_after_prefix by blast
        obtain left_child where left_member:
            "left_child \<in> set (children q control)"
          and left_value:
            "left (Suc weight) = value left_child (p + exponent_delta q control)"
          using left_child_exists by blast
        obtain right_child where right_member:
            "right_child \<in> set (children q control)"
          and right_value:
            "right (Suc weight) = value right_child (p + exponent_delta q control)"
          using right_child_exists by blast
        have left_inputs:
          "valid left_child \<and> 5 \<le> p + exponent_delta q control \<and>
            (p + exponent_delta q control) mod 924 = phase left_child"
          by (rule bspec[OF children_admitted left_member])
        have left_child_valid: "valid left_child"
          using left_inputs by blast
        have left_child_phase:
          "(p + exponent_delta q control) mod 924 = phase left_child"
          using left_inputs by blast
        have right_inputs:
          "valid right_child \<and> 5 \<le> p + exponent_delta q control \<and>
            (p + exponent_delta q control) mod 924 = phase right_child"
          by (rule bspec[OF children_admitted right_member])
        have right_child_valid: "valid right_child"
          using right_inputs by blast
        have right_child_phase:
          "(p + exponent_delta q control) mod 924 = phase right_child"
          using right_inputs by blast
        have next_exponent: "5 \<le> p + exponent_delta q control"
          using left_inputs by blast
        have left_tail_start:
          "(\<lambda>j. left (Suc weight + j)) 0 = value left_child
            (p + exponent_delta q control)"
          using left_value by simp
        have right_tail_start:
          "(\<lambda>j. right (Suc weight + j)) 0 = value right_child
            (p + exponent_delta q control)"
          using right_value by simp
        have left_tail_edges:
          "comma_child (left (Suc weight + j)) (left (Suc weight + Suc j))" for j
          using left_edges[of "Suc weight + j"] by (simp add: add.assoc)
        have right_tail_edges:
          "comma_child (right (Suc weight + j)) (right (Suc weight + Suc j))" for j
          using right_edges[of "Suc weight + j"] by (simp add: add.assoc)
        have left_tail:
          "comma_semantic_infinite_path value left_child
            (p + exponent_delta q control) (\<lambda>j. left (Suc weight + j))"
          using left_tail_start left_tail_edges
          by (simp add: comma_semantic_infinite_path_def)
        have right_tail:
          "comma_semantic_infinite_path value right_child
            (p + exponent_delta q control) (\<lambda>j. right (Suc weight + j))"
          using right_tail_start right_tail_edges
          by (simp add: comma_semantic_infinite_path_def)
        have left_child_unranked: "rank left_child = None"
        proof (cases "rank left_child")
          case None
          then show ?thesis .
        next
          case (Some k)
          have no_tail:
            "\<not> comma_semantic_infinite_path value left_child
              (p + exponent_delta q control) (\<lambda>j. left (Suc weight + j))"
            by (rule comma_semantic_ranked_state_no_infinite_path
              [OF weak_bridge checked left_child_valid next_exponent
                left_child_phase Some])
          show ?thesis using no_tail left_tail by contradiction
        qed
        have right_child_unranked: "rank right_child = None"
        proof (cases "rank right_child")
          case None
          then show ?thesis .
        next
          case (Some k)
          have no_tail:
            "\<not> comma_semantic_infinite_path value right_child
              (p + exponent_delta q control) (\<lambda>j. right (Suc weight + j))"
            by (rule comma_semantic_ranked_state_no_infinite_path
              [OF weak_bridge checked right_child_valid next_exponent
                right_child_phase Some])
          show ?thesis using no_tail right_tail by contradiction
        qed
        have control_not_landmine: "control \<noteq> Comma_Future_Landmine"
        proof
          assume landmine: "control = Comma_Future_Landmine"
          have no_children: "children q Comma_Future_Landmine = []"
            using complete_control landmine by simp
          show False using left_member no_children landmine by simp
        qed
        obtain a where fork: "control = Comma_Future_Fork a"
          using control_not_landmine by (cases control) auto
        have forced_control_eq: "forced_control = control"
          using forced_step control_step by simp
        have forced_member_fork:
          "forced_child \<in> set (children q (Comma_Future_Fork a))"
          using forced_member forced_control_eq fork by simp
        have forced_siblings_ranked_fork:
          "\<forall>other\<in>set (children q (Comma_Future_Fork a)).
            other \<noteq> forced_child \<longrightarrow> rank other \<noteq> None"
          using forced_siblings_ranked forced_control_eq fork by simp
        have left_member_fork:
          "left_child \<in> set (children q (Comma_Future_Fork a))"
          using left_member fork by simp
        have right_member_fork:
          "right_child \<in> set (children q (Comma_Future_Fork a))"
          using right_member fork by simp
        have left_is_forced: "left_child = forced_child"
        proof (rule ccontr)
          assume different: "left_child \<noteq> forced_child"
          have "rank left_child \<noteq> None"
            using forced_siblings_ranked_fork left_member_fork different by blast
          then show False using left_child_unranked by contradiction
        qed
        have right_is_forced: "right_child = forced_child"
        proof (rule ccontr)
          assume different: "right_child \<noteq> forced_child"
          have "rank right_child \<noteq> None"
            using forced_siblings_ranked_fork right_member_fork different by blast
          then show False using right_child_unranked by contradiction
        qed
        have children_equal: "left_child = right_child"
          using left_is_forced right_is_forced by simp
        have smaller: "?P ?m" using less.IH[OF m_less] .
        have tails_equal:
          "(\<lambda>j. left (Suc weight + j)) ?m =
            (\<lambda>j. right (Suc weight + j)) ?m"
          using smaller left_child_valid next_exponent left_child_phase
            right_child_valid right_child_phase children_equal left_tail right_tail
          by blast
        show ?thesis using tails_equal n_split by simp
      qed
    qed
  qed
  show ?thesis using all_indices by blast
qed

ML \<open>
  val checked = @{thms comma_semantic_strong_occurrence_bridge_implies
    comma_unique_literal_path_prefix comma_semantic_infinite_paths_agree}
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Semantic arbitrary-path uniqueness depends on a theorem oracle"
\<close>

end
