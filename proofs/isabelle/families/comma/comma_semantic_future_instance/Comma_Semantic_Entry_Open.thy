theory Comma_Semantic_Entry_Open
  imports Comma_Semantic_Future_Instance
begin

text \<open>The fixed exponent-five root classification is published by the
checked M204 instance. Its finite demand follows authenticated weight and class
paths and retains the exact [3,34,75] result. The path arguments below consume
the same physical summary and ordered class-rank refinement.\<close>

lemma comma_semantic_infinite_boundary_path_unranked:
  assumes path: "comma_semantic_infinite_path comma_boundary_value q p stream"
    and valid: "comma_boundary_valid q"
    and exponent: "5 \<le> p"
    and phase: "p mod 924 = snd (snd q)"
  shows "comma_semantic_concrete_future_rank q = None"
proof (cases "comma_semantic_concrete_future_rank q")
  case None
  then show ?thesis .
next
  case (Some rank)
  have no_path: "\<not> comma_semantic_infinite_path comma_boundary_value q p stream"
    by (rule comma_semantic_ranked_state_no_infinite_path
      [OF comma_semantic_concrete_boundary_occurrence_bridge
        comma_semantic_concrete_future_rank_check valid exponent phase Some])
  show ?thesis using path no_path by contradiction
qed

theorem comma_semantic_p5_entry_infinite_imp_open:
  fixes stream :: "nat \<Rightarrow> nat"
  assumes offset: "x \<le> 90"
    and start: "stream 0 = 100000 + x"
    and edges: "\<And>j. comma_child (stream j) (stream (Suc j))"
  shows "comma_semantic_p5_entry_future_open x"
proof -
  have root: "comma_offset_orbit x < 46"
    by (rule comma_offset_orbit_bound)
  have r_bound: "5 < 924" by simp
  have phase_match: "5 mod 924 = 5" by simp
  have exponent: "5 \<le> 5" by simp
  have exact_orbit:
    "\<And>r i. r < 924 \<Longrightarrow> i < 46 \<Longrightarrow>
      (\<lambda>q j. comma_semantic_b1_action_power 5 q j) r i =
        comma_semantic_b1_of_word (comma_orbit_word 5 r i)"
  proof -
    fix r i
    assume r_bound: "r < 924" and i_bound: "i < 46"
    show "(\<lambda>q j. comma_semantic_b1_action_power 5 q j) r i =
        comma_semantic_b1_of_word (comma_orbit_word 5 r i)"
      by (rule comma_semantic_b1_action_power_refines_orbit[OF r_bound i_bound])
  qed
  obtain d where stop:
      "comma_semantic_b1_action_power 5 5 (comma_offset_orbit x) =
        Comma_Semantic_B1_Stop d"
    and d_bound: "d \<le> 242"
    by (rule comma_semantic_b1_action_power_b32_stop242[OF root r_bound])
  let ?provider = "\<lambda>q i. comma_semantic_b1_action_power 5 q i"
  have stopped: "?provider 5 (comma_offset_orbit x) =
      Comma_Semantic_B1_Stop d"
    using stop by simp
  have path_start:
    "stream 0 = comma_chart_value 5 (Comma_Entry 1 0 x)"
    using start by (simp add: comma_chart_value_def)
  show ?thesis
  proof (rule comma_semantic_b32_entry_infinite_path_projects_summary_child
      [OF exact_orbit r_bound offset exponent phase_match stopped d_bound
        path_start edges])
    fix h terminal weight t endpoint successor tail
    assume decoded: "comma_terminal_weight_decode d = (h,terminal)"
      and height: "h \<le> 26"
      and summary: "comma_decade_exact_summary (Comma_Decade 5 x) h terminal"
      and unique:
        "comma_unique_literal_path weight
          (comma_chart_value 5 (Comma_Entry 1 0 x)) endpoint"
      and endpoint_eq: "endpoint = comma_chart_value (5+h) t"
      and terminal_admitted: "comma_round_admitted t"
      and terminal_delta: "comma_round_delta t = 0"
      and terminal_move:
        "comma_finite_step ((5+h) mod 924) t =
          comma_summary_terminal_move terminal"
      and children_eq:
        "comma_large_children (comma_sector_number t) (5+h) endpoint =
          comma_summary_ordered_children terminal (5+h)"
      and complete_children:
        "\<forall>v. comma_child endpoint v \<longleftrightarrow>
          v \<in> set (comma_summary_ordered_children terminal (5+h))"
      and selected_endpoint: "stream weight = endpoint"
      and successor_eq: "successor = stream (Suc weight)"
      and successor_member:
        "successor \<in> set (comma_summary_ordered_children terminal (5+h))"
      and tail_start: "tail 0 = successor"
      and tail_edges:
        "\<forall>j. comma_child (tail j) (tail (Suc j))"
    have summary_lookup:
      "comma_semantic_decade_summary (Comma_Decade 5 x) =
        Some (h,terminal)"
      using stop decoded offset
      by (simp add: comma_semantic_decade_summary_def)
    have tail_edges_rule:
      "comma_child (tail j) (tail (Suc j))" for j
      using tail_edges by simp
    have semantic_open:
      "comma_semantic_p5_entry_future_open x"
    proof (cases terminal)
      case Comma_Terminal_Landmine
      have empty:
        "set (comma_summary_ordered_children terminal (5+h)) = {}"
        using Comma_Terminal_Landmine
        by (simp add: comma_summary_ordered_children.simps)
      have False using successor_member empty by simp
      then show ?thesis by contradiction
    next
      case (Comma_Terminal_Fork a)
      have terminal_eq: "terminal = Comma_Terminal_Fork a"
        using Comma_Terminal_Fork .
      have bounds: "2 \<le> a" "a \<le> 9"
        using comma_decade_terminal_fork_bounds[OF summary] terminal_eq
        by auto
      have near_valid:
        "comma_boundary_valid (Comma_N,a,(5+h) mod 924)"
        using bounds by (simp add: comma_boundary_valid_def)
      have zero_valid:
        "comma_boundary_valid (Comma_Z,a,(5+h) mod 924)"
        using bounds by (simp add: comma_boundary_valid_def)
      have child_cases:
        "successor = comma_near_boundary a (5+h) \<or>
         successor = comma_zero_boundary a (5+h)"
        using successor_member terminal_eq successor_eq
        by (auto simp: comma_summary_ordered_children.simps)
      have near_value:
        "comma_near_boundary a (5+h) =
          comma_boundary_value (Comma_N,a,(5+h) mod 924) (5+h)"
        by (simp add: comma_near_boundary_def comma_boundary_value_def)
      have zero_value:
        "comma_zero_boundary a (5+h) =
          comma_boundary_value (Comma_Z,a,(5+h) mod 924) (5+h)"
        by (simp add: comma_zero_boundary_def comma_boundary_value_def)
      from child_cases show ?thesis
      proof
        assume near_selected:
          "successor = comma_near_boundary a (5+h)"
        have tail_initial:
          "tail 0 = comma_near_boundary a (5+h)"
          using tail_start near_selected by simp
        have near_path:
          "comma_semantic_infinite_path comma_boundary_value
            (Comma_N,a,(5+h) mod 924) (5+h) tail"
          using tail_initial tail_edges_rule near_value
          by (simp add: comma_semantic_infinite_path_def)
        have near_exp: "5 \<le> 5+h" by simp
        have near_phase:
          "(5+h) mod 924 = snd (snd (Comma_N,a,(5+h) mod 924))"
          by simp
        have near_rank:
          "comma_semantic_concrete_future_rank
            (Comma_N,a,(5+h) mod 924) = None"
          by (rule comma_semantic_infinite_boundary_path_unranked
            [OF near_path near_valid near_exp near_phase])
        show ?thesis
          unfolding comma_semantic_p5_entry_future_open_def
          using summary_lookup near_valid zero_valid near_rank terminal_eq
          by simp
      next
        assume zero_selected:
          "successor = comma_zero_boundary a (5+h)"
        have tail_initial:
          "tail 0 = comma_zero_boundary a (5+h)"
          using tail_start zero_selected by simp
        have zero_path:
          "comma_semantic_infinite_path comma_boundary_value
            (Comma_Z,a,(5+h) mod 924) (5+h) tail"
          using tail_initial tail_edges_rule zero_value
          by (simp add: comma_semantic_infinite_path_def)
        have zero_exp: "5 \<le> 5+h" by simp
        have zero_phase:
          "(5+h) mod 924 = snd (snd (Comma_Z,a,(5+h) mod 924))"
          by simp
        have zero_rank:
          "comma_semantic_concrete_future_rank
            (Comma_Z,a,(5+h) mod 924) = None"
          by (rule comma_semantic_infinite_boundary_path_unranked
            [OF zero_path zero_valid zero_exp zero_phase])
        show ?thesis
          unfolding comma_semantic_p5_entry_future_open_def
          using summary_lookup near_valid zero_valid zero_rank terminal_eq
          by simp
      qed
    qed
    show ?thesis by (rule semantic_open)
  qed
qed


ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
    comma_semantic_p5_entry_future_open_checked
    comma_semantic_infinite_boundary_path_unranked
    comma_semantic_p5_entry_infinite_imp_open
  }) then ()
  else error "Comma_Semantic_Entry_Open local oracle audit failed"
\<close>
end
