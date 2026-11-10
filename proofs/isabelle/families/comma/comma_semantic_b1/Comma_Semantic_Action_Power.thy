theory Comma_Semantic_Action_Power
  imports Comma_Semantic_B1
begin

text \<open>
  This is the representation-independent powered B1 action.  Its base case
  is the existing functional B1 action and its successor case is chronological
  semantic composition.  The orbit word is used only by the refinement proof;
  there is no dependency on a CRT column, lift binding, MDD, or concrete
  occurrence publisher.  The concrete split representation may later be
  proved to represent this action at an output boundary; it is not part of
  the semantic power contract.
\<close>

fun comma_semantic_b1_action_power ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result" where
  "comma_semantic_b1_action_power 0 phase root =
    comma_semantic_b1 phase root"
| "comma_semantic_b1_action_power (Suc k) phase root =
    comma_semantic_word_then (2^k)
      (comma_semantic_b1_action_power k)
      (comma_semantic_b1_action_power k) phase root"

lemma comma_semantic_b1_action_power_refines_orbit:
  assumes phase: "phase<924" and root: "root<46"
  shows "comma_semantic_b1_action_power k phase root =
    comma_semantic_b1_of_word (comma_orbit_word k phase root)"
  using phase root
proof (induction k arbitrary: phase root)
  case 0
  show ?case
    using comma_semantic_b1_exact_orbit[OF "0.prems"]
    by simp
next
  case (Suc k)
  have phase: "phase<924" using Suc.prems(1) .
  have root: "root<46" using Suc.prems(2) .
  have left_refine:
    "comma_semantic_b1_action_power k phase root =
      comma_semantic_b1_of_word (comma_orbit_word k phase root)"
    by (rule Suc.IH[OF phase root])
  have word_square:
    "comma_orbit_word (Suc k) phase root =
      comma_word_then (2^k) (comma_orbit_word k) (comma_orbit_word k)
        phase root"
    by (rule comma_orbit_word_square[OF phase root])
  have semantic_square:
    "comma_semantic_b1_of_word (comma_orbit_word (Suc k) phase root) =
      comma_semantic_word_then (2^k)
        (\<lambda>p i. comma_semantic_b1_of_word (comma_orbit_word k p i))
        (\<lambda>p i. comma_semantic_b1_of_word (comma_orbit_word k p i))
        phase root"
    using word_square
      comma_semantic_b1_of_word_then
        [of "2^k" "comma_orbit_word k" "comma_orbit_word k" phase root]
    by simp
  have composition_eq:
    "comma_semantic_word_then (2^k)
        (comma_semantic_b1_action_power k)
        (comma_semantic_b1_action_power k) phase root =
      comma_semantic_word_then (2^k)
        (\<lambda>p i. comma_semantic_b1_of_word (comma_orbit_word k p i))
        (\<lambda>p i. comma_semantic_b1_of_word (comma_orbit_word k p i))
        phase root"
  proof (cases "comma_semantic_b1_action_power k phase root")
    case (Comma_Semantic_B1_Live next_root)
    note current = Comma_Semantic_B1_Live
    have orbit_live:
      "comma_orbit_word k phase root = Comma_Word_Live next_root"
    proof (cases "comma_orbit_word k phase root")
      case (Comma_Word_Live output_root)
      note word = Comma_Word_Live
      have same: "output_root=next_root"
        using current left_refine by (simp add: word)
      show ?thesis using word same by simp
    next
      case (Comma_Word_Stop height terminal)
      then show ?thesis using current left_refine by simp
    next
      case Comma_Word_Invalid
      then show ?thesis using current left_refine by simp
    qed
    have next_root_bound: "next_root<46"
      by (rule comma_orbit_word_live_bound[OF orbit_live])
    have next_phase_bound: "((phase+2^k) mod 924)<924"
      by simp
    have right_refine:
      "comma_semantic_b1_action_power k ((phase+2^k) mod 924) next_root =
        comma_semantic_b1_of_word
          (comma_orbit_word k ((phase+2^k) mod 924) next_root)"
      by (rule Suc.IH[OF next_phase_bound next_root_bound])
    show ?thesis
      using current left_refine right_refine
      by (simp add: comma_semantic_word_then_def)
  next
    case (Comma_Semantic_B1_Stop D)
    note current = Comma_Semantic_B1_Stop
    show ?thesis
      using current left_refine
      by (simp add: comma_semantic_word_then_def)
  next
    case Comma_Semantic_B1_Invalid
    note current = Comma_Semantic_B1_Invalid
    show ?thesis
      using current left_refine
      by (simp add: comma_semantic_word_then_def)
  qed
  show ?case
    using composition_eq semantic_square by simp
qed

lemma comma_semantic_b1_action_stop_from_exact_summary:
  assumes phase: "phase<924" and root: "root<46"
    and summary: "comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives!root)) h terminal"
    and height_bound: "h\<le>26"
  shows "comma_semantic_b1_action_power 5 phase root =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode h terminal)
    \<and> comma_terminal_weight_encode h terminal\<le>242"
proof -
  let ?source = "Comma_Decade phase (comma_offset_representatives!root)"
  have representative: "comma_offset_representatives!root\<le>90"
    and representative_index:
      "comma_offset_orbit (comma_offset_representatives!root)=root"
    using comma_orbit_representative_index[OF root] by auto
  have admitted: "comma_decade_admitted ?source"
    using phase representative by simp
  have block_run_stop:
    "comma_decade_block_run 32 ?source=Comma_Block_Stop h terminal"
    by (rule comma_decade_exact_summary_block_stop[OF summary admitted])
      (use height_bound in arith)
  have block_stop:
    "comma_decade_block_power 5 ?source=Comma_Block_Stop h terminal"
    using block_run_stop by (simp add: comma_decade_block_square_refines)
  have orbit_refinement:
    "comma_word_project comma_offset_orbit
        (comma_decade_block_power 5 ?source)=comma_orbit_word 5 phase root"
    using comma_orbit_word_refines[OF admitted] representative_index by simp
  have orbit_stop: "comma_orbit_word 5 phase root=Comma_Word_Stop h terminal"
    using orbit_refinement block_stop by simp
  have semantic_refinement:
    "comma_semantic_b1_action_power 5 phase root=
      comma_semantic_b1_of_word (comma_orbit_word 5 phase root)"
    by (rule comma_semantic_b1_action_power_refines_orbit[OF phase root])
  have action_equation:
    "comma_semantic_b1_action_power 5 phase root=
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode h terminal)"
    using semantic_refinement orbit_stop by simp
  have terminal_admitted:
    "comma_terminal_weight_admitted terminal"
    by (rule comma_decade_exact_summary_terminal_admitted[OF summary])
  have digit_bound: "comma_terminal_weight_digit terminal<9"
    by (rule comma_terminal_weight_digit_bound[OF terminal_admitted])
  have weight_bound: "comma_terminal_weight_encode h terminal\<le>242"
    using height_bound digit_bound
    by (simp add: comma_terminal_weight_encode_def; arith)
  show ?thesis using action_equation weight_bound by blast
qed

ML \<open>
  val checked = @{thms
    comma_semantic_b1_action_power_refines_orbit
    comma_semantic_b1_action_stop_from_exact_summary};
  val _ = Thm.consolidate checked;
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Representation-independent semantic B1 action power" checked;
\<close>

end
