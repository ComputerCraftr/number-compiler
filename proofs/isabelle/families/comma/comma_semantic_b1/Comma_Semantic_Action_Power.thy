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

ML \<open>
  val checked = @{thms
    comma_semantic_b1_action_power_refines_orbit};
  val _ = Thm.consolidate checked;
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Representation-independent semantic B1 action power" checked;
\<close>

end
