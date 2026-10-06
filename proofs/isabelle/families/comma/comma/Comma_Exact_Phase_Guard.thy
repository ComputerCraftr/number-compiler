theory Comma_Exact_Phase_Guard
  imports Comma_Child_Classification
begin

text \<open>The bounded phase guard uses every prefix of a period.  This is
the semantic condition consumed by the production cycle transfer's
PrefixSafety summary, rather than the coarser uniform 99 bound.\<close>

definition comma_phase_digit :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_phase_digit f d j = (d + j * f) mod 10"

definition comma_phase_guard_at :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_phase_guard_at f d j =
    comma_period_displacement f d j +
      10 * comma_phase_digit f d j + (if f < 9 then f + 1 else 9)"

definition comma_phase_max_guard :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_phase_max_guard f d steps =
    Max (insert 0 (comma_phase_guard_at f d ` {..<steps}))"

lemma comma_phase_guard_below_max:
  assumes "j < steps"
  shows "comma_phase_guard_at f d j \<le> comma_phase_max_guard f d steps"
proof -
  have member: "comma_phase_guard_at f d j \<in>
      insert 0 (comma_phase_guard_at f d ` {..<steps})"
    using assms by auto
  have finite: "finite (insert 0 (comma_phase_guard_at f d ` {..<steps}))"
    by simp
  show ?thesis
    unfolding comma_phase_max_guard_def
    by (rule Max_ge[OF finite member])
qed

lemma comma_phase_guard_same_sector:
  assumes source: "comma_sector f p k"
    and bound: "comma_phase_max_guard f (k mod 10) steps <
      comma_headroom f p k"
    and j: "j < steps"
  shows "comma_sector f p (comma_fixed_iter f j k)"
proof -
  let ?d = "k mod 10"
  let ?v = "comma_fixed_iter f j k"
  let ?prefix = "comma_period_displacement f ?d j"
  have guard: "?prefix < comma_headroom f p k"
    using comma_phase_guard_below_max[OF j, of f ?d] bound
    by (simp add: comma_phase_guard_at_def; linarith)
  have exact: "?v = k + ?prefix"
    by (rule comma_fixed_iter_displacement)
  have sum: "k + comma_headroom f p k = (f + 1) * 10 ^ p"
    using comma_sector_headroom[OF source] .
  show ?thesis using source guard exact sum
    by (auto simp: comma_sector_def; linarith)
qed

lemma comma_phase_guard_unique_step:
  assumes source: "comma_sector f p k"
    and exponent: "2 \<le> p"
    and bound: "comma_phase_max_guard f (k mod 10) steps <
      comma_headroom f p k"
    and j: "j < steps"
  shows "comma_child (comma_fixed_iter f j k)
      (comma_fixed_iter f (Suc j) k)"
    "\<And>target. comma_child (comma_fixed_iter f j k) target \<Longrightarrow>
      target = comma_fixed_iter f (Suc j) k"
proof -
  let ?d = "k mod 10"
  let ?v = "comma_fixed_iter f j k"
  let ?prefix = "comma_period_displacement f ?d j"
  let ?phase = "comma_phase_digit f ?d j"
  have admitted: "comma_sector f p ?v"
    by (rule comma_phase_guard_same_sector[OF source bound j])
  have phase: "?v mod 10 = ?phase"
    by (simp add: comma_phase_digit_def comma_fixed_iter_phase)
  have exact: "?v = k + ?prefix"
    by (rule comma_fixed_iter_displacement)
  have headroom: "comma_headroom f p ?v + ?prefix =
      comma_headroom f p k"
    using comma_sector_headroom[OF source]
      comma_sector_headroom[OF admitted] exact by arith
  have guard: "?prefix + 10 * ?phase +
      (if f < 9 then f + 1 else 9) < comma_headroom f p k"
    using comma_phase_guard_below_max[OF j, of f ?d] bound
    by (simp add: comma_phase_guard_at_def; linarith)
  have step: "comma_fixed_iter f (Suc j) k = ?v + 10 * ?phase + f"
    using phase by simp
  show edge: "comma_child ?v (comma_fixed_iter f (Suc j) k)"
  proof (cases "f < 9")
    case True
    have classified: "\<And>x. comma_child ?v x \<longleftrightarrow>
        (x = ?v + 10 * ?phase + f \<and>
          10 * ?phase + f < comma_headroom f p ?v) \<or>
        (x = ?v + 10 * ?phase + f + 1 \<and>
          comma_headroom f p ?v \<le> 10 * ?phase + f + 1)"
      using comma_below_nine_complete_children[OF admitted True exponent]
        phase by simp
    have strict: "10 * ?phase + f + 1 < comma_headroom f p ?v"
      using guard headroom True by simp
    show ?thesis using classified[of "comma_fixed_iter f (Suc j) k"]
      strict step by simp
  next
    case False
    have nine: "f = 9" using source False
      by (auto simp: comma_sector_def)
    have source9: "comma_sector 9 p ?v" using admitted nine by simp
    have classified: "\<And>x. comma_child ?v x \<longleftrightarrow>
        (x = ?v + 10 * ?phase + 9 \<and>
          10 * ?phase + 9 < comma_headroom 9 p ?v) \<or>
        (x = ?v + 10 * ?phase + 1 \<and>
          comma_headroom 9 p ?v \<le> 10 * ?phase + 1)"
      using comma_nine_complete_children[OF source9 exponent]
        phase by simp
    have strict: "10 * ?phase + 9 < comma_headroom 9 p ?v"
      using guard headroom nine by simp
    show ?thesis using classified[of "comma_fixed_iter f (Suc j) k"]
      strict step nine by simp
  qed
  fix target
  assume child: "comma_child ?v target"
  show "target = comma_fixed_iter f (Suc j) k"
  proof (cases "f < 9")
    case True
    have classified: "\<And>x. comma_child ?v x \<longleftrightarrow>
        (x = ?v + 10 * ?phase + f \<and>
          10 * ?phase + f < comma_headroom f p ?v) \<or>
        (x = ?v + 10 * ?phase + f + 1 \<and>
          comma_headroom f p ?v \<le> 10 * ?phase + f + 1)"
      using comma_below_nine_complete_children[OF admitted True exponent]
        phase by simp
    have strict: "10 * ?phase + f + 1 < comma_headroom f p ?v"
      using guard headroom True by simp
    show ?thesis using classified[of target] child strict step by auto
  next
    case False
    have nine: "f = 9" using source False
      by (auto simp: comma_sector_def)
    have source9: "comma_sector 9 p ?v" using admitted nine by simp
    have classified: "\<And>x. comma_child ?v x \<longleftrightarrow>
        (x = ?v + 10 * ?phase + 9 \<and>
          10 * ?phase + 9 < comma_headroom 9 p ?v) \<or>
        (x = ?v + 10 * ?phase + 1 \<and>
          comma_headroom 9 p ?v \<le> 10 * ?phase + 1)"
      using comma_nine_complete_children[OF source9 exponent]
        phase by simp
    have strict: "10 * ?phase + 9 < comma_headroom 9 p ?v"
      using guard headroom nine by simp
    show ?thesis using classified[of target] child strict step nine by auto
  qed
qed

theorem comma_exact_phase_unique_path:
  assumes source: "comma_sector f p k"
    and exponent: "2 \<le> p"
    and bound: "comma_phase_max_guard f (k mod 10) steps <
      comma_headroom f p k"
  shows "\<forall>j<steps. comma_child (comma_fixed_iter f j k)
      (comma_fixed_iter f (Suc j) k) \<and>
      (\<forall>target. comma_child (comma_fixed_iter f j k) target \<longrightarrow>
        target = comma_fixed_iter f (Suc j) k)"
    "\<forall>j\<le>steps. rtranclp comma_child k (comma_fixed_iter f j k)"
proof -
  show edges: "\<forall>j<steps. comma_child (comma_fixed_iter f j k)
      (comma_fixed_iter f (Suc j) k) \<and>
      (\<forall>target. comma_child (comma_fixed_iter f j k) target \<longrightarrow>
        target = comma_fixed_iter f (Suc j) k)"
    using comma_phase_guard_unique_step[OF source exponent bound] by blast
  show "\<forall>j\<le>steps. rtranclp comma_child k (comma_fixed_iter f j k)"
  proof (intro allI impI)
    fix j
    assume within: "j \<le> steps"
    show "rtranclp comma_child k (comma_fixed_iter f j k)"
      using within
    proof (induction j)
      case 0
      then show ?case by simp
    next
      case (Suc j)
      have j: "j < steps" using Suc.prems by simp
      have path: "rtranclp comma_child k (comma_fixed_iter f j k)"
        using Suc.IH j by simp
      have edge: "comma_child (comma_fixed_iter f j k)
          (comma_fixed_iter f (Suc j) k)"
        using edges j by blast
      show ?case using path edge
        by (meson rtranclp.rtrancl_into_rtrancl)
    qed
  qed
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_phase_guard_below_max comma_phase_guard_same_sector
      comma_phase_guard_unique_step comma_exact_phase_unique_path})
    then () else error "Comma exact phase guard proof depends on an oracle";
\<close>
end
