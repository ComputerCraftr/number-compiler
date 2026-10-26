theory Comma_Fast_Decade_Rank
  imports Comma_Decade_Residual_Core.Comma_Decade_Residual_Core
    Comma_Total_Macro.Comma_Total_Macro
begin

text \<open>Candidate ranks and terminal labels are untrusted data. Each row
checks one actual control transition; neither a successor table nor a bounded
trajectory is accepted as evidence.\<close>

definition comma_fast_decade_rank_step ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow> comma_decade_state \<Rightarrow> bool" where
  "comma_fast_decade_rank_step rank s =
    (case comma_fast_decade_control s of
       Comma_Decade_Continue t \<Rightarrow> comma_decade_admitted t \<and> rank t < rank s
     | Comma_Decade_Invalid \<Rightarrow> False
     | _ \<Rightarrow> True)"

lemma comma_fast_decade_rank_step_correct:
  assumes "comma_decade_admitted s"
  shows "comma_fast_decade_rank_step rank s =
    (case comma_decade_control s of
       Comma_Decade_Continue t \<Rightarrow> comma_decade_admitted t \<and> rank t < rank s
     | Comma_Decade_Invalid \<Rightarrow> False
     | _ \<Rightarrow> True)"
  using comma_fast_decade_control_correct[OF assms]
  by (simp only: comma_fast_decade_rank_step_def)

definition comma_fast_decade_rank_check :: "(comma_decade_state \<Rightarrow> nat) \<Rightarrow> bool" where
  "comma_fast_decade_rank_check rank =
    list_all (\<lambda>r. list_all
      (\<lambda>x. comma_fast_decade_rank_step rank (Comma_Decade r x))
      [0..<91]) [0..<924]"

definition comma_fast_decade_rank_range ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_fast_decade_rank_range rank lo hi =
    list_all (\<lambda>r. list_all
      (\<lambda>x. comma_fast_decade_rank_step rank (Comma_Decade r x)) [0..<91]) [lo..<hi]"

lemma comma_fast_decade_rank_range_join:
  assumes "lo\<le>mid" "mid\<le>hi"
  shows "comma_fast_decade_rank_range rank lo hi =
    (comma_fast_decade_rank_range rank lo mid \<and>
     comma_fast_decade_rank_range rank mid hi)"
  using assms by (auto simp: comma_fast_decade_rank_range_def list_all_iff)

lemma comma_fast_decade_rank_range_full:
  "comma_fast_decade_rank_range rank 0 924=comma_fast_decade_rank_check rank"
  by (simp only: comma_fast_decade_rank_range_def comma_fast_decade_rank_check_def)

theorem comma_fast_decade_rank_check_correct:
  "comma_fast_decade_rank_check rank = comma_decade_rank_check rank"
  unfolding comma_fast_decade_rank_check_def comma_decade_rectangle comma_decade_rank_check_def
  by (simp add: comma_fast_decade_rank_step_correct)

theorem comma_fast_decade_rank_check_sound:
  "comma_fast_decade_rank_check rank \<Longrightarrow> comma_decade_rank_check rank"
  by (simp only: comma_fast_decade_rank_check_correct)

corollary comma_fast_decade_checked_rank_totality:
  assumes "comma_fast_decade_rank_check rank" "comma_decade_admitted s"
  shows "\<exists>n. comma_decade_finishes s n \<and> n \<le> Suc (rank s)"
  by (rule comma_decade_checked_rank_totality
    [OF comma_fast_decade_rank_check_sound[OF assms(1)] assms(2)])

corollary comma_fast_decade_checked_rank_bounded:
  assumes "comma_fast_decade_rank_check rank" "comma_decade_admitted s" "rank s\<le>bound"
  shows "\<exists>n. comma_decade_finishes s n \<and> n\<le>Suc bound"
  using comma_fast_decade_checked_rank_totality[OF assms(1,2)] assms(3) by auto

definition comma_fast_decade_bounded_rank_step ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> comma_decade_state \<Rightarrow> bool" where
  "comma_fast_decade_bounded_rank_step rank bound s =
    (rank s\<le>bound \<and> comma_fast_decade_rank_step rank s)"

definition comma_fast_decade_bounded_rank_range ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_fast_decade_bounded_rank_range rank bound lo hi =
    list_all (\<lambda>r. list_all
      (\<lambda>x. comma_fast_decade_bounded_rank_step rank bound (Comma_Decade r x))
      [0..<91]) [lo..<hi]"

lemma comma_fast_decade_bounded_rank_range_join:
  assumes "lo\<le>mid" "mid\<le>hi"
  shows "comma_fast_decade_bounded_rank_range rank bound lo hi =
    (comma_fast_decade_bounded_rank_range rank bound lo mid \<and>
     comma_fast_decade_bounded_rank_range rank bound mid hi)"
  using assms by (auto simp: comma_fast_decade_bounded_rank_range_def list_all_iff)

theorem comma_fast_decade_bounded_rank_range_sound:
  assumes "comma_fast_decade_bounded_rank_range rank bound 0 924"
  shows "comma_decade_rank_check rank"
    "\<And>s. comma_decade_admitted s \<Longrightarrow> rank s\<le>bound"
proof -
  have checked_rows: "\<forall>s. comma_decade_admitted s \<longrightarrow>
    comma_fast_decade_bounded_rank_step rank bound s"
    using assms
    by (simp only: comma_fast_decade_bounded_rank_range_def comma_decade_rectangle)
  have rows: "\<forall>s. comma_decade_admitted s \<longrightarrow>
    rank s\<le>bound \<and> comma_fast_decade_rank_step rank s"
    using checked_rows by (simp only: comma_fast_decade_bounded_rank_step_def)
  have "comma_fast_decade_rank_check rank"
    using rows unfolding comma_fast_decade_rank_check_def comma_decade_rectangle by blast
  then show "comma_decade_rank_check rank"
    by (rule comma_fast_decade_rank_check_sound)
  fix s assume "comma_decade_admitted s"
  then show "rank s\<le>bound" using rows by blast
qed

corollary comma_fast_decade_bounded_rank_range_totality:
  assumes checked: "comma_fast_decade_bounded_rank_range rank bound 0 924"
    and valid: "comma_decade_admitted s"
  shows "\<exists>n. comma_decade_finishes s n \<and> n\<le>Suc bound"
  using comma_decade_checked_rank_totality
    [OF comma_fast_decade_bounded_rank_range_sound(1)[OF checked] valid]
    comma_fast_decade_bounded_rank_range_sound(2)[OF checked valid] by auto

lemma comma_fast_decade_summary_rank:
  "comma_fast_decade_summary_step height terminal s \<Longrightarrow>
    comma_fast_decade_rank_step height s"
  unfolding comma_fast_decade_summary_step_def comma_decade_summary_step_for_def
    comma_fast_decade_rank_step_def
  by (cases "comma_fast_decade_control s") auto

theorem comma_decade_summary_checked_rank:
  assumes "comma_decade_summary_checked height terminal"
  shows "comma_decade_rank_check height"
  apply (rule comma_fast_decade_rank_check_sound)
  unfolding comma_fast_decade_rank_check_def comma_decade_rectangle
  using comma_fast_decade_summary_rank comma_decade_summary_row[OF assms] by blast

corollary comma_residual_classifier_rank:
  assumes classifier: "comma_decade_residual_classifier_ok C"
  shows "comma_decade_rank_check (\<lambda>s. fst (C s))"
proof -
  have canonical:
    "\<And>s. comma_decade_admitted s \<Longrightarrow>
      comma_decade_summary_step (\<lambda>s. fst (C s)) (\<lambda>s. snd (C s)) s"
    using classifier by (auto simp: comma_decade_residual_classifier_ok_def)
  have fast:
    "\<And>s. comma_decade_admitted s \<Longrightarrow>
      comma_fast_decade_summary_step (\<lambda>s. fst (C s)) (\<lambda>s. snd (C s)) s"
  proof -
    fix s assume admitted: "comma_decade_admitted s"
    have equal:
      "comma_fast_decade_summary_step (\<lambda>s. fst (C s)) (\<lambda>s. snd (C s)) s =
       comma_decade_summary_step (\<lambda>s. fst (C s)) (\<lambda>s. snd (C s)) s"
      by (rule comma_fast_decade_summary_step_correct[OF admitted])
    show "comma_fast_decade_summary_step (\<lambda>s. fst (C s)) (\<lambda>s. snd (C s)) s"
      using canonical[OF admitted] equal by simp
  qed
  have fast_check: "comma_fast_decade_rank_check (\<lambda>s. fst (C s))"
    unfolding comma_fast_decade_rank_check_def comma_decade_rectangle
    using fast comma_fast_decade_summary_rank by blast
  show ?thesis by (rule comma_fast_decade_rank_check_sound[OF fast_check])
qed

corollary comma_boundary_macro_exists_from_checked_rank:
  assumes checked: "comma_decade_rank_check rank"
    and valid: "comma_boundary_valid q"
  shows "comma_macro_defined q"
  by (rule comma_boundary_macro_exists[OF _ valid])
    (use comma_decade_checked_rank_totality[OF checked] in blast)

corollary comma_total_macro_from_checked_rank:
  assumes "comma_decade_rank_check rank" "comma_boundary_valid q"
  shows "\<exists>fuel. comma_finite_macro fuel q=Some (comma_total_macro q)"
  by (rule comma_total_macro_correct[OF comma_boundary_macro_exists_from_checked_rank[OF assms]])

corollary comma_total_weighted_macro_from_checked_rank:
  assumes "comma_decade_rank_check rank" "comma_boundary_valid q"
    "5\<le>p" "p mod 924=snd (snd q)"
  shows "\<exists>fuel. comma_finite_weighted_macro fuel p q=
    Some (comma_total_weighted_macro p q)"
  by (rule comma_total_weighted_macro_correct[OF comma_macro_defined_weighted
    [OF comma_boundary_macro_exists_from_checked_rank[OF assms(1,2)] assms(3,4)]])

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_boundary_macro_exists_from_checked_rank
      comma_total_macro_from_checked_rank comma_total_weighted_macro_from_checked_rank
      comma_fast_decade_rank_check_correct comma_fast_decade_checked_rank_totality
      comma_fast_decade_bounded_rank_range_sound comma_fast_decade_bounded_rank_range_totality
      comma_decade_summary_checked_rank comma_residual_classifier_rank
      comma_decade_checked_rank_residual comma_decade_checked_rank_B32})
    then () else error "Fast decade rank regression depends on an oracle";
\<close>
end
