theory Comma_Prefix_Selection
  imports Comma_Closed_Near.Comma_Closed_Near
begin

text \<open>Executable bisection on physical prefix weights. This stores no
weighted port tree. The interval width decreases; it is not a fuel parameter.\<close>

function comma_prefix_select ::
  "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_prefix_select P b lo hi =
    (if Suc lo < hi then
      (let m = (lo+hi) div 2 in
       if P m \<le> b then comma_prefix_select P b m hi
       else comma_prefix_select P b lo m)
     else lo)"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(P,b,lo,hi). hi-lo)")
  apply simp
  apply (simp add: Let_def)
  by (simp add: Let_def)

declare comma_prefix_select.simps [simp del]

lemma comma_prefix_select_interval:
  assumes "lo < hi" "P lo \<le> b" "b < P hi"
  shows "lo \<le> comma_prefix_select P b lo hi \<and>
    comma_prefix_select P b lo hi < hi \<and>
    P (comma_prefix_select P b lo hi) \<le> b \<and>
    b < P (Suc (comma_prefix_select P b lo hi))"
  using assms
proof (induction P b lo hi rule: comma_prefix_select.induct)
  case (1 P b lo hi)
  note prems = "1.prems"
  note ih = "1.IH"
  show ?case
  proof (cases "Suc lo < hi")
    case False
    have adjacent: "hi = Suc lo" using prems False by arith
    have endpoint: "b < P (Suc lo)" using prems(3) adjacent by simp
    show ?thesis using prems False endpoint
      by (simp only: comma_prefix_select.simps[of P b lo hi]) simp
  next
    case True
    let ?m = "(lo+hi) div 2"
    have mid: "lo < ?m" "?m < hi" using True by presburger+
    show ?thesis
    proof (cases "P ?m \<le> b")
      case True
      have tail: "?m \<le> comma_prefix_select P b ?m hi \<and>
        comma_prefix_select P b ?m hi < hi \<and>
        P (comma_prefix_select P b ?m hi) \<le> b \<and>
        b < P (Suc (comma_prefix_select P b ?m hi))"
        using ih(1) prems mid True by auto
      show ?thesis using tail mid True \<open>Suc lo < hi\<close>
        by (simp only: comma_prefix_select.simps[of P b lo hi]) (auto simp: Let_def)
    next
      case False
      have tail: "lo \<le> comma_prefix_select P b lo ?m \<and>
        comma_prefix_select P b lo ?m < ?m \<and>
        P (comma_prefix_select P b lo ?m) \<le> b \<and>
        b < P (Suc (comma_prefix_select P b lo ?m))"
        using ih(2) prems mid False by auto
      show ?thesis using tail mid False \<open>Suc lo < hi\<close>
        by (simp only: comma_prefix_select.simps[of P b lo hi]) (auto simp: Let_def)
    qed
  qed
qed

lemma comma_prefix_interval_unique:
  fixes P :: "nat \<Rightarrow> nat"
  assumes "mono P" "P i \<le> b" "b < P (Suc i)"
    "P j \<le> b" "b < P (Suc j)"
  shows "i=j"
proof (rule ccontr)
  assume "i \<noteq> j"
  then consider "Suc i \<le> j" | "Suc j \<le> i" by arith
  then show False
  proof cases
    case 1
    have "P (Suc i) \<le> P j" using assms(1) 1 by (rule monoD)
    then show False using assms by arith
  next
    case 2
    have "P (Suc j) \<le> P i" using assms(1) 2 by (rule monoD)
    then show False using assms by arith
  qed
qed

lemma comma_prefix_select_refines_residual:
  assumes "d<10" "0<L"
    "b < comma_period_displacement f d L"
    "comma_near_residual_count (L-1) f d b=(j,u)"
  shows "comma_prefix_select (comma_period_displacement f d) b 0 L=j"
proof -
  have initial: "comma_period_displacement f d 0 \<le> b"
    by (simp add: comma_period_displacement_def)
  have selected: "comma_period_displacement f d
      (comma_prefix_select (comma_period_displacement f d) b 0 L) \<le> b"
    "b < comma_period_displacement f d
      (Suc (comma_prefix_select (comma_period_displacement f d) b 0 L))"
    using comma_prefix_select_interval[OF assms(2) initial assms(3)] by auto
  have reference: "comma_period_displacement f d j+u=b"
    "b < comma_period_displacement f d (Suc j)"
    by (rule comma_near_residual_maximal[OF assms])+
  have monotone: "mono (comma_period_displacement f d)"
    by (rule monoI, rule comma_period_displacement_mono)
  show ?thesis
    by (rule comma_prefix_interval_unique[OF monotone selected _ reference(2)])
       (use reference(1) in arith)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms
    comma_prefix_select_interval comma_prefix_select_refines_residual})
    then () else error "Prefix selection depends on an oracle";
\<close>
end
