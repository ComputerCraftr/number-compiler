theory Reverse_Growth_Run_Admission
  imports "Reverse_Residuals.Reverse_Invariant"
begin

text \<open>The growth-run bound is derived from the actual symmetric source
pair field and physical LSD-to-MSD carry. It is not an assumed grammar bound.
This removes a premise used in live radial reduction; it does not construct
future pair fields, carry domains, or a powered output morphism.\<close>

definition edge_growth_rank :: "nat \<Rightarrow> nat" where
  "edge_growth_rank e = (if e=18 then 3 else if e=9 then 2
    else if 10 \<le> e then 1 else 0)"

lemma edge_growth_rank_bound: "edge_growth_rank e \<le> 3"
  by (simp add: edge_growth_rank_def)

lemma edge_growth_rank_decreases:
  assumes "9 \<le> e" "e \<le> 18"
  shows "edge_growth_rank (1+e mod 10)+1 = edge_growth_rank e"
proof -
  have "e=9 \<or> e=10 \<or> e=11 \<or> e=12 \<or> e=13 \<or> e=14 \<or>
    e=15 \<or> e=16 \<or> e=17 \<or> e=18" using assms by arith
  then show ?thesis by (auto simp: edge_growth_rank_def)
qed

lemma source_growth_requires_edge:
  assumes valid: "valid_pair ss" and growth: "carry_out False ss"
  shows "9 \<le> hd ss" "hd ss \<le> 18"
proof -
  have nonempty: "ss \<noteq> []" and symmetric: "rev ss=ss"
    and bounded: "\<forall>s\<in>set ss. s \<le> 18"
    using valid unfolding valid_pair_def by auto
  have mirror: "hd ss = last ss" using nonempty symmetric by (metis hd_rev)
  obtain xs a where snoc: "ss=xs@[a]" using nonempty by (cases ss rule: rev_cases) auto
  have "carry_apply (domain a) (carry_out False xs)"
    using growth by (simp add: snoc carry_out_def fold_append)
  then have "9 \<le> a" by (auto simp: domain_def split: if_splits)
  then show "9 \<le> hd ss" using mirror by (simp add: snoc)
  show "hd ss \<le> 18" using bounded hd_in_set[OF nonempty] by blast
qed

lemma source_growth_edge_successor:
  assumes "ss \<noteq> []" "carry_out False ss"
  shows "hd (step ss) = 1 + hd ss mod 10"
  using assms by (cases ss) (simp_all add: step_def digits_def)

lemma source_growth_rank_decreases:
  assumes "valid_pair ss" "carry_out False ss"
  shows "edge_growth_rank (hd (step ss))+1 = edge_growth_rank (hd ss)"
proof -
  have nonempty: "ss \<noteq> []" using assms(1) by (simp add: valid_pair_def)
  have eq: "hd (step ss) = 1 + hd ss mod 10"
    by (rule source_growth_edge_successor[OF nonempty assms(2)])
  have drop: "edge_growth_rank (1+hd ss mod 10)+1 = edge_growth_rank (hd ss)"
    by (rule edge_growth_rank_decreases[OF source_growth_requires_edge(1)[OF assms]
      source_growth_requires_edge(2)[OF assms]])
  show ?thesis by (simp only: eq drop)
qed

fun source_growth_count :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "source_growth_count 0 ss = 0"
| "source_growth_count (Suc n) ss =
    (if carry_out False ss then 1 else 0) + source_growth_count n (step ss)"

fun source_no_growth_count :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "source_no_growth_count 0 ss = 0"
| "source_no_growth_count (Suc n) ss =
    (if carry_out False ss then 0 else 1) + source_no_growth_count n (step ss)"

lemma source_growth_accounting:
  "source_growth_count n ss + source_no_growth_count n ss = n"
  by (induct n arbitrary: ss) auto

theorem source_growth_potential:
  assumes "valid_pair ss"
  shows "source_growth_count n ss + edge_growth_rank (hd (run step n ss))
    \<le> 3 * source_no_growth_count n ss + edge_growth_rank (hd ss)"
using assms
proof (induct n arbitrary: ss)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have next_valid: "valid_pair (step ss)" by (rule valid_pair_successor[OF Suc.prems])
  have ih: "source_growth_count n (step ss) + edge_growth_rank (hd (run step n (step ss)))
    \<le> 3 * source_no_growth_count n (step ss) + edge_growth_rank (hd (step ss))"
    by (rule Suc.hyps[OF next_valid])
  show ?case
  proof (cases "carry_out False ss")
    case True
    have drop: "edge_growth_rank (hd (step ss))+1 = edge_growth_rank (hd ss)"
      by (rule source_growth_rank_decreases[OF Suc.prems True])
    show ?thesis using ih drop by (simp add: True; arith)
  next
    case False
    have bound: "edge_growth_rank (hd (step ss)) \<le> 3"
      by (rule edge_growth_rank_bound)
    show ?thesis using ih bound by (simp add: False; arith)
  qed
qed

theorem source_radial_growth_bound:
  assumes "valid_pair ss"
  shows "source_growth_count n ss \<le> 3*(source_no_growth_count n ss+1)"
  using source_growth_potential[OF assms, of n] edge_growth_rank_bound[of "hd ss"]
  by arith

corollary source_live_radial_age:
  assumes valid: "valid_pair ss" and live: "source_no_growth_count n ss < bits"
  shows "n < 4*bits" "source_growth_count n ss \<le> 3*bits"
  using source_radial_growth_bound[OF valid, of n] source_growth_accounting[of n ss] live
  by arith+

corollary source_196_live_radial_age:
  assumes "source_no_growth_count n (run step t [7,18,7]) < 5"
  shows "n < 20" "source_growth_count n (run step t [7,18,7]) \<le> 15"
  using source_live_radial_age[OF all_196_pair_fields_valid assms] by auto

corollary source_four_step_no_growth:
  assumes "valid_pair ss" "4 \<le> n"
  shows "1 \<le> source_no_growth_count n ss"
  using source_live_radial_age(1)[OF assms(1), of n 1] assms(2) by force

corollary source_block_parity_forcing:
  assumes "valid_pair ss" "4 \<le> n"
  shows "((2::int)^source_no_growth_count n ss * x + forcing) mod 2 =
    forcing mod 2"
proof -
  obtain q where q: "source_no_growth_count n ss = Suc q"
    using source_four_step_no_growth[OF assms] by (cases "source_no_growth_count n ss") auto
  have even: "((2::int)^source_no_growth_count n ss * x) mod 2 = 0"
    by (simp add: q power_Suc mult.assoc)
  have "((2::int)^source_no_growth_count n ss * x + forcing) mod 2 =
    (((2::int)^source_no_growth_count n ss * x) mod 2 + forcing mod 2) mod 2"
    by (rule mod_add_eq[symmetric])
  also have "... = forcing mod 2" by (simp add: even)
  finally show ?thesis .
qed

corollary source_196_block_parity_forcing:
  assumes "4 \<le> n"
  shows "((2::int)^source_no_growth_count n (run step t [7,18,7]) *
    x + forcing) mod 2 = forcing mod 2"
  by (rule source_block_parity_forcing[OF all_196_pair_fields_valid assms])

text \<open>Here x may include the entire neighbor-power contribution. Only
the homogeneous source term is erased. The forcing can still depend on the
original source through intervening carries and must be pulled back before
composing admitted blocks. No spatial scan or grammar-size bound follows.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms source_growth_requires_edge source_growth_edge_successor
      source_growth_rank_decreases source_growth_potential source_radial_growth_bound
      source_live_radial_age source_196_live_radial_age
      source_four_step_no_growth source_block_parity_forcing
      source_196_block_parity_forcing})
    then () else error "Source growth admission depends on an oracle";
\<close>

end
