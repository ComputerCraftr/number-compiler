theory Reverse_Pair_Temporal_Moments
  imports Reverse_Invariant Shared_Carry_Dynamics.Temporal_Moment_Algebra
begin

text \<open>The decimal value of the completed reverse/add pair is an exact
source observable.  The moment records below are projected from authenticated
pair-field endpoints; their composition is source-aligned and does not infer
an independent action from a finite port clock.\<close>

fun decimal_list_value :: "nat list \<Rightarrow> nat" where
  "decimal_list_value [] = 0"
| "decimal_list_value (d # ds) = d + 10 * decimal_list_value ds"

lemma decimal_list_value_append:
  "decimal_list_value (left @ right) = decimal_list_value left +
    10 ^ length left * decimal_list_value right"
  by (induction left) (simp_all add: algebra_simps power_Suc)

lemma carry_digit_balance:
  assumes bound: "s \<le> 18"
  shows "(s + (if carry then 1 else 0)) mod 10 +
      10 * (if carry_apply (domain s) carry then 1 else 0) =
    s + (if carry then 1 else 0)"
  using bound
proof (cases carry)
  case False
  then show ?thesis using bound
    by (simp add: domain_def carry_apply.simps split: if_splits; presburger)
next
  case True
  then show ?thesis using bound
    by (simp add: domain_def carry_apply.simps split: if_splits; presburger)
qed

lemma emit_decimal_balance:
  assumes bound: "\<forall>s\<in>set ss. s \<le> 18"
  shows "decimal_list_value (emit carry ss) +
      10 ^ length ss * (if carry_out carry ss then 1 else 0) =
    decimal_list_value ss + (if carry then 1 else 0)"
  using bound
proof (induction ss arbitrary: carry)
  case Nil
  then show ?case by (simp add: carry_out_def)
next
  case (Cons s ss)
  let ?next = "carry_apply (domain s) carry"
  have s_bound: "s \<le> 18" using Cons.prems by simp
  have tail_bound: "\<forall>x\<in>set ss. x \<le> 18" using Cons.prems by simp
  have tail:
    "decimal_list_value (emit ?next ss) +
        10 ^ length ss * (if carry_out ?next ss then 1 else 0) =
      decimal_list_value ss + (if ?next then 1 else 0)"
    using Cons.IH[of ?next] tail_bound by blast
  have carry_tail: "carry_out carry (s # ss) = carry_out ?next ss"
    by (simp add: carry_out_def)
  have digit:
    "(s + (if carry then 1 else 0)) mod 10 +
       10 * (if ?next then 1 else 0) = s + (if carry then 1 else 0)"
    by (rule carry_digit_balance[OF s_bound])
  show ?case
    using tail carry_tail digit s_bound
    by (simp add: algebra_simps power_Suc)
qed

theorem digits_preserve_decimal_value:
  assumes bounded: "\<forall>s\<in>set ss. s \<le> 18"
  shows "decimal_list_value (digits ss) = decimal_list_value ss"
proof -
  have balance:
    "decimal_list_value (emit False ss) +
        10 ^ length ss * (if carry_out False ss then 1 else 0) =
      decimal_list_value ss"
    using emit_decimal_balance[OF bounded, of False] by simp
  have append_value:
    "decimal_list_value (digits ss) = decimal_list_value (emit False ss) +
      10 ^ length ss * (if carry_out False ss then 1 else 0)"
    by (simp add: digits_def decimal_list_value_append)
  show ?thesis using balance append_value by simp
qed

lemma decimal_list_value_zip_add:
  assumes lengths: "length left = length right"
  shows "decimal_list_value
      (map (\<lambda>(a,b). a+b) (zip left right)) =
    decimal_list_value left + decimal_list_value right"
  using lengths
proof (induction left arbitrary: right)
  case Nil
  then show ?case by (cases right) simp_all
next
  case (Cons a left)
  then obtain b tail where right: "right = b # tail" by (cases right) auto
  have rest: "length left = length tail" using Cons.prems right by simp
  have ih: "decimal_list_value
      (map (\<lambda>(x,y). x+y) (zip left tail)) =
      decimal_list_value left + decimal_list_value tail"
    by (rule Cons.IH[OF rest])
  show ?case using ih right by (simp add: algebra_simps)
qed

definition reverse_add_pair_term :: "nat list \<Rightarrow> nat" where
  "reverse_add_pair_term ss = decimal_list_value (digits ss)"

definition reverse_add_pair_reverse :: "nat list \<Rightarrow> nat" where
  "reverse_add_pair_reverse ss = decimal_list_value (rev (digits ss))"

theorem reverse_add_completed_pair_successor:
  assumes valid: "valid_pair ss"
  shows "reverse_add_pair_term (step ss) =
    reverse_add_pair_term ss + reverse_add_pair_reverse ss"
proof -
  have bounded: "\<forall>s\<in>set ss. s \<le> 18"
    using valid unfolding valid_pair_def by blast
  have next_valid: "valid_pair (step ss)"
    using valid by (rule valid_pair_successor)
  have next_bounded: "\<forall>s\<in>set (step ss). s \<le> 18"
    using next_valid unfolding valid_pair_def by blast
  have digits_source: "decimal_list_value (digits ss) =
      decimal_list_value ss"
    by (rule digits_preserve_decimal_value[OF bounded])
  have digits_next: "decimal_list_value (digits (step ss)) =
      decimal_list_value (step ss)"
    by (rule digits_preserve_decimal_value[OF next_bounded])
  have zip_value:
    "decimal_list_value (step ss) =
      decimal_list_value (digits ss) +
        decimal_list_value (rev (digits ss))"
    unfolding step_def
    by (rule decimal_list_value_zip_add) simp
  show ?thesis
    unfolding reverse_add_pair_term_def reverse_add_pair_reverse_def
    using digits_source digits_next zip_value by simp
qed

definition reverse_add_interval_moments ::
    "nat list \<Rightarrow> nat \<Rightarrow> increment_moments" where
  "reverse_add_interval_moments source duration =
    (let first = run step duration source;
         x0 = int (reverse_add_pair_term source);
         x1 = int (reverse_add_pair_term first);
         r0 = int (reverse_add_pair_reverse source);
         r1 = int (reverse_add_pair_reverse first)
     in \<lparr>im_span = duration, im_sum = r1-r0,
          im_skew = x1-x0-int duration*r0\<rparr>)"

lemma run_commutes_with_step:
  "run step count (step source) = step (run step count source)"
  by (induction count arbitrary: source) simp_all

lemma reverse_add_run_add:
  "run step (first + second) source =
    run step second (run step first source)"
proof (induction second arbitrary: source)
  case 0
  then show ?case by simp
next
  case (Suc second)
  have ih: "run step (first + second) (step source) =
      run step second (run step first (step source))"
    by (rule Suc.IH)
  show ?case
    using ih run_commutes_with_step[of first source]
    by (simp add: add.commute)
qed

theorem reverse_add_interval_moments_source_aligned:
  "reverse_add_interval_moments source (first+second) =
    increment_moments_then
      (reverse_add_interval_moments source first)
      (reverse_add_interval_moments (run step first source) second)"
  unfolding reverse_add_interval_moments_def
  using reverse_add_run_add[of first second source]
  by (simp add: Let_def increment_moments_then_def algebra_simps)

ML \<open>
  val checked = @{thms decimal_list_value_append carry_digit_balance
    emit_decimal_balance digits_preserve_decimal_value
    decimal_list_value_zip_add reverse_add_completed_pair_successor
    reverse_add_interval_moments_source_aligned};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse pair moment refinement depends on an oracle";
\<close>

end
