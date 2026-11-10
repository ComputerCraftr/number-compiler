theory Double_Reverse_Decimal_Source_Carry_Mask
  imports Double_Reverse_Four_Port_Defect_Refinement
begin

text \<open>Decimal numeral sources and their exact threshold carry masks.\<close>

function double_reverse_decimal_threshold_mask :: "nat \<Rightarrow> nat" where
  "double_reverse_decimal_threshold_mask n =
    (if n < 10 then threshold5_digit n
     else threshold5_digit (n mod 10) +
       10 * double_reverse_decimal_threshold_mask (n div 10))"
  by pat_completeness auto
termination
  by (relation "measure id") auto

declare double_reverse_decimal_threshold_mask.simps [simp del]

lemma double_reverse_decimal_threshold_mask_small:
  assumes "n < 10"
  shows "double_reverse_decimal_threshold_mask n = threshold5_digit n"
proof -
  have equation:
    "double_reverse_decimal_threshold_mask n =
      (if n < 10 then threshold5_digit n else
        threshold5_digit (n mod 10) +
          10 * double_reverse_decimal_threshold_mask (n div 10))"
    by (rule double_reverse_decimal_threshold_mask.simps)
  show ?thesis using equation assms by simp
qed

lemma double_reverse_decimal_threshold_mask_zero [simp]:
  "double_reverse_decimal_threshold_mask 0 = 0"
  using double_reverse_decimal_threshold_mask_small[of 0]
  by (simp add: threshold5_digit_def)

lemma double_reverse_decimal_threshold_mask_step:
  "double_reverse_decimal_threshold_mask n =
    threshold5_digit (n mod 10) +
      10 * double_reverse_decimal_threshold_mask (n div 10)"
proof (cases "n < 10")
  case True
  have small: "double_reverse_decimal_threshold_mask n = threshold5_digit n"
    by (rule double_reverse_decimal_threshold_mask_small[OF True])
  have zero: "double_reverse_decimal_threshold_mask (n div 10) = 0"
    using True double_reverse_decimal_threshold_mask_small[of 0]
    by (simp add: threshold5_digit_def)
  show ?thesis using small zero True by (simp add: threshold5_digit_def)
next
  case False
  have equation:
    "double_reverse_decimal_threshold_mask n =
      (if n < 10 then threshold5_digit n else
        threshold5_digit (n mod 10) +
          10 * double_reverse_decimal_threshold_mask (n div 10))"
    by (rule double_reverse_decimal_threshold_mask.simps)
  show ?thesis using equation False by simp
qed

function double_reverse_decimal_source :: "nat \<Rightarrow> nat list" where
  "double_reverse_decimal_source n =
    (if n < 10 then [n] else
      double_reverse_decimal_source (n div 10) @ [n mod 10])"
  by pat_completeness auto
termination
  by (relation "measure id") auto

declare double_reverse_decimal_source.simps [simp del]

lemma double_reverse_decimal_source_small:
  assumes "n < 10"
  shows "double_reverse_decimal_source n = [n]"
proof -
  have equation:
    "double_reverse_decimal_source n =
      (if n < 10 then [n]
       else double_reverse_decimal_source (n div 10) @ [n mod 10])"
    by (rule double_reverse_decimal_source.simps)
  show ?thesis using equation assms by simp
qed

lemma double_reverse_decimal_source_step:
  assumes "\<not> n < 10"
  shows "double_reverse_decimal_source n =
    double_reverse_decimal_source (n div 10) @ [n mod 10]"
proof -
  have equation:
    "double_reverse_decimal_source n =
      (if n < 10 then [n]
       else double_reverse_decimal_source (n div 10) @ [n mod 10])"
    by (rule double_reverse_decimal_source.simps)
  show ?thesis using equation assms by simp
qed

lemma double_reverse_decimal_source_nonempty:
  "double_reverse_decimal_source n \<noteq> []"
proof (cases "n < 10")
  case True
  then show ?thesis
    using double_reverse_decimal_source_small[of n] by simp
next
  case False
  then show ?thesis
    using double_reverse_decimal_source_step[of n] by simp
qed

lemma double_reverse_decimal_source_digits:
  "list_all (\<lambda>digit. digit < 10)
    (double_reverse_decimal_source n)"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 10")
    case True
    then show ?thesis
      using double_reverse_decimal_source_small[of n] by simp
  next
    case False
    have quotient_smaller: "n div 10 < n"
      using False by simp
    have tail_digits:
      "list_all (\<lambda>digit. digit < 10)
        (double_reverse_decimal_source (n div 10))"
      by (rule less.IH[OF quotient_smaller])
    have source_step:
      "double_reverse_decimal_source n =
        double_reverse_decimal_source (n div 10) @ [n mod 10]"
      by (rule double_reverse_decimal_source_step[OF False])
    have appended_digits:
      "list_all (\<lambda>digit. digit < 10)
        (double_reverse_decimal_source (n div 10) @ [n mod 10])"
      using tail_digits by simp
    show ?thesis using source_step appended_digits by metis
  qed
qed

lemma double_reverse_decimal_source_value:
  "double_reverse_msf_value (double_reverse_decimal_source n) = n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 10")
    case True
    then show ?thesis
      using double_reverse_decimal_source_small[of n]
      by (simp add: double_reverse_msf_value_singleton)
  next
    case False
    have quotient_smaller: "n div 10 < n"
      using False by simp
    have tail_value:
      "double_reverse_msf_value
        (double_reverse_decimal_source (n div 10)) = n div 10"
      by (rule less.IH[OF quotient_smaller])
    have decimal_decomposition: "n = 10 * (n div 10) + n mod 10"
      using div_mult_mod_eq[of n 10] by (simp add: mult.commute)
    have source_step:
      "double_reverse_decimal_source n =
        double_reverse_decimal_source (n div 10) @ [n mod 10]"
      by (rule double_reverse_decimal_source_step[OF False])
    have value_step:
      "double_reverse_msf_value (double_reverse_decimal_source n) =
        10 * double_reverse_msf_value
          (double_reverse_decimal_source (n div 10)) + n mod 10"
    proof -
      have "double_reverse_msf_value (double_reverse_decimal_source n) =
          double_reverse_msf_value
            (double_reverse_decimal_source (n div 10) @ [n mod 10])"
        by (rule arg_cong[OF source_step])
      also have "... = 10 * double_reverse_msf_value
          (double_reverse_decimal_source (n div 10)) + n mod 10"
        by (rule double_reverse_msf_value_append_digit)
      finally show ?thesis .
    qed
    show ?thesis using tail_value decimal_decomposition value_step by simp
  qed
qed

lemma double_reverse_decimal_source_last:
  "last (double_reverse_decimal_source n) = n mod 10"
proof (cases "n < 10")
  case True
  then show ?thesis
    using double_reverse_decimal_source_small[of n] by simp
next
  case False
  have source_step:
    "double_reverse_decimal_source n =
      double_reverse_decimal_source (n div 10) @ [n mod 10]"
    by (rule double_reverse_decimal_source_step[OF False])
  show ?thesis using source_step by (metis last_snoc)
qed

lemma double_reverse_decimal_source_first_positive:
  assumes "n > 0"
  shows "hd (double_reverse_decimal_source n) > 0"
  using assms
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 10")
    case True
    then show ?thesis
      using less.prems double_reverse_decimal_source_small[of n] by simp
  next
    case False
    have quotient_positive: "n div 10 > 0"
      using False by simp
    have quotient_smaller: "n div 10 < n"
      using False by simp
    have quotient_source_nonempty:
      "double_reverse_decimal_source (n div 10) \<noteq> []"
      by (rule double_reverse_decimal_source_nonempty)
    have tail_positive:
      "hd (double_reverse_decimal_source (n div 10)) > 0"
      by (rule less.IH[OF quotient_smaller quotient_positive])
    have source_step:
      "double_reverse_decimal_source n =
        double_reverse_decimal_source (n div 10) @ [n mod 10]"
      by (rule double_reverse_decimal_source_step[OF False])
    have first_append:
      "hd (double_reverse_decimal_source (n div 10) @ [n mod 10]) =
        hd (double_reverse_decimal_source (n div 10))"
      by (rule hd_append2[OF quotient_source_nonempty])
    have first:
      "hd (double_reverse_decimal_source n) =
        hd (double_reverse_decimal_source (n div 10))"
      using source_step first_append by metis
    show ?thesis using first tail_positive by simp
  qed
qed

lemma double_reverse_decimal_source_canonical:
  assumes positive: "n > 0" and units: "n mod 10 > 0"
  shows "double_reverse_canonical_source
    (double_reverse_decimal_source n)"
  using positive units
    double_reverse_decimal_source_nonempty
    double_reverse_decimal_source_digits
    double_reverse_decimal_source_last
    double_reverse_decimal_source_first_positive
  unfolding double_reverse_canonical_source_def
  by simp

lemma double_reverse_decimal_threshold_mask_source:
  "double_reverse_source_carry_mask
      (double_reverse_decimal_source n) =
    double_reverse_decimal_threshold_mask n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 10")
    case True
    have source_small: "double_reverse_decimal_source n = [n]"
      by (rule double_reverse_decimal_source_small[OF True])
    have mask_small:
      "double_reverse_decimal_threshold_mask n = threshold5_digit n"
      by (rule double_reverse_decimal_threshold_mask_small[OF True])
    show ?thesis
      using source_small mask_small
      unfolding double_reverse_source_carry_mask_def
      by (simp add: double_reverse_msf_value_singleton)
  next
    case False
    have quotient_smaller: "n div 10 < n"
      using False by simp
    have tail_mask:
      "double_reverse_source_carry_mask
        (double_reverse_decimal_source (n div 10)) =
       double_reverse_decimal_threshold_mask (n div 10)"
      by (rule less.IH[OF quotient_smaller])
    have source_step:
      "double_reverse_decimal_source n =
        double_reverse_decimal_source (n div 10) @ [n mod 10]"
      by (rule double_reverse_decimal_source_step[OF False])
    have append_mask:
      "double_reverse_source_carry_mask
          (double_reverse_decimal_source (n div 10) @ [n mod 10]) =
        threshold5_digit (n mod 10) +
          10 * double_reverse_source_carry_mask
            (double_reverse_decimal_source (n div 10))"
      unfolding double_reverse_source_carry_mask_def
      by (simp add: double_reverse_msf_value_append_digit map_append)
    have source_mask_step:
      "double_reverse_source_carry_mask
          (double_reverse_decimal_source n) =
        double_reverse_source_carry_mask
          (double_reverse_decimal_source (n div 10) @ [n mod 10])"
      by (rule arg_cong[OF source_step])
    show ?thesis
      using source_mask_step append_mask tail_mask
        double_reverse_decimal_threshold_mask_step[of n]
      by (simp add: algebra_simps)
  qed
qed

lemma double_reverse_decimal_threshold_mask_div:
  "double_reverse_decimal_threshold_mask n div 10 =
    double_reverse_decimal_threshold_mask (n div 10)"
  and double_reverse_decimal_threshold_mask_mod:
  "double_reverse_decimal_threshold_mask n mod 10 =
    threshold5_digit (n mod 10)"
proof -
  let ?q = "double_reverse_decimal_threshold_mask (n div 10)"
  let ?r = "threshold5_digit (n mod 10)"
  have small: "?r < 10"
    by (simp add: threshold5_digit_def)
  have split:
    "double_reverse_decimal_threshold_mask n = 10 * ?q + ?r"
    using double_reverse_decimal_threshold_mask_step[of n]
    by (simp add: algebra_simps)
  have quotient:
    "(10 * ?q + ?r) div 10 = ?q"
    and remainder:
    "(10 * ?q + ?r) mod 10 = ?r"
    by (rule double_reverse_decimal_split[OF small])+
  show "double_reverse_decimal_threshold_mask n div 10 = ?q"
    using split quotient by simp
  show "double_reverse_decimal_threshold_mask n mod 10 = ?r"
    using split remainder by simp
qed

lemma double_reverse_decimal_threshold_mask_mod_power:
  "double_reverse_decimal_threshold_mask n mod 10^places =
    double_reverse_decimal_threshold_mask (n mod 10^places)"
proof (induction places arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc places)
  let ?low = "n mod 10"
  let ?high = "n div 10 mod 10^places"
  have power: "10^(Suc places) = 10 * 10^places"
    by (simp add: power_Suc mult.commute)
  have number_split:
    "n mod 10^(Suc places) = 10 * ?high + ?low"
    using mod_mult2_eq[of n 10 "10^places"] power by simp
  have mask_split:
    "double_reverse_decimal_threshold_mask
        (n mod 10^(Suc places)) =
      threshold5_digit ?low +
        10 * double_reverse_decimal_threshold_mask ?high"
    using double_reverse_decimal_threshold_mask_step[of
        "n mod 10^(Suc places)"] number_split
    by simp
  have mask_mod_split:
    "double_reverse_decimal_threshold_mask n mod 10^(Suc places) =
      10 * (double_reverse_decimal_threshold_mask (n div 10) mod
        10^places) + threshold5_digit ?low"
    using mod_mult2_eq[of "double_reverse_decimal_threshold_mask n" 10
        "10^places"] power
      double_reverse_decimal_threshold_mask_div[of n]
      double_reverse_decimal_threshold_mask_mod[of n]
    by simp
  have ih:
    "double_reverse_decimal_threshold_mask (n div 10) mod 10^places =
      double_reverse_decimal_threshold_mask
        (n div 10 mod 10^places)"
    by (rule Suc.IH)
  show ?case
    using mask_split mask_mod_split ih by (simp add: add.commute)
qed

lemma double_reverse_decimal_threshold_mask_div_power:
  "double_reverse_decimal_threshold_mask n div 10^places =
    double_reverse_decimal_threshold_mask (n div 10^places)"
proof (induction places arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc places)
  have power: "10^(Suc places) = 10 * 10^places"
    by (simp add: power_Suc mult.commute)
  have mask_div:
    "double_reverse_decimal_threshold_mask n div 10^(Suc places) =
      (double_reverse_decimal_threshold_mask n div 10) div 10^places"
    using div_mult2_eq[of "double_reverse_decimal_threshold_mask n" 10
        "10^places"] power by simp
  have source_div:
    "n div 10^(Suc places) = (n div 10) div 10^places"
    using div_mult2_eq[of n 10 "10^places"] power by simp
  show ?case
    using mask_div source_div
      double_reverse_decimal_threshold_mask_div[of n]
      Suc.IH[of "n div 10"] by simp
qed

lemma double_reverse_decimal_threshold_mask_split_power:
  "double_reverse_decimal_threshold_mask n =
    double_reverse_decimal_threshold_mask (n mod 10^places) +
      10^places * double_reverse_decimal_threshold_mask (n div 10^places)"
proof -
  have euclidean:
    "double_reverse_decimal_threshold_mask n =
      double_reverse_decimal_threshold_mask n mod 10^places +
        10^places * (double_reverse_decimal_threshold_mask n div 10^places)"
    using div_mult_mod_eq[of "double_reverse_decimal_threshold_mask n"
        "10^places"] by (simp add: mult.commute)
  show ?thesis
    using euclidean
      double_reverse_decimal_threshold_mask_mod_power[of n places]
      double_reverse_decimal_threshold_mask_div_power[of n places]
    by simp
qed

lemmas double_reverse_decimal_source_carry_mask_audit_bundle =
  double_reverse_decimal_threshold_mask_zero
  double_reverse_decimal_threshold_mask_small
  double_reverse_decimal_threshold_mask_step
  double_reverse_decimal_source_small
  double_reverse_decimal_source_step
  double_reverse_decimal_source_nonempty
  double_reverse_decimal_source_digits
  double_reverse_decimal_source_value
  double_reverse_decimal_source_last
  double_reverse_decimal_source_first_positive
  double_reverse_decimal_source_canonical
  double_reverse_decimal_threshold_mask_source
  double_reverse_decimal_threshold_mask_step
  double_reverse_decimal_threshold_mask_div
  double_reverse_decimal_threshold_mask_mod_power
  double_reverse_decimal_threshold_mask_div_power
  double_reverse_decimal_threshold_mask_split_power

ML \<open>
  val checked = @{thms double_reverse_decimal_source_carry_mask_audit_bundle};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Decimal source carry mask depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped decimal source carry mask proof" else ();
\<close>


end
