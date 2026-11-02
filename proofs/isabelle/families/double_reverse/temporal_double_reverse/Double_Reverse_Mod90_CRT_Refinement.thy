theory Double_Reverse_Mod90_CRT_Refinement
  imports Double_Reverse_Four_Port_Numeric_Refinement
    Shared_S_Arithmetic.CRT_Predicate
begin

text \<open>The bounded doubled-digit channel concatenates the decimal token
for twice each source digit.  Its modulo-90 value is the arithmetic doubling
projection.  The proof uses digit-sum modulo nine and the final decimal digit;
it does not infer any carry-word or future-period authority from this
projection.\<close>

fun double_reverse_digit_token :: "nat \<Rightarrow> nat list" where
  "double_reverse_digit_token digit =
    (if digit < 5 then [2*digit] else [1, 2*digit - 10])"

fun double_reverse_digit_word :: "nat list \<Rightarrow> nat list" where
  "double_reverse_digit_word [] = []"
| "double_reverse_digit_word (digit # digits) =
    double_reverse_digit_token digit @ double_reverse_digit_word digits"

lemma double_reverse_digit_word_append:
  "double_reverse_digit_word (digits @ [digit]) =
    double_reverse_digit_word digits @ double_reverse_digit_token digit"
  by (induction digits) (simp_all add: append_assoc)

lemma double_reverse_digit_word_nonempty:
  assumes "digits \<noteq> []"
  shows "double_reverse_digit_word digits \<noteq> []"
  using assms by (cases digits) (simp_all)

lemma double_reverse_token_last:
  assumes digit: "digit < 10"
  shows "last (double_reverse_digit_token digit) = (2*digit) mod 10"
proof (cases "digit < 5")
  case True
  then show ?thesis by simp
next
  case False
  have lower: "5 \<le> digit" using False by simp
  show ?thesis using digit lower
    by (simp; arith)
qed

lemma double_reverse_msf_value_mod10_last:
  assumes nonempty: "digits \<noteq> []"
  shows "double_reverse_msf_value digits mod 10 = last digits mod 10"
proof -
  have decomposition: "digits = butlast digits @ [last digits]"
    by (rule sym, rule append_butlast_last_id[OF nonempty])
  have msf_eq:
    "double_reverse_msf_value digits =
      10 * double_reverse_msf_value (butlast digits) + last digits"
  proof -
    have rewrite:
      "double_reverse_msf_value digits =
        double_reverse_msf_value (butlast digits @ [last digits])"
      by (rule arg_cong[where f=double_reverse_msf_value, OF decomposition])
    have append_digit:
      "double_reverse_msf_value (butlast digits @ [last digits]) =
        10 * double_reverse_msf_value (butlast digits) + last digits"
      by (rule double_reverse_msf_value_append_digit)
    show ?thesis using rewrite append_digit by simp
  qed
  show ?thesis using msf_eq by simp
qed

lemma double_reverse_digit_word_last:
  assumes nonempty: "digits \<noteq> []"
      and decimal: "list_all (\<lambda>digit. digit < 10) digits"
  shows "last (double_reverse_digit_word digits) =
      (2 * last digits) mod 10"
  using nonempty decimal
proof (induction digits rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc digit digits)
  have digit_bound: "digit < 10"
    using snoc.prems(2) by simp
  have token_nonempty: "double_reverse_digit_token digit \<noteq> []"
    by (cases "digit < 5") simp_all
  have append:
    "double_reverse_digit_word (digits @ [digit]) =
      double_reverse_digit_word digits @ double_reverse_digit_token digit"
    by (rule double_reverse_digit_word_append)
  have last_token:
    "last (double_reverse_digit_token digit) = (2 * digit) mod 10"
    by (rule double_reverse_token_last[OF digit_bound])
  have last_after_append:
    "last (double_reverse_digit_word digits @
        double_reverse_digit_token digit) =
      last (double_reverse_digit_token digit)"
    by (rule last_appendR[OF token_nonempty])
  have final_last:
    "last (double_reverse_digit_word (digits @ [digit])) =
      last (double_reverse_digit_token digit)"
    by (simp only: append last_after_append)
  show ?case by (simp only: final_last last_token last_snoc)
qed

lemma double_reverse_ten_power_mod_nine:
  "(10::nat)^n mod 9 = 1"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have power_step: "(10::nat)^Suc n = (10::nat)^n * 10"
    by (simp add: power_Suc)
  have reduced_product:
    "((10::nat)^n * 10) mod 9 =
      (((10::nat)^n mod 9) * 10) mod 9"
    by (rule mod_mult_left_eq[symmetric])
  have step:
    "(10::nat)^Suc n mod 9 = ((10::nat)^n mod 9 * 10) mod 9"
  proof -
    have initial:
      "(10::nat)^Suc n mod 9 = ((10::nat)^n * 10) mod 9"
      by (simp only: power_step)
    also have "... = (((10::nat)^n mod 9) * 10) mod 9"
      by (rule reduced_product)
    finally show ?thesis .
  qed
  show ?case using step Suc.IH by simp
qed

lemma double_reverse_msf_value_mod_nine_sum:
  "double_reverse_msf_value digits mod 9 = sum_list digits mod 9"
proof (induction digits)
  case Nil
  then show ?case by (simp add: double_reverse_msf_value_def)
next
  case (Cons digit digits)
  have power:
    "(10::nat)^length digits mod 9 = 1"
    by (rule double_reverse_ten_power_mod_nine)
  have power_factor:
    "(10::nat)^length digits mod 9 = 1 mod 9"
    using power by simp
  have head:
    "(digit * 10^length digits) mod 9 = digit mod 9"
    using mod_mult_cong[OF refl power_factor] by simp
  have msf_residue:
    "double_reverse_msf_value (digit # digits) mod 9 =
      (digit + double_reverse_msf_value digits) mod 9"
    unfolding double_reverse_msf_value_cons
    by (rule mod_add_cong[OF head refl])
  have tail:
    "(digit + double_reverse_msf_value digits) mod 9 =
      (digit + sum_list digits) mod 9"
    by (rule mod_add_cong[OF refl Cons.IH])
  show ?case using msf_residue tail by simp
qed

lemma double_reverse_digit_token_sum_mod_nine:
  assumes digit: "digit < 10"
  shows "sum_list (double_reverse_digit_token digit) mod 9 =
    (2*digit) mod 9"
proof (cases "digit < 5")
  case True
  then show ?thesis by simp
next
  case False
  have lower: "5 \<le> digit" using False by simp
  have token_value:
    "sum_list (double_reverse_digit_token digit) + 9 = 2*digit"
    using lower digit by (simp; arith)
  have shifted:
    "sum_list (double_reverse_digit_token digit) mod 9 =
      (sum_list (double_reverse_digit_token digit) + 9) mod 9"
    by (simp add: mod_add_self2)
  show ?thesis
  proof -
    have "sum_list (double_reverse_digit_token digit) mod 9 =
        (sum_list (double_reverse_digit_token digit) + 9) mod 9"
      by (rule shifted)
    also have "... = (2*digit) mod 9"
      by (simp only: token_value)
    finally show ?thesis .
  qed
qed

lemma double_reverse_digit_word_sum_mod_nine:
  assumes decimal: "list_all (\<lambda>digit. digit < 10) digits"
  shows "sum_list (double_reverse_digit_word digits) mod 9 =
    (2 * sum_list digits) mod 9"
  using decimal
proof (induction digits)
  case Nil
  then show ?case by simp
next
  case (Cons digit digits)
  have digit_bound: "digit < 10" using Cons.prems by simp
  have head:
    "sum_list (double_reverse_digit_token digit) mod 9 =
      (2*digit) mod 9"
    by (rule double_reverse_digit_token_sum_mod_nine[OF digit_bound])
  have tail:
    "sum_list (double_reverse_digit_word digits) mod 9 =
      (2 * sum_list digits) mod 9"
    by (rule Cons.IH) (use Cons.prems in simp)
  have combined:
    "(sum_list (double_reverse_digit_token digit) +
        sum_list (double_reverse_digit_word digits)) mod 9 =
      (2*digit + 2*sum_list digits) mod 9"
    by (rule mod_add_cong[OF head tail])
  show ?case using combined by (simp add: algebra_simps)
qed

theorem double_reverse_doubled_digit_word_mod90:
  assumes decimal: "list_all (\<lambda>digit. digit < 10) digits"
  shows
  "double_reverse_msf_value (double_reverse_digit_word digits) mod 90 =
    (2 * double_reverse_msf_value digits) mod 90"
proof -
  let ?word = "double_reverse_digit_word digits"
  let ?source = "double_reverse_msf_value digits"
  let ?doubled = "double_reverse_msf_value ?word"
  let ?target = "(2 * ?source) mod 90"
  have residue_nine:
    "?doubled mod 9 = ?target mod 9"
  proof -
    have nine_divides_ninety: "(9::nat) dvd 90"
      by simp
    have target_reduce:
      "?target mod 9 = (2 * ?source) mod 9"
      by (rule mod_mod_cancel[OF nine_divides_ninety])
    have word_sum:
      "sum_list ?word mod 9 = (2 * sum_list digits) mod 9"
      by (rule double_reverse_digit_word_sum_mod_nine[OF decimal])
    have source_sum:
      "?source mod 9 = sum_list digits mod 9"
      by (rule double_reverse_msf_value_mod_nine_sum)
    have output_sum:
      "?doubled mod 9 = sum_list ?word mod 9"
      by (rule double_reverse_msf_value_mod_nine_sum)
    have scaled_source:
      "(2 * ?source) mod 9 = (2 * sum_list digits) mod 9"
    proof -
      have source_scale:
        "(2 * ?source) mod 9 = (2 * (?source mod 9)) mod 9"
        by (rule mod_mult_right_eq[symmetric])
      have reduced_scale:
        "(2 * (?source mod 9)) mod 9 =
          (2 * (sum_list digits mod 9)) mod 9"
        by (rule arg_cong[where f="\<lambda>value. (2 * value) mod 9",
            OF source_sum])
      have sum_scale:
        "(2 * (sum_list digits mod 9)) mod 9 =
          (2 * sum_list digits) mod 9"
        by (rule mod_mult_right_eq)
      show ?thesis using source_scale reduced_scale sum_scale
        by (blast intro: trans)
    qed
    show ?thesis using output_sum word_sum scaled_source target_reduce
      by simp
  qed
  have residue_ten:
    "?doubled mod 10 = ?target mod 10"
  proof (cases digits)
    case Nil
    then show ?thesis
      by (simp add: double_reverse_msf_value_empty)
  next
    case (Cons digit rest)
    have nonempty: "digits \<noteq> []" using Cons by simp
    have source_last:
      "?source mod 10 = last digits mod 10"
      by (rule double_reverse_msf_value_mod10_last[OF nonempty])
    have word_nonempty: "?word \<noteq> []"
      by (rule double_reverse_digit_word_nonempty[OF nonempty])
    have word_last:
      "last ?word = (2 * last digits) mod 10"
      by (rule double_reverse_digit_word_last[OF nonempty decimal])
    have output_last:
      "?doubled mod 10 = last ?word mod 10"
      by (rule double_reverse_msf_value_mod10_last[OF word_nonempty])
    have scale:
      "(2 * ?source) mod 10 = (2 * last digits) mod 10"
      by (rule mod_mult_cong[OF refl source_last])
    have ten_divides_ninety: "(10::nat) dvd 90" by simp
    have target_reduce:
      "?target mod 10 = (2 * ?source) mod 10"
      by (rule mod_mod_cancel[OF ten_divides_ninety])
    show ?thesis using output_last word_last scale target_reduce by simp
  qed
  have lcm_value: "90 = lcm (9::nat) 10"
    by (simp add: lcm_nat_def gcd_nat.simps)
  have canonical: "?target < 90" by simp
  have p_positive: "0 < (9::nat)" by simp
  have q_positive: "0 < (10::nat)" by simp
  have left_witness: "?target mod 9 = ?target mod 9" by simp
  have right_witness: "?target mod 10 = ?target mod 10" by simp
  have crt:
    "(?doubled mod 9 = ?target mod 9 \<and>
      ?doubled mod 10 = ?target mod 10) \<longleftrightarrow>
      ?doubled mod 90 = ?target"
    by (rule residue_predicate_lcm[OF p_positive q_positive lcm_value
          canonical left_witness right_witness])
  show ?thesis using crt residue_nine residue_ten by blast
qed

text \<open>The 198-clock and terminal mod-5 projection determine the unique
modulo-990 source residue.  This is a CRT uniqueness theorem for an already
authenticated source; it does not supply either projection or a temporal
period.\<close>

theorem double_reverse_mod990_projection_unique:
  fixes left right :: nat
  assumes mod198: "left mod 198 = right mod 198"
      and mod5: "left mod 5 = right mod 5"
  shows "left mod 990 = right mod 990"
proof -
  let ?c = "right mod 990"
  have lcm_value: "990 = lcm (198::nat) 5"
    by (simp add: lcm_nat_def gcd_nat.simps)
  have canonical: "?c < 990" by simp
  have p_positive: "0 < (198::nat)" by simp
  have q_positive: "0 < (5::nat)" by simp
  have p_divides: "(198::nat) dvd 990" by simp
  have q_divides: "(5::nat) dvd 990" by simp
  have left_witness: "?c mod 198 = right mod 198"
    by (rule mod_mod_cancel[OF p_divides])
  have right_witness: "?c mod 5 = right mod 5"
    by (rule mod_mod_cancel[OF q_divides])
  have combined:
    "(left mod 198 = right mod 198 \<and>
      left mod 5 = right mod 5) \<longleftrightarrow>
      left mod 990 = ?c"
    by (rule residue_predicate_lcm[OF p_positive q_positive lcm_value
          canonical left_witness right_witness])
  have result: "left mod 990 = ?c"
    using combined mod198 mod5 by blast
  show ?thesis using result by simp
qed

ML \<open>
  val checked = @{thms double_reverse_doubled_digit_word_mod90
    double_reverse_mod990_projection_unique};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse mod-90/990 refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped double-reverse mod-90/990 refinement proof" else ();
\<close>

end
