theory Reflected_Padded_Digit_Word
  imports Decimal_Block_Action
begin

text \<open>Finite decimal multiplication in least-significant-first order.
The final carry is retained as an explicit padded high digit.\<close>

definition reflected_msf_value :: "nat list \<Rightarrow> nat" where
  "reflected_msf_value digits = decimal_lsd_value (rev digits)"

lemma decimal_lsd_value_append:
  "decimal_lsd_value (left @ right) =
    decimal_lsd_value left + 10 ^ length left * decimal_lsd_value right"
  by (induction left) (simp_all add: algebra_simps power_Suc)

lemma reflected_multiplier_incoming_carry_independent:
  fixes multiplier digit incoming :: nat
  assumes "multiplier = 2 \<or> multiplier = 5" "digit < 10"
      "incoming < multiplier"
  shows "(multiplier * digit + incoming) div 10 = multiplier * digit div 10"
proof -
  have digit_cases: "digit = 0 \<or> digit = 1 \<or> digit = 2 \<or> digit = 3 \<or>
      digit = 4 \<or> digit = 5 \<or> digit = 6 \<or> digit = 7 \<or>
      digit = 8 \<or> digit = 9"
    using assms by arith
  have carry_cases: "incoming = 0 \<or> incoming = 1 \<or> incoming = 2 \<or>
      incoming = 3 \<or> incoming = 4"
    using assms by arith
  show ?thesis using assms digit_cases carry_cases by auto
qed

definition reflected_padded_multiply :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reflected_padded_multiply multiplier word =
    (let result = decimal_block_run multiplier word 0
     in fst result @ [snd result])"

definition reflected_padded_E :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reflected_padded_E multiplier word =
    rev (reflected_padded_multiply multiplier (rev word))"

definition reflected_padded_H :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "reflected_padded_H multiplier word =
    reflected_padded_E multiplier (reflected_padded_multiply multiplier word)"

lemma reflected_padded_multiply_zero_low_digit:
  "reflected_padded_multiply multiplier (0 # source) =
    0 # reflected_padded_multiply multiplier source"
  by (simp add: reflected_padded_multiply_def Let_def split: prod.splits)

lemma reflected_padded_multiply_low_normalization:
  "dropWhile ((=) 0)
      (reflected_padded_multiply multiplier (dropWhile ((=) 0) source)) =
    dropWhile ((=) 0) (reflected_padded_multiply multiplier source)"
  by (induction source) (auto simp: reflected_padded_multiply_zero_low_digit)

lemma reflected_padded_multiply_append_zero:
  assumes "snd (decimal_block_run multiplier source 0) < 10"
  shows "reflected_padded_multiply multiplier (source @ [0]) =
    reflected_padded_multiply multiplier source @ [0]"
  using assms
  by (auto simp: reflected_padded_multiply_def decimal_block_run_append
      Let_def split: prod.splits)

lemma reflected_padded_E_zero_low_digit:
  assumes "snd (decimal_block_run multiplier (rev source) 0) < 10"
  shows "reflected_padded_E multiplier (0 # source) =
    0 # reflected_padded_E multiplier source"
  using reflected_padded_multiply_append_zero[OF assms]
  by (simp add: reflected_padded_E_def)

lemma reflected_digit_pass_carry_bound:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "list_all (\<lambda>digit. digit < 10) source"
    and inlet: "incoming < multiplier"
  shows "snd (decimal_block_run multiplier source incoming) < multiplier"
  using digits inlet
proof (induction source arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons digit rest)
  have next_inlet: "(multiplier * digit + incoming) div 10 < multiplier"
    using multiplier Cons.prems by (elim disjE; simp_all; arith)
  have tail: "list_all (\<lambda>digit. digit < 10) rest"
    using Cons.prems by simp
  show ?case using Cons.IH[OF tail next_inlet]
    by (simp add: Let_def split: prod.splits)
qed

theorem reflected_padded_E_zero_transport:
  assumes "multiplier = 2 \<or> multiplier = 5"
    and "list_all (\<lambda>digit. digit < 10) source"
  shows "reflected_padded_E multiplier (0 # source) =
    0 # reflected_padded_E multiplier source"
proof -
  have carry: "snd (decimal_block_run multiplier (rev source) 0) < multiplier"
    by (rule reflected_digit_pass_carry_bound[OF assms(1)])
       (use assms in auto)
  have "snd (decimal_block_run multiplier (rev source) 0) < 10"
    using carry assms by arith
  then show ?thesis by (rule reflected_padded_E_zero_low_digit)
qed

lemma reflected_digit_pass_length:
  "length (fst (decimal_block_run multiplier source incoming)) = length source"
  by (induction source arbitrary: incoming) (simp_all add: Let_def split: prod.splits)

lemma reflected_digit_pass_value:
  "decimal_lsd_value (fst (decimal_block_run multiplier source incoming)) +
    10 ^ length source * snd (decimal_block_run multiplier source incoming) =
      multiplier * decimal_lsd_value source + incoming"
  using decimal_multiplier_columns_exact[of multiplier source incoming]
  by (simp only: decimal_block_run_def add.commute)

lemma reflected_padded_multiply_value:
  "decimal_lsd_value (reflected_padded_multiply multiplier source) =
    multiplier * decimal_lsd_value source"
  using reflected_digit_pass_value[of multiplier source 0]
  by (simp add: reflected_padded_multiply_def Let_def
      decimal_lsd_value_append reflected_digit_pass_length split: prod.splits)

theorem reflected_padded_E_reversed_value:
  "reflected_msf_value (reflected_padded_E multiplier source) =
    multiplier * reflected_msf_value source"
  unfolding reflected_padded_E_def reflected_msf_value_def
  by (simp only: rev_rev_ident reflected_padded_multiply_value)

ML \<open>
  val checked = @{thms reflected_padded_multiply_zero_low_digit
    reflected_padded_multiply_low_normalization reflected_padded_multiply_append_zero
    reflected_padded_E_zero_low_digit reflected_digit_pass_carry_bound
    reflected_padded_E_zero_transport
    reflected_digit_pass_length reflected_digit_pass_value
    reflected_padded_multiply_value reflected_padded_E_reversed_value};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected padded word proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reflected padded word proof" else ();
\<close>

end
