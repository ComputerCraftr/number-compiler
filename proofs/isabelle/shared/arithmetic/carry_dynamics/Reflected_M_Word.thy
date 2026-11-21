theory Reflected_M_Word
  imports Reflected_H_Cells
begin

text \<open>The emitted column is an affine function of its current digit and
incoming carry. The quotient digit determines the outgoing carry.\<close>

lemma reflected_multiplier_emitted_digit:
  fixes multiplier digit carry :: nat
  assumes "multiplier = 2 \<or> multiplier = 5" "digit < 10"
    "carry < multiplier"
  shows "(multiplier * digit + carry) mod 10 =
    multiplier * (digit mod (10 div multiplier)) + carry"
proof -
  have digit_cases: "digit = 0 \<or> digit = 1 \<or> digit = 2 \<or> digit = 3 \<or>
      digit = 4 \<or> digit = 5 \<or> digit = 6 \<or> digit = 7 \<or>
      digit = 8 \<or> digit = 9" using assms by arith
  have carry_cases: "carry = 0 \<or> carry = 1 \<or> carry = 2 \<or>
      carry = 3 \<or> carry = 4" using assms by arith
  show ?thesis using assms digit_cases carry_cases by auto
qed

theorem reflected_multiplier_column_exact:
  fixes multiplier digit carry :: nat
  assumes "multiplier = 2 \<or> multiplier = 5" "digit < 10"
    "carry < multiplier"
  shows "((multiplier * digit + carry) mod 10,
      (multiplier * digit + carry) div 10) =
    (multiplier * (digit mod (10 div multiplier)) + carry,
      multiplier * digit div 10)"
  using reflected_multiplier_emitted_digit[OF assms]
    reflected_multiplier_incoming_carry_independent[OF assms] by simp

definition reflected_padded_pass ::
  "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "reflected_padded_pass multiplier source inlet =
    (let result = decimal_block_run multiplier source inlet
     in fst result @ [snd result])"

fun reflected_M_pass :: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "reflected_M_pass multiplier [] inlet = [inlet]"
| "reflected_M_pass multiplier (digit # rest) inlet =
    (multiplier * (digit mod (10 div multiplier)) + inlet) #
      reflected_M_pass multiplier rest (multiplier * digit div 10)"

theorem reflected_padded_pass_M_exact:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "list_all (\<lambda>digit. digit < 10) source"
    and inlet: "inlet < multiplier"
  shows "reflected_padded_pass multiplier source inlet =
    reflected_M_pass multiplier source inlet"
  using digits inlet
proof (induction source arbitrary: inlet)
  case Nil
  then show ?case by (simp add: reflected_padded_pass_def)
next
  case (Cons digit rest)
  have digit: "digit < 10" and tail: "list_all (\<lambda>digit. digit < 10) rest"
    using Cons.prems by simp_all
  have emitted:
    "(multiplier * digit + inlet) mod 10 =
      multiplier * (digit mod (10 div multiplier)) + inlet"
    by (rule reflected_multiplier_emitted_digit[OF multiplier digit Cons.prems(2)])
  have carry: "(multiplier * digit + inlet) div 10 = multiplier * digit div 10"
    by (rule reflected_multiplier_incoming_carry_independent[OF multiplier digit Cons.prems(2)])
  have next_carry: "multiplier * digit div 10 < multiplier"
    using reflected_digit_pass_carry_bound[OF multiplier, of "[digit]" inlet]
      digit Cons.prems(2) carry by simp
  have recursive:
    "reflected_padded_pass multiplier rest (multiplier * digit div 10) =
      reflected_M_pass multiplier rest (multiplier * digit div 10)"
    by (rule Cons.IH[OF tail next_carry])
  show ?case using emitted carry recursive
    by (simp add: reflected_padded_pass_def Let_def split: prod.splits)
qed

corollary reflected_padded_multiply_M_exact:
  assumes "multiplier = 2 \<or> multiplier = 5"
    "list_all (\<lambda>digit. digit < 10) source"
  shows "reflected_padded_multiply multiplier source =
    reflected_M_pass multiplier source 0"
proof -
  have positive: "0 < multiplier" using assms(1) by auto
  show ?thesis using reflected_padded_pass_M_exact[OF assms positive]
    by (simp add: reflected_padded_multiply_def reflected_padded_pass_def)
qed

lemma reflected_padded_source_cons:
  "reflected_padded_source (digit # rest) 0 = digit"
  "reflected_padded_source (digit # rest) (Suc i) = reflected_padded_source rest i"
  by (simp_all add: reflected_padded_source_def)

lemma reflected_M_pass_padded_source:
  assumes multiplier: "multiplier = 2 \<or> multiplier = 5"
    and digits: "list_all (\<lambda>digit. digit < 10) source"
    and inlet: "inlet < multiplier"
  shows "reflected_padded_source (reflected_M_pass multiplier source inlet) i =
    (if i = 0 then multiplier *
        (reflected_padded_source source 0 mod (10 div multiplier)) + inlet
     else reflected_M_digit multiplier (reflected_padded_source source) i)"
  using digits inlet
proof (induction source arbitrary: inlet i)
  case Nil
  then show ?case
    by (cases i) (simp_all add: reflected_padded_source_def
        reflected_M_digit_def reflected_previous_def)
next
  case (Cons digit rest)
  have digit: "digit < 10" and tail: "list_all (\<lambda>digit. digit < 10) rest"
    using Cons.prems by simp_all
  have carry: "(multiplier * digit + inlet) div 10 = multiplier * digit div 10"
    by (rule reflected_multiplier_incoming_carry_independent[OF multiplier digit Cons.prems(2)])
  have carry_column: "multiplier * digit div 10 = digit div (10 div multiplier)"
  proof -
    have small: "digit = 0 \<or> digit = 1 \<or> digit = 2 \<or> digit = 3 \<or>
        digit = 4 \<or> digit = 5 \<or> digit = 6 \<or> digit = 7 \<or>
        digit = 8 \<or> digit = 9" using digit by arith
    show ?thesis using multiplier small by auto
  qed
  have next_carry: "multiplier * digit div 10 < multiplier"
    using reflected_digit_pass_carry_bound[OF multiplier, of "[digit]" inlet]
      digit Cons.prems(2) carry by simp
  have tail_result:
    "reflected_padded_source
        (reflected_M_pass multiplier rest (multiplier * digit div 10)) j =
      (if j = 0 then multiplier *
          (reflected_padded_source rest 0 mod (10 div multiplier)) +
            multiplier * digit div 10
       else reflected_M_digit multiplier (reflected_padded_source rest) j)" for j
    by (rule Cons.IH[OF tail next_carry])
  show ?case
  proof (cases i)
    case 0
    then show ?thesis by (simp add: reflected_padded_source_cons)
  next
    case (Suc j)
    show ?thesis
      using tail_result[of j] Suc carry_column
      by (cases j) (simp_all add: reflected_padded_source_cons
          reflected_M_digit_def reflected_previous_def)
  qed
qed

theorem reflected_padded_multiply_M_source:
  assumes "multiplier = 2 \<or> multiplier = 5"
    "list_all (\<lambda>digit. digit < 10) source"
  shows "reflected_padded_source (reflected_padded_multiply multiplier source) i =
    reflected_M_digit multiplier (reflected_padded_source source) i"
proof -
  have positive: "0 < multiplier" using assms(1) by auto
  show ?thesis
    using reflected_M_pass_padded_source[OF assms positive, of i]
      reflected_padded_multiply_M_exact[OF assms]
    by (cases i) (simp_all add: reflected_M_digit_def reflected_previous_def)
qed

ML \<open>
  val checked = @{thms reflected_multiplier_column_exact
    reflected_padded_pass_M_exact reflected_padded_multiply_M_source};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected M word proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reflected M word proof" else ();
\<close>

end
