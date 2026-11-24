theory Mahler_CF_Pow5_Source
  imports "Shared_Carry_Dynamics.Reflected_Padded_Orbit"
    "Shared_Carry_Dynamics.Reflected_Block_Repeat"
begin

text \<open>The physical ×5 source reads one LSD-first word and publishes the
ordered output with its final high carry, omitting a zero carry. Every row is
an exact power of five. This theorem supplies source-value authority to
consumers which independently authenticate their finite word and cut.\<close>

definition mahler_cf_mul5_word :: "nat list \<Rightarrow> nat list" where
  "mahler_cf_mul5_word source =
    (let result = decimal_block_run 5 source 0
     in if snd result = 0 then fst result else fst result @ [snd result])"

lemma mahler_cf_mul5_word_value:
  "decimal_lsd_value (mahler_cf_mul5_word source) =
    5 * decimal_lsd_value source"
  using reflected_padded_multiply_value[of 5 source]
  by (auto simp: mahler_cf_mul5_word_def reflected_padded_multiply_def
      decimal_lsd_value_append Let_def split: prod.splits)

lemma mahler_cf_mul5_word_digits:
  assumes "list_all (\<lambda>digit. digit < 10) source"
  shows "list_all (\<lambda>digit. digit < 10) (mahler_cf_mul5_word source)"
  using reflected_padded_multiply_decimal[of 5 source] assms
  by (auto simp: mahler_cf_mul5_word_def reflected_padded_multiply_def
      Let_def split: prod.splits if_splits)

fun mahler_cf_pow5_word :: "nat \<Rightarrow> nat list" where
  "mahler_cf_pow5_word 0 = [1]"
| "mahler_cf_pow5_word (Suc n) = mahler_cf_mul5_word (mahler_cf_pow5_word n)"

theorem mahler_cf_pow5_word_consumer:
  "decimal_lsd_value (mahler_cf_pow5_word n) = 5^n"
  "list_all (\<lambda>digit. digit < 10) (mahler_cf_pow5_word n)"
  by (induction n) (auto simp: mahler_cf_mul5_word_value
      mahler_cf_mul5_word_digits power_Suc)


text \<open>The selected-inlet compiler follows these shared ordered word laws.
Only the inlet reached by the source is needed at a concatenation; a repeated
nonempty word uses its first response followed by the stable response.\<close>

lemma mahler_cf_digit_carry:
  fixes d c :: nat
  assumes "d < 10" "c < 5"
  shows "(5 * d + c) div 10 = d div 2"
proof -
  have "((5::nat) * d + c) div 10 = 5 * d div 10"
    by (rule reflected_multiplier_incoming_carry_independent) (use assms in auto)
  also have "... = d div 2"
  proof -
    have cases: "d = 0 \<or> d = 1 \<or> d = 2 \<or> d = 3 \<or> d = 4 \<or>
        d = 5 \<or> d = 6 \<or> d = 7 \<or> d = 8 \<or> d = 9"
      using assms by arith
    show ?thesis using cases by auto
  qed
  finally show ?thesis .
qed

lemma mahler_cf_nonempty_exit:
  assumes decimal: "list_all (\<lambda>d. d < 10) tile"
      and nonempty: "tile \<noteq> []" and inlet: "c < 5"
  shows "snd (decimal_block_run 5 tile c) = last tile div 2"
proof -
  obtain prefix digit where word: "tile = prefix @ [digit]"
    using nonempty by (cases tile rule: rev_cases) auto
  have prefix: "list_all (\<lambda>d. d < 10) prefix" and digit: "digit < 10"
    using decimal word by auto
  have bound: "snd (decimal_block_run 5 prefix c) < 5"
    by (rule reflected_digit_pass_carry_bound) (use prefix inlet in auto)
  have exit: "(5 * digit + snd (decimal_block_run 5 prefix c)) div 10 = digit div 2"
    by (rule mahler_cf_digit_carry[OF digit bound])
  show ?thesis
    using word by (simp add: decimal_block_run_append Let_def exit split: prod.splits)
qed

lemma mahler_cf_selected_concat:
  "decimal_block_run 5 (left @ right) c =
    (let a = decimal_block_run 5 left c;
         b = decimal_block_run 5 right (snd a)
     in (fst a @ fst b, snd b))"
  by (rule decimal_block_run_append)

lemma mahler_cf_selected_repeat:
  assumes "list_all (\<lambda>d. d < 10) tile" "tile \<noteq> []" "c < 5"
  defines "steady \<equiv> snd (decimal_block_run 5 tile c)"
  shows "decimal_block_run 5 (concat (replicate (Suc n) tile)) c =
    (fst (decimal_block_run 5 tile c) @
      concat (replicate n (fst (decimal_block_run 5 tile steady))), steady)"
proof -
  have bound: "steady < 5"
    unfolding steady_def
    by (rule reflected_digit_pass_carry_bound) (use assms in auto)
  have stable: "snd (decimal_block_run 5 tile steady) = steady"
    using reflected_nonempty_tile_exit_independent[where m=5 and tile=tile
        and c=steady and c'=c] assms bound
    by (simp add: steady_def)
  have repeated:
    "decimal_block_run 5 (concat (replicate n tile)) steady =
      (concat (replicate n (fst (decimal_block_run 5 tile steady))), steady)"
    by (rule decimal_steady_tile_repeats[OF stable])
  show ?thesis
    by (simp only: decimal_block_repeat_step steady_def[symmetric] repeated Let_def
        fst_conv snd_conv)
qed

text \<open>The reachable carry responses selected by the source grammar
compose in LSD-first order. A repeat uses one first response and one
steady response, with no premise identifying the resulting physical word.\<close>

inductive mahler_cf_pointed_response ::
  "nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  empty: "mahler_cf_pointed_response [] c [] c"
| digit: "mahler_cf_pointed_response [d] c [(5*d+c) mod 10] ((5*d+c) div 10)"
| concat: "\<lbrakk>mahler_cf_pointed_response left c first seam;
    mahler_cf_pointed_response right seam second carry\<rbrakk> \<Longrightarrow>
    mahler_cf_pointed_response (left @ right) c (first @ second) carry"
| repeat: "\<lbrakk>list_all (\<lambda>d. d < 10) tile; tile \<noteq> []; c < 5;
    mahler_cf_pointed_response tile c first steady;
    mahler_cf_pointed_response tile steady rest steady\<rbrakk> \<Longrightarrow>
    mahler_cf_pointed_response (concat (replicate (Suc k) tile)) c
      (first @ concat (replicate k rest)) steady"

lemma mahler_cf_pointed_response_exact:
  assumes "mahler_cf_pointed_response source inlet output carry"
  shows "decimal_block_run 5 source inlet = (output, carry)"
  using assms
proof (induction rule: mahler_cf_pointed_response.induct)
  case (concat left c first seam right second carry)
  then show ?case by (simp add: mahler_cf_selected_concat Let_def)
next
  case (repeat tile c first steady rest k)
  have first: "decimal_block_run 5 tile c = (first, steady)"
    using repeat.IH(1) .
  have rest: "decimal_block_run 5 tile steady = (rest, steady)"
    using repeat.IH(2) .
  have response: "decimal_block_run 5 (concat (replicate (Suc k) tile)) c =
      (fst (decimal_block_run 5 tile c) @
        concat (replicate k
          (fst (decimal_block_run 5 tile (snd (decimal_block_run 5 tile c))))),
        snd (decimal_block_run 5 tile c))"
    by (rule mahler_cf_selected_repeat[OF repeat.hyps(1-3)])
  show ?case using response by (simp only: first rest fst_conv snd_conv)
qed (simp_all add: Let_def)

theorem mahler_cf_pointed_publisher:
  assumes response: "mahler_cf_pointed_response (mahler_cf_pow5_word n) 0 output carry"
  shows "output @ (if carry = 0 then [] else [carry]) = mahler_cf_pow5_word (Suc n)"
    "decimal_lsd_value (output @ (if carry = 0 then [] else [carry])) = 5^(Suc n)"
proof -
  have step: "output @ (if carry = 0 then [] else [carry]) = mahler_cf_pow5_word (Suc n)"
    using mahler_cf_pointed_response_exact[OF response]
    by (simp add: mahler_cf_mul5_word_def Let_def)
  show "output @ (if carry = 0 then [] else [carry]) = mahler_cf_pow5_word (Suc n)"
    by (rule step)
  show "decimal_lsd_value (output @ (if carry = 0 then [] else [carry])) = 5^(Suc n)"
    by (simp only: step mahler_cf_pow5_word_consumer)
qed

ML \<open>
  val checked = @{thms mahler_cf_mul5_word_value mahler_cf_mul5_word_digits
    mahler_cf_pow5_word_consumer mahler_cf_digit_carry mahler_cf_nonempty_exit
    mahler_cf_selected_concat mahler_cf_selected_repeat
    mahler_cf_pointed_response_exact mahler_cf_pointed_publisher};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mahler CF source refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Mahler CF source proof" else ();
\<close>

end
