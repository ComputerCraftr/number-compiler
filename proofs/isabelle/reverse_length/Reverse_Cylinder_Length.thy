theory Reverse_Cylinder_Length
  imports "Reverse_Residuals.Reverse_196_Publisher_Refinement"
begin

text \<open>This theory records the finite length and terminal-carry facts
needed by a source-bound reverse/add publisher.  It reasons through the
carry fold and queried pair positions; it does not introduce a recursive
normalizer or a complexity claim.\<close>

fun first_reset :: "nat list \<Rightarrow> bool option" where
  "first_reset [] = None"
| "first_reset (s # ss) =
    (if s = 9 then first_reset ss else Some (10 \<le> s))"

definition first_non_neutral_carry :: "nat list \<Rightarrow> bool" where
  "first_non_neutral_carry ss =
    (case first_reset ss of None \<Rightarrow> False | Some c \<Rightarrow> c)"

lemma first_reset_append:
  "first_reset (xs@ys) =
    (case first_reset xs of None \<Rightarrow> first_reset ys | Some c \<Rightarrow> Some c)"
  by (induct xs; auto split: option.splits)

lemma first_reset_none_iff:
  "first_reset ss = None \<longleftrightarrow> (\<forall>x\<in>set ss. x = 9)"
  by (induct ss; auto)

lemma carry_out_reverse_first_reset:
  "carry_out c (rev ss) =
    (case first_reset ss of None \<Rightarrow> c | Some b \<Rightarrow> b)"
  by (induct ss; auto simp: carry_out_append carry_out_def domain_def
      split: option.splits)

lemma palindrome_terminal_carry_first_non_neutral:
  assumes palindrome: "rev ss = ss"
  shows "carry_out False ss = first_non_neutral_carry ss"
  using carry_out_reverse_first_reset[of False ss] palindrome
  by (simp add: first_non_neutral_carry_def)

lemma all_nines_terminal_carry_false:
  assumes all_nines: "\<forall>x\<in>set ss. x = 9"
  shows "carry_out False ss = False"
proof -
  have neutral: "first_reset (rev ss) = None"
    using all_nines by (simp add: first_reset_none_iff)
  show ?thesis
    using carry_out_reverse_first_reset[of False "rev ss"] neutral by simp
qed

lemma first_reset_palindrome_prefix:
  assumes palindrome: "rev ss = ss" and cover: "length ss \<le> 2*k"
  shows "first_reset (take k ss) = first_reset ss"
proof (cases "first_reset (take k ss)")
  case None
  have prefix: "\<forall>x\<in>set (take k ss). x = 9"
    using None by (simp add: first_reset_none_iff)
  have all: "\<forall>i<length ss. ss!i = 9"
  proof (intro allI impI)
    fix i
    assume bound: "i < length ss"
    show "ss!i = 9"
    proof (cases "i < k")
      case True
      have inside: "i < length (take k ss)" using bound True by simp
      have "(take k ss)!i \<in> set (take k ss)"
        using nth_mem[OF inside] .
      then show ?thesis using prefix True by simp
    next
      case False
      let ?j = "length ss - Suc i"
      have jbound: "?j < length ss" using bound by arith
      have jprefix: "?j < k" using bound False cover by arith
      have inside: "?j < length (take k ss)" using jbound jprefix by simp
      have "(take k ss)!?j \<in> set (take k ss)"
        using nth_mem[OF inside] .
      then have source_value: "ss!?j = 9" using prefix jprefix by simp
      have reflected: "ss!?j = ss!i"
        using rev_nth[OF bound] palindrome by simp
      show ?thesis using source_value reflected by simp
    qed
  qed
  have "first_reset ss = None"
    using all by (auto simp: first_reset_none_iff in_set_conv_nth)
  then show ?thesis using None by simp
next
  case (Some b)
  show ?thesis
    using first_reset_append[of "take k ss" "drop k ss"] Some by simp
qed

fun first_reset_queries :: "nat list \<Rightarrow> nat" where
  "first_reset_queries [] = 0"
| "first_reset_queries (s#ss) =
    (if s = 9 then Suc (first_reset_queries ss) else 1)"

lemma first_reset_queries_bound:
  "first_reset_queries (take k ss) \<le> k"
proof -
  have "\<And>xs. first_reset_queries xs \<le> length xs"
    by (induct_tac xs; auto)
  then have "first_reset_queries (take k ss) \<le> length (take k ss)" .
  also have "length (take k ss) \<le> k" by simp
  finally show ?thesis .
qed

definition cylinder_length_query :: "nat list \<Rightarrow> nat" where
  "cylinder_length_query ss = length ss +
    (if first_non_neutral_carry (take ((length ss+1) div 2) ss) then 1 else 0)"

theorem cylinder_length_query_exact:
  assumes palindrome: "rev ss = ss"
  shows "cylinder_length_query ss = length (digits ss)"
proof -
  have cover: "length ss \<le> 2*((length ss+1) div 2)" by presburger
  have prefix: "first_reset (take ((length ss+1) div 2) ss) = first_reset ss"
    using first_reset_palindrome_prefix[OF palindrome cover] .
  show ?thesis
    using palindrome_terminal_carry_first_non_neutral[OF palindrome] prefix
    by (simp add: cylinder_length_query_def length_digits_exact first_non_neutral_carry_def)
qed

corollary publisher_two_step_length_query_exact:
  assumes valid: "valid_pair ss"
  shows "cylinder_length_query (reverse_two_port_publisher ss) =
    length (digits (step ss))"
  using cylinder_length_query_exact[OF step_symmetric, of ss]
    reverse_two_port_publisher_refines_step[OF valid] by simp


lemma no_growth_reflected_coordinate:
  assumes position: "i < length ss"
      and no_growth: "\<not> carry_out False ss"
  shows "length (digits ss) - Suc i = length ss - Suc i"
  using position no_growth
  by (simp add: length_digits_exact)

lemma growth_reflected_coordinate:
  assumes position: "i \<le> length ss"
      and growth: "carry_out False ss"
  shows "length (digits ss) - Suc i = length ss - i"
proof -
  have length_growth: "length (digits ss) = length ss + 1"
    using growth by (simp add: length_digits_exact)
  show ?thesis using position length_growth by arith
qed

lemma growth_edge_digit_one:
  assumes growth: "carry_out False ss"
  shows "digits ss ! length ss = 1"
  using digits_growth_last[OF growth] .

lemma growth_edge_coordinate_is_leading_one:
  assumes growth: "carry_out False ss"
  shows "length (digits ss) = length ss + 1"
    and "digits ss ! length ss = 1"
  using growth_edge_digit_one[OF growth]
    length_digits_exact[of ss] growth by simp_all

ML \<open>
  val checked = @{thms first_reset_append first_reset_none_iff
    carry_out_reverse_first_reset palindrome_terminal_carry_first_non_neutral
    first_reset_palindrome_prefix first_reset_queries_bound cylinder_length_query_exact
    publisher_two_step_length_query_exact
    all_nines_terminal_carry_false no_growth_reflected_coordinate
    growth_reflected_coordinate growth_edge_digit_one
    growth_edge_coordinate_is_leading_one};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse cylinder length proof depends on an oracle";
\<close>

end
