theory Reverse_EQ_Phase_Guard
  imports Reverse_Carry_Suffix_Refinement
begin

text \<open>The two local ports keep the complete pair coefficient and the
physical prefix carry.  The phase expression is an implementation of the
same source digit and carry, including the EQ-9 case.\<close>

definition reverse_eq_phase_digit :: "nat \<Rightarrow> bool \<Rightarrow> nat" where
  "reverse_eq_phase_digit s carry =
    ((s mod 5 + carry_bit carry) mod 5) +
      5 * (if ((s div 5) mod 2 = 1) \<noteq> (carry \<and> s mod 5 = 4)
        then 1 else 0)"

definition reverse_eq_phase_carry :: "nat \<Rightarrow> bool \<Rightarrow> bool" where
  "reverse_eq_phase_carry s carry = (9 < s \<or> (s = 9 \<and> carry))"

lemma reverse_eq_phase_digit_exact:
  assumes "s < 19"
  shows "reverse_eq_phase_digit s carry = (s + carry_bit carry) mod 10"
proof -
  have cases: "s = 0 \<or> s = 1 \<or> s = 2 \<or> s = 3 \<or> s = 4 \<or>
      s = 5 \<or> s = 6 \<or> s = 7 \<or> s = 8 \<or> s = 9 \<or>
      s = 10 \<or> s = 11 \<or> s = 12 \<or> s = 13 \<or> s = 14 \<or>
      s = 15 \<or> s = 16 \<or> s = 17 \<or> s = 18"
    using assms by (rule nat_less_nineteen_cases)
  show ?thesis using cases
    by (cases carry; elim disjE; simp add: reverse_eq_phase_digit_def carry_bit_def)
qed

lemma reverse_eq_phase_carry_exact:
  assumes "s < 19"
  shows "reverse_eq_phase_carry s carry = carry_apply (domain s) carry"
proof -
  have cases: "s = 0 \<or> s = 1 \<or> s = 2 \<or> s = 3 \<or> s = 4 \<or>
      s = 5 \<or> s = 6 \<or> s = 7 \<or> s = 8 \<or> s = 9 \<or>
      s = 10 \<or> s = 11 \<or> s = 12 \<or> s = 13 \<or> s = 14 \<or>
      s = 15 \<or> s = 16 \<or> s = 17 \<or> s = 18"
    using assms by (rule nat_less_nineteen_cases)
  show ?thesis using cases
    by (cases carry; elim disjE; simp add: reverse_eq_phase_carry_def domain_def)
qed

lemma reverse_eq_phase_physical_digit:
  assumes bound: "i < length source" and pair: "source ! i < 19"
  shows "digits source ! i =
    reverse_eq_phase_digit (source ! i) (punctured_prefix_carry source i)"
proof -
  have physical:
    "digits source ! i =
      (source ! i + carry_bit (punctured_prefix_carry source i)) mod 10"
  proof (cases "carry_out False source")
    case True
    then show ?thesis using digits_nth_growth[OF bound True]
      by (simp add: punctured_prefix_carry_def)
  next
    case False
    then show ?thesis using digits_nth_no_growth[OF bound]
      by (simp add: punctured_prefix_carry_def)
  qed
  show ?thesis using physical reverse_eq_phase_digit_exact[OF pair] by simp
qed

lemma reverse_eq_phase_physical_carry:
  assumes bound: "i < length source" and pair: "source ! i < 19"
  shows "punctured_prefix_carry source (Suc i) =
    reverse_eq_phase_carry (source ! i) (punctured_prefix_carry source i)"
  using carry_out_take_successor[OF bound] reverse_eq_phase_carry_exact[OF pair]
  by (simp add: punctured_prefix_carry_def)

theorem reverse_eq_phase_source_no_growth:
  assumes prefix: "\<forall>x\<in>set xs. x < 19"
      and suffix: "\<forall>x\<in>set ys. x < 19"
      and cell: "s < 19"
      and quiet: "\<not> carry_out
        (carry_apply (domain s) (carry_out False xs)) ys"
  shows "reverse_emit (reverse_left_fold xs) s (reverse_right_fold ys) =
    reverse_eq_phase_digit s (carry_out False xs) +
      reverse_eq_phase_digit s (carry_out False (rev ys))"
  using reverse_emit_no_growth_cell[OF prefix suffix cell quiet]
    reverse_eq_phase_digit_exact[OF cell]
  by (simp add: mirror_pair_step_def)

theorem reverse_eq_phase_source_growth_interior:
  assumes prefix: "\<forall>x\<in>set xs. x < 19"
      and suffix: "\<forall>x\<in>set ys. x < 19"
      and cell: "s < 19" and interior: "xs \<noteq> []"
      and growth: "carry_out
        (carry_apply (domain s) (carry_out False xs)) ys"
  shows "reverse_emit (reverse_left_fold xs) s (reverse_right_fold ys) =
    reverse_eq_phase_digit s (carry_out False xs) +
      reverse_eq_phase_digit (last xs)
        (carry_apply (domain s) (carry_out False (rev ys)))"
proof -
  have previous: "last xs < 19"
    using prefix interior by (simp add: last_in_set)
  show ?thesis
    using reverse_emit_growth_interior[OF prefix suffix cell interior growth]
      reverse_eq_phase_digit_exact[OF cell]
      reverse_eq_phase_digit_exact[OF previous]
    by (simp add: growth_pair_step_def)
qed

lemma reverse_eq_phase_quiet_eq:
  assumes "s < 19"
  shows "(reverse_eq_phase_digit s left + reverse_eq_phase_digit s right = 9) =
    (s mod 5 = 4 \<and> left \<noteq> right)"
proof -
  have table:
    "list_all (\<lambda>x. list_all (\<lambda>l. list_all (\<lambda>r.
      (reverse_eq_phase_digit x l + reverse_eq_phase_digit x r = 9) =
        (x mod 5 = 4 \<and> l \<noteq> r)) [False, True]) [False, True]) [0..<19]"
    by code_simp
  show ?thesis using table assms
    by (cases left; cases right; simp add: list_all_iff)
qed

corollary reverse_eq_phase_source_no_growth_eq:
  assumes prefix: "\<forall>x\<in>set xs. x < 19"
      and suffix: "\<forall>x\<in>set ys. x < 19"
      and cell: "s < 19"
      and quiet: "\<not> carry_out
        (carry_apply (domain s) (carry_out False xs)) ys"
  shows "(reverse_emit (reverse_left_fold xs) s (reverse_right_fold ys) = 9) =
    (s mod 5 = 4 \<and> carry_out False xs \<noteq> carry_out False (rev ys))"
  using reverse_eq_phase_source_no_growth[OF prefix suffix cell quiet]
    reverse_eq_phase_quiet_eq[OF cell] by simp

lemma reverse_eq_reset_independent_carry:
  assumes "s < 19" "s \<noteq> 9"
  shows "reverse_eq_phase_carry s incoming = (9 < s)"
  using assms by (simp add: reverse_eq_phase_carry_def)

lemma reverse_eq_reset_next_digit:
  assumes reset: "s < 19" "s \<noteq> 9"
  shows "reverse_eq_phase_digit t (reverse_eq_phase_carry s incoming) =
    reverse_eq_phase_digit t (9 < s)"
  using reverse_eq_reset_independent_carry[OF reset] by simp

lemma reverse_eq_physical_reset_next_digit:
  assumes bound: "Suc i < length source"
      and reset: "source ! i < 19" "source ! i \<noteq> 9"
      and next_pair: "source ! Suc i < 19"
  shows "digits source ! Suc i = reverse_eq_phase_digit (source ! Suc i) (9 < source ! i)"
proof -
  have prefix: "i < length source" using bound by simp
  show ?thesis
    using reverse_eq_phase_physical_digit[OF bound next_pair]
      reverse_eq_phase_physical_carry[OF prefix reset(1)]
      reverse_eq_reset_independent_carry[OF reset]
    by simp
qed


text \<open>The ordered mask action keeps both inlet carries.  The right inlet
is transported through the suffix before a cell is evaluated.  This also
makes the overlap between adjacent grammar fragments explicit.\<close>

fun reverse_eq_mask :: "bool \<Rightarrow> bool \<Rightarrow> nat list \<Rightarrow> bool list" where
  "reverse_eq_mask left right [] = []"
| "reverse_eq_mask left right (s # ss) =
    (s mod 5 = 4 \<and> left \<noteq> carry_out right (rev ss)) #
      reverse_eq_mask (carry_apply (domain s) left) right ss"

lemma reverse_eq_mask_length [simp]:
  "length (reverse_eq_mask left right ss) = length ss"
  by (induction ss arbitrary: left) simp_all

lemma reverse_eq_mask_nth:
  assumes "i < length ss"
  shows "reverse_eq_mask left right ss ! i =
    (ss ! i mod 5 = 4 \<and>
      carry_out left (take i ss) \<noteq>
        carry_out right (rev (drop (Suc i) ss)))"
  using assms
proof (induction ss arbitrary: left i)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  then show ?case
    by (cases i) (simp_all add: carry_out_def)
qed

lemma reverse_eq_mask_append:
  "reverse_eq_mask left right (xs @ ys) =
    reverse_eq_mask left (carry_out right (rev ys)) xs @
      reverse_eq_mask (carry_out left xs) right ys"
  by (induction xs arbitrary: left)
    (simp_all add: carry_out_append carry_out_def)

lemma reverse_eq_mask_quiet_source_cell:
  assumes valid: "valid_pair source"
      and quiet: "\<not> carry_out False source"
      and index: "i < length source"
  shows "reverse_eq_mask False False source ! i = (step source ! i = 9)"
proof -
  have admitted: "\<forall>x\<in>set source. x < 19"
    using valid by (auto simp: valid_pair_def)
  have prefix: "\<forall>x\<in>set (take i source). x < 19"
    using admitted by (meson in_set_takeD)
  have suffix: "\<forall>x\<in>set (drop (Suc i) source). x < 19"
    using admitted by (meson in_set_dropD)
  have cell: "source ! i < 19" using admitted index by simp
  have branch:
    "\<not> carry_out
      (carry_apply (domain (source ! i)) (carry_out False (take i source)))
      (drop (Suc i) source)"
    using carry_out_split_nth[OF index, of False] quiet by simp
  have scan:
    "reverse_emit (reverse_left_fold (take i source)) (source ! i)
       (reverse_right_fold (drop (Suc i) source)) = step source ! i"
    using reverse_two_port_scan_nth[of i "source @ [19]"]
      reverse_two_port_scan_no_growth[OF valid quiet] index
    by (simp add: reverse_two_port_scan_length nth_append take_append drop_append
        length_digits_exact)
  show ?thesis
    using reverse_eq_mask_nth[OF index, of False False]
      reverse_eq_phase_source_no_growth_eq[OF prefix suffix cell branch] scan
    by simp
qed


type_synonym reverse_eq_action =
  "(bool \<Rightarrow> bool) \<times> (bool \<Rightarrow> bool) \<times>
    (bool \<Rightarrow> bool \<Rightarrow> bool list)"

definition reverse_eq_action_word :: "nat list \<Rightarrow> reverse_eq_action" where
  "reverse_eq_action_word source =
    ((\<lambda>c. carry_out c source), (\<lambda>c. carry_out c (rev source)),
      (\<lambda>left right. reverse_eq_mask left right source))"

definition reverse_eq_action_join ::
    "reverse_eq_action \<Rightarrow> reverse_eq_action \<Rightarrow> reverse_eq_action" where
  "reverse_eq_action_join first second =
    ((\<lambda>c. fst second (fst first c)),
      (\<lambda>c. fst (snd first) (fst (snd second) c)),
      (\<lambda>left right.
        snd (snd first) left (fst (snd second) right) @
          snd (snd second) (fst first left) right))"

lemma reverse_eq_action_word_join:
  "reverse_eq_action_word (xs @ ys) =
    reverse_eq_action_join (reverse_eq_action_word xs) (reverse_eq_action_word ys)"
  by (simp add: reverse_eq_action_word_def reverse_eq_action_join_def
      carry_out_append reverse_eq_mask_append)

lemma reverse_eq_action_join_associative:
  "reverse_eq_action_join (reverse_eq_action_join a b) c =
    reverse_eq_action_join a (reverse_eq_action_join b c)"
  by (cases a; cases b; cases c)
    (simp add: reverse_eq_action_join_def fun_eq_iff append_assoc)

lemma reverse_eq_action_empty_left:
  "reverse_eq_action_join (reverse_eq_action_word []) a = a"
  by (cases a)
    (simp add: reverse_eq_action_join_def reverse_eq_action_word_def
      carry_out_def fun_eq_iff)

lemma reverse_eq_action_empty_right:
  "reverse_eq_action_join a (reverse_eq_action_word []) = a"
  by (cases a)
    (simp add: reverse_eq_action_join_def reverse_eq_action_word_def
      carry_out_def fun_eq_iff)

fun reverse_eq_action_repeat :: "nat \<Rightarrow> reverse_eq_action \<Rightarrow> reverse_eq_action" where
  "reverse_eq_action_repeat 0 action = reverse_eq_action_word []"
| "reverse_eq_action_repeat (Suc n) action =
    reverse_eq_action_join action (reverse_eq_action_repeat n action)"

lemma reverse_eq_action_repeat_exact:
  "reverse_eq_action_repeat n (reverse_eq_action_word source) =
    reverse_eq_action_word (concat (replicate n source))"
  by (induction n) (simp_all add: reverse_eq_action_word_join)

datatype reverse_eq_source_grammar =
    Reverse_EQ_Atom nat
  | Reverse_EQ_Concat reverse_eq_source_grammar reverse_eq_source_grammar
  | Reverse_EQ_Repeat nat reverse_eq_source_grammar

fun reverse_eq_source_word :: "reverse_eq_source_grammar \<Rightarrow> nat list" where
  "reverse_eq_source_word (Reverse_EQ_Atom s) = [s]"
| "reverse_eq_source_word (Reverse_EQ_Concat first second) =
    reverse_eq_source_word first @ reverse_eq_source_word second"
| "reverse_eq_source_word (Reverse_EQ_Repeat n source) =
    concat (replicate n (reverse_eq_source_word source))"

fun reverse_eq_source_action :: "reverse_eq_source_grammar \<Rightarrow> reverse_eq_action" where
  "reverse_eq_source_action (Reverse_EQ_Atom s) = reverse_eq_action_word [s]"
| "reverse_eq_source_action (Reverse_EQ_Concat first second) =
    reverse_eq_action_join (reverse_eq_source_action first)
      (reverse_eq_source_action second)"
| "reverse_eq_source_action (Reverse_EQ_Repeat n source) =
    reverse_eq_action_repeat n (reverse_eq_source_action source)"

theorem reverse_eq_source_grammar_action:
  "reverse_eq_source_action source = reverse_eq_action_word (reverse_eq_source_word source)"
  by (induction source) (simp_all add: reverse_eq_action_word_join
      reverse_eq_action_repeat_exact)

theorem reverse_eq_source_grammar_quiet_cell:
  assumes valid: "valid_pair (reverse_eq_source_word source)"
      and quiet: "\<not> carry_out False (reverse_eq_source_word source)"
      and index: "i < length (reverse_eq_source_word source)"
  shows "snd (snd (reverse_eq_source_action source)) False False ! i =
    (step (reverse_eq_source_word source) ! i = 9)"
  using reverse_eq_source_grammar_action[of source]
    reverse_eq_mask_quiet_source_cell[OF valid quiet index]
  by (simp add: reverse_eq_action_word_def)

lemma reverse_eq_mask_opposite_inlets:
  "reverse_eq_mask False True [9,9] = [True,True]"
  "reverse_eq_mask False False [9,9] = [False,False]"
  by (simp_all add: carry_out_def domain_def)

lemma reverse_eq_source_outer_seventeen_forces_birth:
  assumes valid: "valid_pair source" and outer: "hd source = 17"
  shows "carry_out False source"
proof -
  have nonempty: "source \<noteq> []" and symmetric: "rev source = source"
    using valid by (auto simp: valid_pair_def)
  obtain prefix symbol where split: "source = prefix @ [symbol]"
    using nonempty by (cases source rule: rev_cases) auto
  have "last source = hd source" using nonempty symmetric by (metis hd_rev)
  then have "symbol = 17" using split outer by simp
  then show ?thesis using split
    by (simp add: carry_out_append carry_out_def domain_def)
qed


lemma reverse_eq_mask_reset_clips_remote_inlet:
  assumes reset: "reset < 19" "reset \<noteq> 9"
  shows "take (length prefix)
      (reverse_eq_mask left right (prefix @ reset # suffix)) =
    reverse_eq_mask left (9 < reset) prefix"
proof -
  have reset_carry:
    "carry_out right (rev suffix @ [reset]) = (9 < reset)"
    using reverse_eq_reset_independent_carry[OF reset,
        of "carry_out right (rev suffix)"]
      reverse_eq_phase_carry_exact[OF reset(1),
        of "carry_out right (rev suffix)"]
    by (simp add: carry_out_append carry_out_def)
  show ?thesis using reverse_eq_mask_append[of left right prefix "reset # suffix"]
    by (simp add: reset_carry)
qed


lemma reverse_eq_phase_seventeen_digit:
  "reverse_eq_phase_digit 17 carry = 7 + carry_bit carry"
  by (cases carry) (simp_all add: reverse_eq_phase_digit_def carry_bit_def)

theorem reverse_eq_first_birth_interior:
  assumes valid: "valid_pair (17 # s # ys)"
  shows "step (17 # s # ys) ! 1 =
    reverse_eq_phase_digit s True + 7 +
      carry_bit (carry_apply (domain s) (carry_out False (rev ys)))"
proof -
  let ?source = "17 # s # ys"
  have growth: "carry_out False ?source"
    by (rule reverse_eq_source_outer_seventeen_forces_birth[OF valid]) simp
  have bounded: "s < 19" and suffix: "\<forall>x\<in>set ys. x < 19"
    using valid by (auto simp: valid_pair_def)
  have branch:
    "carry_out (carry_apply (domain s) (carry_out False [17])) ys"
    using carry_out_split_nth[of 1 ?source False] growth by simp
  have emitted:
    "reverse_emit (reverse_left_fold [17]) s (reverse_right_fold ys) =
      reverse_eq_phase_digit s True + 7 +
        carry_bit (carry_apply (domain s) (carry_out False (rev ys)))"
    using reverse_eq_phase_source_growth_interior[of "[17]" ys s]
      bounded suffix branch
    by (simp add: carry_out_def domain_def reverse_eq_phase_seventeen_digit
        carry_bit_def split: bool.splits)
  have scan:
    "reverse_emit (reverse_left_fold [17]) s (reverse_right_fold ys) =
      step ?source ! 1"
    using reverse_two_port_scan_nth[of 1 "?source @ [19]"]
      reverse_two_port_scan_growth[OF valid growth]
    by simp
  show ?thesis using scan emitted by simp
qed

ML \<open>
  val checked = @{thms reverse_eq_phase_digit_exact reverse_eq_phase_carry_exact
    reverse_eq_phase_physical_digit reverse_eq_phase_physical_carry
    reverse_eq_phase_source_no_growth reverse_eq_phase_source_growth_interior
    reverse_eq_phase_quiet_eq reverse_eq_phase_source_no_growth_eq
    reverse_eq_reset_independent_carry reverse_eq_physical_reset_next_digit
    reverse_eq_mask_nth reverse_eq_mask_append reverse_eq_mask_quiet_source_cell
    reverse_eq_action_word_join reverse_eq_action_join_associative
    reverse_eq_action_repeat_exact reverse_eq_source_grammar_action
    reverse_eq_source_grammar_quiet_cell reverse_eq_mask_opposite_inlets
    reverse_eq_source_outer_seventeen_forces_birth
    reverse_eq_mask_reset_clips_remote_inlet
    reverse_eq_first_birth_interior};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse EQ phase guard depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reverse EQ phase guard proof" else ();
\<close>

end
