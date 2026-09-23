theory Reverse_196_Publisher_Refinement
  imports Reverse_196_Universal_Emit Reverse_Invariant
begin

lemma carry_out_append:
  "carry_out c (xs@ys) = carry_out (carry_out c xs) ys"
  by (simp add: carry_out_def fold_append)

lemma emit_nth_carry_prefix:
  assumes "i < length ss"
  shows "emit c ss ! i =
    (ss!i + (if carry_out c (take i ss) then 1 else 0)) mod 10"
  using assms
proof (induct ss arbitrary: c i)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis by (simp add: carry_out_def)
  next
    case (Suc j)
    with Cons.prems have bound: "j < length ss" by simp
    show ?thesis unfolding Suc
      using Cons.hyps[OF bound, of "carry_apply (domain s) c"]
      by (simp add: carry_out_def)
  qed
qed

lemma reverse_right_fold_terminal_blank [simp]:
  "reverse_right_fold (ys@[19]) = reverse_right_fold ys"
  by (induct ys) (simp_all add: reverse_right_advance_def)

lemma reverse_two_port_scan_from_nth:
  assumes "i < length ss"
  shows "reverse_two_port_scan_from l ss ! i =
    reverse_emit (reverse_left_fold_from l (take i ss)) (ss!i)
      (reverse_right_fold (drop (Suc i) ss))"
  using assms
proof (induct ss arbitrary: l i)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis by simp
  next
    case (Suc j)
    with Cons.prems have bound: "j < length ss" by simp
    show ?thesis unfolding Suc
      using Cons.hyps[OF bound, of "reverse_left_advance l s"] by simp
  qed
qed

lemma reverse_two_port_scan_nth:
  assumes "i < length ss"
  shows "reverse_two_port_scan ss ! i =
    reverse_emit (reverse_left_fold (take i ss)) (ss!i)
      (reverse_right_fold (drop (Suc i) ss))"
  unfolding reverse_two_port_scan_def reverse_left_fold_def
  using reverse_two_port_scan_from_nth[OF assms, of reverse_left_initial]
  by simp

lemma carry_out_split_nth:
  assumes bound: "i < length ss"
  shows "carry_out
      (carry_apply (domain (ss!i)) (carry_out c (take i ss)))
      (drop (Suc i) ss) = carry_out c ss"
proof -
  have split: "ss = take i ss @ ss!i # drop (Suc i) ss"
    using id_take_nth_drop[OF bound] by simp
  show ?thesis
    by (subst split, simp add: carry_out_append carry_out_def)
qed

lemma length_digits_exact:
  "length (digits ss) =
    length ss + (if carry_out False ss then 1 else 0)"
  by (simp add: digits_def)

lemma length_step_exact [simp]:
  "length (step ss) = length (digits ss)"
  by (simp add: step_def)

lemma digits_nth_no_growth:
  assumes bound: "i < length ss" and no_growth: "\<not> carry_out False ss"
  shows "digits ss ! i =
    (ss!i + carry_bit (carry_out False (take i ss))) mod 10"
  unfolding digits_def carry_bit_def
  using emit_nth_carry_prefix[OF bound, of False] no_growth by simp

lemma palindrome_reverse_drop:
  assumes palindrome: "rev ss = ss" and bound: "i < length ss"
  shows "rev (drop (Suc i) ss) = take (length ss-Suc i) ss"
  using palindrome by (simp add: rev_drop)

lemma strip_blank_tail_append_blank:
  assumes "\<forall>x\<in>set xs. x<19"
  shows "strip_blank_tail (xs@[19]) = xs"
  using assms
  by (induct xs) (auto split: list.split)

theorem reverse_two_port_scan_no_growth:
  assumes valid: "valid_pair ss"
      and no_growth: "\<not> carry_out False ss"
  shows "reverse_two_port_scan (ss@[19]) = step ss@[19]"
proof (rule nth_equalityI)
  have admitted: "\<forall>x\<in>set ss. x<19"
    using valid by (auto simp: valid_pair_def)
  show "length (reverse_two_port_scan (ss@[19])) = length (step ss@[19])"
    using no_growth by (simp add: reverse_two_port_scan_length length_digits_exact)
  fix i
  assume ibound: "i < length (reverse_two_port_scan (ss@[19]))"
  then have ile: "i \<le> length ss"
    by (simp add: reverse_two_port_scan_length)
  show "reverse_two_port_scan (ss@[19]) ! i = (step ss@[19]) ! i"
  proof (cases "i < length ss")
    case True
    have source: "ss!i < 19" using admitted True by simp
    have prefix: "\<forall>x\<in>set (take i ss). x<19"
      using admitted by (meson in_set_takeD)
    have suffix: "\<forall>x\<in>set (drop (Suc i) ss). x<19"
      using admitted by (meson in_set_dropD)
    have branch:
      "\<not> carry_out
        (carry_apply (domain (ss!i)) (carry_out False (take i ss)))
        (drop (Suc i) ss)"
      using carry_out_split_nth[OF True, of False] no_growth by simp
    have emitted:
      "reverse_emit (reverse_left_fold (take i ss)) (ss!i)
          (reverse_right_fold (drop (Suc i) ss)) =
       mirror_pair_step (ss!i)
          (carry_bit (carry_out False (take i ss)))
          (carry_bit (carry_out False (rev (drop (Suc i) ss))))"
      using reverse_emit_no_growth_cell[OF prefix suffix source branch] .
    have scan:
      "reverse_two_port_scan (ss@[19]) ! i =
       reverse_emit (reverse_left_fold (take i ss)) (ss!i)
          (reverse_right_fold (drop (Suc i) ss))"
    proof -
      have current: "(ss@[19])!i = ss!i"
        using True by (simp add: nth_append)
      show ?thesis
        using reverse_two_port_scan_nth[of i "ss@[19]"] True current
        by (simp add: take_append drop_append)
    qed
    have palindrome: "rev ss=ss" using valid by (simp add: valid_pair_def)
    let ?j = "length ss-Suc i"
    have jbound: "?j < length ss" using True by arith
    have digit_i:
      "digits ss!i =
        (ss!i + carry_bit (carry_out False (take i ss))) mod 10"
      using digits_nth_no_growth[OF True no_growth] .
    have digit_j:
      "digits ss!?j =
        (ss!?j + carry_bit (carry_out False (take ?j ss))) mod 10"
      using digits_nth_no_growth[OF jbound no_growth] .
    have reflected_source: "ss!?j = ss!i"
      using palindrome_nth_reflect[OF palindrome True] .
    have reflected_prefix:
      "take ?j ss = rev (drop (Suc i) ss)"
      using palindrome_reverse_drop[OF palindrome True] by simp
    have step_cell: "step ss!i = digits ss!i + digits ss!?j"
      using True no_growth
      by (simp add: step_def digits_def rev_nth)
    have step_bound: "i < length (step ss)"
      using True no_growth by (simp add: length_digits_exact)
    have target: "(step ss@[19])!i = step ss!i"
      using step_bound by (simp add: nth_append)
    show ?thesis
      using scan emitted step_cell digit_i digit_j reflected_source
        reflected_prefix target
      by (simp add: mirror_pair_step_def carry_bit_def)
  next
    case False
    with ile have at_end: "i=length ss" by arith
    have terminal:
      "reverse_emit (reverse_left_fold ss) 19 reverse_right_initial = 19"
      using reverse_emit_terminal_blank_no_growth[OF admitted no_growth] .
    have step_length: "length (step ss) = length ss"
      using no_growth by (simp add: length_digits_exact)
    show ?thesis
      using at_end reverse_two_port_scan_nth[of i "ss@[19]"] terminal
        step_length
      by (simp add: reverse_right_initial_def nth_append)
  qed
qed

theorem reverse_two_port_publisher_no_growth:
  assumes valid: "valid_pair ss"
      and no_growth: "\<not> carry_out False ss"
  shows "reverse_two_port_publisher ss = step ss"
proof -
  have bounded: "\<forall>x\<in>set (step ss). x<19"
    using step_bounded by fastforce
  show ?thesis
    unfolding reverse_two_port_publisher_def
    using reverse_two_port_scan_no_growth[OF valid no_growth]
      strip_blank_tail_append_blank[OF bounded]
    by simp
qed

lemma digits_nth_growth:
  assumes bound: "i < length ss" and growth: "carry_out False ss"
  shows "digits ss!i =
    (ss!i + carry_bit (carry_out False (take i ss))) mod 10"
proof -
  have emit_bound: "i < length (emit False ss)" using bound by simp
  show ?thesis
    unfolding digits_def carry_bit_def
    using emit_nth_carry_prefix[OF bound, of False] growth emit_bound
    by (simp add: nth_append)
qed

lemma digits_growth_last:
  assumes "carry_out False ss"
  shows "digits ss ! length ss = 1"
  using assms by (simp add: digits_def nth_append)

lemma strip_blank_tail_identity:
  assumes "\<forall>x\<in>set xs. x<19"
  shows "strip_blank_tail xs = xs"
  using assms
  by (induct xs) (auto split: list.split)

theorem reverse_two_port_scan_growth:
  assumes valid: "valid_pair ss"
      and growth: "carry_out False ss"
  shows "reverse_two_port_scan (ss@[19]) = step ss"
proof (rule nth_equalityI)
  have admitted: "\<forall>x\<in>set ss. x<19"
    using valid by (auto simp: valid_pair_def)
  have nonempty: "ss\<noteq>[]" using valid by (simp add: valid_pair_def)
  have palindrome: "rev ss=ss" using valid by (simp add: valid_pair_def)
  show "length (reverse_two_port_scan (ss@[19])) = length (step ss)"
    using growth by (simp add: reverse_two_port_scan_length length_digits_exact)
  fix i
  assume ibound: "i < length (reverse_two_port_scan (ss@[19]))"
  then have ile: "i\<le>length ss"
    by (simp add: reverse_two_port_scan_length)
  show "reverse_two_port_scan (ss@[19])!i = step ss!i"
  proof (cases "i<length ss")
    case True
    have source: "ss!i<19" using admitted True by simp
    have prefix: "\<forall>x\<in>set (take i ss). x<19"
      using admitted by (meson in_set_takeD)
    have suffix: "\<forall>x\<in>set (drop (Suc i) ss). x<19"
      using admitted by (meson in_set_dropD)
    have branch:
      "carry_out
        (carry_apply (domain (ss!i)) (carry_out False (take i ss)))
        (drop (Suc i) ss)"
      using carry_out_split_nth[OF True, of False] growth by simp
    have scan:
      "reverse_two_port_scan (ss@[19])!i =
       reverse_emit (reverse_left_fold (take i ss)) (ss!i)
        (reverse_right_fold (drop (Suc i) ss))"
    proof -
      have current: "(ss@[19])!i=ss!i"
        using True by (simp add: nth_append)
      show ?thesis
        using reverse_two_port_scan_nth[of i "ss@[19]"] True current
        by (simp add: take_append drop_append)
    qed
    show ?thesis
    proof (cases i)
      case 0
      have suffix0: "\<forall>x\<in>set (drop 1 ss). x<19"
        using suffix unfolding 0 by simp
      have source0: "ss!0<19" using source unfolding 0 by simp
      have branch0:
        "carry_out (carry_apply (domain (ss!0)) False) (drop 1 ss)"
        using branch unfolding 0 by (simp add: carry_out_def)
      have emitted:
        "reverse_emit reverse_left_initial (ss!0)
            (reverse_right_fold (drop 1 ss)) =
         growth_pair_step (ss!0) 1 0 0"
        using reverse_emit_growth_first_cell[OF suffix0 source0 branch0] .
      have digit_zero: "digits ss!0 = ss!0 mod 10"
        using digits_nth_growth[OF True growth]
        unfolding 0 carry_bit_def by (simp add: carry_out_def)
      have digit_last: "digits ss!length ss=1"
        using digits_growth_last[OF growth] .
      have step_zero:
        "step ss!0 = digits ss!0 + digits ss!length ss"
        using growth nonempty
        by (simp add: step_def length_digits_exact rev_nth)
      have "reverse_two_port_scan (ss@[19])!i =
          growth_pair_step (ss!0) 1 0 0"
        using scan emitted unfolding 0
        by (simp add: reverse_left_fold_def)
      also have "... = digits ss!0 + digits ss!length ss"
        using digit_zero digit_last by (simp add: growth_pair_step_def)
      also have "... = step ss!i" using step_zero unfolding 0 by simp
      finally show ?thesis .
    next
      case (Suc k)
      have positive: "0<i" unfolding Suc by simp
      let ?j = "length ss-i"
      let ?k = "length ss-Suc i"
      have jbound: "?j<length ss" using True positive by arith
      have kbound: "?k<length ss" using True by arith
      have jstep: "?j=Suc ?k" using True by arith
      have reflected_source: "ss!?j = ss!(i-1)"
      proof -
        have "length ss-Suc (i-1)=?j" using positive True by arith
        then show ?thesis
          using palindrome_nth_reflect[OF palindrome, of "i-1"]
            positive True by simp
      qed
      have reflected_current: "ss!?k=ss!i"
        using palindrome_nth_reflect[OF palindrome True] .
      have reflected_prefix:
        "take ?j ss = rev (drop (Suc i) ss)@[ss!i]"
      proof -
        have take_step:
          "take ?j ss = take ?k ss@[ss!?k]"
          using take_Suc_conv_app_nth[OF kbound] jstep by simp
        have reverse_suffix:
          "rev (drop (Suc i) ss)=take ?k ss"
          using palindrome_reverse_drop[OF palindrome True] .
        show ?thesis using take_step reverse_suffix reflected_current by simp
      qed
      have carry_reflected:
        "carry_out False (take ?j ss) =
         carry_apply (domain (ss!i))
           (carry_out False (rev (drop (Suc i) ss)))"
        using reflected_prefix by (simp add: carry_out_append carry_out_def)
      have take_nonempty: "take i ss \<noteq> []"
      proof -
        have "0 < length (take i ss)" using positive True by simp
        then show ?thesis by auto
      qed
      have previous_value: "last (take i ss) = ss!(i-1)"
      proof -
        have kbound: "k<length ss" using True unfolding Suc by arith
        have take_step: "take i ss=take k ss@[ss!k]"
          unfolding Suc using take_Suc_conv_app_nth[OF kbound] .
        show ?thesis using take_step unfolding Suc by simp
      qed
      have emitted:
        "reverse_emit (reverse_left_fold (take i ss)) (ss!i)
            (reverse_right_fold (drop (Suc i) ss)) =
         growth_pair_step (ss!i) (ss!(i-1))
           (carry_bit (carry_out False (take i ss)))
           (carry_bit (carry_out False (take ?j ss)))"
      proof -
        have raw:
          "reverse_emit (reverse_left_fold (take i ss)) (ss!i)
              (reverse_right_fold (drop (Suc i) ss)) =
           growth_pair_step (ss!i) (last (take i ss))
             (carry_bit (carry_out False (take i ss)))
             (carry_bit (carry_apply (domain (ss!i))
               (carry_out False (rev (drop (Suc i) ss)))))"
          using reverse_emit_growth_interior[
            OF prefix suffix source take_nonempty branch] .
        show ?thesis
          using raw by (simp only: carry_reflected previous_value)
      qed
      have digit_i:
        "digits ss!i =
          (ss!i+carry_bit (carry_out False (take i ss))) mod 10"
        using digits_nth_growth[OF True growth] .
      have digit_j:
        "digits ss!?j =
          (ss!?j+carry_bit (carry_out False (take ?j ss))) mod 10"
        using digits_nth_growth[OF jbound growth] .
      have step_cell: "step ss!i = digits ss!i+digits ss!?j"
        using True growth
        by (simp add: step_def length_digits_exact rev_nth)
      have "reverse_two_port_scan (ss@[19])!i =
          growth_pair_step (ss!i) (ss!(i-1))
            (carry_bit (carry_out False (take i ss)))
            (carry_bit (carry_out False (take ?j ss)))"
        using scan emitted by simp
      also have "... = digits ss!i + digits ss!?j"
        using digit_i digit_j reflected_source
        by (simp add: growth_pair_step_def)
      also have "... = step ss!i" using step_cell by simp
      finally show ?thesis .
    qed
  next
    case False
    with ile have at_end: "i=length ss" by arith
    have terminal:
      "reverse_emit (reverse_left_fold ss) 19 reverse_right_initial =
        last ss mod 10+1"
      using reverse_emit_terminal_blank_growth[OF admitted nonempty growth] .
    have first_last: "last ss=ss!0"
    proof -
      have "last ss = last (rev ss)" using palindrome by simp
      also have "... = hd ss" by (rule last_rev)
      also have "... = ss!0" by (rule hd_conv_nth[OF nonempty])
      finally show ?thesis .
    qed
    have digit_zero: "digits ss!0=ss!0 mod 10"
      using digits_nth_growth[of 0 ss, OF _ growth] nonempty
      by (simp add: carry_bit_def carry_out_def)
    have digit_last: "digits ss!length ss=1"
      using digits_growth_last[OF growth] .
    have step_end:
      "step ss!length ss = digits ss!length ss+digits ss!0"
      using growth nonempty
      by (simp add: step_def length_digits_exact rev_nth)
    have scan_end:
      "reverse_two_port_scan (ss@[19])!i =
       reverse_emit (reverse_left_fold ss) 19 reverse_right_initial"
      using at_end reverse_two_port_scan_nth[of i "ss@[19]"]
      by (simp add: reverse_right_initial_def)
    have "reverse_two_port_scan (ss@[19])!i = last ss mod 10+1"
      using scan_end terminal by simp
    also have "... = digits ss!length ss+digits ss!0"
      using first_last digit_zero digit_last by simp
    also have "... = step ss!i" using step_end at_end by simp
    finally show ?thesis .
  qed
qed

theorem reverse_two_port_publisher_growth:
  assumes valid: "valid_pair ss"
      and growth: "carry_out False ss"
  shows "reverse_two_port_publisher ss = step ss"
proof -
  have bounded: "\<forall>x\<in>set (step ss). x<19"
    using step_bounded by fastforce
  show ?thesis
    unfolding reverse_two_port_publisher_def
    using reverse_two_port_scan_growth[OF valid growth]
      strip_blank_tail_identity[OF bounded]
    by simp
qed

theorem reverse_two_port_publisher_refines_step:
  assumes "valid_pair ss"
  shows "reverse_two_port_publisher ss = step ss"
  using reverse_two_port_publisher_no_growth[OF assms]
    reverse_two_port_publisher_growth[OF assms]
  by blast

corollary reverse_two_port_publisher_refines_all_196_steps:
  "reverse_two_port_publisher (run step n [7,18,7]) =
    step (run step n [7,18,7])"
  using reverse_two_port_publisher_refines_step all_196_pair_fields_valid by blast

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms reverse_two_port_scan_no_growth
      reverse_two_port_publisher_no_growth reverse_two_port_scan_growth
      reverse_two_port_publisher_growth reverse_two_port_publisher_refines_step
      reverse_two_port_publisher_refines_all_196_steps}) then ()
    else error "Reverse 196 publisher refinement depends on an oracle";
\<close>

text \<open>The checked whole-list result splits on the exact terminal carry.
Each scan cell and decimal digit reduces to the same prefix carry.  Palindrome
symmetry identifies a reversed right suffix with the reflected prefix; growth
contributes the two edge cells and shifts the interior pairing by one.\<close>

end
