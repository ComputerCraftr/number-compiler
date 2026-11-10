theory Reverse_Carry_Suffix_Refinement
  imports Reverse_Growth_Run_Admission
    "Reverse_Residuals.Reverse_Punctured_T2_Coefficients"
begin

text \<open>A physical Q19 source step has the coefficient operator
@{term "2"} on a quiet row and @{term "1+z"} on a growth row.  Its signed
forcing below is built from the punctured T2 coefficient producer, whose
definitions use the actual prefix-carry track.  It is not defined as the
difference between an assumed endpoint and the old field.  This theory proves
the finite source recurrence and its five-quiet-row erasure; it does not turn
arbitrary carry rows into source-authority witnesses.\<close>

definition reverse_q19_source_coefficient :: "nat list \<Rightarrow> nat \<Rightarrow> int" where
  "reverse_q19_source_coefficient source i =
    (if i < length source then int (source ! i) else 0)"

definition reverse_q19_homogeneous_coefficient ::
    "bool \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int" where
  "reverse_q19_homogeneous_coefficient growth source i =
    (if growth then source i + (if i=0 then 0 else source (i-1))
     else 2 * source i)"

definition reverse_q19_source_forcing_coefficient ::
    "nat list \<Rightarrow> nat \<Rightarrow> int" where
  "reverse_q19_source_forcing_coefficient source i =
    (if carry_out False source then
      if i=0 \<or> i=length source then
        int (punctured_growth_edge_coefficient source) -
          reverse_q19_homogeneous_coefficient True
            (reverse_q19_source_coefficient source) i
      else if i < length source then
        int (punctured_growth_interior_coefficient source i) -
          reverse_q19_homogeneous_coefficient True
            (reverse_q19_source_coefficient source) i
      else 0
     else if i < length source then
        int (punctured_no_growth_coefficient source i) -
          reverse_q19_homogeneous_coefficient False
            (reverse_q19_source_coefficient source) i
     else 0)"

definition reverse_q19_carry_forcing_coefficient ::
    "nat list \<Rightarrow> nat \<Rightarrow> int" where
  "reverse_q19_carry_forcing_coefficient source i =
    (if carry_out False source then
      if i=0 \<or> i=length source then
        1 - 10 * int (carry_bit (punctured_prefix_carry source 1))
      else if i < length source then
        int (carry_bit (punctured_prefix_carry source i)) +
        int (carry_bit (punctured_prefix_carry source (length source-i))) -
        10 * (int (carry_bit (punctured_prefix_carry source (Suc i))) +
          int (carry_bit (punctured_prefix_carry source
            (Suc (length source-i)))))
      else 0
     else if i < length source then
        int (carry_bit (punctured_prefix_carry source i)) +
        int (carry_bit (punctured_prefix_carry source (length source-Suc i))) -
        10 * (int (carry_bit (punctured_prefix_carry source (Suc i))) +
          int (carry_bit (punctured_prefix_carry source (length source-i))) )
     else 0)"

lemma reverse_q19_digit_int_carry_balance:
  assumes index: "i < length source" and symbol: "source ! i < 19"
  shows "int (digits source ! i) =
    int (source ! i) +
      int (carry_bit (punctured_prefix_carry source i)) -
      10 * int (carry_bit (punctured_prefix_carry source (Suc i)))"
proof -
  let ?incoming = "punctured_prefix_carry source i"
  let ?outgoing = "punctured_prefix_carry source (Suc i)"
  have outgoing:
    "?outgoing = carry_apply (domain (source ! i)) ?incoming"
    using carry_out_take_successor[OF index]
    by (simp add: punctured_prefix_carry_def)
  have subtract_bound:
    "10 * carry_bit ?outgoing \<le> source ! i + carry_bit ?incoming"
    using punctured_carry_subtrahend_bound[of "source ! i" ?incoming]
      outgoing by simp
  have normalized:
    "digits source ! i = source ! i + carry_bit ?incoming -
      10 * carry_bit ?outgoing"
    by (rule punctured_digits_cell_exact[OF index symbol])
  have balance:
    "source ! i + carry_bit ?incoming =
      digits source ! i + 10 * carry_bit ?outgoing"
    using normalized subtract_bound by arith
  have int_balance:
    "int (source ! i) + int (carry_bit ?incoming) =
      int (digits source ! i) + 10 * int (carry_bit ?outgoing)"
    using balance by simp
  show ?thesis using int_balance by linarith
qed

lemma reverse_q19_source_forcing_quiet_carry_formula:
  assumes valid: "valid_pair source"
      and quiet: "\<not> carry_out False source"
      and index: "i < length source"
  shows "reverse_q19_source_forcing_coefficient source i =
    int (carry_bit (punctured_prefix_carry source i)) +
    int (carry_bit (punctured_prefix_carry source (length source-Suc i))) -
    10 * (int (carry_bit (punctured_prefix_carry source (Suc i))) +
      int (carry_bit (punctured_prefix_carry source (length source-i))))"
proof -
  let ?j = "length source - Suc i"
  have symmetric: "rev source = source"
    using valid by (simp add: valid_pair_def)
  have j_index: "?j < length source" using index by arith
  have j_succ: "Suc ?j = length source-i" using index by arith
  have reflected: "source ! ?j = source ! i"
    using palindrome_nth_reflect[OF symmetric index] by simp
  have source_i_member: "source ! i \<in> set source"
    by (rule nth_mem[OF index])
  have source_i_le: "source ! i \<le> 18"
    using valid source_i_member by (auto simp: valid_pair_def)
  have source_i: "source ! i < 19" using source_i_le by arith
  have source_j_member: "source ! ?j \<in> set source"
    by (rule nth_mem[OF j_index])
  have source_j_le: "source ! ?j \<le> 18"
    using valid source_j_member by (auto simp: valid_pair_def)
  have source_j: "source ! ?j < 19" using source_j_le by arith
  have producer:
    "punctured_no_growth_coefficient source i = step source ! i"
    by (rule punctured_no_growth_coefficient_refines_step[OF valid quiet index])
  have step_cell:
    "step source ! i = digits source ! i + digits source ! ?j"
    using quiet index by (simp add: step_def digits_def rev_nth)
  have producer_digits:
    "punctured_no_growth_coefficient source i =
      digits source ! i + digits source ! ?j"
    using producer step_cell by simp
  have digit_i:
    "int (digits source ! i) = int (source ! i) +
      int (carry_bit (punctured_prefix_carry source i)) -
      10 * int (carry_bit (punctured_prefix_carry source (Suc i)))"
    by (rule reverse_q19_digit_int_carry_balance[OF index source_i])
  have digit_j:
    "int (digits source ! ?j) = int (source ! ?j) +
      int (carry_bit (punctured_prefix_carry source ?j)) -
      10 * int (carry_bit (punctured_prefix_carry source (Suc ?j)))"
    by (rule reverse_q19_digit_int_carry_balance[OF j_index source_j])
  have carry_formula:
    "int (punctured_no_growth_coefficient source i) - 2 * int (source ! i) =
      int (carry_bit (punctured_prefix_carry source i)) +
      int (carry_bit (punctured_prefix_carry source ?j)) -
      10 * (int (carry_bit (punctured_prefix_carry source (Suc i))) +
        int (carry_bit (punctured_prefix_carry source (Suc ?j))))"
    using producer_digits digit_i digit_j reflected
    by (simp only: of_nat_add producer_digits; simp add: algebra_simps)
  have producer_residual:
    "reverse_q19_source_forcing_coefficient source i =
      int (punctured_no_growth_coefficient source i) - 2 * int (source ! i)"
    using quiet index
    by (simp add: reverse_q19_source_forcing_coefficient_def
        reverse_q19_homogeneous_coefficient_def reverse_q19_source_coefficient_def)
  show ?thesis
    using producer_residual carry_formula quiet index j_succ
    by (simp add: reverse_q19_carry_forcing_coefficient_def)
qed

lemma reverse_q19_source_forcing_growth_interior_carry_formula:
  assumes valid: "valid_pair source"
      and growth: "carry_out False source"
      and positive: "0 < i"
      and index: "i < length source"
  shows "reverse_q19_source_forcing_coefficient source i =
    int (carry_bit (punctured_prefix_carry source i)) +
    int (carry_bit (punctured_prefix_carry source (length source-i))) -
    10 * (int (carry_bit (punctured_prefix_carry source (Suc i))) +
      int (carry_bit (punctured_prefix_carry source (Suc (length source-i)))) )"
proof -
  let ?j = "length source-i"
  have symmetric: "rev source = source"
    using valid by (simp add: valid_pair_def)
  have previous_index: "i-1 < length source" using index by arith
  have j_index: "?j < length source" using positive index by arith
  have j_succ: "Suc ?j = Suc (length source-i)" by simp
  have reflected: "source ! ?j = source ! (i-1)"
    using palindrome_nth_reflect[OF symmetric previous_index] positive by simp
  have source_i_member: "source ! i \<in> set source"
    by (rule nth_mem[OF index])
  have source_i_le: "source ! i \<le> 18"
    using valid source_i_member by (auto simp: valid_pair_def)
  have source_i: "source ! i < 19" using source_i_le by arith
  have source_j_member: "source ! ?j \<in> set source"
    by (rule nth_mem[OF j_index])
  have source_j_le: "source ! ?j \<le> 18"
    using valid source_j_member by (auto simp: valid_pair_def)
  have source_j: "source ! ?j < 19" using source_j_le by arith
  have producer:
    "punctured_growth_interior_coefficient source i = step source ! i"
    by (rule punctured_growth_interior_coefficient_refines_step
        [OF valid growth positive index])
  have step_cell:
    "step source ! i = digits source ! i + digits source ! ?j"
    using growth positive index j_index
    by (simp add: step_def length_digits_exact rev_nth nth_append)
  have producer_digits:
    "punctured_growth_interior_coefficient source i =
      digits source ! i + digits source ! ?j"
    using producer step_cell by simp
  have digit_i:
    "int (digits source ! i) = int (source ! i) +
      int (carry_bit (punctured_prefix_carry source i)) -
      10 * int (carry_bit (punctured_prefix_carry source (Suc i)))"
    by (rule reverse_q19_digit_int_carry_balance[OF index source_i])
  have digit_j:
    "int (digits source ! ?j) = int (source ! ?j) +
      int (carry_bit (punctured_prefix_carry source ?j)) -
      10 * int (carry_bit (punctured_prefix_carry source (Suc ?j)))"
    by (rule reverse_q19_digit_int_carry_balance[OF j_index source_j])
  have carry_formula:
    "int (punctured_growth_interior_coefficient source i) -
        (int (source ! i) + int (source ! (i-1))) =
      int (carry_bit (punctured_prefix_carry source i)) +
      int (carry_bit (punctured_prefix_carry source ?j)) -
      10 * (int (carry_bit (punctured_prefix_carry source (Suc i))) +
        int (carry_bit (punctured_prefix_carry source (Suc ?j))))"
    using producer_digits digit_i digit_j reflected
    by (simp only: of_nat_add producer_digits; simp add: algebra_simps)
  have producer_residual:
    "reverse_q19_source_forcing_coefficient source i =
      int (punctured_growth_interior_coefficient source i) -
        (int (source ! i) + int (source ! (i-1)))"
    using growth positive index
    by (simp add: reverse_q19_source_forcing_coefficient_def
        reverse_q19_homogeneous_coefficient_def reverse_q19_source_coefficient_def)
  show ?thesis
    using producer_residual carry_formula growth positive index
    by (simp add: reverse_q19_carry_forcing_coefficient_def)
qed

lemma reverse_q19_source_forcing_growth_edge_carry_formula:
  assumes valid: "valid_pair source"
      and growth: "carry_out False source"
      and edge: "i=0 \<or> i=length source"
  shows "reverse_q19_source_forcing_coefficient source i =
    1 - 10 * int (carry_bit (punctured_prefix_carry source 1))"
proof -
  have nonempty: "source \<noteq> []" using valid by (simp add: valid_pair_def)
  have symmetric: "rev source=source"
    using valid by (simp add: valid_pair_def)
  have homogeneous_edge:
    "reverse_q19_homogeneous_coefficient True
      (reverse_q19_source_coefficient source) i = int (source!0)"
  proof (cases "i=0")
    case first: True
    then show ?thesis using nonempty
      by (simp add: reverse_q19_homogeneous_coefficient_def
          reverse_q19_source_coefficient_def)
  next
    case not_first: False
    then have last: "i=length source" using edge by simp
    have reflected: "source!(length source-1)=source!0"
      using palindrome_nth_reflect[OF symmetric, of 0] nonempty by simp
    show ?thesis using last nonempty reflected
      by (simp add: reverse_q19_homogeneous_coefficient_def
          reverse_q19_source_coefficient_def)
  qed
  have edge_digit:
    "punctured_growth_edge_coefficient source = digits source!0 + 1"
  proof -
    have producer:
      "punctured_growth_edge_coefficient source = step source!0"
      by (rule punctured_growth_edge_coefficient_refines_first[OF valid growth])
    have terminal: "digits source ! length source = 1"
      by (rule digits_growth_last[OF growth])
    have step_cell:
      "step source!0 = digits source!0 + digits source!length source"
      using nonempty growth
      by (simp add: step_def length_digits_exact rev_nth)
    show ?thesis using producer terminal step_cell by simp
  qed
  have first_index: "0 < length source" using nonempty by simp
  have first_member: "source ! 0 \<in> set source"
    by (rule nth_mem[OF first_index])
  have first_symbol_le: "source ! 0 \<le> 18"
    using valid first_member by (auto simp: valid_pair_def)
  have first_symbol: "source!0 < 19" using first_symbol_le by arith
  have first_digit:
    "int (digits source!0) = int (source!0) -
      10 * int (carry_bit (punctured_prefix_carry source 1))"
  proof -
    have balance:
      "int (digits source!0) = int (source!0) +
        int (carry_bit (punctured_prefix_carry source 0)) -
        10 * int (carry_bit (punctured_prefix_carry source 1))"
      using reverse_q19_digit_int_carry_balance[OF first_index first_symbol]
      by simp
    have carry0: "punctured_prefix_carry source 0 = False"
      by (simp add: punctured_prefix_carry_def carry_out_def)
    show ?thesis using balance carry0 by (simp add: carry_bit_def)
  qed
  have producer_residual:
    "reverse_q19_source_forcing_coefficient source i =
      int (punctured_growth_edge_coefficient source) - int (source!0)"
    using growth edge homogeneous_edge
    by (simp add: reverse_q19_source_forcing_coefficient_def)
  show ?thesis
    using producer_residual edge_digit first_digit
    by (simp add: algebra_simps)
qed

lemma reverse_q19_source_forcing_carry_formula:
  assumes valid: "valid_pair source"
  shows "reverse_q19_source_forcing_coefficient source i =
    reverse_q19_carry_forcing_coefficient source i"
proof (cases "carry_out False source")
  case growth: True
  show ?thesis
  proof (cases "i=0 \<or> i=length source")
    case edge: True
    have formula:
      "reverse_q19_source_forcing_coefficient source i =
        1 - 10 * int (carry_bit (punctured_prefix_carry source 1))"
      by (rule reverse_q19_source_forcing_growth_edge_carry_formula
          [OF valid growth edge])
    show ?thesis using formula growth edge
      by (simp add: reverse_q19_carry_forcing_coefficient_def)
  next
    case not_edge: False
    show ?thesis
    proof (cases "i<length source")
      case interior: True
      have positive: "0<i" using not_edge by simp
      have formula:
        "reverse_q19_source_forcing_coefficient source i =
          int (carry_bit (punctured_prefix_carry source i)) +
          int (carry_bit (punctured_prefix_carry source (length source-i))) -
          10 * (int (carry_bit (punctured_prefix_carry source (Suc i))) +
            int (carry_bit (punctured_prefix_carry source (Suc (length source-i)))))"
        by (rule reverse_q19_source_forcing_growth_interior_carry_formula
            [OF valid growth positive interior])
      show ?thesis using formula growth not_edge interior
        by (simp add: reverse_q19_carry_forcing_coefficient_def)
    next
      case outside: False
      then have beyond: "length source < i" using not_edge by arith
      show ?thesis using growth not_edge outside beyond
        by (simp add: reverse_q19_source_forcing_coefficient_def
            reverse_q19_carry_forcing_coefficient_def)
    qed
  qed
next
  case quiet: False
  show ?thesis
  proof (cases "i<length source")
    case inside: True
    have formula:
      "reverse_q19_source_forcing_coefficient source i =
        int (carry_bit (punctured_prefix_carry source i)) +
        int (carry_bit (punctured_prefix_carry source (length source-Suc i))) -
        10 * (int (carry_bit (punctured_prefix_carry source (Suc i))) +
          int (carry_bit (punctured_prefix_carry source (length source-i))))"
      by (rule reverse_q19_source_forcing_quiet_carry_formula
          [OF valid quiet inside])
    show ?thesis using formula quiet inside
      by (simp add: reverse_q19_carry_forcing_coefficient_def)
  next
    case outside: False
    show ?thesis using quiet outside
      by (simp add: reverse_q19_source_forcing_coefficient_def
          reverse_q19_carry_forcing_coefficient_def)
  qed
qed

lemma reverse_q19_source_coefficient_one_step:
  assumes valid: "valid_pair source"
  shows "reverse_q19_source_coefficient (step source) i =
    reverse_q19_homogeneous_coefficient (carry_out False source)
      (reverse_q19_source_coefficient source) i +
    reverse_q19_source_forcing_coefficient source i"
proof -
  have nonempty: "source \<noteq> []"
    using valid by (simp add: valid_pair_def)
  have length_step:
    "length (step source) =
      length source + (if carry_out False source then 1 else 0)"
    by (rule step_length_exact)
  show ?thesis
  proof (cases "carry_out False source")
    case growth: True
    have length_step_growth: "length (step source) = Suc (length source)"
      using length_step growth by simp
    show ?thesis
    proof (cases "i=0")
      case at_first: True
      have producer:
        "punctured_growth_edge_coefficient source = step source ! 0"
        by (rule punctured_growth_edge_coefficient_refines_first
            [OF valid growth])
      show ?thesis
        using producer growth at_first length_step_growth
        by (simp add: reverse_q19_source_coefficient_def
            reverse_q19_homogeneous_coefficient_def
            reverse_q19_source_forcing_coefficient_def algebra_simps)
    next
      case not_first: False
      show ?thesis
      proof (cases "i=length source")
        case at_last: True
        have producer:
          "punctured_growth_edge_coefficient source =
            step source ! length source"
          by (rule punctured_growth_edge_coefficient_refines_last
              [OF valid growth])
        show ?thesis
          using producer growth at_last not_first nonempty length_step_growth
          by (simp add: reverse_q19_source_coefficient_def
              reverse_q19_homogeneous_coefficient_def
              reverse_q19_source_forcing_coefficient_def algebra_simps)
      next
        case not_last: False
        show ?thesis
        proof (cases "i < length source")
          case interior: True
          have producer:
            "punctured_growth_interior_coefficient source i = step source ! i"
            by (rule punctured_growth_interior_coefficient_refines_step
                [OF valid growth]) (use not_first interior in simp_all)
          show ?thesis
            using producer growth not_first not_last interior length_step_growth
            by (simp add: reverse_q19_source_coefficient_def
                reverse_q19_homogeneous_coefficient_def
                reverse_q19_source_forcing_coefficient_def algebra_simps)
        next
          case outside: False
          then have beyond: "length source < i" using not_last by arith
          have source_zero: "reverse_q19_source_coefficient source i = 0"
            using outside by (simp add: reverse_q19_source_coefficient_def)
          have predecessor_zero:
            "reverse_q19_source_coefficient source (i-1) = 0"
            using beyond by (simp add: reverse_q19_source_coefficient_def)
          show ?thesis
            using growth outside beyond source_zero predecessor_zero length_step_growth
            by (simp add: reverse_q19_source_coefficient_def
                reverse_q19_homogeneous_coefficient_def
                reverse_q19_source_forcing_coefficient_def)
        qed
      qed
    qed
  next
    case quiet: False
    have length_step_quiet: "length (step source) = length source"
      using length_step quiet by simp
    show ?thesis
    proof (cases "i < length source")
      case inside: True
      have producer:
        "punctured_no_growth_coefficient source i = step source ! i"
        by (rule punctured_no_growth_coefficient_refines_step
            [OF valid quiet inside])
      show ?thesis
        using producer quiet inside length_step_quiet
        by (simp add: reverse_q19_source_coefficient_def
            reverse_q19_homogeneous_coefficient_def
            reverse_q19_source_forcing_coefficient_def algebra_simps)
    next
      case outside: False
      have source_zero: "reverse_q19_source_coefficient source i = 0"
        using outside by (simp add: reverse_q19_source_coefficient_def)
      show ?thesis
        using quiet outside source_zero length_step_quiet
        by (simp add: reverse_q19_source_coefficient_def
            reverse_q19_homogeneous_coefficient_def
            reverse_q19_source_forcing_coefficient_def)
    qed
  qed
qed

lemma reverse_q19_source_coefficient_carry_one_step:
  assumes valid: "valid_pair source"
  shows "reverse_q19_source_coefficient (step source) i =
    reverse_q19_homogeneous_coefficient (carry_out False source)
      (reverse_q19_source_coefficient source) i +
    reverse_q19_carry_forcing_coefficient source i"
proof -
  have producer:
    "reverse_q19_source_coefficient (step source) i =
      reverse_q19_homogeneous_coefficient (carry_out False source)
        (reverse_q19_source_coefficient source) i +
      reverse_q19_source_forcing_coefficient source i"
    by (rule reverse_q19_source_coefficient_one_step[OF valid])
  have forcing:
    "reverse_q19_source_forcing_coefficient source i =
      reverse_q19_carry_forcing_coefficient source i"
    by (rule reverse_q19_source_forcing_carry_formula[OF valid])
  show ?thesis using producer forcing by simp
qed

fun reverse_q19_source_horner ::
    "nat \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int" where
  "reverse_q19_source_horner 0 source initial i = initial i"
| "reverse_q19_source_horner (Suc n) source initial i =
    reverse_q19_source_horner n (step source)
      (\<lambda>j. reverse_q19_homogeneous_coefficient
          (carry_out False source) initial j +
        reverse_q19_carry_forcing_coefficient source j) i"

fun reverse_q19_homogeneous_horner ::
    "nat \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int" where
  "reverse_q19_homogeneous_horner 0 source initial i = initial i"
| "reverse_q19_homogeneous_horner (Suc n) source initial i =
    reverse_q19_homogeneous_horner n (step source)
      (\<lambda>j. reverse_q19_homogeneous_coefficient
          (carry_out False source) initial j) i"

lemma reverse_q19_source_horner_exact:
  assumes valid: "valid_pair source"
  shows "reverse_q19_source_horner n source
      (reverse_q19_source_coefficient source) i =
    reverse_q19_source_coefficient (run step n source) i"
  using valid
proof (induction n arbitrary: source)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have next_valid: "valid_pair (step source)"
    by (rule valid_pair_successor[OF Suc.prems])
  have ih:
    "reverse_q19_source_horner n (step source)
        (reverse_q19_source_coefficient (step source)) i =
      reverse_q19_source_coefficient (run step n (step source)) i"
    by (rule Suc.IH[OF next_valid])
  have one_step:
    "reverse_q19_source_coefficient (step source) =
      (\<lambda>j. reverse_q19_homogeneous_coefficient
          (carry_out False source)
          (reverse_q19_source_coefficient source) j +
        reverse_q19_carry_forcing_coefficient source j)"
    by (rule ext, rule reverse_q19_source_coefficient_carry_one_step[OF Suc.prems])
  show ?case using ih one_step by simp
qed

lemma reverse_q19_homogeneous_coefficient_linear:
  "reverse_q19_homogeneous_coefficient growth
      (\<lambda>j. left j - right j) i =
    reverse_q19_homogeneous_coefficient growth left i -
      reverse_q19_homogeneous_coefficient growth right i"
  by (cases growth; cases i)
    (simp_all add: reverse_q19_homogeneous_coefficient_def algebra_simps)

lemma reverse_q19_source_horner_difference:
  "reverse_q19_source_horner n source left i -
      reverse_q19_source_horner n source right i =
    reverse_q19_homogeneous_horner n source
      (\<lambda>j. left j - right j) i"
proof (induction n arbitrary: source left right i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?growth = "carry_out False source"
  let ?forcing = "reverse_q19_carry_forcing_coefficient source"
  let ?left = "\<lambda>j. reverse_q19_homogeneous_coefficient ?growth left j + ?forcing j"
  let ?right = "\<lambda>j. reverse_q19_homogeneous_coefficient ?growth right j + ?forcing j"
  have step_difference:
    "(\<lambda>j. ?left j - ?right j) =
      (\<lambda>j. reverse_q19_homogeneous_coefficient ?growth
          (\<lambda>k. left k-right k) j)"
    by (rule ext) (simp add: reverse_q19_homogeneous_coefficient_linear
        algebra_simps)
  have ih:
    "reverse_q19_source_horner n (step source) ?left i -
        reverse_q19_source_horner n (step source) ?right i =
      reverse_q19_homogeneous_horner n (step source)
        (\<lambda>j. ?left j - ?right j) i"
    by (rule Suc.IH)
  show ?case using ih step_difference by simp
qed

lemma reverse_q19_homogeneous_horner_scale:
  "reverse_q19_homogeneous_horner n source (\<lambda>j. c * initial j) i =
    c * reverse_q19_homogeneous_horner n source initial i"
proof (induction n arbitrary: source initial i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have scale_step:
    "(\<lambda>j. reverse_q19_homogeneous_coefficient
        (carry_out False source) (\<lambda>k. c*initial k) j) =
      (\<lambda>j. c * reverse_q19_homogeneous_coefficient
        (carry_out False source) initial j)"
    by (rule ext) (simp add: reverse_q19_homogeneous_coefficient_def
        algebra_simps)
  show ?case using Suc.IH[of "step source"
      "\<lambda>j. reverse_q19_homogeneous_coefficient
        (carry_out False source) initial j" i]
    by (simp only: reverse_q19_homogeneous_horner.simps(2) scale_step)
qed

lemma reverse_q19_homogeneous_horner_quiet_divisibility:
  "(2::int)^source_no_growth_count n source dvd
    reverse_q19_homogeneous_horner n source initial i"
proof (induction n arbitrary: source initial i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "carry_out False source")
    case growth: True
    have count:
      "source_no_growth_count (Suc n) source =
        source_no_growth_count n (step source)"
      using growth by simp
    show ?thesis
      using Suc.IH[of "step source"
        "\<lambda>j. reverse_q19_homogeneous_coefficient True initial j" i]
        growth
      by (simp only: reverse_q19_homogeneous_horner.simps(2) count)
  next
    case quiet: False
    let ?q = "source_no_growth_count n (step source)"
    have count: "source_no_growth_count (Suc n) source = Suc ?q"
      using quiet by simp
    have ih:
      "(2::int)^?q dvd
        reverse_q19_homogeneous_horner n (step source) initial i"
      by (rule Suc.IH)
    then obtain k where divisible:
      "reverse_q19_homogeneous_horner n (step source) initial i =
        (2::int)^?q * k"
      by (auto simp: dvd_def)
    have scaled:
      "reverse_q19_homogeneous_horner n (step source)
          (\<lambda>j. 2*initial j) i =
        2 * reverse_q19_homogeneous_horner n (step source) initial i"
      by (rule reverse_q19_homogeneous_horner_scale)
    have scaled_value:
      "reverse_q19_homogeneous_horner n (step source)
          (\<lambda>j. 2*initial j) i = (2::int)^Suc ?q * k"
      using divisible scaled by (simp add: power_Suc algebra_simps)
    have quiet_operator:
      "reverse_q19_homogeneous_coefficient (carry_out False source) initial =
        (\<lambda>j. 2*initial j)"
    proof -
      have carry: "carry_out False source = False" using quiet by simp
      show ?thesis
      proof (rule ext)
        fix j
        show "reverse_q19_homogeneous_coefficient
            (carry_out False source) initial j = 2*initial j"
          using carry by (simp add: reverse_q19_homogeneous_coefficient_def)
      qed
    qed
    have one_step:
      "reverse_q19_homogeneous_horner (Suc n) source initial i =
        reverse_q19_homogeneous_horner n (step source)
          (\<lambda>j. 2*initial j) i"
      using quiet_operator
      by (simp only: reverse_q19_homogeneous_horner.simps(2) quiet_operator)
    show ?thesis
      unfolding count
      using one_step scaled_value by (simp add: dvd_def)
  qed
qed

lemma reverse_q19_homogeneous_horner_mod32_erasure:
  assumes quiet: "5 \<le> source_no_growth_count n source"
  shows "reverse_q19_homogeneous_horner n source initial i mod 32 = 0"
proof -
  let ?q = "source_no_growth_count n source"
  have divisible:
    "(2::int)^?q dvd reverse_q19_homogeneous_horner n source initial i"
    by (rule reverse_q19_homogeneous_horner_quiet_divisibility)
  then obtain k where factor:
    "reverse_q19_homogeneous_horner n source initial i = (2::int)^?q*k"
    by (auto simp: dvd_def)
  have q_split: "?q = 5 + (?q-5)" using quiet by arith
  have exponent:
    "(2::int)^?q = 32 * (2::int)^(?q-5)"
  proof -
    have exponent_eq: "(2::int)^?q = (2::int)^(5+(?q-5))"
      by (rule arg_cong[where f="\<lambda>m. (2::int)^m", OF q_split])
    also have "... = (2::int)^5 * (2::int)^(?q-5)"
      by (rule power_add)
    also have "... = 32 * (2::int)^(?q-5)" by simp
    finally show ?thesis .
  qed
  show ?thesis using factor exponent by simp
qed

definition reverse_q19_source_forcing_image ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> int" where
  "reverse_q19_source_forcing_image n source i =
    reverse_q19_source_horner n source (\<lambda>_. 0) i mod 32"

theorem reverse_q19_source_suffix_forcing_congruence:
  assumes valid: "valid_pair source"
      and quiet: "5 \<le> source_no_growth_count n source"
  shows "reverse_q19_source_coefficient (run step n source) i mod 32 =
    reverse_q19_source_forcing_image n source i"
proof -
  let ?initial = "reverse_q19_source_coefficient source"
  have actual:
    "reverse_q19_source_horner n source ?initial i =
      reverse_q19_source_coefficient (run step n source) i"
    by (rule reverse_q19_source_horner_exact[OF valid])
  have difference_raw:
    "reverse_q19_source_horner n source ?initial i -
      reverse_q19_source_horner n source (\<lambda>_. 0) i =
      reverse_q19_homogeneous_horner n source
        (\<lambda>j. ?initial j - 0) i"
    by (rule reverse_q19_source_horner_difference)
  have initial_minus_zero: "(\<lambda>j. ?initial j - 0) = ?initial"
    by (rule ext) simp
  have difference:
    "reverse_q19_source_horner n source ?initial i -
      reverse_q19_source_horner n source (\<lambda>_. 0) i =
      reverse_q19_homogeneous_horner n source ?initial i"
    using difference_raw initial_minus_zero by simp
  have erased:
    "reverse_q19_homogeneous_horner n source ?initial i mod 32 = 0"
    by (rule reverse_q19_homogeneous_horner_mod32_erasure[OF quiet])
  have force_zero:
    "(reverse_q19_source_horner n source (\<lambda>_. 0) i) mod 32 =
      reverse_q19_source_forcing_image n source i"
    by (simp add: reverse_q19_source_forcing_image_def)
  have actual_sum:
    "reverse_q19_source_coefficient (run step n source) i =
      reverse_q19_homogeneous_horner n source ?initial i +
        reverse_q19_source_horner n source (\<lambda>_. 0) i"
    using actual difference by linarith
  have modulo:
    "(reverse_q19_homogeneous_horner n source ?initial i +
        reverse_q19_source_horner n source (\<lambda>_. 0) i) mod 32 =
      (reverse_q19_source_horner n source (\<lambda>_. 0) i) mod 32"
  proof -
    have add_left:
      "(reverse_q19_homogeneous_horner n source ?initial i mod 32 +
          reverse_q19_source_horner n source (\<lambda>_. 0) i) mod 32 =
        (reverse_q19_homogeneous_horner n source ?initial i +
          reverse_q19_source_horner n source (\<lambda>_. 0) i) mod 32"
      by (rule mod_add_left_eq
          [of "reverse_q19_homogeneous_horner n source ?initial i" 32
            "reverse_q19_source_horner n source (\<lambda>_. 0) i"])
    show ?thesis using add_left erased by simp
  qed
  show ?thesis using actual_sum modulo force_zero by simp
qed

theorem reverse_q19_source_suffix_forcing_exact:
  assumes valid: "valid_pair source"
      and quiet: "5 \<le> source_no_growth_count n source"
      and index: "i < length (run step n source)"
  shows "int (run step n source ! i) =
    reverse_q19_source_forcing_image n source i"
proof -
  let ?final = "run step n source"
  let ?value = "int (?final ! i)"
  let ?image = "reverse_q19_source_forcing_image n source i"
  have final_valid: "valid_pair ?final"
    by (rule valid_pair_run[OF valid])
  have final_member: "?final ! i \<in> set ?final"
    by (rule nth_mem[OF index])
  have final_le: "?final ! i \<le> 18"
    using final_valid final_member by (auto simp: valid_pair_def)
  have final_bounded: "?final ! i < 19" using final_le by arith
  have value_nonnegative: "0 \<le> ?value" by simp
  have value_bounded: "?value < 32" using final_bounded by simp
  have value_mod: "?value mod 32 = ?value"
    using value_nonnegative value_bounded by simp
  have congruence: "?value mod 32 = ?image"
    using reverse_q19_source_suffix_forcing_congruence
      [OF valid quiet, where i=i] index
    by (simp add: reverse_q19_source_coefficient_def)
  show ?thesis using congruence value_mod by simp
qed

text \<open>The congruence is coefficientwise for every index and derives from the
exact one-step T2 producer recurrence followed by chronological Horner
transport.  The endpoint coefficient word itself is source-generated by
@{const run}; a naked list of carry rows is not admitted by this theorem.\<close>

ML \<open>
  val checked = @{thms reverse_q19_source_forcing_quiet_carry_formula
    reverse_q19_source_forcing_growth_interior_carry_formula
    reverse_q19_source_forcing_growth_edge_carry_formula
    reverse_q19_source_forcing_carry_formula
    reverse_q19_source_coefficient_one_step
    reverse_q19_source_coefficient_carry_one_step
    reverse_q19_source_horner_exact reverse_q19_source_horner_difference
    reverse_q19_homogeneous_horner_quiet_divisibility
    reverse_q19_homogeneous_horner_mod32_erasure
    reverse_q19_source_suffix_forcing_congruence
    reverse_q19_source_suffix_forcing_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse carry-suffix refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reverse carry-suffix refinement proof" else ();
\<close>

end
