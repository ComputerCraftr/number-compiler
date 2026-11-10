theory Reverse_Growth_Run_Admission
  imports "Reverse_Residuals.Reverse_Invariant"
    "Reverse_Residuals.Reverse_196_Residue_Quotient"
    "Shared_Carry_Dynamics.Decimal_Normalization_Morphism"
begin

text \<open>The growth-run bound is derived from the actual symmetric source
pair field and physical LSD-to-MSD carry. It is not an assumed grammar bound.
This removes a premise used in live radial reduction; it does not construct
future pair fields, carry domains, or a powered output morphism.\<close>

definition edge_growth_rank :: "nat \<Rightarrow> nat" where
  "edge_growth_rank e = (if e=18 then 3 else if e=9 then 2
    else if 10 \<le> e then 1 else 0)"

lemma edge_growth_rank_bound: "edge_growth_rank e \<le> 3"
  by (simp add: edge_growth_rank_def)

lemma edge_growth_rank_decreases:
  assumes "9 \<le> e" "e \<le> 18"
  shows "edge_growth_rank (1+e mod 10)+1 = edge_growth_rank e"
proof -
  have "e=9 \<or> e=10 \<or> e=11 \<or> e=12 \<or> e=13 \<or> e=14 \<or>
    e=15 \<or> e=16 \<or> e=17 \<or> e=18" using assms by arith
  then show ?thesis by (auto simp: edge_growth_rank_def)
qed

lemma source_growth_requires_edge:
  assumes valid: "valid_pair ss" and growth: "carry_out False ss"
  shows "9 \<le> hd ss" "hd ss \<le> 18"
proof -
  have nonempty: "ss \<noteq> []" and symmetric: "rev ss=ss"
    and bounded: "\<forall>s\<in>set ss. s \<le> 18"
    using valid unfolding valid_pair_def by auto
  have mirror: "hd ss = last ss" using nonempty symmetric by (metis hd_rev)
  obtain xs a where snoc: "ss=xs@[a]" using nonempty by (cases ss rule: rev_cases) auto
  have "carry_apply (domain a) (carry_out False xs)"
    using growth by (simp add: snoc carry_out_def fold_append)
  then have "9 \<le> a" by (auto simp: domain_def split: if_splits)
  then show "9 \<le> hd ss" using mirror by (simp add: snoc)
  show "hd ss \<le> 18" using bounded hd_in_set[OF nonempty] by blast
qed

lemma source_nongrowth_outer_coefficient_bounds:
  assumes valid: "valid_pair ss"
      and no_growth: "\<not> carry_out False ss"
  shows "hd (step ss) \<ge> 2 * hd ss"
    and "hd (step ss) \<le> 2 * hd ss + 1"
proof -
  have nonempty: "ss \<noteq> []" and symmetric: "rev ss = ss"
    using valid unfolding valid_pair_def by auto
  obtain xs a where split: "ss = xs @ [a]"
    using nonempty by (cases ss rule: rev_cases) auto
  have outer: "a = hd ss"
  proof -
    have "last ss = hd ss" using nonempty symmetric by (metis hd_rev)
    then show ?thesis using split by simp
  qed
  have a_bound: "a < 10"
  proof (rule ccontr)
    assume "\<not> a < 10"
    then have "10 \<le> a" by arith
    then have "carry_out False ss"
      using split by (simp add: carry_out_append carry_out_def domain_def)
    then show False using no_growth by contradiction
  qed
  have length_digits: "length (digits ss) = length ss"
    using no_growth by (simp add: length_digits_exact)
  have index_bound: "length xs < length ss" using split by simp
  have source_last: "ss ! length xs = a" using split by simp
  have first_digit:
    "digits ss ! 0 = a"
  proof -
    have formula: "digits ss ! 0 =
        (ss ! 0 + (if carry_out False (take 0 ss) then 1 else 0)) mod 10"
      using digits_nth_no_growth[of 0 ss] nonempty no_growth
      by (simp add: carry_bit_def)
    have empty_carry: "carry_out False [] = False"
      unfolding carry_out_def by simp
    have prefix_empty: "carry_out False (take 0 ss) = False"
      using empty_carry by simp
    have first_cell: "ss ! 0 = hd ss"
      using hd_conv_nth[OF nonempty] by simp
    show ?thesis using formula outer a_bound prefix_empty first_cell by simp
  qed
  have last_digit_formula:
    "digits ss ! length xs =
      (a + (if carry_out False xs then 1 else 0)) mod 10"
  proof -
    have formula: "digits ss ! length xs =
        (ss ! length xs +
          (if carry_out False (take (length xs) ss) then 1 else 0)) mod 10"
      using digits_nth_no_growth[OF index_bound no_growth]
      by (simp add: carry_bit_def)
    show ?thesis using formula source_last split by simp
  qed
  have edge_carry:
    "carry_out False ss = carry_apply (domain a) (carry_out False xs)"
  proof -
    have "carry_out False (xs@[a]) = carry_out (carry_out False xs) [a]"
      by (rule carry_out_append)
    also have "... = carry_apply (domain a) (carry_out False xs)"
      by (simp add: carry_out_def)
    finally show ?thesis using split by simp
  qed
  have last_digit_bound: "a \<le> digits ss ! length xs"
  proof (cases "a = 9")
    case True
    have prefix_quiet: "\<not> carry_out False xs"
      using no_growth edge_carry True by (simp add: domain_def)
    show ?thesis using last_digit_formula True prefix_quiet by simp
  next
    case False
    have a_lt_nine: "a < 9" using a_bound False by arith
    show ?thesis
    proof (cases "carry_out False xs")
      case True
      have plus_lt_ten: "a + 1 < 10" using a_lt_nine by arith
      have reduce: "(a + 1) mod 10 = a + 1"
        by (rule mod_less[OF plus_lt_ten])
      show ?thesis using last_digit_formula True reduce by simp
    next
      case False
      have a_lt_ten: "a < 10" using a_lt_nine by arith
      have reduce: "a mod 10 = a" by (rule mod_less[OF a_lt_ten])
      show ?thesis using last_digit_formula False reduce by simp
    qed
  qed
  have digits_nonempty: "digits ss \<noteq> []"
    using nonempty length_digits by auto
  have step_head:
    "hd (step ss) = digits ss ! 0 + digits ss ! length xs"
  proof -
    have rev_nonempty: "rev (digits ss) \<noteq> []"
      using digits_nonempty by simp
    have zipped_nonempty:
      "zip (digits ss) (rev (digits ss)) \<noteq> []"
      using digits_nonempty by simp
    have zip_head:
      "hd (zip (digits ss) (rev (digits ss))) =
        (hd (digits ss), hd (rev (digits ss)))"
      by (rule hd_zip[OF digits_nonempty rev_nonempty])
    have map_head:
      "hd (map (\<lambda>(a,b). a+b)
        (zip (digits ss) (rev (digits ss)))) =
        hd (digits ss) + hd (rev (digits ss))"
      using zipped_nonempty zip_head by (simp add: hd_map)
    have hd_nth: "hd (digits ss) = digits ss ! 0"
      by (rule hd_conv_nth[OF digits_nonempty])
    have last_nth:
      "last (digits ss) = digits ss ! (length (digits ss) - 1)"
      by (rule last_conv_nth[OF digits_nonempty])
    have last_index: "length (digits ss) - 1 = length xs"
      using split length_digits by simp
    have "hd (step ss) = hd (digits ss) + last (digits ss)"
      using map_head by (simp add: step_def hd_rev)
    also have "... = digits ss ! 0 + digits ss ! length xs"
      using hd_nth last_nth last_index by simp
    finally show ?thesis .
  qed
  show "hd (step ss) \<ge> 2 * hd ss"
    using step_head first_digit last_digit_bound outer by arith
  have last_upper: "digits ss ! length xs \<le> a + 1"
    using last_digit_formula mod_less_eq_dividend[of a 10]
      mod_less_eq_dividend[of "a+1" 10]
    by (cases "carry_out False xs") auto
  show "hd (step ss) \<le> 2 * hd ss + 1"
    using step_head first_digit last_upper outer by arith
qed

lemmas source_nongrowth_outer_coefficient_doubles =
  source_nongrowth_outer_coefficient_bounds(1)

lemma source_growth_edge_successor:
  assumes "ss \<noteq> []" "carry_out False ss"
  shows "hd (step ss) = 1 + hd ss mod 10"
  using assms by (cases ss) (simp_all add: step_def digits_def)

lemma source_growth_rank_decreases:
  assumes "valid_pair ss" "carry_out False ss"
  shows "edge_growth_rank (hd (step ss))+1 = edge_growth_rank (hd ss)"
proof -
  have nonempty: "ss \<noteq> []" using assms(1) by (simp add: valid_pair_def)
  have eq: "hd (step ss) = 1 + hd ss mod 10"
    by (rule source_growth_edge_successor[OF nonempty assms(2)])
  have drop: "edge_growth_rank (1+hd ss mod 10)+1 = edge_growth_rank (hd ss)"
    by (rule edge_growth_rank_decreases[OF source_growth_requires_edge(1)[OF assms]
      source_growth_requires_edge(2)[OF assms]])
  show ?thesis by (simp only: eq drop)
qed

fun source_growth_count :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "source_growth_count 0 ss = 0"
| "source_growth_count (Suc n) ss =
    (if carry_out False ss then 1 else 0) + source_growth_count n (step ss)"

fun source_no_growth_count :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "source_no_growth_count 0 ss = 0"
| "source_no_growth_count (Suc n) ss =
    (if carry_out False ss then 0 else 1) + source_no_growth_count n (step ss)"

text \<open>The following word records the actual branch bit at each physical
source successor.  It is only a proof index for the homogeneous factor; the
carry rows and their forcing events are not encoded or authenticated by this
word.\<close>

fun source_chronological_growth_word :: "nat \<Rightarrow> nat list \<Rightarrow> bool list" where
  "source_chronological_growth_word 0 ss = []"
| "source_chronological_growth_word (Suc n) ss =
    carry_out False ss # source_chronological_growth_word n (step ss)"

lemma source_chronological_growth_word_counts:
  "length (filter id (source_chronological_growth_word n ss)) =
      source_growth_count n ss"
  "length (filter Not (source_chronological_growth_word n ss)) =
      source_no_growth_count n ss"
  by (induction n arbitrary: ss) auto

definition source_growth_homogeneous_factor :: "int \<Rightarrow> bool list \<Rightarrow> int" where
  "source_growth_homogeneous_factor z word =
    prod_list (map (\<lambda>growth. if growth then 1+z else 2) word)"

lemma source_growth_homogeneous_factor_counts:
  "source_growth_homogeneous_factor z word =
    (2::int)^length (filter Not word) *
      (1+z)^length (filter id word)"
  by (induction word) (auto simp: source_growth_homogeneous_factor_def
      algebra_simps)

lemma source_growth_word_homogeneous_mod32_erasure:
  fixes z x :: int
  assumes quiet: "5 \<le> length (filter Not word)"
  shows "(source_growth_homogeneous_factor z word * x) mod 32 = 0"
proof -
  let ?q = "length (filter Not word)"
  let ?g = "length (filter id word)"
  have factor:
    "source_growth_homogeneous_factor z word =
      (2::int)^?q * (1+z)^?g"
    by (rule source_growth_homogeneous_factor_counts)
  have q_split: "?q = 5 + (?q - 5)" using quiet by arith
  have binary_factor: "(2::int)^?q = 32 * (2::int)^(?q - 5)"
  proof -
    have exponent: "(2::int)^?q = (2::int)^(5 + (?q - 5))"
      by (rule arg_cong[where f="\<lambda>n. (2::int)^n", OF q_split])
    also have "... = (2::int)^5 * (2::int)^(?q - 5)"
      by (rule power_add)
    also have "... = 32 * (2::int)^(?q - 5)"
      by simp
    finally show ?thesis .
  qed
  show ?thesis
    by (simp only: factor binary_factor) (simp add: algebra_simps)
qed

corollary source_chronological_homogeneous_mod32_erasure:
  fixes z x :: int
  assumes quiet: "5 \<le> source_no_growth_count n ss"
  shows "(source_growth_homogeneous_factor z
      (source_chronological_growth_word n ss) * x) mod 32 = 0"
  by (rule source_growth_word_homogeneous_mod32_erasure)
    (use source_chronological_growth_word_counts(2)[of n ss] quiet in simp)

text \<open>This is the coefficient-level decimal consequence used by a later
forcing producer.  Its factors are the homogeneous coefficient formula
@{term "2^q * residual"}; the shared normalization theorem accounts for the
additional powers of ten in a spatial Laurent evaluation.\<close>

theorem source_decimal_homogeneous_coefficient_erasure:
  fixes coefficient residual z :: "nat \<Rightarrow> 'a::comm_ring_1"
  assumes characteristic: "(32::'a)=0"
      and quiet: "5 \<le> q"
      and factors: "\<And>j. j<width \<Longrightarrow>
        coefficient j=2^q*residual j"
  shows "(\<Sum>j<width. coefficient j*10^j*z j) = 0"
proof -
  have erased:
    "(\<Sum>j<width. coefficient j*10^j*z j) =
      (\<Sum>j<width. if 5 \<le> q+j then 0
        else coefficient j*10^j*z j)"
    by (rule decimal_mod32_erase_annihilated_coefficients
        [where order="\<lambda>j. q", OF characteristic])
      (use factors in auto)
  have zero:
    "(\<Sum>j<width. if 5 \<le> q+j then 0
      else coefficient j*10^j*z j) = 0"
  proof -
    have all_zero:
      "(\<Sum>j<width. if 5 \<le> q+j then 0
        else coefficient j*10^j*z j) = (\<Sum>j<width. 0)"
    proof (rule sum.cong)
      show "{..<width} = {..<width}" by rule
      fix j
      assume index: "j \<in> {..<width}"
      have nonnegative: "0 \<le> j" using index by simp
      have threshold: "5 \<le> q+j" using quiet nonnegative by arith
      show "(if 5 \<le> q+j then 0
          else coefficient j*10^j*z j) = 0"
        by (simp only: threshold if_True)
    qed
    show ?thesis using all_zero by (simp add: sum.neutral)
  qed
  show ?thesis using erased zero by simp
qed

text \<open>The actual chronological growth word and its nongrowth count are now
source-derived, and every homogeneous Laurent coefficient with the resulting
five factors is erased.  This theory does not yet construct the signed forcing
row from a physical carry mask or prove the full vector recurrence
@{term "Q_next = A_growth Q + E"}; consequently it makes no endpoint-equals-
forcing-image claim.  That producer refinement must use the punctured T2
coefficient equations before a finite carry suffix can be promoted to an
endpoint coefficient word.\<close>

text \<open>This count is computed from the actual source carry at each temporal
successor. It is not inferred from a finite radial observer or from an extent
expression. The following recurrence is the source-side producer contract;
it does not yet identify a Python action payload with this count.\<close>

lemma step_length_exact:
  "length (step ss) = length ss + (if carry_out False ss then 1 else 0)"
  by (simp add: step_def digits_def)

theorem source_run_length_exact:
  "length (run step n ss) = length ss + source_growth_count n ss"
proof (induct n arbitrary: ss)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have ih: "length (run step n (step ss)) =
      length (step ss) + source_growth_count n (step ss)"
    by (rule Suc.hyps[of "step ss"])
  show ?case using ih step_length_exact[of ss]
    by (simp; arith)
qed

theorem source_growth_count_chronological:
  "source_growth_count (a+b) ss = source_growth_count a ss +
    source_growth_count b (run step a ss)"
proof (induct a arbitrary: ss)
  case 0
  then show ?case by simp
next
  case (Suc a)
  have ih: "source_growth_count (a+b) (step ss) =
      source_growth_count a (step ss) +
        source_growth_count b (run step a (step ss))"
    by (rule Suc.hyps[of "step ss"])
  show ?case using ih by (simp; arith)
qed

definition source_growth_phase :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "source_growth_phase n ss = source_growth_count n ss mod 10"

definition source_width_phase :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "source_width_phase n ss = length (run step n ss) mod 10"

lemma source_growth_phase_chronological:
  "source_growth_phase (a+b) ss =
    (source_growth_phase a ss + source_growth_phase b (run step a ss)) mod 10"
  using source_growth_count_chronological[of a b ss]
  by (simp add: source_growth_phase_def mod_add_eq)

lemma source_width_phase_exact:
  "source_width_phase n ss =
    (length ss + source_growth_count n ss) mod 10"
  by (simp add: source_width_phase_def source_run_length_exact)

lemma source_width_phase_chronological:
  "source_width_phase (a+b) ss =
    (source_width_phase a ss + source_growth_phase b (run step a ss)) mod 10"
  using source_run_length_exact[of "a+b" ss]
    source_run_length_exact[of a ss]
    source_growth_count_chronological[of a b ss]
  by (simp add: source_width_phase_def source_growth_phase_def mod_add_eq
      algebra_simps)

lemma source_growth_accounting:
  "source_growth_count n ss + source_no_growth_count n ss = n"
  by (induct n arbitrary: ss) auto

lemma source_no_growth_count_le:
  "source_no_growth_count n ss \<le> n"
proof (induction n arbitrary: ss)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have ih: "source_no_growth_count n (step ss) \<le> n"
    by (rule Suc.IH)
  show ?case
  proof (cases "carry_out False ss")
    case True
    have equation:
      "source_no_growth_count (Suc n) ss = source_no_growth_count n (step ss)"
      using True by simp
    show ?thesis using equation ih by arith
  next
    case False
    have equation:
      "source_no_growth_count (Suc n) ss = 1 + source_no_growth_count n (step ss)"
      using False by simp
    show ?thesis using equation ih by arith
  qed
qed

theorem source_nongrowth_outer_bound:
  assumes valid: "valid_pair ss"
      and quiet: "source_no_growth_count n ss = n"
  shows "hd (run step n ss) \<ge> (2::nat)^n * hd ss"
  using valid quiet
proof (induction n arbitrary: ss)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have count_eq:
    "source_no_growth_count (Suc n) ss =
      (if carry_out False ss then 0 else 1) +
        source_no_growth_count n (step ss)"
    by simp
  have current_quiet: "\<not> carry_out False ss"
    using Suc.prems count_eq source_no_growth_count_le[of n "step ss"]
    by (cases "carry_out False ss") auto
  have tail_quiet: "source_no_growth_count n (step ss) = n"
    using Suc.prems count_eq current_quiet by simp
  have next_valid: "valid_pair (step ss)"
    by (rule valid_pair_successor[OF Suc.prems(1)])
  have ih:
    "hd (run step n (step ss)) \<ge> (2::nat)^n * hd (step ss)"
    by (rule Suc.IH[OF next_valid tail_quiet])
  have outer:
    "hd (step ss) \<ge> 2 * hd ss"
    by (rule source_nongrowth_outer_coefficient_doubles[OF Suc.prems(1)
        current_quiet])
  have scaled:
    "2 * ((2::nat)^n * hd ss) \<le> (2::nat)^n * hd (step ss)"
  proof -
    have "(2 * hd ss) * (2::nat)^n \<le> hd (step ss) * (2::nat)^n"
      by (rule mult_le_mono1[OF outer])
    then show ?thesis by (simp add: mult.assoc mult.commute)
  qed
  have combined:
    "2 * ((2::nat)^n * hd ss) \<le> hd (run step n (step ss))"
    by (rule order_trans[OF scaled ih])
  have power:
    "(2::nat)^(Suc n) * hd ss = 2 * ((2::nat)^n * hd ss)"
    by (simp add: power_Suc mult.assoc mult.commute)
  show ?case using combined power by simp
qed

theorem source_five_step_growth_positive:
  assumes valid: "valid_pair ss" and positive: "0 < hd ss"
  shows "source_growth_count 5 ss \<ge> 1"
proof (rule ccontr)
  assume "\<not> 1 \<le> source_growth_count 5 ss"
  then have zero_growth: "source_growth_count 5 ss = 0" by arith
  have all_quiet: "source_no_growth_count 5 ss = 5"
    using source_growth_accounting[of 5 ss] zero_growth by simp
  have outer_bound:
    "hd (run step 5 ss) \<ge> (2::nat)^5 * hd ss"
    by (rule source_nongrowth_outer_bound[OF valid all_quiet])
  have final_valid: "valid_pair (run step 5 ss)"
  proof -
    have "valid_pair (run step n source)" if "valid_pair source" for n source
      using that by (induction n arbitrary: source)
        (auto intro: valid_pair_successor)
    then show ?thesis using valid by blast
  qed
  have final_edge: "hd (run step 5 ss) \<le> 18"
    using final_valid by (auto simp: valid_pair_def)
  have two_power: "(2::nat)^5 = 32" by simp
  have positive_nat: "1 \<le> hd ss" using positive by simp
  have lower_bound: "32 \<le> (2::nat)^5 * hd ss"
  proof -
    have "32 * 1 \<le> 32 * hd ss"
      by (rule mult_left_mono[OF positive_nat]) simp
    then have "32 \<le> 32 * hd ss" by simp
    then show ?thesis using two_power by simp
  qed
  show False using outer_bound final_edge lower_bound by linarith
qed

lemma source_positive_growth_has_odd_prefix_exists:
  assumes positive: "0 < source_growth_count n ss"
  shows "\<exists>k\<le>n. odd (source_growth_count k ss)"
  using positive
proof (induction n arbitrary: ss)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "carry_out False ss")
    case True
    have first: "source_growth_count 1 ss = 1"
      using True by simp
    show ?thesis
      using first by (intro exI[of _ 1]) simp
  next
    case False
    have tail_positive: "0 < source_growth_count n (step ss)"
      using Suc.prems False by simp
    obtain k where k_bound: "k \<le> n"
        and odd_tail: "odd (source_growth_count k (step ss))"
      using Suc.IH[OF tail_positive] by blast
    have chronological:
      "source_growth_count (Suc k) ss =
        source_growth_count 1 ss + source_growth_count k (step ss)"
      using source_growth_count_chronological[of 1 k ss] by simp
    have no_first_growth: "source_growth_count 1 ss = 0"
      using False by simp
    show ?thesis
      using k_bound odd_tail chronological no_first_growth
      by (intro exI[of _ "Suc k"]) simp
  qed
qed

lemma source_positive_growth_has_odd_prefix:
  assumes positive: "0 < source_growth_count n ss"
  obtains k where "k \<le> n" and "odd (source_growth_count k ss)"
  using source_positive_growth_has_odd_prefix_exists[OF positive] by blast

theorem source_even_width_state_within_five:
  assumes valid: "valid_pair ss" and positive: "0 < hd ss"
  obtains k where "k \<le> 5" and "even (length (run step k ss))"
proof (cases "even (length ss)")
  case True
  have zero_bound: "(0::nat) \<le> (5::nat)" by simp
  have zero_width: "even (length (run step 0 ss))"
    using True by simp
  show thesis using that[of 0] zero_bound zero_width by blast
next
  case False
  have growth: "1 \<le> source_growth_count 5 ss"
    by (rule source_five_step_growth_positive[OF valid positive])
  have growth_positive: "0 < source_growth_count 5 ss"
    using growth by arith
  obtain k where k_bound: "k \<le> 5"
      and odd_growth: "odd (source_growth_count k ss)"
    using source_positive_growth_has_odd_prefix[OF growth_positive] by blast
  have width: "length (run step k ss) =
      length ss + source_growth_count k ss"
    by (rule source_run_length_exact)
  have even_width: "even (length (run step k ss))"
    using False odd_growth width by simp
  show thesis using that[of k] k_bound even_width by blast
qed

theorem source_sixth_value_mod11:
  assumes valid: "valid_pair ss" and positive: "0 < hd ss"
  shows "reverse_add_pair_term (run step 5 ss) mod 11 = 0"
proof -
  obtain k where k_bound: "k \<le> 5"
      and even_width: "even (length (run step k ss))"
    by (rule source_even_width_state_within_five[OF valid positive])
  have state_valid: "valid_pair (run step k ss)"
  proof -
    have "valid_pair (run step n source)" if "valid_pair source" for n source
      using that by (induction n arbitrary: source)
        (auto intro: valid_pair_successor)
    then show ?thesis using valid by blast
  qed
  have source_zero:
    "reverse_add_pair_term (run step k ss) mod 11 = 0"
    by (rule reverse_add_pair_term_even_source_width_mod11[OF state_valid
        even_width])
  have tail_zero:
    "reverse_add_pair_term (run step (5-k) (run step k ss)) mod 11 = 0"
    by (rule reverse_add_pair_run_mod11_preserves_zero[OF state_valid source_zero])
  have index_sum: "k + (5-k) = 5" using k_bound by arith
  have run_rewrite:
    "run step 5 ss = run step (k + (5-k)) ss"
    using index_sum by (simp only: index_sum)
  have run_composition:
    "run step (k + (5-k)) ss = run step (5-k) (run step k ss)"
    by (rule reverse_add_run_add)
  have joined:
    "run step 5 ss = run step (5-k) (run step k ss)"
    by (rule trans[OF run_rewrite run_composition])
  show ?thesis by (simp only: joined tail_zero)
qed

theorem source_pair_run_residue99:
  assumes valid: "valid_pair ss"
      and positive: "0 < hd ss"
      and enough_steps: "6 \<le> n"
  shows "reverse_add_pair_term (run step (n-1) ss) mod 99 =
    (55 * ((5 * reverse_add_pair_term ss) mod 9) * (2::nat)^n) mod 99"
proof -
  let ?x = "reverse_add_pair_term ss"
  let ?raw = "55 * ((5 * ?x) mod 9) * (2::nat)^n"
  have n_positive: "0 < n" using enough_steps by arith
  have actual_mod9:
    "reverse_add_pair_term (run step (n-1) ss) mod 9 =
      ((2::nat)^(n-1) * ?x) mod 9"
    by (rule reverse_add_run_mod9_doubling[OF valid])
  have raw_mod9:
    "?raw mod 9 = ((2::nat)^(n-1) * ?x) mod 9"
    by (rule reverse_add_formula_mod9[OF n_positive])
  have actual_mod11:
    "reverse_add_pair_term (run step (n-1) ss) mod 11 = 0"
  proof -
    have sixth_zero: "reverse_add_pair_term (run step 5 ss) mod 11 = 0"
      by (rule source_sixth_value_mod11[OF valid positive])
    have tail_valid: "valid_pair (run step 5 ss)"
      by (rule valid_pair_run[OF valid])
    have tail_zero:
      "reverse_add_pair_term (run step (n-6) (run step 5 ss)) mod 11 = 0"
      by (rule reverse_add_pair_run_mod11_preserves_zero[OF tail_valid sixth_zero])
    have indices: "n-1 = 5 + (n-6)" using enough_steps by presburger
    have run_rewrite:
      "run step (n-1) ss = run step (5 + (n-6)) ss"
      by (simp only: indices)
    have run_composition:
      "run step (5 + (n-6)) ss = run step (n-6) (run step 5 ss)"
      by (rule reverse_add_run_add)
    have joined:
      "run step (n-1) ss = run step (n-6) (run step 5 ss)"
      by (rule trans[OF run_rewrite run_composition])
    show ?thesis by (simp only: joined tail_zero)
  qed
  have raw_mod11: "?raw mod 11 = 0"
  proof -
    have factor: "(55::nat) mod 11 = 0" by simp
    have "?raw mod 11 =
        ((((55::nat) mod 11) * (((5 * ?x) mod 9) mod 11)) mod 11 *
          ((2::nat)^n mod 11)) mod 11"
      by (simp only: mod_mult_eq)
    then show ?thesis using factor by simp
  qed
  have residues:
    "reverse_add_pair_term (run step (n-1) ss) mod 9 = ?raw mod 9"
    "reverse_add_pair_term (run step (n-1) ss) mod 11 = ?raw mod 11"
    using actual_mod9 raw_mod9 actual_mod11 raw_mod11 by simp_all
  show ?thesis
    by (rule mod_9_11_equal_mod99[OF residues])
qed

theorem source_growth_potential:
  assumes "valid_pair ss"
  shows "source_growth_count n ss + edge_growth_rank (hd (run step n ss))
    \<le> 3 * source_no_growth_count n ss + edge_growth_rank (hd ss)"
using assms
proof (induct n arbitrary: ss)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have next_valid: "valid_pair (step ss)" by (rule valid_pair_successor[OF Suc.prems])
  have ih: "source_growth_count n (step ss) + edge_growth_rank (hd (run step n (step ss)))
    \<le> 3 * source_no_growth_count n (step ss) + edge_growth_rank (hd (step ss))"
    by (rule Suc.hyps[OF next_valid])
  show ?case
  proof (cases "carry_out False ss")
    case True
    have drop: "edge_growth_rank (hd (step ss))+1 = edge_growth_rank (hd ss)"
      by (rule source_growth_rank_decreases[OF Suc.prems True])
    show ?thesis using ih drop by (simp add: True; arith)
  next
    case False
    have bound: "edge_growth_rank (hd (step ss)) \<le> 3"
      by (rule edge_growth_rank_bound)
    show ?thesis using ih bound by (simp add: False; arith)
  qed
qed

theorem source_radial_growth_bound:
  assumes "valid_pair ss"
  shows "source_growth_count n ss \<le> 3*(source_no_growth_count n ss+1)"
  using source_growth_potential[OF assms, of n] edge_growth_rank_bound[of "hd ss"]
  by arith

text \<open>The two-sided outer coefficient gives a sharper accounting
potential than the consecutive-growth rank.  This is a proof measure on an
already admitted source, not a temporal-state ID or a future selector.\<close>

definition edge_carry_potential :: "nat \<Rightarrow> nat" where
  "edge_carry_potential e =
    (if e=18 then 3
     else if e\<in>{9,13,15,16,17} then 2
     else if e\<in>{4,6,7,8,10,11,12,14} then 1 else 0)"

lemma edge_carry_potential_bound: "edge_carry_potential e \<le> 3"
  by (simp add: edge_carry_potential_def)

lemma edge_carry_potential_growth:
  assumes "9\<le>e" "e\<le>18"
  shows "edge_carry_potential (1+e mod 10)+1 = edge_carry_potential e"
proof -
  have "e=9 \<or> e=10 \<or> e=11 \<or> e=12 \<or> e=13 \<or> e=14 \<or>
    e=15 \<or> e=16 \<or> e=17 \<or> e=18" using assms by arith
  then show ?thesis by (auto simp: edge_carry_potential_def)
qed

lemma edge_carry_potential_nongrowth:
  assumes "2*e\<le>y" "y\<le>2*e+1" "y\<le>18"
  shows "edge_carry_potential y \<le> edge_carry_potential e+1"
proof -
  have e_bound: "e\<le>9" using assms by arith
  have cases: "e=0 \<or> e=1 \<or> e=2 \<or> e=3 \<or> e=4 \<or> e=5 \<or>
    e=6 \<or> e=7 \<or> e=8 \<or> e=9" using e_bound by arith
  have adjacent: "y=2*e \<or> y=2*e+1" using assms by arith
  show ?thesis using cases adjacent assms(3)
    by (auto simp: edge_carry_potential_def)
qed

theorem source_carry_potential_accounting:
  assumes "valid_pair ss"
  shows "source_growth_count n ss + edge_carry_potential (hd (run step n ss))
    \<le> source_no_growth_count n ss + edge_carry_potential (hd ss)"
using assms
proof (induction n arbitrary: ss)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have next_valid: "valid_pair (step ss)"
    by (rule valid_pair_successor[OF Suc.prems])
  have ih: "source_growth_count n (step ss) +
      edge_carry_potential (hd (run step n (step ss))) \<le>
      source_no_growth_count n (step ss) + edge_carry_potential (hd (step ss))"
    by (rule Suc.IH[OF next_valid])
  show ?case
  proof (cases "carry_out False ss")
    case True
    have nonempty: "ss\<noteq>[]" using Suc.prems
      by (simp add: valid_pair_def)
    have outer: "hd (step ss)=1+hd ss mod 10"
      by (rule source_growth_edge_successor[OF nonempty True])
    have drop: "edge_carry_potential (hd (step ss))+1 = edge_carry_potential (hd ss)"
      using edge_carry_potential_growth[OF source_growth_requires_edge[OF Suc.prems True]]
      by (simp only: outer)
    show ?thesis using ih drop by (simp add: True; arith)
  next
    case False
    have next_edge: "hd (step ss)\<le>18"
      using next_valid by (auto simp: valid_pair_def)
    have rise: "edge_carry_potential (hd (step ss))\<le>edge_carry_potential (hd ss)+1"
      by (rule edge_carry_potential_nongrowth
        [OF source_nongrowth_outer_coefficient_bounds[OF Suc.prems False] next_edge])
    show ?thesis using ih rise by (simp add: False; arith)
  qed
qed

corollary source_decimal_twelve_step_nongrowth:
  assumes "valid_pair ss"
  shows "5\<le>source_no_growth_count 12 ss"
  using source_carry_potential_accounting[OF assms, of 12]
    edge_carry_potential_bound[of "hd ss"] source_growth_accounting[of 12 ss]
  by arith

corollary source_decimal_twelve_step_mod32_erasure:
  assumes "valid_pair ss"
  shows "((2::int)^source_no_growth_count 12 ss * x) mod 32 = 0"
proof -
  have count: "source_no_growth_count 12 ss =
      5 + (source_no_growth_count 12 ss - 5)"
    using source_decimal_twelve_step_nongrowth[OF assms] by arith
  show ?thesis by (subst count) (simp add: power_add mult.assoc)
qed

corollary source_live_radial_age:
  assumes valid: "valid_pair ss" and live: "source_no_growth_count n ss < bits"
  shows "n < 4*bits" "source_growth_count n ss \<le> 3*bits"
  using source_radial_growth_bound[OF valid, of n] source_growth_accounting[of n ss] live
  by arith+

corollary source_196_live_radial_age:
  assumes "source_no_growth_count n (run step t [7,18,7]) < 5"
  shows "n < 20" "source_growth_count n (run step t [7,18,7]) \<le> 15"
  using source_live_radial_age[OF all_196_pair_fields_valid assms] by auto

corollary source_four_step_no_growth:
  assumes "valid_pair ss" "4 \<le> n"
  shows "1 \<le> source_no_growth_count n ss"
  using source_live_radial_age(1)[OF assms(1), of n 1] assms(2) by force

corollary source_block_parity_forcing:
  assumes "valid_pair ss" "4 \<le> n"
  shows "((2::int)^source_no_growth_count n ss * x + forcing) mod 2 =
    forcing mod 2"
proof -
  obtain q where q: "source_no_growth_count n ss = Suc q"
    using source_four_step_no_growth[OF assms] by (cases "source_no_growth_count n ss") auto
  have even: "((2::int)^source_no_growth_count n ss * x) mod 2 = 0"
    by (simp add: q power_Suc mult.assoc)
  have "((2::int)^source_no_growth_count n ss * x + forcing) mod 2 =
    (((2::int)^source_no_growth_count n ss * x) mod 2 + forcing mod 2) mod 2"
    by (rule mod_add_eq[symmetric])
  also have "... = forcing mod 2" by (simp add: even)
  finally show ?thesis .
qed

corollary source_196_block_parity_forcing:
  assumes "4 \<le> n"
  shows "((2::int)^source_no_growth_count n (run step t [7,18,7]) *
    x + forcing) mod 2 = forcing mod 2"
  by (rule source_block_parity_forcing[OF all_196_pair_fields_valid assms])

text \<open>Here x may include the entire neighbor-power contribution. Only
the homogeneous source term is erased. The forcing can still depend on the
original source through intervening carries and must be pulled back before
composing admitted blocks. No spatial scan or grammar-size bound follows.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms source_chronological_growth_word_counts
      source_growth_homogeneous_factor_counts
      source_growth_word_homogeneous_mod32_erasure
      source_chronological_homogeneous_mod32_erasure
      source_decimal_homogeneous_coefficient_erasure
      step_length_exact source_run_length_exact
      source_growth_count_chronological source_growth_phase_chronological
      source_width_phase_exact source_width_phase_chronological
      source_growth_requires_edge source_growth_edge_successor
      source_nongrowth_outer_coefficient_doubles
      source_nongrowth_outer_coefficient_bounds
      source_growth_rank_decreases source_growth_potential source_radial_growth_bound
      edge_carry_potential_bound edge_carry_potential_growth
      edge_carry_potential_nongrowth source_carry_potential_accounting
      source_decimal_twelve_step_nongrowth
      source_decimal_twelve_step_mod32_erasure
      source_nongrowth_outer_bound source_five_step_growth_positive
      source_positive_growth_has_odd_prefix source_even_width_state_within_five
      source_sixth_value_mod11 source_pair_run_residue99
      source_live_radial_age source_196_live_radial_age
      source_four_step_no_growth source_block_parity_forcing
      source_196_block_parity_forcing})
    then () else error "Source growth admission depends on an oracle";
\<close>

end
