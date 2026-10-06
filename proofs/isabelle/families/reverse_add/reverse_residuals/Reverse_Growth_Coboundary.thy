theory Reverse_Growth_Coboundary
  imports Mirror_Pair_Step
begin

text \<open>The growth branch has a carry/value coboundary quotient.  This
theory states only the forward factorization: equal quotient symbols imply
equal growth outputs.  It does not claim that equal outputs determine the
quotient.  Source values and carry ports are kept separate in the hypotheses,
so the proof does not treat carries as an independent state plane.\<close>

definition decimal_carry :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "decimal_carry s c = (if 10 \<le> s+c then 1 else 0)"

text \<open>The following radix lemma is the small arithmetic fact used at a
growth seam. Two digits below a base, together with an incoming bit, are at
most \(2b-1\), so the outgoing carry is a bit.\<close>

definition radix_pair_carry :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "radix_pair_carry b x y c = (x+y+c) div b"

lemma radix_pair_sum_carry_bound:
  fixes b x y c :: nat
  assumes base: "(2::nat) \<le> b" and left: "x < b" and right: "y < b"
      and incoming: "c < (2::nat)"
  shows "x+y+c < (2::nat)*b"
  using base left right incoming by arith

theorem radix_pair_carry_is_bit:
  fixes b x y c :: nat
  assumes base: "2 \<le> b" and left: "x < b" and right: "y < b"
      and incoming: "c < 2"
  shows "radix_pair_carry b x y c = 0 \<or>
    radix_pair_carry b x y c = 1"
proof -
  have bound: "x+y+c < 2*b"
    using radix_pair_sum_carry_bound[OF assms] .
  have positive: "0 < b" using base by arith
  have quotient: "(x+y+c) div b < 2"
    using bound by (simp only: div_less_iff_less_mult[OF positive])
  show ?thesis
    unfolding radix_pair_carry_def
    using quotient by arith
qed

definition valid_growth_carries ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_growth_carries S C L \<longleftrightarrow>
    C 0 = 0 \<and> C L = 1 \<and>
    (\<forall>i<L. S i < 19 \<and> C i < 2 \<and>
      C (Suc i) = decimal_carry (S i) (C i))"

definition symmetric_source :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "symmetric_source S L \<longleftrightarrow>
    (\<forall>i<L. S i = S (L-Suc i))"

definition growth_q ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> int" where
  "growth_q S C i = int (S i) - 9 * int (C (Suc i))"

definition growth_delta :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "growth_delta C L i = int (C (L-i)) - int (C (Suc i))"

definition normalized_growth_digit ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> int" where
  "normalized_growth_digit S C i =
    int (S i) + int (C i) - 10 * int (C (Suc i))"

definition growth_edge_output ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> int" where
  "growth_edge_output S C = normalized_growth_digit S C 0 + 1"

definition growth_interior_output ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "growth_interior_output S C L i =
    normalized_growth_digit S C i + normalized_growth_digit S C (L-i)"

text \<open>A source-bound growth publisher has one extra output cell when
the terminal carry is one.  The definitions below retain the carry port and
the source extent together; they do not introduce a midpoint word.  The
general extent is L + C L, while the admitted growth rule supplies C L = 1.\<close>

definition growth_first_output_extent :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "growth_first_output_extent C L = L + C L"

definition growth_first_output_digit ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> int" where
  "growth_first_output_digit S C L i =
    (if i < L then normalized_growth_digit S C i
     else if i = L \<and> C L = 1 then 1 else 0)"

definition growth_first_output_pair ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> int" where
  "growth_first_output_pair S C L i =
    growth_first_output_digit S C L i +
      growth_first_output_digit S C L
        (growth_first_output_extent C L - Suc i)"

definition no_growth_pair_output ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> int" where
  "no_growth_pair_output S C L i =
    normalized_growth_digit S C i +
      normalized_growth_digit S C (L-Suc i)"

text \<open>The repeated no-growth chamber is represented by its affine
source coordinate.  The parameter beta is the fixed carry/pair correction;
the endpoint guard below is deliberately a source predicate, so it does not
turn carry geometry into a new successor state.\<close>

definition no_growth_affine_step :: "int \<Rightarrow> int \<Rightarrow> int" where
  "no_growth_affine_step beta s = 2*s + beta"

fun no_growth_affine_iter :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "no_growth_affine_iter 0 beta s = s"
| "no_growth_affine_iter (Suc t) beta s =
    no_growth_affine_step beta (no_growth_affine_iter t beta s)"

definition no_growth_pair_guard :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "no_growth_pair_guard lo hi s = (lo \<le> s \<and> s \<le> hi)"

lemma no_growth_affine_iter_closed:
  "no_growth_affine_iter t beta s = (2::int)^t * (s+beta) - beta"
proof (induct t)
  case 0
  then show ?case by simp
next
  case (Suc t)
  then show ?case
    by (simp add: no_growth_affine_step_def algebra_simps power_Suc)
qed

lemma no_growth_affine_step_mono_nonnegative:
  assumes coefficient: "0 \<le> s+beta"
  shows "no_growth_affine_iter t beta s \<le>
    no_growth_affine_iter (Suc t) beta s"
proof -
  have power_nonnegative: "0 \<le> (2::int)^t"
    by simp
  have product_nonnegative: "0 \<le> (2::int)^t * (s+beta)"
    using power_nonnegative coefficient by (rule mult_nonneg_nonneg)
  show ?thesis
    unfolding no_growth_affine_iter_closed
    using product_nonnegative by (simp add: power_Suc algebra_simps)
qed

lemma no_growth_affine_step_mono_nonpositive:
  assumes coefficient: "s+beta \<le> 0"
  shows "no_growth_affine_iter (Suc t) beta s \<le>
    no_growth_affine_iter t beta s"
proof -
  have power_nonnegative: "0 \<le> (2::int)^t"
    by simp
  have product_nonpositive: "(2::int)^t * (s+beta) \<le> 0"
    using power_nonnegative coefficient by (rule mult_nonneg_nonpos)
  show ?thesis
    unfolding no_growth_affine_iter_closed
    using product_nonpositive by (simp add: power_Suc algebra_simps)
qed

lemma no_growth_affine_iter_mono_nonnegative:
  assumes coefficient: "0 \<le> s+beta" and order: "t \<le> u"
  shows "no_growth_affine_iter t beta s \<le>
    no_growth_affine_iter u beta s"
using order
proof (induct u arbitrary: t)
  case 0
  then show ?case by simp
next
  case (Suc u)
  consider (last) "t = Suc u" | (before) "t \<le> u"
    using Suc.prems by arith
  then show ?case
  proof cases
    case last
    then show ?thesis by simp
  next
    case before
    have prefix:
      "no_growth_affine_iter t beta s \<le>
          no_growth_affine_iter u beta s"
      using Suc.hyps[OF before] .
    have suffix:
        "no_growth_affine_iter u beta s \<le>
          no_growth_affine_iter (Suc u) beta s"
      using no_growth_affine_step_mono_nonnegative[OF coefficient] .
    then show ?thesis using prefix by simp
  qed
qed

lemma no_growth_affine_iter_mono_nonpositive:
  assumes coefficient: "s+beta \<le> 0" and order: "t \<le> u"
  shows "no_growth_affine_iter u beta s \<le>
    no_growth_affine_iter t beta s"
using order
proof (induct u arbitrary: t)
  case 0
  then show ?case by simp
next
  case (Suc u)
  consider (last) "t = Suc u" | (before) "t \<le> u"
    using Suc.prems by arith
  then show ?case
  proof cases
    case last
    then show ?thesis by simp
  next
    case before
    have prefix:
      "no_growth_affine_iter u beta s \<le>
          no_growth_affine_iter t beta s"
      using Suc.hyps[OF before] .
    have suffix:
        "no_growth_affine_iter (Suc u) beta s \<le>
          no_growth_affine_iter u beta s"
      using no_growth_affine_step_mono_nonpositive[OF coefficient] .
    then show ?thesis using suffix prefix by simp
  qed
qed

theorem no_growth_affine_chamber_between_nonnegative:
  assumes coefficient: "0 \<le> s+beta" and order: "t \<le> n"
      and lower_start: "no_growth_pair_guard lo hi
        (no_growth_affine_iter 0 beta s)"
      and upper_start: "no_growth_pair_guard lo hi
        (no_growth_affine_iter n beta s)"
  shows "no_growth_pair_guard lo hi
    (no_growth_affine_iter t beta s)"
proof -
  have lower_start':
      "lo \<le> no_growth_affine_iter 0 beta s \<and>
        no_growth_affine_iter 0 beta s \<le> hi"
    using lower_start by (simp add: no_growth_pair_guard_def)
  have upper_start':
      "lo \<le> no_growth_affine_iter n beta s \<and>
        no_growth_affine_iter n beta s \<le> hi"
    using upper_start by (simp add: no_growth_pair_guard_def)
  have from_start:
      "no_growth_affine_iter 0 beta s \<le>
        no_growth_affine_iter t beta s"
    using no_growth_affine_iter_mono_nonnegative[OF coefficient, of 0 t]
      by simp
  have to_end:
      "no_growth_affine_iter t beta s \<le>
        no_growth_affine_iter n beta s"
    using no_growth_affine_iter_mono_nonnegative[OF coefficient order] .
  show ?thesis
    unfolding no_growth_pair_guard_def
    using lower_start' upper_start' from_start to_end by arith
qed

theorem no_growth_affine_chamber_between_nonpositive:
  assumes coefficient: "s+beta \<le> 0" and order: "t \<le> n"
      and lower_start: "no_growth_pair_guard lo hi
        (no_growth_affine_iter 0 beta s)"
      and upper_start: "no_growth_pair_guard lo hi
        (no_growth_affine_iter n beta s)"
  shows "no_growth_pair_guard lo hi
    (no_growth_affine_iter t beta s)"
proof -
  have lower_start':
      "lo \<le> no_growth_affine_iter 0 beta s \<and>
        no_growth_affine_iter 0 beta s \<le> hi"
    using lower_start by (simp add: no_growth_pair_guard_def)
  have upper_start':
      "lo \<le> no_growth_affine_iter n beta s \<and>
        no_growth_affine_iter n beta s \<le> hi"
    using upper_start by (simp add: no_growth_pair_guard_def)
  have from_start:
      "no_growth_affine_iter t beta s \<le>
        no_growth_affine_iter 0 beta s"
    using no_growth_affine_iter_mono_nonpositive[OF coefficient, of 0 t]
      by simp
  have to_end:
      "no_growth_affine_iter n beta s \<le>
        no_growth_affine_iter t beta s"
    using no_growth_affine_iter_mono_nonpositive[OF coefficient order] .
  show ?thesis
    unfolding no_growth_pair_guard_def
    using lower_start' upper_start' from_start to_end by arith
qed


text \<open>The executable chamber checks pair bounds and equality of the
outgoing carry at the final endpoint. This conjunction is exactly an interval,
so endpoint propagation applies to both signs of the affine coefficient.\<close>

definition fixed_radix_carry_guard ::
    "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "fixed_radix_carry_guard b cin cout s =
    (0 \<le> s \<and> s \<le> 2*b-2 \<and>
      ((b \<le> s+cin) = (cout = 1)))"

lemma fixed_radix_carry_guard_interval:
  assumes base: "2 \<le> b" and incoming: "cin = 0 \<or> cin = 1"
      and outgoing: "cout = 0 \<or> cout = 1"
  shows "fixed_radix_carry_guard b cin cout s =
    no_growth_pair_guard (if cout = 1 then b-cin else 0)
      (if cout = 1 then 2*b-2 else b-1-cin) s"
  using base incoming outgoing
  unfolding fixed_radix_carry_guard_def no_growth_pair_guard_def
  by (elim disjE; auto; linarith)

theorem no_growth_fixed_carry_endpoint_admission:
  assumes base: "2 \<le> b" and incoming: "cin = 0 \<or> cin = 1"
      and outgoing: "cout = 0 \<or> cout = 1" and order: "t \<le> n"
      and initial: "fixed_radix_carry_guard b cin cout
        (no_growth_affine_iter 0 beta s)"
      and terminal: "fixed_radix_carry_guard b cin cout
        (no_growth_affine_iter n beta s)"
  shows "fixed_radix_carry_guard b cin cout
    (no_growth_affine_iter t beta s)"
proof -
  let ?lo = "if cout = 1 then b-cin else 0"
  let ?hi = "if cout = 1 then 2*b-2 else b-1-cin"
  have first: "no_growth_pair_guard ?lo ?hi (no_growth_affine_iter 0 beta s)"
    using initial fixed_radix_carry_guard_interval[OF base incoming outgoing]
    by simp
  have last: "no_growth_pair_guard ?lo ?hi (no_growth_affine_iter n beta s)"
    using terminal fixed_radix_carry_guard_interval[OF base incoming outgoing]
    by simp
  have middle: "no_growth_pair_guard ?lo ?hi (no_growth_affine_iter t beta s)"
  proof (cases "0 \<le> s+beta")
    case True
    show ?thesis
      using no_growth_affine_chamber_between_nonnegative[OF True order first last] .
  next
    case False
    have negative: "s+beta \<le> 0" using False by arith
    show ?thesis
      using no_growth_affine_chamber_between_nonpositive[OF negative order first last] .
  qed
  show ?thesis
    using middle fixed_radix_carry_guard_interval[OF base incoming outgoing]
    by simp
qed

lemma symmetric_source_at:
  assumes symmetry: "symmetric_source S L" and position: "i < L"
  shows "S i = S (L-Suc i)"
proof -
  have all: "\<forall>j. j < L \<longrightarrow> S j = S (L-Suc j)"
    using symmetry unfolding symmetric_source_def .
  have implication: "i < L \<longrightarrow> S i = S (L-Suc i)"
    using all by (rule spec)
  show ?thesis using implication position by (rule mp)
qed

lemma decimal_carry_bit [simp]: "decimal_carry s c < 2"
  by (simp add: decimal_carry_def)

lemma growth_q_residue_view:
  assumes source: "s < 19" and incoming: "c < 2"
  defines "out \<equiv> decimal_carry s c"
  shows "int s - 9 * int out = int ((s mod 10 + out) mod 10)"
proof -
  have s_cases: "s = 0 \<or> s = 1 \<or> s = 2 \<or> s = 3 \<or> s = 4 \<or>
      s = 5 \<or> s = 6 \<or> s = 7 \<or> s = 8 \<or> s = 9 \<or>
      s = 10 \<or> s = 11 \<or> s = 12 \<or> s = 13 \<or> s = 14 \<or>
      s = 15 \<or> s = 16 \<or> s = 17 \<or> s = 18"
    using source by (rule nat_less_nineteen_cases)
  have c_cases: "c = 0 \<or> c = 1"
    using incoming by (rule nat_less_two_cases)
  show ?thesis using s_cases c_cases
    by (elim disjE; simp add: out_def decimal_carry_def)
qed

theorem valid_growth_q_is_decimal_view:
  assumes valid: "valid_growth_carries S C L" and position: "i < L"
  shows "growth_q S C i = int ((S i mod 10 + C (Suc i)) mod 10)"
proof -
  have source: "S i < 19" and incoming: "C i < 2"
    using valid position by (auto simp: valid_growth_carries_def)
  have carry: "C (Suc i) = decimal_carry (S i) (C i)"
    using valid position by (auto simp: valid_growth_carries_def)
  show ?thesis
    unfolding growth_q_def carry
    using growth_q_residue_view[OF source incoming] by simp
qed

corollary valid_growth_q_range:
  assumes "valid_growth_carries S C L" "i < L"
  shows "0 \<le> growth_q S C i" "growth_q S C i \<le> 9"
  using valid_growth_q_is_decimal_view[OF assms] by simp_all

lemma growth_skew_is_q_difference:
  assumes position: "i < L" and symmetry: "symmetric_source S L"
  shows "growth_q S C i - growth_q S C (L-Suc i) =
    9 * growth_delta C L i"
proof -
  have source_mirror: "S i = S (L-Suc i)"
    using symmetric_source_at[OF symmetry position] .
  have index: "Suc (L-Suc i) = L-i"
    using position by arith
  show ?thesis
    unfolding growth_q_def growth_delta_def
    using source_mirror index by (simp add: algebra_simps)
qed

corollary growth_delta_range:
  assumes valid: "valid_growth_carries S C L" and position: "i < L"
  shows "-1 \<le> growth_delta C L i" "growth_delta C L i \<le> 1"
proof -
  have left: "C (L-i) < 2"
  proof (cases "i = 0")
    case True
    then show ?thesis using valid by (simp add: valid_growth_carries_def)
  next
    case False
    with position have "L-i < L" by arith
    then show ?thesis using valid by (cases L; auto simp: valid_growth_carries_def)
  qed
  have right: "C (Suc i) < 2"
  proof (cases "Suc i = L")
    case True
    then show ?thesis using valid by (simp add: valid_growth_carries_def)
  next
    case False
    with position have "Suc i < L" by arith
    then show ?thesis using valid by (cases L; auto simp: valid_growth_carries_def)
  qed
  show "-1 \<le> growth_delta C L i" "growth_delta C L i \<le> 1"
    unfolding growth_delta_def using left right by linarith+
qed

theorem growth_symbol_has_twelve_forms:
  assumes valid: "valid_growth_carries S C L" and symmetry: "symmetric_source S L"
      and position: "i < L"
  shows "(growth_delta C L i = -1 \<and> growth_q S C i = 0) \<or>
    (growth_delta C L i = 0 \<and>
      0 \<le> growth_q S C i \<and> growth_q S C i \<le> 9) \<or>
    (growth_delta C L i = 1 \<and> growth_q S C i = 9)"
proof -
  have mirror_position: "L-Suc i < L" using position by arith
  have q_bounds: "0 \<le> growth_q S C i" "growth_q S C i \<le> 9"
    using valid_growth_q_range[OF valid position] by simp_all
  have mirror_bounds: "0 \<le> growth_q S C (L-Suc i)"
      "growth_q S C (L-Suc i) \<le> 9"
    using valid_growth_q_range[OF valid mirror_position] by simp_all
  have skew: "growth_q S C i - growth_q S C (L-Suc i) =
      9 * growth_delta C L i"
    using growth_skew_is_q_difference[OF position symmetry] .
  have delta_bounds: "-1 \<le> growth_delta C L i"
      "growth_delta C L i \<le> 1"
    using growth_delta_range[OF valid position] by simp_all
  have delta_cases: "growth_delta C L i = -1 \<or>
      growth_delta C L i = 0 \<or> growth_delta C L i = 1"
    using delta_bounds by arith
  show ?thesis using q_bounds mirror_bounds skew delta_cases
    by (elim disjE; auto; linarith)
qed

theorem nonzero_growth_skew_requires_equal_domain_source:
  assumes valid: "valid_growth_carries S C L" and symmetry: "symmetric_source S L"
      and position: "i < L" and nonzero: "growth_delta C L i \<noteq> 0"
  shows "S i = 9"
proof -
  let ?j = "L-Suc i"
  have mirror_position: "?j < L" using position by arith
  have source: "S i < 19" and left_in: "C i < 2"
    using valid position by (auto simp: valid_growth_carries_def)
  have right_in: "C ?j < 2"
    using valid mirror_position by (auto simp: valid_growth_carries_def)
  have source_mirror: "S ?j = S i"
    using symmetric_source_at[OF symmetry position] by simp
  have left_out: "C (Suc i) = decimal_carry (S i) (C i)"
    using valid position by (auto simp: valid_growth_carries_def)
  have right_index: "Suc ?j = L-i" using position by arith
  have right_raw: "C (Suc ?j) = decimal_carry (S ?j) (C ?j)"
    using valid mirror_position by (auto simp: valid_growth_carries_def)
  have right_out: "C (L-i) = decimal_carry (S i) (C ?j)"
    using right_raw source_mirror right_index by simp
  have outputs_differ: "C (L-i) \<noteq> C (Suc i)"
    using nonzero by (auto simp: growth_delta_def)
  consider (below) "S i < 9" | (equal) "S i = 9" | (above) "9 < S i"
    by arith
  then show ?thesis
  proof cases
    case below
    have "S i + C i < 10" "S i + C ?j < 10"
      using below left_in right_in by arith+
    then show ?thesis using left_out right_out outputs_differ
      by (simp add: decimal_carry_def)
  next
    case equal
    then show ?thesis .
  next
    case above
    have "10 \<le> S i + C i" "10 \<le> S i + C ?j"
      using above by arith+
    then show ?thesis using left_out right_out outputs_differ
      by (simp add: decimal_carry_def)
  qed
qed

theorem growth_edge_coboundary_factorization:
  assumes left_endpoint: "C 0 = 0" and right_endpoint: "C L = 1"
  shows "growth_edge_output S C =
    growth_q S C 0 + growth_delta C L 0"
  unfolding growth_edge_output_def normalized_growth_digit_def
    growth_q_def growth_delta_def
  using assms by simp

text \<open>These are the concrete growth boundary equations consumed by the
two-port publisher. The first is the exact leading-one correction; the
second records the reflected source index after that appended digit shifts
the pairing by one cell.\<close>

theorem growth_edge_pair_equation:
  "growth_pair_step r 1 0 0 = r mod 10 + 1"
  by (simp add: growth_pair_step_def)

theorem growth_digits_append_one:
  assumes growth: "carry_out False ss"
  shows "digits ss = emit False ss @ [1]"
  by (simp add: digits_def growth)

theorem growth_reflection_shift:
  assumes palindrome: "rev ss = ss"
      and positive: "0 < i" and bound: "i < length ss"
  shows "ss ! (length ss-i) = ss!(i-1)"
proof -
  have previous: "i-1 < length ss" using positive bound by arith
  have reflected:
    "ss ! (length ss-Suc (i-1)) = ss!(i-1)"
    using palindrome_nth_reflect[OF palindrome previous] .
  show ?thesis using reflected positive by simp
qed

lemma no_growth_pair_output_expanded:
  assumes position: "i < L"
  shows "no_growth_pair_output S C L i =
    int (S i) + int (S (L-Suc i)) + int (C i) + int (C (L-Suc i))
      - 10 * (int (C (Suc i)) + int (C (L-i)))"
proof -
  have index: "L-i = Suc (L-Suc i)"
    using position by arith
  show ?thesis
    unfolding no_growth_pair_output_def normalized_growth_digit_def
    using position index by (simp add: algebra_simps)
qed

theorem no_growth_symmetric_pair_formula:
  assumes symmetry: "symmetric_source S L" and position: "i < L"
  shows "no_growth_pair_output S C L i =
    2 * int (S i) + int (C i) + int (C (L-Suc i))
      - 10 * (int (C (Suc i)) + int (C (L-i)))"
proof -
  have mirror: "S (L-Suc i) = S i"
    using symmetric_source_at[OF symmetry position] by simp
  show ?thesis
    using no_growth_pair_output_expanded[OF position] mirror
    by simp
qed

definition no_growth_pair_beta ::
    "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "no_growth_pair_beta C L i =
    int (C i) + int (C (L-Suc i))
      - 10 * (int (C (Suc i)) + int (C (L-i)))"

theorem no_growth_symmetric_pair_affine:
  assumes symmetry: "symmetric_source S L" and position: "i < L"
  shows "no_growth_pair_output S C L i =
    2 * int (S i) + no_growth_pair_beta C L i"
  using no_growth_symmetric_pair_formula[OF symmetry position]
  by (simp add: no_growth_pair_beta_def)

lemma growth_first_output_pair_zero:
  assumes valid: "valid_growth_carries S C L"
  shows "growth_first_output_pair S C L 0 = growth_edge_output S C"
proof -
  have endpoint: "C L = 1"
    using valid by (simp add: valid_growth_carries_def)
  have nonempty: "0 < L"
    using valid by (cases L; auto simp: valid_growth_carries_def)
  show ?thesis
    unfolding growth_first_output_pair_def growth_first_output_digit_def
      growth_first_output_extent_def growth_edge_output_def
    using endpoint nonempty by (simp add: add.commute)
qed

lemma growth_first_output_pair_last:
  assumes valid: "valid_growth_carries S C L"
  shows "growth_first_output_pair S C L L = growth_edge_output S C"
proof -
  have endpoint: "C L = 1"
    using valid by (simp add: valid_growth_carries_def)
  have nonempty: "0 < L"
    using valid by (cases L; auto simp: valid_growth_carries_def)
  show ?thesis
    unfolding growth_first_output_pair_def growth_first_output_digit_def
      growth_first_output_extent_def growth_edge_output_def
    using endpoint nonempty by (simp add: add.commute)
qed

theorem growth_edge_source_formula:
  assumes valid: "valid_growth_carries S C L"
  shows "growth_first_output_pair S C L 0 =
      int (S 0) + 1 - 10 * int (C (Suc 0))"
    and "growth_first_output_pair S C L L =
      int (S 0) + 1 - 10 * int (C (Suc 0))"
proof -
  have left:
      "growth_first_output_pair S C L 0 = growth_edge_output S C"
    using growth_first_output_pair_zero[OF valid] .
  have right:
      "growth_first_output_pair S C L L = growth_edge_output S C"
    using growth_first_output_pair_last[OF valid] .
  have endpoint: "C 0 = 0"
    using valid by (simp add: valid_growth_carries_def)
  show "growth_first_output_pair S C L 0 =
      int (S 0) + 1 - 10 * int (C (Suc 0))"
    using left endpoint by (simp add: growth_edge_output_def
      normalized_growth_digit_def)
  show "growth_first_output_pair S C L L =
      int (S 0) + 1 - 10 * int (C (Suc 0))"
    using right endpoint by (simp add: growth_edge_output_def
      normalized_growth_digit_def)
qed

lemma growth_first_output_pair_interior:
  assumes valid: "valid_growth_carries S C L"
      and lower: "0 < i" and upper: "i < L"
  shows "growth_first_output_pair S C L i =
    growth_interior_output S C L i"
proof -
  have endpoint: "C L = 1"
    using valid by (simp add: valid_growth_carries_def)
  have reflected_index: "L + C L - Suc i = L-i"
    using endpoint upper by arith
  have right_position: "L-i < L"
    using lower upper by arith
  show ?thesis
    unfolding growth_first_output_pair_def growth_first_output_digit_def
      growth_first_output_extent_def growth_interior_output_def
    using endpoint lower upper right_position reflected_index
    by simp
qed

theorem growth_symmetric_interior_source_formula:
  assumes valid: "valid_growth_carries S C L"
      and symmetry: "symmetric_source S L"
      and lower: "0 < i" and upper: "i < L"
  shows "growth_first_output_pair S C L i =
    int (S i) + int (S (i-1)) + int (C i) + int (C (L-i))
      - 10 * (int (C (Suc i)) + int (C (Suc (L-i))))"
proof -
  have previous: "i-1 < L"
    using upper by arith
  have source_mirror: "S (L-i) = S (i-1)"
  proof -
    have reflected: "S (i-1) = S (L-Suc (i-1))"
      using symmetric_source_at[OF symmetry previous] .
    have index: "L-Suc (i-1) = L-i"
      using lower by arith
    show ?thesis using reflected index by simp
  qed
  have interior:
      "growth_first_output_pair S C L i =
        growth_interior_output S C L i"
    using growth_first_output_pair_interior[OF valid lower upper] .
  show ?thesis
    using interior source_mirror
    by (simp add: growth_interior_output_def normalized_growth_digit_def algebra_simps)
qed

theorem growth_first_output_pair_source_formula:
  assumes valid: "valid_growth_carries S C L"
      and symmetry: "symmetric_source S L"
      and position: "i < growth_first_output_extent C L"
  shows "(i = 0 \<and>
      growth_first_output_pair S C L i = growth_edge_output S C) \<or>
    (0 < i \<and> i < L \<and>
      growth_first_output_pair S C L i = growth_interior_output S C L i) \<or>
    (i = L \<and>
      growth_first_output_pair S C L i = growth_edge_output S C)"
proof -
  have endpoint: "C L = 1"
    using valid by (simp add: valid_growth_carries_def)
  have extent: "growth_first_output_extent C L = L+1"
    using endpoint by (simp add: growth_first_output_extent_def)
  have bound: "i < L+1"
    using position extent by simp
  consider (left) "i=0" | (middle) "0<i \<and> i<L" | (right) "i=L"
    using bound by arith
  then show ?thesis
  proof cases
    case left
    then show ?thesis
      using growth_first_output_pair_zero[OF valid] by simp
  next
    case middle
    have lower: "0 < i" using middle by arith
    have upper: "i < L" using middle by arith
    show ?thesis
      using growth_first_output_pair_interior[OF valid lower upper]
      middle by simp
  next
    case right
    then show ?thesis
      using growth_first_output_pair_last[OF valid] by simp
  qed
qed

lemma decimal_carry_idempotent:
  assumes incoming: "c < 2"
  shows "decimal_carry s (decimal_carry s c) = decimal_carry s c"
proof -
  have c_cases: "c = 0 \<or> c = 1"
    using incoming by (rule nat_less_two_cases)
  consider (above) "10 \<le> s" | (equal) "s = 9" | (below) "s < 9"
    by arith
  then show ?thesis
  proof cases
    case above
    then show ?thesis by (simp add: decimal_carry_def)
  next
    case equal
    then show ?thesis using c_cases
      by (elim disjE; simp add: decimal_carry_def)
  next
    case below
    then show ?thesis using c_cases
      by (elim disjE; simp add: decimal_carry_def)
  qed
qed

lemma valid_even_growth_central_carry:
  assumes nonempty: "0 < n" and valid: "valid_growth_carries S C (2*n)"
      and symmetry: "symmetric_source S (2*n)"
  shows "C n = C (Suc n)"
proof -
  have previous_position: "n-1 < 2*n" using nonempty by arith
  have center_position: "n < 2*n" using nonempty by arith
  have previous_in: "C (n-1) < 2"
    using valid previous_position by (auto simp: valid_growth_carries_def)
  have previous_carry:
      "C n = decimal_carry (S (n-1)) (C (n-1))"
    using valid previous_position nonempty
    by (auto simp: valid_growth_carries_def)
  have center_carry: "C (Suc n) = decimal_carry (S n) (C n)"
    using valid center_position by (auto simp: valid_growth_carries_def)
  have source: "S n = S (n-1)"
  proof -
    have reflected: "S (n-1) = S (2*n-Suc (n-1))"
      using symmetric_source_at[OF symmetry previous_position] .
    moreover have "2*n-Suc (n-1) = n" using nonempty by arith
    ultimately show ?thesis by simp
  qed
  have "C (Suc n) =
      decimal_carry (S (n-1)) (decimal_carry (S (n-1)) (C (n-1)))"
    using center_carry source previous_carry by simp
  also have "... = decimal_carry (S (n-1)) (C (n-1))"
    using decimal_carry_idempotent[OF previous_in] .
  also have "... = C n" using previous_carry by simp
  finally show ?thesis by simp
qed

theorem growth_interior_coboundary_factorization:
  assumes lower: "0 < i" and upper: "i < L"
      and symmetry: "symmetric_source S L"
  shows "growth_interior_output S C L i =
    growth_q S C i + growth_q S C (i-1) + growth_delta C L i
      - 10 * growth_delta C L (i-1)"
proof -
  have mirror: "S (L-i) = S (i-1)"
  proof -
    have previous_position: "i-1 < L" using lower upper by arith
    have "S (i-1) = S (L-Suc (i-1))"
      using symmetric_source_at[OF symmetry previous_position] .
    moreover have "L-Suc (i-1) = L-i" using lower upper by arith
    ultimately show ?thesis by simp
  qed
  have index: "Suc (i-1) = i" using lower by arith
  have mirror_carry_index: "L-(i-1) = Suc (L-i)"
    using lower upper by arith
  show ?thesis
    unfolding growth_interior_output_def normalized_growth_digit_def
      growth_q_def growth_delta_def
    using mirror index mirror_carry_index by (simp add: algebra_simps)
qed

theorem growth_even_center_coboundary_factorization:
  assumes nonempty: "0 < n" and symmetry: "symmetric_source S (2*n)"
      and valid: "valid_growth_carries S C (2*n)"
  shows "2 * normalized_growth_digit S C n =
    2 * growth_q S C (n-1)"
proof -
  have central_carry: "C n = C (Suc n)"
    using valid_even_growth_central_carry[OF nonempty valid symmetry] .
  have source: "S n = S (n-1)"
  proof -
    have previous_position: "n-1 < 2*n" using nonempty by arith
    have "S (n-1) = S (2*n-Suc (n-1))"
      using symmetric_source_at[OF symmetry previous_position] .
    moreover have "2*n-Suc (n-1) = n" using nonempty by arith
    ultimately show ?thesis by simp
  qed
  have index: "Suc (n-1) = n" using nonempty by arith
  show ?thesis
    unfolding normalized_growth_digit_def growth_q_def
    using source central_carry index by (simp add: algebra_simps)
qed

corollary growth_edge_forward_congruence:
  assumes endpoints_C: "C 0 = 0" "C L = 1"
      and endpoints_D: "D 0 = 0" "D L = 1"
      and quotient_q: "growth_q S C 0 = growth_q T D 0"
      and quotient_delta: "growth_delta C L 0 = growth_delta D L 0"
  shows "growth_edge_output S C = growth_edge_output T D"
  using growth_edge_coboundary_factorization[OF endpoints_C]
    growth_edge_coboundary_factorization[OF endpoints_D]
    quotient_q quotient_delta by simp

corollary growth_interior_forward_congruence:
  assumes lower: "0 < i" and upper: "i < L"
      and symmetry_S: "symmetric_source S L"
      and symmetry_T: "symmetric_source T L"
      and q_i: "growth_q S C i = growth_q T D i"
      and q_previous: "growth_q S C (i-1) = growth_q T D (i-1)"
      and delta_i: "growth_delta C L i = growth_delta D L i"
      and delta_previous:
        "growth_delta C L (i-1) = growth_delta D L (i-1)"
  shows "growth_interior_output S C L i = growth_interior_output T D L i"
  using growth_interior_coboundary_factorization[OF lower upper symmetry_S]
    growth_interior_coboundary_factorization[OF lower upper symmetry_T]
    q_i q_previous delta_i delta_previous by simp

corollary growth_even_center_forward_congruence:
  assumes nonempty: "0 < n"
      and symmetry_S: "symmetric_source S (2*n)"
      and symmetry_T: "symmetric_source T (2*n)"
      and valid_C: "valid_growth_carries S C (2*n)"
      and valid_D: "valid_growth_carries T D (2*n)"
      and quotient_q: "growth_q S C (n-1) = growth_q T D (n-1)"
  shows "2 * normalized_growth_digit S C n =
    2 * normalized_growth_digit T D n"
  using growth_even_center_coboundary_factorization[OF nonempty symmetry_S valid_C]
    growth_even_center_coboundary_factorization[OF nonempty symmetry_T valid_D]
    quotient_q by simp

ML \<open>
  val checked = @{thms growth_q_residue_view valid_growth_q_is_decimal_view
    radix_pair_sum_carry_bound radix_pair_carry_is_bit
    valid_growth_q_range growth_skew_is_q_difference growth_delta_range
    growth_symbol_has_twelve_forms
    nonzero_growth_skew_requires_equal_domain_source
    growth_edge_coboundary_factorization growth_edge_pair_equation
    palindrome_nth_reflect growth_digits_append_one
    growth_reflection_shift
    no_growth_pair_output_expanded no_growth_symmetric_pair_formula
    no_growth_symmetric_pair_affine
    fixed_radix_carry_guard_interval no_growth_fixed_carry_endpoint_admission
    no_growth_affine_iter_closed
    no_growth_affine_step_mono_nonnegative
    no_growth_affine_step_mono_nonpositive
    no_growth_affine_iter_mono_nonnegative
    no_growth_affine_iter_mono_nonpositive
    no_growth_affine_chamber_between_nonnegative
    no_growth_affine_chamber_between_nonpositive
    growth_first_output_pair_zero growth_first_output_pair_last
    growth_edge_source_formula
    growth_first_output_pair_interior growth_symmetric_interior_source_formula
    growth_first_output_pair_source_formula
    decimal_carry_idempotent valid_even_growth_central_carry
    growth_interior_coboundary_factorization
    growth_even_center_coboundary_factorization
    growth_edge_forward_congruence growth_interior_forward_congruence
    growth_even_center_forward_congruence};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Growth coboundary proof depends on an oracle";
\<close>

end
