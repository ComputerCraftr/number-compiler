theory Prime_Prefix_Image_Projection_Refinement
  imports Prime_Python_Count_Transition_Refinement
begin

text \<open>This theory connects the checked deterministic Phi evaluator to the
zero-phase, single-forbidden-residue prefix image observed by
\<open>PrimeSuccessorActionArena.rank_before\<close>.  The semantic list is used only
for the proof: production constructs \<open>prefix(width)\<close> by binary action
composition and does not materialize these marks.\<close>

definition zero_phase_prefix_word ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "zero_phase_prefix_word parent q W =
    fresh_block_word (wheel_sift (rev parent) {1..W}) q {0} 0 W"

lemma zero_phase_prefix_word_length [simp]:
  "length (zero_phase_prefix_word parent q W) = W"
  by (simp add: zero_phase_prefix_word_def fresh_block_word_def)

theorem zero_phase_prefix_rank_exact:
  assumes stop: "stop \<le> W"
    and distinct: "distinct (parent @ [q])"
    and primes: "\<forall>p \<in> set (parent @ [q]). prime p"
  shows "mark_rank_before (zero_phase_prefix_word parent q W) stop =
    numerical_Phi (parent @ [q]) (Suc (length parent)) stop"
proof -
  let ?indices =
    "filter (\<lambda>i. fresh_mark (wheel_sift (rev parent) {1..W})
      q {0} 0 (Suc i)) [0..<stop]"
  have rank_indices:
      "mark_rank_before (zero_phase_prefix_word parent q W) stop =
        length ?indices"
  proof -
    have take_indices: "take stop [0..<W] = [0..<stop]"
      using stop by simp
    show ?thesis
      by (simp only: mark_rank_before_def zero_phase_prefix_word_def
          fresh_block_word_def take_map take_indices filter_map length_map
          o_def id_def)
  qed
  have distinct_indices: "distinct ?indices" by simp
  have list_card: "length ?indices = card (set ?indices)"
    using distinct_card[OF distinct_indices] by simp
  have image_card: "card (Suc ` set ?indices) = card (set ?indices)"
    by (rule card_image) simp
  have rank_card:
      "mark_rank_before (zero_phase_prefix_word parent q W) stop =
        card (Suc ` set ?indices)"
    using rank_indices list_card image_card by simp
  have q_prime: "prime q" using primes by simp
  have q_positive: "0 < q"
    using prime_gt_1_nat[OF q_prime] by simp
  have marked_set:
      "Suc ` set ?indices = wheel_sift (q # rev parent) {1..stop}"
  proof (rule Set.set_eqI)
    fix n
    show "n \<in> Suc ` set ?indices \<longleftrightarrow>
        n \<in> wheel_sift (q # rev parent) {1..stop}"
    proof (cases n)
      case 0
      then show ?thesis
        by (simp add: wheel_sift_membership)
    next
      case (Suc i)
      then show ?thesis
        using stop q_positive
        by (auto simp: fresh_mark_def wheel_sift_membership
            mod_eq_0_iff_dvd)
    qed
  qed
  have semantic:
      "numerical_Phi (parent @ [q]) (Suc (length parent)) stop =
        card (wheel_sift (q # rev parent) {1..stop})"
    by (rule fresh_successor_partial_count_semantics[OF distinct primes])
  show ?thesis using rank_card marked_set semantic by simp
qed

corollary zero_phase_prefix_rank_extension:
  assumes first: "stop \<le> W" and extension: "W \<le> W'"
    and distinct: "distinct (parent @ [q])"
    and primes: "\<forall>p \<in> set (parent @ [q]). prime p"
  shows "mark_rank_before (zero_phase_prefix_word parent q W) stop =
    mark_rank_before (zero_phase_prefix_word parent q W') stop"
proof -
  have later: "stop \<le> W'" using first extension by simp
  show ?thesis
    using zero_phase_prefix_rank_exact[OF first distinct primes]
      zero_phase_prefix_rank_exact[OF later distinct primes]
    by simp
qed

lemma zero_phase_prefix_rank_interval:
  assumes lower: "1 \<le> lo" and order: "lo \<le> hi"
    and cached: "hi - 1 \<le> W"
    and distinct: "distinct (parent @ [q])"
    and primes: "\<forall>p \<in> set (parent @ [q]). prime p"
  shows
    "mark_rank_before (zero_phase_prefix_word parent q W) (hi - 1) -
       mark_rank_before (zero_phase_prefix_word parent q W) (lo - 1) =
     card (wheel_half_open (q # rev parent) lo hi)"
proof -
  let ?full = "parent @ [q]"
  let ?high = "wheel_sift (q # rev parent) {1..hi - 1}"
  let ?low = "wheel_sift (q # rev parent) {1..lo - 1}"
  have low_cached: "lo - 1 \<le> W" using order cached by arith
  have high_rank:
      "mark_rank_before (zero_phase_prefix_word parent q W) (hi - 1) =
        card ?high"
    using zero_phase_prefix_rank_exact[OF cached distinct primes]
      fresh_successor_partial_count_semantics[OF distinct primes,
        of "hi - 1"]
    by simp
  have low_rank:
      "mark_rank_before (zero_phase_prefix_word parent q W) (lo - 1) =
        card ?low"
    using zero_phase_prefix_rank_exact[OF low_cached distinct primes]
      fresh_successor_partial_count_semantics[OF distinct primes,
        of "lo - 1"]
    by simp
  have finite_low: "finite ?low" by (rule finite_wheel_sift) simp
  have subset: "?low \<subseteq> ?high" using order
    by (auto simp: wheel_sift_membership)
  have difference:
      "?high - ?low = wheel_half_open (q # rev parent) lo hi"
    using lower order
    by (auto simp: wheel_half_open_def wheel_sift_membership)
  show ?thesis
    using high_rank low_rank card_Diff_subset[OF finite_low subset] difference
    by simp
qed

fun ordered_cyclotomic_divisor_terms :: "nat list \<Rightarrow>
    (nat \<times> int) list" where
  "ordered_cyclotomic_divisor_terms [] = [(1, 1)]"
| "ordered_cyclotomic_divisor_terms (q # qs) =
    ordered_cyclotomic_divisor_terms qs @
      map (\<lambda>(divisor, sign). (divisor * q, -sign))
        (ordered_cyclotomic_divisor_terms qs)"

definition ordered_cyclotomic_term_value ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<times> int \<Rightarrow> int" where
  "ordered_cyclotomic_term_value base limit term =
    (case term of (divisor, sign) \<Rightarrow>
      sign * int (numerical_Phi base (length base) (limit div divisor)))"

definition ordered_cyclotomic_suffix_projection ::
    "nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> int" where
  "ordered_cyclotomic_suffix_projection base suffix limit =
    sum_list (map (ordered_cyclotomic_term_value base limit)
      (ordered_cyclotomic_divisor_terms (rev suffix)))"

lemma sum_list_neg_map_int:
  fixes f :: "'a \<Rightarrow> int"
  shows "sum_list (map (\<lambda>item. - f item) items) =
    - sum_list (map f items)"
  by (induction items) (simp_all add: algebra_simps)

lemma ordered_cyclotomic_suffix_projection_append:
  "ordered_cyclotomic_suffix_projection base (suffix @ [q]) limit =
    ordered_cyclotomic_suffix_projection base suffix limit -
      ordered_cyclotomic_suffix_projection base suffix (limit div q)"
proof -
  let ?terms = "ordered_cyclotomic_divisor_terms (rev suffix)"
  let ?extend = "\<lambda>(divisor, sign). (divisor * q, - sign)"
  have quotient:
    "limit div (divisor * q) = (limit div q) div divisor"
    for divisor
    by (simp add: div_mult2_eq[symmetric] mult.commute)
  have term_value:
    "ordered_cyclotomic_term_value base limit (?extend entry) =
      - ordered_cyclotomic_term_value base (limit div q) entry"
    for entry
  proof (cases entry)
    case (Pair divisor sign)
    have phi_equal:
      "numerical_Phi base (length base) (limit div (divisor * q)) =
        numerical_Phi base (length base) (limit div q div divisor)"
      using quotient by simp
    show ?thesis
      using Pair phi_equal
      unfolding ordered_cyclotomic_term_value_def
      by (simp add: algebra_simps)
  qed
  have transformed:
    "map (ordered_cyclotomic_term_value base limit) (map ?extend ?terms) =
      map (\<lambda>term. - ordered_cyclotomic_term_value base (limit div q) term)
        ?terms"
    by (induction ?terms) (simp_all add: term_value)
  have transformed_sum:
    "sum_list (map (ordered_cyclotomic_term_value base limit) (map ?extend ?terms)) =
      - sum_list (map (ordered_cyclotomic_term_value base (limit div q)) ?terms)"
    using transformed by (simp only: sum_list_neg_map_int)
  have terms:
    "ordered_cyclotomic_divisor_terms (rev (suffix @ [q])) =
      ?terms @ map ?extend ?terms"
    by (simp add: ordered_cyclotomic_divisor_terms.simps)
  show ?thesis
    unfolding ordered_cyclotomic_suffix_projection_def
    using terms transformed_sum
    by (simp add: sum_list_append algebra_simps)
qed

lemma ordered_cyclotomic_divisor_terms_length:
  "length (ordered_cyclotomic_divisor_terms factors) = 2 ^ length factors"
  by (induction factors) simp_all

lemma numerical_Phi_append_prefix:
  assumes depth: "depth \<le> length prefix"
  shows "numerical_Phi (prefix @ suffix) depth limit =
    numerical_Phi prefix depth limit"
  using depth
proof (induction depth arbitrary: prefix limit)
  case 0
  then show ?case by simp
next
  case (Suc depth)
  have index: "depth < length prefix" using Suc.prems by simp
  have indexed_factor: "(prefix @ suffix) ! depth = prefix ! depth"
    using index by (simp add: nth_append)
  have left:
    "numerical_Phi (prefix @ suffix) depth limit =
      numerical_Phi prefix depth limit"
    by (rule Suc.IH) (use Suc.prems in simp)
  have right:
    "numerical_Phi (prefix @ suffix) depth (limit div (prefix ! depth)) =
      numerical_Phi prefix depth (limit div (prefix ! depth))"
    by (rule Suc.IH) (use Suc.prems in simp)
  show ?case
    using indexed_factor left right
    by (simp only: numerical_Phi.simps indexed_factor left right)
qed

corollary ordered_cyclotomic_four_factor_packet_bounded:
  assumes "length suffix \<le> 4"
  shows "length (ordered_cyclotomic_divisor_terms (rev suffix)) \<le> 16"
proof -
  have base_ge_one: "(1::nat) \<le> 2" by arith
  have power_bound: "(2::nat) ^ length suffix \<le> 2 ^ 4"
    by (rule power_increasing[OF assms base_ge_one])
  have term_count:
    "length (ordered_cyclotomic_divisor_terms (rev suffix)) =
      2 ^ length suffix"
    using ordered_cyclotomic_divisor_terms_length[of "rev suffix"] by simp
  have numeric_bound: "(2::nat) ^ length suffix \<le> (16::nat)"
    using power_bound by simp
  show ?thesis using term_count numeric_bound by linarith
qed

theorem ordered_cyclotomic_suffix_projection_exact:
  assumes distinct: "distinct (base @ suffix)"
      and primes: "\<forall>p \<in> set (base @ suffix). prime p"
  shows "int (numerical_Phi (base @ suffix)
        (length base + length suffix) limit) =
    ordered_cyclotomic_suffix_projection base suffix limit"
  using distinct primes
proof (induction suffix arbitrary: limit rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: ordered_cyclotomic_suffix_projection_def
        ordered_cyclotomic_term_value_def)
next
  case (snoc q suffix)
  let ?parent = "base @ suffix"
  let ?full = "?parent @ [q]"
  have full_distinct: "distinct ?full" using snoc.prems(1) by simp
  have full_primes: "\<forall>p \<in> set ?full. prime p"
    using snoc.prems(2) by auto
  have parent_distinct: "distinct ?parent"
    using full_distinct by simp
  have parent_primes: "\<forall>p \<in> set ?parent. prime p"
    using full_primes by auto
  have parent_depth: "length ?parent \<le> length ?full" by simp
  have quotient_le: "limit div q \<le> limit" by simp
  have monotone:
    "numerical_Phi ?full (length ?parent) (limit div q) \<le>
      numerical_Phi ?full (length ?parent) limit"
    by (rule numerical_Phi_mono_limit[OF quotient_le parent_depth
        full_distinct full_primes])
  have recurrence:
    "numerical_Phi ?full (Suc (length ?parent)) limit =
      numerical_Phi ?full (length ?parent) limit -
        numerical_Phi ?full (length ?parent) (limit div q)"
    by (rule fresh_successor_partial_count_equation)
  have prefix_limit:
    "numerical_Phi ?full (length ?parent) limit =
      numerical_Phi ?parent (length ?parent) limit"
    by (rule numerical_Phi_append_prefix) simp
  have prefix_quotient:
    "numerical_Phi ?full (length ?parent) (limit div q) =
      numerical_Phi ?parent (length ?parent) (limit div q)"
    by (rule numerical_Phi_append_prefix) simp
  have integer_recurrence:
    "int (numerical_Phi ?full (Suc (length ?parent)) limit) =
      int (numerical_Phi ?parent (length ?parent) limit) -
        int (numerical_Phi ?parent (length ?parent) (limit div q))"
    using recurrence monotone prefix_limit prefix_quotient
    by (simp add: of_nat_diff)
  have prior_limit:
    "int (numerical_Phi ?parent (length ?parent) limit) =
      ordered_cyclotomic_suffix_projection base suffix limit"
    using snoc.IH[OF parent_distinct parent_primes] by simp
  have prior_quotient:
    "int (numerical_Phi ?parent (length ?parent) (limit div q)) =
      ordered_cyclotomic_suffix_projection base suffix (limit div q)"
    using snoc.IH[OF parent_distinct parent_primes] by simp
  have projected_recurrence:
    "ordered_cyclotomic_suffix_projection base (suffix @ [q]) limit =
      ordered_cyclotomic_suffix_projection base suffix limit -
        ordered_cyclotomic_suffix_projection base suffix (limit div q)"
    by (rule ordered_cyclotomic_suffix_projection_append)
  show ?case
    using integer_recurrence prior_limit prior_quotient projected_recurrence
    by simp
qed

theorem ordered_wheel_210_rank_exact:
  "int (numerical_Phi [2, 3, 5, 7] 4 limit) =
      int limit - int (limit div 2) - int (limit div 3) -
      int (limit div 5) - int (limit div 7) +
      int (limit div 6) + int (limit div 10) + int (limit div 14) +
      int (limit div 15) + int (limit div 21) + int (limit div 35) -
      int (limit div 30) - int (limit div 42) - int (limit div 70) -
      int (limit div 105) + int (limit div 210)"
proof -
  have exact:
    "int (numerical_Phi [2, 3, 5, 7] 4 limit) =
      ordered_cyclotomic_suffix_projection [] [2, 3, 5, 7] limit"
  proof -
    have distinct: "distinct (([]::nat list) @ [2, 3, 5, 7])" by simp
    have prime_two: "prime (2::nat)" by simp
    have prime_three: "prime (3::nat)" by simp
    have prime_five: "prime (5::nat)" by simp
    have prime_seven: "prime (7::nat)" by simp
    have primes: "\<forall>p \<in> set (([]::nat list) @ [2, 3, 5, 7]). prime p"
      using prime_two prime_three prime_five prime_seven by auto
    have append_empty:
      "([]::nat list) @ ([2, 3, 5, 7]::nat list) =
        ([2, 3, 5, 7]::nat list)"
      by simp
    have empty_length: "length ([]::nat list) = 0" by simp
    have factor_length: "length ([2, 3, 5, 7]::nat list) = 4" by simp
    have depth:
      "length ([]::nat list) + length ([2, 3, 5, 7]::nat list) = 4"
      using empty_length factor_length by simp
    have projected:
      "int (numerical_Phi (([]::nat list) @ ([2, 3, 5, 7]::nat list))
          (length ([]::nat list) + length ([2, 3, 5, 7]::nat list)) limit) =
        ordered_cyclotomic_suffix_projection ([]::nat list) ([2, 3, 5, 7]::nat list) limit"
      by (rule ordered_cyclotomic_suffix_projection_exact[OF distinct primes])
    show ?thesis using projected append_empty depth
      by (simp only: append_empty depth)
  qed
  have expansion:
    "ordered_cyclotomic_suffix_projection [] [2, 3, 5, 7] limit =
      int limit - int (limit div 2) - int (limit div 3) -
      int (limit div 5) - int (limit div 7) +
      int (limit div 6) + int (limit div 10) + int (limit div 14) +
      int (limit div 15) + int (limit div 21) + int (limit div 35) -
      int (limit div 30) - int (limit div 42) - int (limit div 70) -
      int (limit div 105) + int (limit div 210)"
    unfolding ordered_cyclotomic_suffix_projection_def
    by (simp add: ordered_cyclotomic_divisor_terms.simps
        ordered_cyclotomic_term_value_def; presburger)
  show ?thesis by (rule trans[OF exact expansion])
qed

theorem ordered_wheel_2310_boundary_rank:
  "numerical_Phi [2, 3, 5, 7, 11] 5 2310 = 480"
proof -
  have five_as_suc: "(5::nat) = Suc 4" by simp
  have last_factor: "([2, 3, 5, 7, 11]::nat list) ! 4 = 11"
    by simp
  have successor_equation:
    "numerical_Phi [2, 3, 5, 7, 11] (Suc 4) 2310 =
      numerical_Phi [2, 3, 5, 7, 11] 4 2310 -
        numerical_Phi [2, 3, 5, 7, 11] 4
          (2310 div (([2, 3, 5, 7, 11]::nat list) ! 4))"
    by (rule numerical_Phi.simps(2))
  have recurrence:
    "numerical_Phi [2, 3, 5, 7, 11] 5 2310 =
      numerical_Phi [2, 3, 5, 7, 11] 4 2310 -
        numerical_Phi [2, 3, 5, 7, 11] 4 (2310 div 11)"
    using successor_equation five_as_suc last_factor
    by (simp only: successor_equation five_as_suc last_factor)
  have prefix_2310:
    "numerical_Phi (([2, 3, 5, 7]::nat list) @ [11]) 4 2310 =
      numerical_Phi [2, 3, 5, 7] 4 2310"
    by (rule numerical_Phi_append_prefix) simp
  have prefix_210:
    "numerical_Phi (([2, 3, 5, 7]::nat list) @ [11]) 4 210 =
      numerical_Phi [2, 3, 5, 7] 4 210"
    by (rule numerical_Phi_append_prefix) simp
  have base_2310:
    "numerical_Phi [2, 3, 5, 7] 4 2310 = 528"
    using ordered_wheel_210_rank_exact[of 2310] by simp
  have base_210:
    "numerical_Phi [2, 3, 5, 7] 4 210 = 48"
    using ordered_wheel_210_rank_exact[of 210] by simp
  have full_list:
    "([2, 3, 5, 7]::nat list) @ [11] = [2, 3, 5, 7, 11]"
    by simp
  have divisor: "(2310::nat) div 11 = 210" by simp
  have recurrence_literal:
    "numerical_Phi [2, 3, 5, 7, 11] 5 2310 =
      numerical_Phi [2, 3, 5, 7, 11] 4 2310 -
        numerical_Phi [2, 3, 5, 7, 11] 4 210"
    using recurrence divisor by (simp only: divisor)
  have full_2310:
    "numerical_Phi [2, 3, 5, 7, 11] 4 2310 = 528"
    using prefix_2310 base_2310
    by (simp only: full_list[symmetric] prefix_2310 base_2310)
  have full_210:
    "numerical_Phi [2, 3, 5, 7, 11] 4 210 = 48"
    using prefix_210 base_210
    by (simp only: full_list[symmetric] prefix_210 base_210)
  show ?thesis
    using recurrence_literal full_2310 full_210 by simp
qed

theorem complete_prefix_cached_image_interval_exact:
  assumes prefix: "complete_prime_prefix (parent @ [q]) H"
    and lower: "2 \<le> lo"
    and order: "lo \<le> hi"
    and upper: "hi \<le> Suc H"
    and cached: "hi - 1 \<le> W"
  shows
    "card {p \<in> set (parent @ [q]). lo \<le> p \<and> p < hi} +
       (mark_rank_before (zero_phase_prefix_word parent q W) (hi - 1) -
        mark_rank_before (zero_phase_prefix_word parent q W) (lo - 1)) =
     card {p. prime p \<and> lo \<le> p \<and> p < hi}"
proof -
  have nonempty: "parent @ [q] \<noteq> []" by simp
  have distinct: "distinct (parent @ [q])"
    using complete_prime_prefix_distinct_sorted[OF prefix] by simp
  have primes: "\<forall>p \<in> set (parent @ [q]). prime p"
    using complete_prime_prefix_set[OF prefix] by auto
  have rank_interval:
      "mark_rank_before (zero_phase_prefix_word parent q W) (hi - 1) -
         mark_rank_before (zero_phase_prefix_word parent q W) (lo - 1) =
       card (wheel_half_open (q # rev parent) lo hi)"
    by (rule zero_phase_prefix_rank_interval)
      (use lower order cached distinct primes in auto)
  have exact:
      "card {p \<in> set (parent @ [q]). lo \<le> p \<and> p < hi} +
         card (wheel_half_open (rev (parent @ [q])) lo hi) =
       card {p. prime p \<and> lo \<le> p \<and> p < hi}"
    by (rule complete_prefix_half_open_prime_count[OF prefix nonempty lower
          order upper])
  show ?thesis using rank_interval exact by simp
qed

text \<open>The first theorem is the arithmetic observation used by
\<open>successor_action.py:496-507\<close>.  The extension corollary justifies
projecting an earlier stop from the larger image retained at
\<open>partial_successor_image.py:141-160\<close>, and the final theorem is the
two-rank-plus-known-prefix result returned at lines 163-166 when the caller
uses the whole admitted factor prefix, as \<open>select.py:267\<close> does.

The theory does not identify Python arena handles with this word, prove that
binary \<open>prefix\<close> construction preserves width, authenticate scheduler
images, or refine \<open>PrimeSuccessorActionArena.select\<close>.  It also leaves
the routine representation lemma equating Python's sorted-list
\<open>bisect_right\<close> difference with the finite descriptor cardinality to
a future source-language refinement.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms ordered_cyclotomic_suffix_projection_append
      ordered_cyclotomic_divisor_terms_length
      ordered_cyclotomic_four_factor_packet_bounded
      ordered_cyclotomic_suffix_projection_exact
      ordered_wheel_210_rank_exact ordered_wheel_2310_boundary_rank
      numerical_Phi_append_prefix
      zero_phase_prefix_rank_exact zero_phase_prefix_rank_extension
      zero_phase_prefix_rank_interval
      complete_prefix_cached_image_interval_exact}) then ()
    else error "Prime prefix image projection refinement depends on an oracle";
\<close>

end
