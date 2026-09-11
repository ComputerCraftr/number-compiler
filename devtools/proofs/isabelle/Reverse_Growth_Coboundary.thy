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
    then show ?thesis using valid by (auto simp: valid_growth_carries_def)
  qed
  have right: "C (Suc i) < 2"
  proof (cases "Suc i = L")
    case True
    then show ?thesis using valid by (simp add: valid_growth_carries_def)
  next
    case False
    with position have "Suc i < L" by arith
    then show ?thesis using valid by (auto simp: valid_growth_carries_def)
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
    valid_growth_q_range growth_skew_is_q_difference growth_delta_range
    growth_symbol_has_twelve_forms
    nonzero_growth_skew_requires_equal_domain_source
    growth_edge_coboundary_factorization
    decimal_carry_idempotent valid_even_growth_central_carry
    growth_interior_coboundary_factorization
    growth_even_center_coboundary_factorization
    growth_edge_forward_congruence growth_interior_forward_congruence
    growth_even_center_forward_congruence};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Growth coboundary proof depends on an oracle";
\<close>

end
