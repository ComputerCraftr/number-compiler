theory Five_Bit_Folded_Square
  imports Temporal_Clock_Jumps
begin

text \<open>The two low component residues of the five-bit folded-square
projection form a 32-element packet.  This theory proves only the finite
arithmetic factorization.  Using the packet for a Fermat or Mersenne carrier
still requires a separate theorem that its admitted observable factors through
these two residues.\<close>

type_synonym folded_square_packet = "nat \<times> nat"

definition residue_packet :: "int \<Rightarrow> int \<Rightarrow> folded_square_packet" where
  "residue_packet r1 r2 = (nat (r1 mod 4), nat (r2 mod 8))"

definition folded_packet_space :: "folded_square_packet set" where
  "folded_packet_space = {0..<4} \<times> {0..<8}"

definition folded_r1 :: "int \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "folded_r1 c1 c w s = c1 + s * c (w + 1)"

definition folded_r2 :: "int \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "folded_r2 c2 c w s = c2 + s * c (w + 2)"

definition folded_square_projection ::
  "int \<Rightarrow> int \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int \<Rightarrow>
    folded_square_packet" where
  "folded_square_projection c1 c2 c w s =
    residue_packet (folded_r1 c1 c w s) (folded_r2 c2 c w s)"

definition full_fold_coefficient ::
  "(nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "full_fold_coefficient c w s k =
    (\<Sum>j<2*w. if j mod w = k then (if j < w then c j else s * c j) else 0)"

definition packet_zero :: "folded_square_packet \<Rightarrow> bool" where
  "packet_zero p \<longleftrightarrow> fst p = 0 \<and> snd p = 0"

lemma int_mod_add_factor:
  "(a + b :: int) mod m = ((a mod m) + (b mod m)) mod m"
  by (simp add: mod_add_eq)

lemma int_mod_mult_factor:
  "(a * b :: int) mod m = ((a mod m) * (b mod m)) mod m"
  by (simp add: mod_mult_left_eq mod_mult_right_eq)

lemma residue_packet_bounds:
  "residue_packet r1 r2 \<in> folded_packet_space"
proof -
  have nonnegative_4: "0 \<le> r1 mod 4" by simp
  have nonnegative_8: "0 \<le> r2 mod 8" by simp
  have bound_4: "nat (r1 mod 4) < 4"
    using nonnegative_4 by (simp add: nat_less_iff)
  have bound_8: "nat (r2 mod 8) < 8"
    using nonnegative_8 by (simp add: nat_less_iff)
  show ?thesis using bound_4 bound_8
    by (simp add: residue_packet_def folded_packet_space_def)
qed

lemma folded_packet_space_card:
  "card folded_packet_space = 32"
  by (simp add: folded_packet_space_def)

lemma folded_projection_equations:
  "folded_square_projection c1 c2 c w s =
    (nat ((c1 + s * c (w + 1)) mod 4),
     nat ((c2 + s * c (w + 2)) mod 8))"
  by (simp add: folded_square_projection_def residue_packet_def
    folded_r1_def folded_r2_def)

lemma folded_projection_in_space:
  "folded_square_projection c1 c2 c w s \<in> folded_packet_space"
  by (simp add: folded_square_projection_def residue_packet_bounds)

lemma two_period_residue_positions:
  fixes w k j :: nat
  assumes positive: "0 < w" and below: "k < w"
      and range: "j < 2*w" and residue: "j mod w = k"
  shows "j = k \<or> j = w + k"
proof -
  have quotient: "j div w < 2"
    using range by (simp only: div_less_iff_less_mult[OF positive])
  have decomposition: "j = (j div w) * w + k"
    using div_mult_mod_eq[of j w] residue by arith
  from quotient have "j div w = 0 \<or> j div w = 1" by arith
  with decomposition show ?thesis by auto
qed

lemma full_fold_coefficient_two_terms:
  assumes positive: "0 < w" and below: "k < w"
  shows "full_fold_coefficient c w s k = c k + s * c (w + k)"
proof -
  have classify:
    "\<And>j. j < 2*w \<Longrightarrow> (j mod w = k) = (j = k \<or> j = w + k)"
  proof -
    fix j
    assume range: "j < 2*w"
    have forward:
      "j mod w = k \<Longrightarrow> j = k \<or> j = w + k"
      by (rule two_period_residue_positions[OF positive below range])
    show "(j mod w = k) = (j = k \<or> j = w + k)"
      using forward positive below by auto
  qed
  have first_member: "k < 2*w" using positive below by arith
  have second_member: "w + k < 2*w" using below by arith
  have distinct: "k \<noteq> w + k" using positive by arith
  let ?term =
    "\<lambda>j. if j mod w = k then (if j < w then c j else s * c j) else 0"
  have reduced:
    "(\<Sum>j<2*w. ?term j) = (\<Sum>j\<in>{k, w + k}. ?term j)"
  proof (rule sum.mono_neutral_cong_right)
    show "finite {..<2*w}" by simp
    show "{k, w + k} \<subseteq> {..<2*w}"
      using first_member second_member by auto
    show "\<forall>j \<in> {..<2*w} - {k, w + k}. ?term j = 0"
      using classify by auto
    show "\<And>j. j \<in> {k, w + k} \<Longrightarrow> ?term j = ?term j" by simp
  qed
  show ?thesis
    unfolding full_fold_coefficient_def
    using reduced distinct positive below
    by simp
qed

lemma folded_square_projection_from_full_fold:
  assumes width: "3 \<le> w"
  shows
    "folded_square_projection (c 1) (c 2) c w s =
      residue_packet (full_fold_coefficient c w s 1)
        (full_fold_coefficient c w s 2)"
proof -
  have positive: "0 < w" and one: "1 < w" and two: "2 < w"
    using width by arith+
  have fold_one:
    "full_fold_coefficient c w s 1 = c 1 + s * c (w + 1)"
    by (rule full_fold_coefficient_two_terms[OF positive one])
  have fold_two:
    "full_fold_coefficient c w s 2 = c 2 + s * c (w + 2)"
    by (rule full_fold_coefficient_two_terms[OF positive two])
  show ?thesis
    unfolding folded_square_projection_def folded_r1_def folded_r2_def
    using fold_one fold_two by metis
qed

lemma residue_congruence_determines_packet:
  assumes r1: "r1 mod 4 = r1' mod 4"
      and r2: "r2 mod 8 = r2' mod 8"
  shows "residue_packet r1 r2 = residue_packet r1' r2'"
  using r1 r2 by (simp add: residue_packet_def)

lemma component_congruence_determines_projection:
  assumes first:
    "(c1 + s * c (w + 1)) mod 4 =
      (c1' + s' * c' (w' + 1)) mod 4"
      and second:
    "(c2 + s * c (w + 2)) mod 8 =
      (c2' + s' * c' (w' + 2)) mod 8"
  shows
    "folded_square_projection c1 c2 c w s =
      folded_square_projection c1' c2' c' w' s'"
  using first second
  by (simp add: folded_square_projection_def residue_packet_def
    folded_r1_def folded_r2_def)

lemma component_congruence_preserves_zero_predicate:
  assumes first:
    "(c1 + s * c (w + 1)) mod 4 =
      (c1' + s' * c' (w' + 1)) mod 4"
      and second:
    "(c2 + s * c (w + 2)) mod 8 =
      (c2' + s' * c' (w' + 2)) mod 8"
  shows
    "packet_zero (folded_square_projection c1 c2 c w s) =
      packet_zero (folded_square_projection c1' c2' c' w' s')"
  using component_congruence_determines_projection[OF first second] by simp

lemma signed_folded_projection:
  assumes "s = 1 \<or> s = -1"
  shows
    "folded_square_projection c1 c2 c w s =
      residue_packet (c1 + s * c (w + 1)) (c2 + s * c (w + 2))"
  using assms by (simp add: folded_square_projection_def folded_r1_def folded_r2_def)

text \<open>The following transfer is deliberately conditional.  The premise
is the missing admitted-corpus theorem: the real consumer must be shown to be
a function of this packet before the 32-state arithmetic result can replace
its existing observation.\<close>

lemma conditional_packet_consumer_transfer:
  fixes observe :: "folded_square_packet \<Rightarrow> 'b"
    and encode :: "'s \<Rightarrow> folded_square_packet"
  assumes factor: "\<And>x. x \<in> admitted \<Longrightarrow> exact x = observe (encode x)"
      and member: "x \<in> admitted"
      and same: "encode x = encode y"
      and member_y: "y \<in> admitted"
  shows "exact x = exact y"
  using factor member member_y same by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms int_mod_add_factor int_mod_mult_factor residue_packet_bounds
      folded_packet_space_card folded_projection_equations
      folded_projection_in_space two_period_residue_positions
      full_fold_coefficient_two_terms folded_square_projection_from_full_fold
      residue_congruence_determines_packet
      component_congruence_determines_projection
      component_congruence_preserves_zero_predicate signed_folded_projection
      conditional_packet_consumer_transfer})
    then () else error "Five-bit folded-square proof depends on an oracle";
\<close>

end
