theory Cylinder_Radial_Sections
  imports Cylinder_Innovation_Transport
begin

text \<open>
  A bounded polynomial identity for the radial reverse/add multiplier.
  This theory is coefficient algebra only: it carries no source occurrence,
  carry admission, temporal grammar, or construction bound.
\<close>

definition radial_term ::
    "'a::comm_ring_1 => nat => nat => 'a" where
  "radial_term z h j =
    of_nat (h choose j) * (2*z)^j * (1 + z^2)^(h-j)"

definition radial_full ::
    "'a::comm_ring_1 => nat => 'a" where
  "radial_full z h = (\<Sum>j\<le>h. radial_term z h j)"

definition radial_truncated ::
    "'a::comm_ring_1 => nat => nat => 'a" where
  "radial_truncated z bits h =
    (\<Sum>j\<in>{j. j \<le> h \<and> j < bits}. radial_term z h j)"

lemma radial_two_square:
  fixes z :: "'a::comm_ring_1"
  shows "(1 + z)^2 = (1 + z^2) + 2*z"
  by (simp add: power2_eq_square algebra_simps)

lemma radial_binomial_identity:
  fixes z :: "'a::comm_ring_1"
  shows "(1 + z)^(2*h + e) =
      radial_full z h * (1 + z)^e"
proof -
  have full: "((1 + z)^2)^h = radial_full z h"
    unfolding radial_full_def radial_term_def
    using binomial_ring[of "2*z" "1 + z^2" h]
    by (simp only: radial_two_square add.commute)
  show ?thesis
    by (simp only: power_add power_mult full)
qed

lemma radial_high_power_zero:
  fixes z :: "'a::comm_ring_1"
  assumes nilpotent: "(2::'a)^bits = 0" and high: "bits \<le> j"
  shows "(2*z)^j = 0"
proof -
  obtain k where split: "j = bits + k"
    using high by (auto simp add: le_iff_add)
  have power_zero: "(2::'a)^j = 0"
    using nilpotent split by (simp add: power_add)
  show ?thesis
    using power_zero by (simp add: power_mult_distrib)
qed

lemma radial_truncation:
  fixes z :: "'a::comm_ring_1"
  assumes nilpotent: "(2::'a)^bits = 0"
  shows "radial_full z h = radial_truncated z bits h"
proof -
  let ?all = "{..<Suc h}"
  let ?kept = "{j. j \<le> h \<and> j < bits}"
  have finite_all: "finite ?all" by simp
  have kept_subset: "?kept \<subseteq> ?all" by auto
  have zero_outside:
      "\<forall>j \<in> ?all - ?kept. radial_term z h j = 0"
  proof
    fix j
    assume member: "j \<in> ?all - ?kept"
    have jbound: "j \<le> h" using member by auto
    have high: "bits \<le> j" using member by auto
    have zero: "(2*z)^j = 0"
      using radial_high_power_zero[OF nilpotent high] .
    show "radial_term z h j = 0"
      unfolding radial_term_def using zero by simp
  qed
  have reduced:
      "(\<Sum>j\<in>?all. radial_term z h j) =
        (\<Sum>j\<in>?kept. radial_term z h j)"
    by (rule sum.mono_neutral_cong_right)
       (use finite_all kept_subset zero_outside in auto)
  show ?thesis
    unfolding radial_full_def radial_truncated_def
    using reduced by (simp only: lessThan_Suc_atMost)
qed

theorem radial_truncated_identity:
  fixes z :: "'a::comm_ring_1"
  assumes nilpotent: "(2::'a)^bits = 0"
  shows "(1 + z)^(2*h + e) =
      radial_truncated z bits h * (1 + z)^e"
proof -
  have truncated: "radial_full z h = radial_truncated z bits h"
    by (rule radial_truncation[OF nilpotent])
  show ?thesis using radial_binomial_identity[of z h e] truncated by simp
qed

lemma radial_scaled_truncation:
  fixes z :: "'a::comm_ring_1"
  assumes nilpotent: "(2::'a)^bits = 0"
  shows "2^q * radial_full z h =
    2^q * radial_truncated z (bits-q) h"
proof -
  let ?all = "{..h}"
  let ?kept = "{j. j \<le> h \<and> j < bits-q}"
  have zero_outside: "\<forall>j \<in> ?all - ?kept. 2^q * radial_term z h j = 0"
  proof
    fix j
    assume member: "j \<in> ?all - ?kept"
    have high: "bits \<le> q+j" using member by auto
    have zero: "(2::'a)^(q+j) = 0"
      using radial_high_power_zero[OF nilpotent high, of 1] by simp
    have factor: "2^q * radial_term z h j =
      of_nat (h choose j) * 2^(q+j) * z^j * (1+z^2)^(h-j)"
      by (simp add: radial_term_def power_mult_distrib power_add algebra_simps)
    show "2^q * radial_term z h j = 0" using factor zero by simp
  qed
  have reduced:
    "(\<Sum>j\<in>?all. 2^q * radial_term z h j) =
      (\<Sum>j\<in>?kept. 2^q * radial_term z h j)"
    by (rule sum.mono_neutral_cong_right) (use zero_outside in auto)
  show ?thesis
    unfolding radial_full_def radial_truncated_def
    using reduced by (simp only: sum_distrib_left)
qed

theorem radial_scaled_identity:
  fixes z :: "'a::comm_ring_1"
  assumes nilpotent: "(2::'a)^bits = 0"
  shows "2^q * (1+z)^(2*h+e) =
    (2^q * radial_truncated z (bits-q) h) * (1+z)^e"
  using radial_binomial_identity[of z h e]
    radial_scaled_truncation[OF nilpotent, where z=z and q=q and h=h]
  by (simp only: mult.assoc[symmetric])

lemma radial_retained_indices:
  "card {j::nat. j \<le> h \<and> j < bits} = min bits (Suc h)"
proof -
  have sets: "{j::nat. j \<le> h \<and> j < bits} = {..<min bits (Suc h)}"
    by auto
  show ?thesis by (simp only: sets card_lessThan)
qed

definition section_lane :: "int => int => int => int" where
  "section_lane slope lane offset =
    (slope * lane + offset) mod 2"

definition section_offset :: "int => int => int => int => int" where
  "section_offset slope lane offset i =
    slope * i + (slope * lane + offset) div 2"

lemma signed_section_chart:
  fixes slope lane offset i :: int
  assumes slope_one: "slope = 1 \<or> slope = -1"
  shows "slope * (2*i + lane) + offset =
      2 * section_offset slope lane offset i +
        section_lane slope lane offset"
proof -
  have decomposition:
      "slope * lane + offset =
        2 * ((slope * lane + offset) div 2) +
          (slope * lane + offset) mod 2"
    using div_mult_mod_eq[of "slope * lane + offset" 2]
    by (simp add: algebra_simps)
  show ?thesis
    unfolding section_offset_def section_lane_def
    using decomposition by (simp add: algebra_simps)
qed

definition cartier_section :: "int => (int => 'a) => int => 'a" where
  "cartier_section lane f i = f (2*i + lane)"

lemma section_lane_bound:
  "0 \<le> section_lane slope lane offset \<and>
    section_lane slope lane offset < 2"
  by (simp add: section_lane_def)

lemma cartier_chart_transport:
  assumes slope: "slope = 1 \<or> slope = -1"
  shows "cartier_section lane (\<lambda>j. f (slope*j + offset)) i =
    cartier_section (section_lane slope lane offset) f
      (section_offset slope lane offset i)"
  unfolding cartier_section_def
  using signed_section_chart[OF slope, of i lane offset] by simp

lemma cartier_neighbor_even:
  "cartier_section 0 (innovation_neighbor f) i =
    cartier_section 0 f i + cartier_section 1 f (i - 1)"
  by (simp add: cartier_section_def innovation_neighbor_def algebra_simps)

lemma cartier_neighbor_odd:
  "cartier_section 1 (innovation_neighbor f) i =
    cartier_section 1 f i + cartier_section 0 f i"
  by (simp add: cartier_section_def innovation_neighbor_def algebra_simps)

text \<open>
  The theorem has at most min(bits,Suc h) retained binomial indices.  It is
  not a finite state bound: each retained coefficient is still an element of
  the ambient ring, and a source/range theorem is required before residues
  can be used as decimal carry decisions.
\<close>

ML \<open>
  val checked = @{thms radial_two_square radial_binomial_identity
    radial_high_power_zero radial_truncation radial_truncated_identity
    radial_scaled_truncation radial_scaled_identity radial_retained_indices
    signed_section_chart section_lane_bound cartier_chart_transport
    cartier_neighbor_even cartier_neighbor_odd};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "radial section identity depends on an oracle";
\<close>

end
