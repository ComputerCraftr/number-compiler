theory Double_Reverse_Packed_Nibble_Boolean_Refinement
  imports Double_Reverse_Packed_Nibble_Word_Refinement
begin

unbundle bit_operations_syntax

text \<open>The production fast path replaces eight equality masks with four
Boolean expressions over the packed source bit planes.  These scalar
definitions state each expression's meaning on one nibble lane.  The
source-plane theorem below composes their exact decimal-lane equivalence with
the packed-word refinement; it does not rely on a sidecar truth table.\<close>

definition double_reverse_nibble_plane_mod_ge_three_boolean :: "nat \<Rightarrow> bool" where
  "double_reverse_nibble_plane_mod_ge_three_boolean d =
    (bit d 3 \<or> (bit d 2 \<and> \<not> bit d 0 \<and> \<not> bit d 1) \<or>
      (bit d 0 \<and> bit d 1 \<and> \<not> bit d 2))"

definition double_reverse_nibble_plane_times_four_bit_two_boolean :: "nat \<Rightarrow> bool" where
  "double_reverse_nibble_plane_times_four_bit_two_boolean d =
    ((bit d 0 \<and> \<not> bit d 1 \<and> \<not> bit d 2) \<or>
      (bit d 2 \<and> \<not> bit d 0))"

definition double_reverse_nibble_plane_mod_equals_two_boolean :: "nat \<Rightarrow> bool" where
  "double_reverse_nibble_plane_mod_equals_two_boolean d =
    (bit d 1 \<and> (bit d 0 = bit d 2))"

definition double_reverse_nibble_plane_high_boolean :: "nat \<Rightarrow> bool" where
  "double_reverse_nibble_plane_high_boolean d =
    (bit d 3 \<or> (bit d 2 \<and> (bit d 0 \<or> bit d 1)))"

theorem double_reverse_nibble_boolean_predicates_exact:
  assumes decimal: "d < 10"
  shows
    "double_reverse_nibble_plane_mod_ge_three_boolean d =
      double_reverse_nibble_plane_mod_ge_three d"
    and
    "double_reverse_nibble_plane_times_four_bit_two_boolean d =
      double_reverse_nibble_plane_times_four_bit_two d"
    and
    "double_reverse_nibble_plane_mod_equals_two_boolean d =
      double_reverse_nibble_plane_mod_equals_two d"
    and
    "double_reverse_nibble_plane_high_boolean d =
      double_reverse_nibble_plane_high d"
proof -
  have cases: "d = 0 \<or> d = 1 \<or> d = 2 \<or> d = 3 \<or> d = 4 \<or>
      d = 5 \<or> d = 6 \<or> d = 7 \<or> d = 8 \<or> d = 9"
    using decimal by arith
  show "double_reverse_nibble_plane_mod_ge_three_boolean d =
      double_reverse_nibble_plane_mod_ge_three d"
    using cases
    by (elim disjE; simp add: double_reverse_nibble_plane_mod_ge_three_boolean_def
        double_reverse_nibble_plane_mod_ge_three_def bit_simps)
  show "double_reverse_nibble_plane_times_four_bit_two_boolean d =
      double_reverse_nibble_plane_times_four_bit_two d"
    using cases
    by (elim disjE;
        simp add: double_reverse_nibble_plane_times_four_bit_two_boolean_def
          double_reverse_nibble_plane_times_four_bit_two_def bit_simps)
  show "double_reverse_nibble_plane_mod_equals_two_boolean d =
      double_reverse_nibble_plane_mod_equals_two d"
    using cases
    by (elim disjE;
        simp add: double_reverse_nibble_plane_mod_equals_two_boolean_def
          double_reverse_nibble_plane_mod_equals_two_def bit_simps)
  show "double_reverse_nibble_plane_high_boolean d =
      double_reverse_nibble_plane_high d"
    using cases
    by (elim disjE;
        simp add: double_reverse_nibble_plane_high_boolean_def
          double_reverse_nibble_plane_high_def bit_simps)
qed

definition double_reverse_packed_nibble_boolean_source_planes ::
    "nat list \<Rightarrow> int \<times> int \<times> int \<times> int" where
  "double_reverse_packed_nibble_boolean_source_planes source_digits =
    (double_reverse_pack16_bits
        (map double_reverse_nibble_plane_mod_ge_three_boolean source_digits),
     double_reverse_pack16_bits
        (map double_reverse_nibble_plane_times_four_bit_two_boolean source_digits),
     double_reverse_pack16_bits
        (map double_reverse_nibble_plane_mod_equals_two_boolean source_digits),
     double_reverse_pack16_bits
        (map double_reverse_nibble_plane_high_boolean source_digits))"

theorem double_reverse_packed_nibble_boolean_source_planes_refine:
  assumes digits: "\<forall>d\<in>set source_digits. d < 10"
  shows "double_reverse_packed_nibble_boolean_source_planes source_digits =
    double_reverse_packed_nibble_source_planes source_digits"
proof -
  have p1:
    "map double_reverse_nibble_plane_mod_ge_three_boolean source_digits =
      map (\<lambda>d. d mod 5 = 3 \<or> d mod 5 = 4) source_digits"
  proof (rule map_cong[OF refl])
    fix d
    assume member: "d \<in> set source_digits"
    have decimal: "d < 10" using digits member by blast
    have boolean_exact:
      "double_reverse_nibble_plane_mod_ge_three_boolean d =
        double_reverse_nibble_plane_mod_ge_three d"
      by (rule double_reverse_nibble_boolean_predicates_exact(1)[OF decimal])
    have selector_exact:
      "double_reverse_nibble_plane_mod_ge_three d =
        (d mod 5 = 3 \<or> d mod 5 = 4)"
      by (rule double_reverse_nibble_planes_exact(1)[OF decimal])
    show "double_reverse_nibble_plane_mod_ge_three_boolean d =
        (d mod 5 = 3 \<or> d mod 5 = 4)"
      using boolean_exact selector_exact by simp
  qed
  have p2:
    "map double_reverse_nibble_plane_times_four_bit_two_boolean source_digits =
      map (\<lambda>d. bit ((4*d) mod 10) 2) source_digits"
  proof (rule map_cong[OF refl])
    fix d
    assume member: "d \<in> set source_digits"
    have decimal: "d < 10" using digits member by blast
    have boolean_exact:
      "double_reverse_nibble_plane_times_four_bit_two_boolean d =
        double_reverse_nibble_plane_times_four_bit_two d"
      by (rule double_reverse_nibble_boolean_predicates_exact(2)[OF decimal])
    have selector_exact:
      "double_reverse_nibble_plane_times_four_bit_two d =
        bit ((4*d) mod 10) 2"
      by (rule double_reverse_nibble_planes_exact(2)[OF decimal])
    show "double_reverse_nibble_plane_times_four_bit_two_boolean d =
        bit ((4*d) mod 10) 2"
      using boolean_exact selector_exact by simp
  qed
  have p3:
    "map double_reverse_nibble_plane_mod_equals_two_boolean source_digits =
      map (\<lambda>d. d mod 5 = 2) source_digits"
  proof (rule map_cong[OF refl])
    fix d
    assume member: "d \<in> set source_digits"
    have decimal: "d < 10" using digits member by blast
    have boolean_exact:
      "double_reverse_nibble_plane_mod_equals_two_boolean d =
        double_reverse_nibble_plane_mod_equals_two d"
      by (rule double_reverse_nibble_boolean_predicates_exact(3)[OF decimal])
    have selector_exact:
      "double_reverse_nibble_plane_mod_equals_two d = (d mod 5 = 2)"
      by (rule double_reverse_nibble_planes_exact(3)[OF decimal])
    show "double_reverse_nibble_plane_mod_equals_two_boolean d =
        (d mod 5 = 2)"
      using boolean_exact selector_exact by simp
  qed
  have p4:
    "map double_reverse_nibble_plane_high_boolean source_digits =
      map (\<lambda>d. 5 \<le> d) source_digits"
  proof (rule map_cong[OF refl])
    fix d
    assume member: "d \<in> set source_digits"
    have decimal: "d < 10" using digits member by blast
    have boolean_exact:
      "double_reverse_nibble_plane_high_boolean d =
        double_reverse_nibble_plane_high d"
      by (rule double_reverse_nibble_boolean_predicates_exact(4)[OF decimal])
    have selector_exact:
      "double_reverse_nibble_plane_high d = (5 \<le> d)"
      by (rule double_reverse_nibble_planes_exact(4)[OF decimal])
    show "double_reverse_nibble_plane_high_boolean d = (5 \<le> d)"
      using boolean_exact selector_exact by simp
  qed
  have source_planes:
    "double_reverse_packed_nibble_source_planes source_digits =
      (double_reverse_pack16_bits
          (map (\<lambda>d. d mod 5 = 3 \<or> d mod 5 = 4) source_digits),
       double_reverse_pack16_bits
          (map (\<lambda>d. bit ((4*d) mod 10) 2) source_digits),
       double_reverse_pack16_bits
          (map (\<lambda>d. d mod 5 = 2) source_digits),
       double_reverse_pack16_bits
          (map (\<lambda>d. 5 \<le> d) source_digits))"
    using double_reverse_packed_nibble_planes_source_exact[OF digits]
    by (simp add: double_reverse_packed_nibble_source_planes_def)
  show ?thesis
    unfolding double_reverse_packed_nibble_boolean_source_planes_def
    by (simp only: source_planes p1 p2 p3 p4)
qed

ML \<open>
  val checked = @{thms
    double_reverse_nibble_boolean_predicates_exact
    double_reverse_packed_nibble_boolean_source_planes_refine};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Packed nibble Boolean refinement depends on an oracle";
\<close>

end
