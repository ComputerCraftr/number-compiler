theory Mersenne_Zero_Key_Counterexample
  imports Mersenne_Etale_Zero_Section
begin

text \<open>The zero section exists for every modulus, including composite
Mersenne candidates.  This theory exhibits its actual one-step cyclic
normalization data for M11.  Thus recovery of D=0 from a primary carry key is
not a primality decision unless a separately proved terminal/all-local
publisher binds that root to the candidate.\<close>

definition m11_zero_digits :: "nat \<Rightarrow> nat" where
  "m11_zero_digits i = 0"

definition m11_zero_carry :: "nat \<Rightarrow> int" where
  "m11_zero_carry i = (if i=1 then -2 else -1)"

definition m11_zero_remainder :: "nat \<Rightarrow> int" where
  "m11_zero_remainder i = (if i=1 then 0 else 1)"

lemma m11_zero_square_field:
  "mersenne_square_field 11 m11_zero_digits i =
    (if i=0 then -2 else 0)"
proof -
  have coefficient: "cyclic_square_coefficient 11 m11_zero_digits i = 0"
    unfolding cyclic_square_coefficient_def
    apply (rule sum.neutral)
    apply (rule ballI)
    apply (rule sum.neutral)
    apply (rule ballI)
    by (simp add: m11_zero_digits_def)
  show ?thesis
    by (simp add: mersenne_square_field_def coefficient)
qed

lemma m11_zero_normalization_steps:
  "mersenne_square_field 11 m11_zero_digits i + m11_zero_carry i =
    m11_zero_remainder i + 2*m11_zero_carry (Suc i)"
  by (cases "i=0"; cases "i=1")
    (simp_all add: m11_zero_square_field m11_zero_carry_def
      m11_zero_remainder_def)

lemma m11_zero_cylinder_boundary:
  "m11_zero_carry 11 = m11_zero_carry 0"
  by (simp add: m11_zero_carry_def)

lemma m11_zero_remainder_value:
  "polynomial_prefix m11_zero_remainder 11 2 = 2045"
proof -
  have width: "(11::nat) =
      Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))"
    by simp
  show ?thesis unfolding width
    by (simp add: polynomial_prefix_def m11_zero_remainder_def
        sum.lessThan_Suc)
qed

lemma m11_zero_primary_key:
  "primary_root_key False 11 m11_zero_carry =
    (False, -1, (14, 5))"
proof -
  have width: "(11::nat) =
      Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))"
    by simp
  show ?thesis unfolding width
    by (simp add: primary_root_key_def jet_reduce_def coefficient_jet_def
        m11_zero_carry_def sum.lessThan_Suc)
qed

lemma m11_is_composite:
  "\<not> prime (2047::nat)"
proof -
  have factor: "gcd (2047::nat) 23 = 23" by (simp add: gcd_nat.simps)
  have low: "1 < gcd (2047::nat) 23" by (simp only: factor; simp)
  have high: "gcd (2047::nat) 23 < 2047" by (simp only: factor; simp)
  show ?thesis
    by (rule coefficient_gcd_prints_exact_factor(3)[OF low high])
qed

theorem m11_composite_has_normalized_zero_root_key:
  "int (2047::nat) = (2::int)^11-1"
  "binary_value 11 m11_zero_digits = 0"
  "2047 dvd binary_value 11 m11_zero_digits *
    (binary_value 11 m11_zero_digits+2)"
  "\<And>i. i<11 \<Longrightarrow>
    mersenne_square_field 11 m11_zero_digits i + m11_zero_carry i =
      m11_zero_remainder i + 2*m11_zero_carry (Suc i)"
  "m11_zero_carry 11 = m11_zero_carry 0"
  "0 \<le> polynomial_prefix m11_zero_remainder 11 2"
  "polynomial_prefix m11_zero_remainder 11 2 < 2047"
  "primary_root_key False 11 m11_zero_carry =
    (False, -1, (14, 5))"
  "\<not> prime (2047::nat)"
proof -
  show "int (2047::nat) = (2::int)^11-1" by simp
  show "binary_value 11 m11_zero_digits = 0"
    by (simp add: binary_value_def m11_zero_digits_def)
  then show "2047 dvd binary_value 11 m11_zero_digits *
      (binary_value 11 m11_zero_digits+2)" by simp
  show "mersenne_square_field 11 m11_zero_digits i + m11_zero_carry i =
      m11_zero_remainder i + 2*m11_zero_carry (Suc i)" if "i<11" for i
    by (rule m11_zero_normalization_steps)
  show "m11_zero_carry 11 = m11_zero_carry 0"
    by (rule m11_zero_cylinder_boundary)
  show "0 \<le> polynomial_prefix m11_zero_remainder 11 2"
    by (simp add: m11_zero_remainder_value)
  show "polynomial_prefix m11_zero_remainder 11 2 < 2047"
    by (simp add: m11_zero_remainder_value)
  show "primary_root_key False 11 m11_zero_carry =
      (False, -1, (14, 5))"
    by (rule m11_zero_primary_key)
  show "\<not> prime (2047::nat)" by (rule m11_is_composite)
qed

text \<open>This is a counterexample only to the invalid implication from a
mathematical zero root or its one-square primary key to primality.  It is not a
counterexample to a candidate-derived terminal shadow-cylinder publisher.  No
such publisher is assumed or constructed here.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms m11_zero_square_field m11_zero_normalization_steps
      m11_zero_cylinder_boundary m11_zero_remainder_value
      m11_zero_primary_key m11_is_composite
      m11_composite_has_normalized_zero_root_key}) then ()
    else error "Mersenne zero-key counterexample depends on an oracle";
\<close>

end
