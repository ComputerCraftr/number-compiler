theory Cylinder_D4_Carry_Admission
  imports Cylinder_D4_Source_Formulas
begin

text \<open>
  This theory isolates the division step from the D4 region formulas.  The
  carry proof first establishes a decimal remainder bound and only then uses
  integer division.  It deliberately keeps the finite width cases separate;
  the large symbolic if-expression is never sent to Presburger arithmetic
  before the width and chamber parameters have been split.
\<close>

lemma int_division_from_remainder:
  fixes z q :: int
  assumes remainder: "0 \<le> z - 10*q \<and> z - 10*q < 10"
  shows "z div 10 = q"
proof -
  have decomposition: "z = 10 * (z div 10) + z mod 10"
    using div_mult_mod_eq[of z 10] by (simp add: algebra_simps)
  have residue_lower: "0 \<le> z mod 10" by simp
  have residue_upper: "z mod 10 < 10" by simp
  show ?thesis
    using remainder decomposition residue_lower residue_upper by arith
qed

lemma d4_q2_remainder_m3:
  assumes width: "m = 3"
      and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
      and active: "0 \<le> i" "i \<le> int m"
  shows "0 \<le> d4_p2 m a b i + d4_c2 m a b i
      - 10 * d4_q2 m a b i
    \<and> d4_p2 m a b i + d4_c2 m a b i
      - 10 * d4_q2 m a b i < 10"
proof -
  have here: "d4_p2 m a b i =
      (if i = 0 \<or> i = 3 then 2*a - 8
       else if i = 1 \<or> i = 2 then 2*a + 4*b - 37 else 0)"
    using d4_p2_m3[OF width] .
  show ?thesis
    unfolding d4_c2_def
    using here width edge interior active
    by (simp add: here width d4_q2_def split: if_splits; arith)
qed

lemma d4_q2_remainder_m4:
  assumes width: "m = 4"
      and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
      and active: "0 \<le> i" "i \<le> int m"
  shows "0 \<le> d4_p2 m a b i + d4_c2 m a b i
      - 10 * d4_q2 m a b i
    \<and> d4_p2 m a b i + d4_c2 m a b i
      - 10 * d4_q2 m a b i < 10"
proof -
  have here: "d4_p2 m a b i =
      (if i = 0 \<or> i = 4 then 2*a - 8
       else if i = 1 \<or> i = 3 then 2*a + 4*b - 36
       else if i = 2 then 8*b - 56 else 0)"
    using d4_p2_m4[OF width] .
  show ?thesis
    unfolding d4_c2_def
    using here width edge interior active
    by (simp add: here width d4_q2_def split: if_splits; arith)
qed

lemma d4_q2_remainder_m5:
  assumes width: "m = 5"
      and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
      and active: "0 \<le> i" "i \<le> int m"
  shows "0 \<le> d4_p2 m a b i + d4_c2 m a b i
      - 10 * d4_q2 m a b i
    \<and> d4_p2 m a b i + d4_c2 m a b i
      - 10 * d4_q2 m a b i < 10"
proof -
  have here: "d4_p2 m a b i =
      (if i = 0 \<or> i = 5 then 2*a - 8
       else if i = 1 \<or> i = 4 then 2*a + 4*b - 36
       else if i = 2 \<or> i = 3 then 8*b - 55 else 0)"
    using d4_p2_m5[OF width] .
  show ?thesis
    unfolding d4_c2_def
    using here width edge interior active
    by (simp add: here width d4_q2_def split: if_splits; arith)
qed

lemma d4_q2_remainder_wide:
  assumes width: "6 \<le> m"
      and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
      and active: "0 \<le> i" "i \<le> int m"
  shows "0 \<le> d4_p2 m a b i + d4_c2 m a b i
      - 10 * d4_q2 m a b i
    \<and> d4_p2 m a b i + d4_c2 m a b i
      - 10 * d4_q2 m a b i < 10"
proof -
  have b_cases: "b = 8 \<or> b = 9" using interior by arith
  have here: "d4_p2 m a b i =
      (if i = 0 \<or> i = int m then 2*a - 8
       else if i = 1 \<or> i = int m - 1 then 2*a + 4*b - 36
       else if i = 2 \<or> i = int m - 2 then 8*b - 55
       else if 3 \<le> i \<and> i \<le> int m - 3 then 8*b - 54
       else 0)"
    using d4_p2_wide[OF width] .
  have not3: "m \<noteq> 3" and not4: "m \<noteq> 4" and not5: "m \<noteq> 5"
    using width by arith+
  have edges: "a = 5 \<or> a = 6 \<or> a = 7 \<or> a = 8" using edge by arith
  from b_cases edges show ?thesis
    unfolding here d4_c2_def
    using width active not3 not4 not5
    by (elim disjE; simp add: d4_q2_def split: if_splits; arith)
qed

lemma d4_q2_forward_admitted:
  assumes extent: "3 \<le> m" and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
      and active: "0 \<le> i" "i \<le> int m"
  shows "d4_q2 m a b i =
    (d4_p2 m a b i + d4_c2 m a b i) div 10"
proof -
  consider (three) "m = 3" | (four) "m = 4" | (five) "m = 5"
    | (wide) "6 \<le> m" using extent by arith
  then have remainder:
    "0 \<le> d4_p2 m a b i + d4_c2 m a b i - 10 * d4_q2 m a b i
     \<and> d4_p2 m a b i + d4_c2 m a b i - 10 * d4_q2 m a b i < 10"
  proof cases
    case three
    show ?thesis by (rule d4_q2_remainder_m3[OF three edge interior active])
  next
    case four
    show ?thesis by (rule d4_q2_remainder_m4[OF four edge interior active])
  next
    case five
    show ?thesis by (rule d4_q2_remainder_m5[OF five edge interior active])
  next
    case wide
    show ?thesis by (rule d4_q2_remainder_wide[OF wide edge interior active])
  qed
  show ?thesis using int_division_from_remainder[OF remainder] by simp
qed

lemma d4_q2_initial:
  "d4_c2 m a b 0 = 0"
  by (simp add: d4_c2_def d4_q2_def)

lemma d4_p2_is_second_successor:
  assumes extent: "3 \<le> m"
  shows "d4_p2 m a b i =
    cylinder_next (int m) (d2_p1 m a b) (d2_q1 m) i"
  using d2_second_successor[OF extent, of a b i]
  by (simp add: d4_p2_def d2_p1_def; arith)

lemma d4_third_directional_output:
  "d4_d2 m a b i = cylinder_normalized 10 (d4_p2 m a b) (d4_q2 m a b) i"
  by (simp add: d4_d2_def d4_c2_def cylinder_normalized_def
      innovation_add_def cylinder_coboundary_def)

lemma d4_pair3_is_third_successor:
  "d4_p3 m a b i = cylinder_next (int m) (d4_p2 m a b) (d4_q2 m a b) i"
  by (simp add: d4_p3_def d4_third_directional_output cylinder_next_def
      innovation_add_def innovation_reflect_def)

lemma d4_third_carry_on_source:
  assumes extent: "3 \<le> m" and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
  shows "cylinder_forward_carry 10 (m+1)
    (cylinder_next (int m) (d2_p1 m a b) (d2_q1 m)) (d4_c2 m a b)"
proof (unfold cylinder_forward_carry_def, intro allI impI)
  fix i
  assume active: "cylinder_window (m+1) i"
  have bounds: "0 \<le> i" "i \<le> int m"
    using active unfolding cylinder_window_def by auto
  show "d4_c2 m a b (i+1) =
    (cylinder_next (int m) (d2_p1 m a b) (d2_q1 m) i + d4_c2 m a b i) div 10"
    using d4_q2_forward_admitted[OF extent edge interior bounds]
      d4_p2_is_second_successor[OF extent, of a b i]
    by (simp add: d4_c2_def)
qed

text \<open>
  The third carry is derived from the actual second source successor, with
  initial carry zero.  The directional third output and its reflected pair
  field use this same carry.  These results do not prove the fourth carry Q3,
  source authentication in Python, complete channel publication or pumping.
\<close>

ML \<open>
  val checked = @{thms int_division_from_remainder d4_q2_remainder_m3
    d4_q2_remainder_m4 d4_q2_remainder_m5 d4_q2_remainder_wide
    d4_q2_forward_admitted d4_q2_initial d4_p2_is_second_successor
    d4_third_directional_output d4_pair3_is_third_successor d4_third_carry_on_source};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "D4 carry admission depends on an oracle";
\<close>

end
