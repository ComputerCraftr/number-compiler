theory Cylinder_D2_Edge_Interior
  imports Cylinder_Coboundary_Publisher
begin

text \<open>
  The bounded D2 source chamber used by
  @{file "../../../../../devtools/experiments/reverse_add/edge_interior_regions.py"}.
  The source has edge value a and interior pair value 2*b.  The two carry
  regions are represented as functions on the complete integer line, so the
  statements include their exterior zero support.  This is only the stated
  m>=3 chamber; it is not a temporal pump or a general successor grammar.
\<close>

definition d2_source :: "nat => int => int => int => int" where
  "d2_source m a b i =
    (if i = 0 \<or> i = int m - 1 then a
     else if 0 \<le> i \<and> i < int m then 2*b else 0)"

definition d2_q0 :: "nat => int => int" where
  "d2_q0 m i = (if 1 \<le> i \<and> i < int m - 1 then 1 else 0)"

definition d2_c0 :: "nat => int => int" where
  "d2_c0 m i = (if 2 \<le> i \<and> i < int m then 1 else 0)"

definition d2_e0 :: "nat => int => int" where
  "d2_e0 m i = d2_q0 m (i - 1) - 10 * d2_q0 m i"

definition d2_beta0 :: "nat => int => int" where
  "d2_beta0 m i = d2_e0 m i + d2_e0 m (int m - 1 - i)"

definition d2_p1 :: "nat => int => int => int => int" where
  "d2_p1 m a b i = 2 * d2_source m a b i + d2_beta0 m i"

definition d2_q1 :: "nat => int => int" where
  "d2_q1 m i = (if 0 \<le> i \<and> i < int m then 1 else 0)"

definition d2_c1 :: "nat => int => int" where
  "d2_c1 m i = (if 1 \<le> i \<and> i \<le> int m then 1 else 0)"

lemma d2_q0_encoding:
  "d2_q0 m i =
    (if cylinder_window m i then d2_c0 m (i + 1) else 0)"
  unfolding d2_q0_def d2_c0_def cylinder_window_def
  by (split if_splits) (simp_all; arith)

lemma d2_q0_initial:
  "d2_c0 m 0 = 0"
  by (simp add: d2_c0_def)

lemma d2_q0_terminal:
  "d2_c0 m (int m) = 0"
  by (simp add: d2_c0_def)

lemma d2_q0_forward:
  assumes extent: "3 \<le> m"
      and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
      and active: "cylinder_window m i"
  shows "d2_c0 m (i + 1) =
    (d2_source m a b i + d2_c0 m i) div 10"
  unfolding d2_c0_def d2_source_def
  using extent edge interior active
  by (split if_splits) (simp_all; arith)

lemma d2_q0_is_exact_forward_carry:
  assumes extent: "3 \<le> m"
      and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
  shows "\<forall>i. cylinder_window m i \<longrightarrow>
      d2_c0 m (i + 1) =
        (d2_source m a b i + d2_c0 m i) div 10"
  using d2_q0_forward[OF extent edge interior] by blast

lemma d2_p1_range:
  assumes extent: "3 \<le> m"
      and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
      and active: "cylinder_window m i"
  shows "10 \<le> d2_p1 m a b i \<and> d2_p1 m a b i \<le> 18"
  using extent edge interior active
  unfolding d2_p1_def d2_beta0_def d2_e0_def d2_source_def
    d2_q0_def cylinder_window_def
  by (auto split: if_splits; arith)

lemma d2_p1_range_on_source:
  assumes extent: "3 \<le> m"
      and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
  shows "\<forall>i. cylinder_window m i \<longrightarrow>
      10 \<le> d2_p1 m a b i \<and> d2_p1 m a b i \<le> 18"
  using d2_p1_range[OF extent edge interior] by blast

lemma d2_q1_encoding:
  "d2_q1 m i =
    (if cylinder_window m i then d2_c1 m (i + 1) else 0)"
  unfolding d2_q1_def d2_c1_def cylinder_window_def
  by (split if_splits) (simp_all; arith)

lemma d2_q1_initial:
  "d2_c1 m 0 = 0"
  by (simp add: d2_c1_def)

lemma d2_q1_terminal:
  assumes positive: "0 < m"
  shows "d2_c1 m (int m) = 1"
  using positive by (simp add: d2_c1_def)

lemma d2_q1_forward:
  assumes extent: "3 \<le> m"
      and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
      and active: "cylinder_window m i"
  shows "d2_c1 m (i + 1) =
    (d2_p1 m a b i + d2_c1 m i) div 10"
proof -
  have range: "10 \<le> d2_p1 m a b i \<and>
      d2_p1 m a b i \<le> 18"
    using d2_p1_range[OF extent edge interior active] .
  show ?thesis
    using active range
    unfolding d2_c1_def cylinder_window_def
    by (auto split: if_splits; arith)
qed

lemma d2_q1_is_exact_forward_carry:
  assumes extent: "3 \<le> m"
      and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
  shows "\<forall>i. cylinder_window m i \<longrightarrow>
      d2_c1 m (i + 1) =
        (d2_p1 m a b i + d2_c1 m i) div 10"
  using d2_q1_forward[OF extent edge interior] by blast

lemma d2_source_reflection:
  assumes "3 \<le> m"
  shows "d2_source m a b (int m - 1 - i) = d2_source m a b i"
  using assms unfolding d2_source_def
  by (auto split: if_splits; arith)

lemma d2_first_successor:
  assumes "3 \<le> m"
  shows "cylinder_next (int m - 1) (d2_source m a b) (d2_q0 m) =
    d2_p1 m a b"
proof (rule ext)
  fix i
  show "cylinder_next (int m - 1) (d2_source m a b) (d2_q0 m) i =
    d2_p1 m a b i"
    unfolding cylinder_next_def cylinder_normalized_def innovation_add_def
      innovation_reflect_def cylinder_coboundary_def d2_p1_def
      d2_beta0_def d2_e0_def
    using d2_source_reflection[OF assms, of a b i] by arith
qed

lemma d2_p1_reflection:
  assumes "3 \<le> m"
  shows "d2_p1 m a b (int m - 1 - i) = d2_p1 m a b i"
  unfolding d2_p1_def d2_beta0_def
  using d2_source_reflection[OF assms, of a b i]
  by (simp add: algebra_simps)

lemma d2_q1_reflection:
  "d2_q1 m (int m - 1 - i) = d2_q1 m i"
  unfolding d2_q1_def by (auto split: if_splits; arith)

text \<open>
  These are whole-function identities for the two Python expression roots:
  the directional output and the next symmetric field.  The carry theorems
  above derive the chosen regions on the stated chamber.  No Python source
  authority or complete temporal-image admission follows from these equations.
\<close>

lemma d2_directional_output:
  "cylinder_normalized 10 (d2_p1 m a b) (d2_q1 m) i =
    2 * d2_source m a b i + d2_beta0 m i +
      cylinder_coboundary 10 (d2_q1 m) i"
  by (simp add: cylinder_normalized_def innovation_add_def d2_p1_def)

lemma d2_second_successor:
  assumes "3 \<le> m"
  shows "cylinder_next (int m) (d2_p1 m a b) (d2_q1 m) i =
    2 * (d2_source m a b i + d2_source m a b (i - 1)) +
    (d2_beta0 m i + d2_beta0 m (i - 1)) -
    9 * (d2_q1 m i + d2_q1 m (i - 1))"
proof -
  have mirrored_p: "d2_p1 m a b (int m - i) = d2_p1 m a b (i - 1)"
    using d2_p1_reflection[OF assms, of a b "i - 1"] by simp
  have mirrored_q: "d2_q1 m (int m - i) = d2_q1 m (i - 1)"
    using d2_q1_reflection[of m "i - 1"] by simp
  have previous_q: "d2_q1 m (int m - i - 1) = d2_q1 m i"
    using d2_q1_reflection[of m i] by (simp add: algebra_simps)
  show ?thesis
    unfolding cylinder_next_def cylinder_normalized_def innovation_add_def
      innovation_reflect_def cylinder_coboundary_def
    using mirrored_p mirrored_q previous_q
    by (simp add: d2_p1_def; arith)
qed

lemma d2_chamber_carry_admission:
  assumes extent: "3 \<le> m"
      and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
  shows "cylinder_forward_carry 10 m (d2_source m a b) (d2_c0 m)"
    and "cylinder_forward_carry 10 m
      (cylinder_next (int m - 1) (d2_source m a b) (d2_q0 m)) (d2_c1 m)"
    and "cylinder_carry_encoding m (d2_c0 m) (d2_q0 m)"
    and "cylinder_carry_encoding m (d2_c1 m) (d2_q1 m)"
    and "d2_c0 m 0 = 0 \<and> d2_c1 m 0 = 0"
    and "d2_c0 m (int m) = 0 \<and> d2_c1 m (int m) = 1"
proof -
  show "cylinder_forward_carry 10 m (d2_source m a b) (d2_c0 m)"
    using d2_q0_is_exact_forward_carry[OF extent edge interior]
    unfolding cylinder_forward_carry_def .
  show "cylinder_forward_carry 10 m
      (cylinder_next (int m - 1) (d2_source m a b) (d2_q0 m)) (d2_c1 m)"
    using d2_q1_is_exact_forward_carry[OF extent edge interior]
    unfolding d2_first_successor[OF extent] cylinder_forward_carry_def .
  show "cylinder_carry_encoding m (d2_c0 m) (d2_q0 m)"
    unfolding cylinder_carry_encoding_def using d2_q0_encoding by blast
  show "cylinder_carry_encoding m (d2_c1 m) (d2_q1 m)"
    unfolding cylinder_carry_encoding_def using d2_q1_encoding by blast
  show "d2_c0 m 0 = 0 \<and> d2_c1 m 0 = 0"
    using d2_q0_initial d2_q1_initial by simp
  have positive: "0 < m" using extent by arith
  show "d2_c0 m (int m) = 0 \<and> d2_c1 m (int m) = 1"
    using d2_q0_terminal d2_q1_terminal[OF positive] by simp
qed

text \<open>
  q0 is the exact first outgoing carry support [1,m-1); p1 is the first
  normalized successor field and is strictly above the decimal carry
  threshold everywhere in the source window; q1 is therefore the exact
  second outgoing carry support [0,m).  These are source-parameter facts,
  not supplied future fields.
\<close>

ML \<open>
  val checked = @{thms d2_q0_encoding d2_q0_forward
    d2_q0_is_exact_forward_carry d2_p1_range d2_p1_range_on_source
    d2_q1_encoding d2_q1_forward d2_q1_is_exact_forward_carry
    d2_first_successor d2_directional_output d2_second_successor
    d2_chamber_carry_admission};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "D2 edge/interior region depends on an oracle";
\<close>

end
