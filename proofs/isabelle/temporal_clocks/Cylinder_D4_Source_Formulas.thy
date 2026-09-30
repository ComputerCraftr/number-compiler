theory Cylinder_D4_Source_Formulas
  imports Cylinder_D2_Edge_Interior
begin

text \<open>
  Source-parametric Q2/Q3 regions for the edge/interior chamber.  These
  definitions mirror the finite interval cases in edge_interior_d4_regions.py
  and are evaluated only under m>=3, 5<=a<=8, 8<=b<=9.  The carry fields are
  predicates on the source parameters and the integer coordinate; no future
  coefficient word is supplied.
\<close>

definition d4_p2 :: "nat => int => int => int => int" where
  "d4_p2 m a b i = d2_p1 m a b i + d2_p1 m a b (i - 1)
      - 9 * (d2_q1 m i + d2_q1 m (i - 1))"

definition d4_q2 :: "nat => int => int => int => int" where
  "d4_q2 m a b i =
    (if m = 3 then
       (if 2*a + 4*b - 37 >= 10 \<and> 1 \<le> i \<and> i < 3 then 1 else 0)
     else if m = 4 then
       (if b = 9 \<and> 1 \<le> i \<and> i < 4 then 1
        else if b = 8 \<and> a >= 7 \<and>
             ((1 \<le> i \<and> i < 2) \<or> (3 \<le> i \<and> i < 4)) then 1
        else 0)
     else if m = 5 then
       (if (b = 9 \<or> a >= 7) \<and> 1 \<le> i \<and> i < 5 then 1 else 0)
     else if b = 9 \<or> a >= 7 then
       (if 1 \<le> i \<and> i < int m then 1 else 0)
     else if b = 8 \<and> a \<le> 6 then
       (if 3 \<le> i \<and> i < int m - 1 then 1 else 0)
     else 0)"

definition d4_c2 :: "nat => int => int => int => int" where
  "d4_c2 m a b i = d4_q2 m a b (i - 1)"

definition d4_d2 :: "nat => int => int => int => int" where
  "d4_d2 m a b i = d4_p2 m a b i + d4_c2 m a b i
      - 10 * d4_c2 m a b (i + 1)"

definition d4_p3 :: "nat => int => int => int => int" where
  "d4_p3 m a b i = d4_d2 m a b i + d4_d2 m a b (int m - i)"

definition d4_q3 :: "nat => int => int => int => int" where
  "d4_q3 m a b i =
    (if m = 3 then
       (if 2*a + 4*b - 37 < 10 then
          (if a >= 7 \<and> 0 \<le> i \<and> i < 4 then 1
           else if 1 \<le> i \<and> i < 3 then 1 else 0)
        else if a = 6 \<and> b = 9 then 0
        else if a = 8 \<and> b = 9 then
          (if 0 \<le> i \<and> i < 4 then 1 else 0)
        else if (i = 0 \<or> i = 3) then 1 else 0)
     else if m = 4 then
       (if b = 8 \<and> a \<le> 6 then
          (if 1 \<le> i \<and> i < 4 then 1 else 0)
        else if b = 8 then
          (if i = 0 \<or> i = 2 \<or> i = 4 then 1 else 0)
        else if a \<le> 6 then
          (if 2 \<le> i \<and> i < 3 then 1 else 0)
        else if 0 \<le> i \<and> i < 5 then 1 else 0)
     else if m = 5 then
       (if b = 8 \<and> a \<le> 6 then
          (if 1 \<le> i \<and> i < 5 then 1 else 0)
        else if b = 8 then
          (if i = 0 \<or> i = 5 then 1 else 0)
        else if a \<le> 6 then
          (if 2 \<le> i \<and> i < 4 then 1 else 0)
        else if 0 \<le> i \<and> i < 6 then 1 else 0)
     else if b = 8 \<and> a \<le> 6 then
       (if (1 \<le> i \<and> i < 3) \<or>
           (int m - 1 \<le> i \<and> i < int m) then 1 else 0)
     else if b = 8 then
       (if i = 0 \<or> i = int m then 1 else 0)
     else if a \<le> 6 then
       (if 2 \<le> i \<and> i < int m - 1 then 1 else 0)
     else if 0 \<le> i \<and> i < int m + 1 then 1 else 0)"

definition d4_c3 :: "nat => int => int => int => int" where
  "d4_c3 m a b i = d4_q3 m a b (i - 1)"

definition d4_g3 :: "int => int" where
  "d4_g3 a = (if a >= 7 then 1 else 0)"

text \<open>Closed P2 coefficient views keep the carry proofs from repeatedly
expanding the complete D2 innovation expression.\<close>


lemma d4_p2_m3:
  assumes width: "m = 3"
  shows "d4_p2 m a b i =
    (if i = 0 \<or> i = 3 then 2*a - 8
     else if i = 1 \<or> i = 2 then 2*a + 4*b - 37 else 0)"
  using width
  by (simp add: width d4_p2_def d2_p1_def d2_beta0_def d2_e0_def
      d2_source_def d2_q0_def d2_q1_def split: if_splits; arith)


lemma d4_p2_m4:
  assumes width: "m = 4"
  shows "d4_p2 m a b i =
    (if i = 0 \<or> i = 4 then 2*a - 8
     else if i = 1 \<or> i = 3 then 2*a + 4*b - 36
     else if i = 2 then 8*b - 56 else 0)"
  using width
  by (simp add: width d4_p2_def d2_p1_def d2_beta0_def d2_e0_def
      d2_source_def d2_q0_def d2_q1_def split: if_splits; arith)


lemma d4_p2_m5:
  assumes width: "m = 5"
  shows "d4_p2 m a b i =
    (if i = 0 \<or> i = 5 then 2*a - 8
     else if i = 1 \<or> i = 4 then 2*a + 4*b - 36
     else if i = 2 \<or> i = 3 then 8*b - 55 else 0)"
  using width
  by (simp add: width d4_p2_def d2_p1_def d2_beta0_def d2_e0_def
      d2_source_def d2_q0_def d2_q1_def split: if_splits; arith)


lemma d4_p2_wide:
  assumes width: "6 \<le> m"
  shows "d4_p2 m a b i =
    (if i = 0 \<or> i = int m then 2*a - 8
     else if i = 1 \<or> i = int m - 1 then 2*a + 4*b - 36
     else if i = 2 \<or> i = int m - 2 then 8*b - 55
     else if 3 \<le> i \<and> i \<le> int m - 3 then 8*b - 54
     else 0)"
  unfolding d4_p2_def d2_p1_def d2_beta0_def d2_e0_def d2_source_def
    d2_q0_def d2_q1_def
  using width by (split if_splits) (simp_all; arith)

lemma d4_p2_closed:
  assumes extent: "3 \<le> m"
  shows "d4_p2 m a b i =
    (if m = 3 then
       (if i = 0 \<or> i = 3 then 2*a - 8
        else if i = 1 \<or> i = 2 then 2*a + 4*b - 37 else 0)
     else if m = 4 then
       (if i = 0 \<or> i = 4 then 2*a - 8
        else if i = 1 \<or> i = 3 then 2*a + 4*b - 36
        else if i = 2 then 8*b - 56 else 0)
     else if m = 5 then
       (if i = 0 \<or> i = 5 then 2*a - 8
        else if i = 1 \<or> i = 4 then 2*a + 4*b - 36
        else if i = 2 \<or> i = 3 then 8*b - 55 else 0)
     else if i = 0 \<or> i = int m then 2*a - 8
     else if i = 1 \<or> i = int m - 1 then 2*a + 4*b - 36
     else if i = 2 \<or> i = int m - 2 then 8*b - 55
     else if 3 \<le> i \<and> i \<le> int m - 3 then 8*b - 54
     else 0)"
proof (cases "m = 3")
  case True
  then show ?thesis using d4_p2_m3[of m a b i] by simp
next
  case False
  have not3: "m \<noteq> 3" using False by simp
  show ?thesis
  proof (cases "m = 4")
    case True
    then show ?thesis using d4_p2_m4[of m a b i] by simp
  next
    case False
    have not4: "m \<noteq> 4" using False by simp
    show ?thesis
    proof (cases "m = 5")
      case True
      then show ?thesis using d4_p2_m5[of m a b i] by simp
    next
      case False
      have not5: "m \<noteq> 5" using False by simp
      have wide: "6 \<le> m" using extent not3 not4 not5 by arith
      show ?thesis using d4_p2_wide[OF wide, of a b i] not3 not4 not5
        by simp
    qed
  qed
qed


lemma d4_q2_terminal:
  assumes extent: "3 \<le> m" and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
  shows "d4_q2 m a b (int m) = 0"
  unfolding d4_q2_def
  using extent edge interior by (split if_splits) (simp_all; arith)

lemma d4_g2_zero:
  assumes extent: "3 \<le> m" and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
  shows "d4_c2 m a b (int m + 1) = 0"
  unfolding d4_c2_def
  using d4_q2_terminal[OF extent edge interior] by simp


lemma d4_q3_terminal:
  assumes extent: "3 \<le> m" and edge: "5 \<le> a" "a \<le> 8"
      and interior: "8 \<le> b" "b \<le> 9"
  shows "d4_q3 m a b (int m) = d4_g3 a"
  unfolding d4_q3_def d4_g3_def
  using extent edge interior by (split if_splits) (simp_all; arith)


text \<open>
  The P2 formulas follow from the checked D2 innovation expression.  The
  declared Q2/Q3 regions have the displayed terminal values, but this theory
  does not prove they are the forward carries of P2/P3.  Those admission
  obligations remain open: a terminal-value identity is not carry admission.
  This theory supplies neither complete D4 output refinement nor production
  source authority, temporal closure or a pumping construction bound.
\<close>

ML \<open>
  val checked = @{thms d4_p2_m3 d4_p2_m4 d4_p2_m5 d4_p2_wide
    d4_p2_closed d4_q2_terminal d4_g2_zero d4_q3_terminal};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "D4 edge/interior regions depend on an oracle";
\<close>

end
