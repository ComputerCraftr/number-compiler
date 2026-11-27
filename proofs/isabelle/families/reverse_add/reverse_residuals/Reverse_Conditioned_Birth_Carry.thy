theory Reverse_Conditioned_Birth_Carry
  imports Reverse_Native_Slab_Clock
begin

definition pair_sum_inlet :: "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool" where
  "pair_sum_inlet b s u \<longleftrightarrow> b \<le> s + carry_bit u"

definition conditioned_birth_sum :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat" where
  "conditioned_birth_sum b l r u v =
    (l + carry_bit (pair_sum_inlet b r u)) mod b +
    (r + carry_bit (pair_sum_inlet b l v)) mod b"

definition conditioned_birth_carry :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "conditioned_birth_carry b l r u v c = pair_sum_inlet b (conditioned_birth_sum b l r u v) c"

lemma conditioned_birth_decimal:
  "conditioned_birth_carry 10 l r u v c =
    carry_apply (domain (reverse_native_slab_birth l r
      (carry_apply (domain l) v) (carry_apply (domain r) u))) c"
  by (simp add: conditioned_birth_carry_def conditioned_birth_sum_def pair_sum_inlet_def
    reverse_native_slab_birth_def reverse_native_slab_digit_def carry_apply_decimal_threshold
    carry_bit_def add.commute)

lemma conditioned_birth_reset:
  assumes "2 \<le> b" "s \<noteq> b - 1"
  shows "pair_sum_inlet b s x = pair_sum_inlet b s False"
  using assms by (cases x; auto simp: pair_sum_inlet_def carry_bit_def; arith)

lemma conditioned_birth_double_eq:
  assumes "2 \<le> b"
  shows "conditioned_birth_carry b (b-1) (b-1) u v c =
    (if u = v then \<not>u else c)"
proof -
  have low: "b - 1 < b" and add: "b - 1 + 1 = b" using assms by arith+
  show ?thesis using assms low add
    by (cases u; cases v; cases c;
        simp add: conditioned_birth_carry_def conditioned_birth_sum_def
        pair_sum_inlet_def carry_bit_def; arith)
qed

definition carry_edge_gain :: "(bool \<Rightarrow> bool) \<Rightarrow> int" where
  "carry_edge_gain f = int (carry_bit (f True)) - int (carry_bit (f False))"

definition carry_hasse_cubic :: "(bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> int" where
  "carry_hasse_cubic f = carry_edge_gain (f True True) - carry_edge_gain (f False True)
    - carry_edge_gain (f True False) + carry_edge_gain (f False False)"

theorem conditioned_birth_cubic:
  assumes b: "2 \<le> b"
  shows "carry_hasse_cubic (conditioned_birth_carry b l r) =
    (if l = b-1 \<and> r = b-1 then -2 else 0)"
proof (cases "r = b-1")
  case False
  have drop: "conditioned_birth_carry b l r True v = conditioned_birth_carry b l r False v" for v
    by (rule ext; simp only: conditioned_birth_carry_def conditioned_birth_sum_def conditioned_birth_reset[OF b False, of True])
  show ?thesis using False by (simp add: carry_hasse_cubic_def drop)
next
  case True
  note right = True
  show ?thesis
  proof (cases "l = b-1")
    case False
    have drop: "conditioned_birth_carry b l r u True = conditioned_birth_carry b l r u False" for u
      by (rule ext; simp only: conditioned_birth_carry_def conditioned_birth_sum_def conditioned_birth_reset[OF b False, of True])
    show ?thesis using False by (simp add: carry_hasse_cubic_def drop)
  next
    case True
    have cell: "conditioned_birth_carry b l r u v c = (if u=v then \<not>u else c)" for u v c
      unfolding True right by (rule conditioned_birth_double_eq[OF b])
    have cubic: "carry_hasse_cubic (conditioned_birth_carry b l r) = -2"
      unfolding carry_hasse_cubic_def carry_edge_gain_def cell carry_bit_def by simp
    show ?thesis unfolding cubic using True right by simp
  qed
qed

lemma conditioned_birth_swap:
  "conditioned_birth_carry b l r u v c = conditioned_birth_carry b r l v u c"
  by (simp only: conditioned_birth_carry_def conditioned_birth_sum_def add.commute)

lemma conditioned_birth_single_eq:
  assumes "l < 19" "l \<noteq> 9"
  shows "conditioned_birth_carry 10 l 9 u v c =
    (if l = 0 then u \<or> c else if l = 18 then u \<and> c
     else conditioned_birth_carry 10 l 9 False False c)"
  using nat_less_nineteen_cases[OF assms(1)] assms(2)
  by (elim disjE; cases u; cases v; cases c;
      simp_all add: conditioned_birth_carry_def conditioned_birth_sum_def pair_sum_inlet_def carry_bit_def)

theorem conditioned_birth_decimal_selection:
  assumes "l < 19" "r < 19"
  shows "conditioned_birth_carry 10 l r u v c =
    (if l=9 \<and> r=9 then (if u=v then \<not>u else c)
     else if l=0 \<and> r=9 then u \<or> c else if l=18 \<and> r=9 then u \<and> c
     else if l=9 \<and> r=0 then v \<or> c else if l=9 \<and> r=18 then v \<and> c
     else conditioned_birth_carry 10 l r False False c)"
proof (cases "r=9")
  case True
  then show ?thesis using conditioned_birth_single_eq[OF assms(1), of u v c]
    conditioned_birth_double_eq[of 10 u v c] by (cases "l=9"; simp)
next
  case False
  note r = False
  show ?thesis
  proof (cases "l=9")
    case True
    have eq: "conditioned_birth_carry 10 9 r u v c =
        (if r=0 then v \<or> c else if r=18 then v \<and> c else conditioned_birth_carry 10 9 r False False c)"
      using conditioned_birth_single_eq[OF assms(2) r, of v u c]
      by (simp only: conditioned_birth_swap[of 10 9 r])
    show ?thesis using eq True r by simp
  next
    case False
    have L: "pair_sum_inlet 10 l v = pair_sum_inlet 10 l False"
      by (rule conditioned_birth_reset; simp add: False)
    have R: "pair_sum_inlet 10 r u = pair_sum_inlet 10 r False"
      by (rule conditioned_birth_reset; simp add: r)
    show ?thesis using False r
      by (simp add: conditioned_birth_carry_def conditioned_birth_sum_def L R)
  qed
qed

lemma pair_sum_edge_gain:
  assumes "2 \<le> b"
  shows "carry_edge_gain (pair_sum_inlet b s) = (if s = b-1 then 1 else 0)"
  using assms by (auto simp: carry_edge_gain_def pair_sum_inlet_def carry_bit_def split: if_splits; arith)

definition conditioned_quiet_carry :: "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "conditioned_quiet_carry b s u v c = pair_sum_inlet b
    ((s + carry_bit u) mod b + (s + carry_bit v) mod b) c"

lemma conditioned_quiet_decimal:
  "conditioned_quiet_carry 10 s u v c = carry_apply (domain (reverse_native_slab_quiet s u v)) c"
  by (simp add: conditioned_quiet_carry_def reverse_native_slab_quiet_def
    reverse_native_slab_digit_def pair_sum_inlet_def carry_apply_decimal_threshold carry_bit_def)

lemma quiet_cubic_edges:
  fixes s :: nat
  assumes "2 \<le> b"
  defines "d \<equiv> s mod b" and "e \<equiv> (s+1) mod b"
  shows "carry_hasse_cubic (conditioned_quiet_carry b s) =
    (if e+e=b-1 then 1 else 0) - 2*(if d+e=b-1 then 1 else 0) + (if d+d=b-1 then 1 else 0)"
proof -
  have at: "carry_edge_gain (conditioned_quiet_carry b s u v) =
    (if (s+carry_bit u) mod b + (s+carry_bit v) mod b = b-1 then 1 else 0)" for u v
    using pair_sum_edge_gain[OF assms(1), of "(s+carry_bit u) mod b + (s+carry_bit v) mod b"]
    by (simp only: conditioned_quiet_carry_def[abs_def])
  show ?thesis unfolding carry_hasse_cubic_def at carry_bit_def d_def e_def
    by (simp add: add.commute; linarith)
qed

lemma conditioned_quiet_cubic_decimal_controls:
  "carry_hasse_cubic (conditioned_quiet_carry 10 4) = -2"
  "carry_hasse_cubic (conditioned_quiet_carry 10 14) = -2"
  "carry_hasse_cubic (conditioned_quiet_carry 3 0) = 1"
  by (simp_all add: quiet_cubic_edges)

lemma quiet_cubic_last_digit:
  assumes b: "2 \<le> b" and end_digit: "s mod b = b-1"
  shows "carry_hasse_cubic (conditioned_quiet_carry b s) = -2"
proof -
  have next_digit: "(s+1) mod b = 0"
    using mod_add_left_eq[of s b 1] end_digit b by simp
  show ?thesis using quiet_cubic_edges[OF b, of s] end_digit next_digit b
    by (simp split: if_splits; arith)
qed

lemma quiet_cubic_even_interior:
  assumes base: "b = 2*n" and b: "2 \<le> b" and inside: "s mod b + 1 < b"
  shows "carry_hasse_cubic (conditioned_quiet_carry b s) = (if s mod b + 1 = n then -2 else 0)"
proof -
  have next_digit: "(s+1) mod b = s mod b + 1"
    using mod_add_left_eq[of s b 1] inside by simp
  have first: "d+d \<noteq> b-1" and last: "(d+1)+(d+1) \<noteq> b-1"
    and middle: "(d+(d+1)=b-1) = (d+1=n)" for d :: nat
    using base b by presburger+
  show ?thesis
    unfolding quiet_cubic_edges[OF b, of s] next_digit
    by (simp only: first last middle if_False; cases "s mod b + 1 = n"; simp)
qed

lemma quiet_cubic_odd_interior:
  assumes base: "b = 2*n+1" and b: "2 \<le> b" and inside: "s mod b + 1 < b"
  shows "carry_hasse_cubic (conditioned_quiet_carry b s) =
    (if s mod b + 1 = n \<or> s mod b = n then 1 else 0)"
proof -
  have next_digit: "(s+1) mod b = s mod b + 1"
    using mod_add_left_eq[of s b 1] inside by simp
  have first: "(d+d=b-1) = (d=n)" and last: "((d+1)+(d+1)=b-1) = (d+1=n)"
    and middle: "d+(d+1) \<noteq> b-1" for d :: nat using base by presburger+
  show ?thesis
    unfolding quiet_cubic_edges[OF b, of s] next_digit
    by (simp only: first last middle if_False; cases "s mod b + 1 = n"; cases "s mod b = n"; simp_all)
qed

ML \<open>
  val checked = @{thms conditioned_birth_decimal conditioned_birth_double_eq conditioned_birth_cubic
    conditioned_birth_decimal_selection conditioned_quiet_decimal quiet_cubic_edges conditioned_quiet_cubic_decimal_controls
    quiet_cubic_last_digit quiet_cubic_even_interior quiet_cubic_odd_interior};
  val _ = if null (Thm_Deps.all_oracles checked) andalso not (Thm_Deps.has_skip_proof checked)
    then () else error "Unchecked conditioned birth carry";
\<close>

end
