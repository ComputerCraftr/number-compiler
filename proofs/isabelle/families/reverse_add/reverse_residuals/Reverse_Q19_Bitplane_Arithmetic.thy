theory Reverse_Q19_Bitplane_Arithmetic
  imports "Reverse_Residuals.Reverse_Native_Slab_Clock" "HOL.Bit_Operations"
begin
unbundle bit_operations_syntax


definition q19_plane_bool :: "bool \<Rightarrow> nat" where "q19_plane_bool b = (if b then 1 else 0)"
definition q19_plane_five_num :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat" where
  "q19_plane_five_num a b d e f = q19_plane_bool a + 2*q19_plane_bool b + 4*q19_plane_bool d + 8*q19_plane_bool e + 16*q19_plane_bool f"
definition q19_plane_gen :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
 "q19_plane_gen b d e f \<longleftrightarrow> f \<or> (e \<and> (b \<or> d))"
definition q19_plane_prop :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
 "q19_plane_prop a b d e f \<longleftrightarrow> a \<and> \<not>b \<and> \<not>d \<and> e \<and> \<not>f"
definition q19_plane_digit_lanes ::
  "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool list" where
 "q19_plane_digit_lanes a b d e f c = (let g=q19_plane_gen b d e f; p=q19_plane_prop a b d e f;
   t0=a; t1=(b \<noteq> g); t2=(d \<noteq> (\<not>b \<and> g)); t3=((e \<noteq> g) \<noteq> (\<not>d \<and> \<not>b \<and> g));
   k=\<not>(p \<and> c)
 in [k \<and> (t0 \<noteq> c), k \<and> (t1 \<noteq> (c \<and> t0)),
     k \<and> (t2 \<noteq> (c \<and> t0 \<and> t1)),
     k \<and> (t3 \<noteq> (c \<and> t0 \<and> t1 \<and> t2))])"


definition q19_plane_digit :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat" where
 "q19_plane_digit a b d e f c = (let v = q19_plane_digit_lanes a b d e f c
 in q19_plane_bool (v!0) + 2*q19_plane_bool(v!1) +
    4*q19_plane_bool(v!2) + 8*q19_plane_bool(v!3))"

lemma q19_plane_classifications:
 "q19_plane_five_num a b d e f < 19 \<Longrightarrow>
 (q19_plane_gen b d e f \<longleftrightarrow> 9 < q19_plane_five_num a b d e f) \<and>
 (q19_plane_prop a b d e f \<longleftrightarrow> q19_plane_five_num a b d e f = 9)"
 by (cases a; cases b; cases d; cases e; cases f; simp add: q19_plane_five_num_def q19_plane_bool_def q19_plane_gen_def q19_plane_prop_def)

lemma q19_plane_decimal_digit:
 "q19_plane_five_num a b d e f < 19 \<Longrightarrow> q19_plane_digit a b d e f c = (q19_plane_five_num a b d e f + q19_plane_bool c) mod 10"
 by (cases a; cases b; cases d; cases e; cases f; cases c; simp add: q19_plane_five_num_def q19_plane_bool_def q19_plane_digit_def q19_plane_digit_lanes_def q19_plane_gen_def q19_plane_prop_def Let_def)

lemma q19_plane_half_or: "((p::nat) OR g) div 2 = ((p div 2) OR (g div 2))"
  using drop_bit_or[of 1 p g] by (simp add: drop_bit_eq_div)

lemma q19_plane_half_xor: "((p::nat) XOR g) div 2 = ((p div 2) XOR (g div 2))"
  using drop_bit_xor[of 1 p g] by (simp add: drop_bit_eq_div)

lemma q19_plane_scan_half:
  assumes "\<not> (odd p \<and> odd g)"
  shows "(((p::nat) OR g) + g + q19_plane_bool c) div 2 =
    ((p div 2) OR (g div 2)) + g div 2 + q19_plane_bool (odd g \<or> (odd p \<and> c))"
proof -
  have eq1: "(p OR g) = 2 * ((p OR g) div 2) + ((p OR g) mod 2)"
    by (metis div_mult_mod_eq mult.commute)
  have eq2: "g = 2 * (g div 2) + (g mod 2)"
    by (metis div_mult_mod_eq mult.commute)
  have mo: "(p OR g) mod 2 = q19_plane_bool (odd p \<or> odd g)"
    by (simp add: q19_plane_bool_def mod2_eq_if even_or_iff)
  have mg: "g mod 2 = q19_plane_bool (odd g)"
    by (simp add: q19_plane_bool_def mod2_eq_if)
  show ?thesis using assms eq1 eq2 mo mg q19_plane_half_or[of p g]
    by (cases "odd p"; cases "odd g"; cases c; simp_all add: q19_plane_bool_def; presburger)
qed

fun q19_plane_scan :: "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> bool" where
  "q19_plane_scan p g c 0 = c"
| "q19_plane_scan p g c (Suc n) = q19_plane_scan (p div 2) (g div 2)
    (odd g \<or> (odd p \<and> c)) n"

lemma q19_plane_scan_word:
  assumes dis: "\<And>k. \<not>(bit p k \<and> bit g k)"
  shows "bit (((p OR g) + g + q19_plane_bool c) XOR p) n \<longleftrightarrow> q19_plane_scan p g c n"
  using dis
proof (induction n arbitrary: p g c)
  case 0
  show ?case using "0.prems"[of 0]
    by (cases "odd p"; cases "odd g"; cases c; auto simp: bit_xor_iff bit_0 q19_plane_bool_def even_or_iff even_xor_iff)
next
  case (Suc n)
  have d0: "\<not>(odd p \<and> odd g)" using Suc.prems[of 0] by (simp add: bit_0)
  have dn: "\<And>k. \<not>(bit (p div 2) k \<and> bit (g div 2) k)"
    using Suc.prems by (simp flip: bit_Suc)
  show ?case using Suc.IH[OF dn, of "odd g \<or> (odd p \<and> c)"]
    by (simp add: bit_Suc bit_xor_iff q19_plane_scan_half[OF d0] q19_plane_half_or q19_plane_half_xor)
qed

lemma q19_plane_scan_physical_step:
  "q19_plane_scan p g c (Suc n) = (bit g n \<or> (bit p n \<and> q19_plane_scan p g c n))"
  by (induction n arbitrary: p g c; simp_all add: bit_0 bit_Suc)

lemma q19_plane_scan_machine_u64:
  assumes dis: "\<And>k. \<not>(bit p k \<and> bit g k)" and bound: "n < 64"
  shows "bit ((take_bit 64 ((p OR g) + g)) XOR p) n \<longleftrightarrow> q19_plane_scan p g False n"
  using q19_plane_scan_word[OF dis, of False n] bound
  by (simp add: q19_plane_bool_def bit_xor_iff bit_take_bit_iff)

fun q19_plane_reverse_carry :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "q19_plane_reverse_carry p g 0 = False"
| "q19_plane_reverse_carry p g (Suc n) =
    (bit g (63-n) \<or> (bit p (63-n) \<and> q19_plane_reverse_carry p g n))"

lemma q19_plane_scan_reverse:
  assumes pr: "\<And>j. j < 64 \<Longrightarrow> bit rp j = bit p (63-j)"
    and gr: "\<And>j. j < 64 \<Longrightarrow> bit rg j = bit g (63-j)"
    and bound: "n \<le> 64"
  shows "q19_plane_scan rp rg False n = q19_plane_reverse_carry p g n"
  using bound
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "n < 64" by simp
  with Suc pr[of n] gr[of n] show ?case
    by (simp only: q19_plane_scan_physical_step q19_plane_reverse_carry.simps; blast)
qed

definition q19_plane_four_num :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat" where
  "q19_plane_four_num a b c d = q19_plane_bool a + 2*q19_plane_bool b + 4*q19_plane_bool c + 8*q19_plane_bool d"

definition q19_plane_add4 :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>
    bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat" where
  "q19_plane_add4 a b c d w x y z = (let
    p0=(a \<noteq> w); p1=(b \<noteq> x); p2=(c \<noteq> y); p3=(d \<noteq> z);
    c1=(a \<and> w); c2=((b \<and> x) \<or> (p1 \<and> c1));
    c3=((c \<and> y) \<or> (p2 \<and> c2)); c4=((d \<and> z) \<or> (p3 \<and> c3))
   in q19_plane_bool p0 + 2*q19_plane_bool(p1 \<noteq> c1) + 4*q19_plane_bool(p2 \<noteq> c2) +
      8*q19_plane_bool(p3 \<noteq> c3) + 16*q19_plane_bool c4)"

lemma q19_plane_add4_exact:
  "q19_plane_add4 a b c d w x y z = q19_plane_four_num a b c d + q19_plane_four_num w x y z"
  by (cases a; cases b; cases c; cases d; cases w; cases x; cases y; cases z;
      simp add: q19_plane_add4_def q19_plane_four_num_def q19_plane_bool_def Let_def)

lemma q19_plane_word_generate:
  "bit ((f::int) OR (e AND (b OR d))) n = q19_plane_gen (bit b n) (bit d n) (bit e n) (bit f n)"
  by (simp add: bit_or_iff bit_and_iff q19_plane_gen_def)

lemma q19_plane_word_propagate:
  "bit ((a::int) AND NOT b AND NOT d AND e AND NOT f) n =
    q19_plane_prop (bit a n) (bit b n) (bit d n) (bit e n) (bit f n)"
  by (simp add: bit_and_iff bit_not_iff q19_plane_prop_def)

lemma q19_plane_word_digit_lane:
  "bit (((base::int) XOR carry) AND NOT (prop AND original_carry)) n =
    ((bit base n \<noteq> bit carry n) \<and> \<not>(bit prop n \<and> bit original_carry n))"
  by (auto simp: bit_and_iff bit_or_iff bit_xor_iff bit_not_iff)

lemma q19_plane_word_add_lane:
  "bit ((a::int) XOR b XOR carry) n = ((bit a n \<noteq> bit b n) \<noteq> bit carry n)"
  "bit ((a::int) AND b OR ((a XOR b) AND carry)) n =
    ((bit a n \<and> bit b n) \<or> ((bit a n \<noteq> bit b n) \<and> bit carry n))"
  by (auto simp: bit_and_iff bit_or_iff bit_xor_iff)

lemma q19_plane_scan_source_disjoint:
  assumes "\<And>j. bit p j = q19_plane_prop (a j) (b j) (d j) (e j) (f j)"
    and "\<And>j. bit g j = q19_plane_gen (b j) (d j) (e j) (f j)"
  shows "\<not>(bit p j \<and> bit g j)"
  using assms by (auto simp: q19_plane_gen_def q19_plane_prop_def)

text \<open>The input plane is the source-issued Q19 coefficient at a physical
position. Its two directional incoming carries remain distinct. The digit
formula supplies the same selected decimal digit as the existing publisher.\<close>

lemma q19_plane_carry_apply:
  assumes "q19_plane_five_num a b d e f < 19"
  shows "carry_apply (domain (q19_plane_five_num a b d e f)) c =
    (q19_plane_gen b d e f \<or> (q19_plane_prop a b d e f \<and> c))"
  using q19_plane_classifications[OF assms]
  by (cases c; auto simp: domain_def)

lemma q19_plane_digit_refinement:
  assumes "q19_plane_five_num a b d e f < 19"
  shows "q19_plane_digit a b d e f c =
    reverse_native_slab_digit (q19_plane_five_num a b d e f) c"
  using q19_plane_decimal_digit[OF assms]
  by (simp add: reverse_native_slab_digit_def carry_bit_def q19_plane_bool_def)

lemma q19_plane_scan_fold:
 "q19_plane_scan p g c n = fold (\<lambda>j z. bit g j \<or> (bit p j \<and> z)) [0..<n] c"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "q19_plane_scan p g c (Suc n) = (bit g n \<or> (bit p n \<and> q19_plane_scan p g c n))"
    by (rule q19_plane_scan_physical_step)
  also have "... = (bit g n \<or> (bit p n \<and> fold (\<lambda>j z. bit g j \<or> (bit p j \<and> z)) [0..<n] c))"
    using Suc.IH by simp
  also have "... = fold (\<lambda>j z. bit g j \<or> (bit p j \<and> z)) [0..<Suc n] c"
    by (simp add: fold_append)
  finally show ?case .
qed

lemma q19_plane_scan_source:
  assumes pb: "\<And>j. bit p j = q19_plane_prop (a j) (b j) (d j) (e j) (f j)"
      and gb: "\<And>j. bit g j = q19_plane_gen (b j) (d j) (e j) (f j)"
      and valid: "\<And>j. q19_plane_five_num (a j) (b j) (d j) (e j) (f j) < 19"
  shows "q19_plane_scan p g c n =
    carry_out c (map (\<lambda>j. q19_plane_five_num (a j) (b j) (d j) (e j) (f j)) [0..<n])"
proof -
  have actions: "(\<lambda>j z. bit g j \<or> (bit p j \<and> z)) =
      (\<lambda>j z. carry_apply (domain (q19_plane_five_num (a j) (b j) (d j) (e j) (f j))) z)"
    using q19_plane_carry_apply[OF valid] pb gb by (intro ext; simp)
  show ?thesis using q19_plane_scan_fold[of p g c n] actions
    by (simp add: carry_out_def fold_map comp_def)
qed

lemma q19_plane_machine_source_carry:
  fixes p g :: nat
  assumes pb: "\<And>j. bit p j = q19_plane_prop (a j) (b j) (d j) (e j) (f j)"
      and gb: "\<And>j. bit g j = q19_plane_gen (b j) (d j) (e j) (f j)"
      and valid: "\<And>j. q19_plane_five_num (a j) (b j) (d j) (e j) (f j) < 19"
      and bound: "n < 64"
  shows "bit ((take_bit 64 ((p OR g) + g)) XOR p) n =
    carry_out False (map (\<lambda>j. q19_plane_five_num (a j) (b j) (d j) (e j) (f j)) [0..<n])"
proof -
  have dis: "\<And>j. \<not>(bit p j \<and> bit g j)"
    by (rule q19_plane_scan_source_disjoint[OF pb gb])
  have machine: "bit ((take_bit 64 ((p OR g) + g)) XOR p) n =
      q19_plane_scan p g False n"
    by (rule q19_plane_scan_machine_u64; fact dis bound)
  have source: "q19_plane_scan p g False n =
      carry_out False (map (\<lambda>j. q19_plane_five_num (a j) (b j) (d j) (e j) (f j)) [0..<n])"
    by (rule q19_plane_scan_source; fact pb gb valid)
  show ?thesis using machine source by simp
qed

lemma q19_plane_machine_reverse_word:
  fixes p g rp rg result :: nat
  assumes pr: "\<And>j. j < 64 \<Longrightarrow> bit rp j = bit p (63-j)"
      and gr: "\<And>j. j < 64 \<Longrightarrow> bit rg j = bit g (63-j)"
      and rr: "\<And>j. j < 64 \<Longrightarrow> bit result j =
        bit ((take_bit 64 ((rp OR rg) + rg)) XOR rp) (63-j)"
      and dis: "\<And>j. \<not>(bit rp j \<and> bit rg j)"
      and bound: "j < 64"
  shows "bit result j = q19_plane_reverse_carry p g (63-j)"
proof -
  have index: "63-j < 64" using bound by simp
  have machine: "bit ((take_bit 64 ((rp OR rg) + rg)) XOR rp) (63-j) =
      q19_plane_scan rp rg False (63-j)"
    by (rule q19_plane_scan_machine_u64; fact dis index)
  have reversed: "q19_plane_scan rp rg False (63-j) = q19_plane_reverse_carry p g (63-j)"
    apply (rule q19_plane_scan_reverse)
      apply (rule pr; assumption)
     apply (rule gr; assumption)
    using index by simp
  show ?thesis using rr[OF bound] machine reversed by simp
qed


lemma q19_plane_digit_lanes_value:
  "q19_plane_four_num ((q19_plane_digit_lanes a b d e f c)!0)
    ((q19_plane_digit_lanes a b d e f c)!1) ((q19_plane_digit_lanes a b d e f c)!2)
    ((q19_plane_digit_lanes a b d e f c)!3) = q19_plane_digit a b d e f c"
  by (simp add: q19_plane_four_num_def q19_plane_digit_lanes_def q19_plane_digit_def Let_def)

theorem q19_plane_two_physical_digits:
  fixes a b d e f c w x y z h t :: bool and ls rs :: "bool list"
  assumes l: "q19_plane_five_num a b d e f < 19"
      and r: "q19_plane_five_num w x y z h < 19"
  defines "ls \<equiv> q19_plane_digit_lanes a b d e f c"
      and "rs \<equiv> q19_plane_digit_lanes w x y z h t"
  shows "q19_plane_add4 (ls!0) (ls!1) (ls!2) (ls!3)
      (rs!0) (rs!1) (rs!2) (rs!3) =
    reverse_native_slab_digit (q19_plane_five_num a b d e f) c +
    reverse_native_slab_digit (q19_plane_five_num w x y z h) t"
  using q19_plane_digit_refinement[OF l, of c] q19_plane_digit_refinement[OF r, of t]
  by (simp only: ls_def rs_def q19_plane_add4_exact q19_plane_digit_lanes_value)

end
