theory Reverse_Q19_Mixed_EQ_Phase
  imports Reverse_Ordered_Carry_Gram Reverse_Native_Slab_Core
begin

text \<open>A three-position mixed-EQ port has one identity carry between two
opposite constant resets. The receiving source supplies both exterior
inlets. These equations are valid for both choices of the high phase and
in every rotation of the ordered period.\<close>

definition q19_mixed_center :: "bool \<Rightarrow> nat \<Rightarrow> nat list" where
  "q19_mixed_center h u = [u + (if h then 10 else 0),9,18 - (u + (if h then 10 else 0))]"

lemma q19_mixed_center_ports:
  assumes "u < 9"
  shows "gram_ports (\<not> h) h (q19_mixed_center h u) 0 = (\<not>h,\<not>h)"
    "gram_ports (\<not> h) h (q19_mixed_center h u) 1 = (h,\<not>h)"
    "gram_ports (\<not> h) h (q19_mixed_center h u) 2 = (h,h)"
proof -
  have choices: "u=0 \<or> u=1 \<or> u=2 \<or> u=3 \<or> u=4 \<or> u=5 \<or> u=6 \<or> u=7 \<or> u=8"
    using assms by arith
  show "gram_ports (\<not> h) h (q19_mixed_center h u) 0 = (\<not>h,\<not>h)"
    using choices by (elim disjE; hypsubst_thin; cases h;
      simp_all add: q19_mixed_center_def gram_ports_def carry_out_def domain_def)
  show "gram_ports (\<not> h) h (q19_mixed_center h u) 1 = (h,\<not>h)"
    using choices by (elim disjE; hypsubst_thin; cases h;
      simp_all add: q19_mixed_center_def gram_ports_def carry_out_def domain_def)
  show "gram_ports (\<not> h) h (q19_mixed_center h u) 2 = (h,h)"
    using choices by (elim disjE; hypsubst_thin; cases h;
      simp_all add: q19_mixed_center_def gram_ports_def carry_out_def domain_def)
qed

lemma q19_mixed_rotated_ports:
  assumes "u < 9"
  shows "gram_ports h (\<not>h) (rotate 1 (q19_mixed_center h u)) 0 = (h,\<not>h)"
    "gram_ports h (\<not>h) (rotate 1 (q19_mixed_center h u)) 1 = (h,h)"
    "gram_ports h (\<not>h) (rotate 1 (q19_mixed_center h u)) 2 = (\<not>h,\<not>h)"
    "gram_ports h (\<not>h) (rotate 2 (q19_mixed_center h u)) 0 = (h,h)"
    "gram_ports h (\<not>h) (rotate 2 (q19_mixed_center h u)) 1 = (\<not>h,\<not>h)"
    "gram_ports h (\<not>h) (rotate 2 (q19_mixed_center h u)) 2 = (h,\<not>h)"
proof -
  have choices: "u=0 \<or> u=1 \<or> u=2 \<or> u=3 \<or> u=4 \<or> u=5 \<or> u=6 \<or> u=7 \<or> u=8"
    using assms by arith
  show "gram_ports h (\<not>h) (rotate 1 (q19_mixed_center h u)) 0 = (h,\<not>h)"
    using choices by (elim disjE; hypsubst_thin; cases h;
      simp_all add: q19_mixed_center_def gram_ports_def carry_out_def domain_def rotate_def eval_nat_numeral)
  show "gram_ports h (\<not>h) (rotate 1 (q19_mixed_center h u)) 1 = (h,h)"
    using choices by (elim disjE; hypsubst_thin; cases h;
      simp_all add: q19_mixed_center_def gram_ports_def carry_out_def domain_def rotate_def eval_nat_numeral)
  show "gram_ports h (\<not>h) (rotate 1 (q19_mixed_center h u)) 2 = (\<not>h,\<not>h)"
    using choices by (elim disjE; hypsubst_thin; cases h;
      simp_all add: q19_mixed_center_def gram_ports_def carry_out_def domain_def rotate_def eval_nat_numeral)
  show "gram_ports h (\<not>h) (rotate 2 (q19_mixed_center h u)) 0 = (h,h)"
    using choices by (elim disjE; hypsubst_thin; cases h;
      simp_all add: q19_mixed_center_def gram_ports_def carry_out_def domain_def rotate_def eval_nat_numeral)
  show "gram_ports h (\<not>h) (rotate 2 (q19_mixed_center h u)) 1 = (\<not>h,\<not>h)"
    using choices by (elim disjE; hypsubst_thin; cases h;
      simp_all add: q19_mixed_center_def gram_ports_def carry_out_def domain_def rotate_def eval_nat_numeral)
  show "gram_ports h (\<not>h) (rotate 2 (q19_mixed_center h u)) 2 = (h,\<not>h)"
    using choices by (elim disjE; hypsubst_thin; cases h;
      simp_all add: q19_mixed_center_def gram_ports_def carry_out_def domain_def rotate_def eval_nat_numeral)
qed

theorem q19_mixed_source_selected_ports:
  assumes range: "u < 9"
      and source: "s = l @ q19_mixed_center h u @ r"
      and left: "carry_out a l = (\<not> h)"
      and right: "carry_out b (rev r) = h"
      and idx: "i < 3"
  shows "gram_ports a b s (length l + i) =
    (if i = 0 then (\<not>h,\<not>h) else if i = 1 then (h,\<not>h) else (h,h))"
proof -
  have within: "i < length (q19_mixed_center h u)"
    using idx by (simp add: q19_mixed_center_def)
  have inside: "gram_ports a b s (length l + i) =
    gram_ports (\<not> h) h (q19_mixed_center h u) i"
    using source left right
    by (simp only: gram_ports_right gram_ports_left[OF within])
  have choices: "i=0 \<or> i=1 \<or> i=2" using idx by arith
  show ?thesis using choices inside q19_mixed_center_ports[OF range]
    by (elim disjE; simp)
qed

definition q19_mixed_bit :: "nat \<Rightarrow> bool \<Rightarrow> nat" where
  "q19_mixed_bit s c = (if 10 \<le> s + (if c then 1 else 0) then 1 else 0)"

definition q19_mixed_digit :: "nat \<Rightarrow> bool \<Rightarrow> nat" where
  "q19_mixed_digit s c = (s + (if c then 1 else 0)) mod 10"

definition q19_mixed_step :: "bool \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat list" where
  "q19_mixed_step growth h u = (let s = q19_mixed_center h u in
    map (\<lambda>i. let (a,b) = gram_ports (\<not>h) h s i;
                   low = q19_mixed_digit (s!i) a;
                   high = (if growth then
                     ((s ! ((i+2) mod 3)) + q19_mixed_bit (s!i) b) mod 10
                     else q19_mixed_digit (s!i) b)
                in low + high) [0,1,2])"

theorem q19_mixed_selected_physical_step:
  assumes "u < 9"
  shows "q19_mixed_step False h u =
    [2*(u+1-(if h then 1 else 0)),9,18-2*(u+1-(if h then 1 else 0))]"
    "q19_mixed_step True h u =
    [9,18-(8-u+(if h then 10 else 0)),8-u+(if h then 10 else 0)]"
proof -
  have choices: "u=0 \<or> u=1 \<or> u=2 \<or> u=3 \<or> u=4 \<or> u=5 \<or> u=6 \<or> u=7 \<or> u=8"
    using assms by arith
  show "q19_mixed_step False h u =
    [2*(u+1-(if h then 1 else 0)),9,18-2*(u+1-(if h then 1 else 0))]"
    using choices by (elim disjE; hypsubst_thin; cases h; simp_all add: q19_mixed_step_def
      q19_mixed_center_def gram_ports_def carry_out_def domain_def
      q19_mixed_bit_def q19_mixed_digit_def Let_def)
  show "q19_mixed_step True h u =
    [9,18-(8-u+(if h then 10 else 0)),8-u+(if h then 10 else 0)]"
    using choices by (elim disjE; hypsubst_thin; cases h; simp_all add: q19_mixed_step_def
      q19_mixed_center_def gram_ports_def carry_out_def domain_def
      q19_mixed_bit_def q19_mixed_digit_def Let_def)
qed

definition q19_mixed_rotated_step :: "nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat list" where
  "q19_mixed_rotated_step k growth h u =
    (let s = rotate k (q19_mixed_center h u);
         a = (if k = 0 then \<not>h else h);
         b = (if k = 0 then h else \<not>h)
     in map (\<lambda>i. let (l,r) = gram_ports a b s i;
                   low = q19_mixed_digit (s!i) l;
                   high = (if growth then
                     ((s ! ((i+2) mod 3)) + q19_mixed_bit (s!i) r) mod 10
                     else q19_mixed_digit (s!i) r)
                in low + high) [0,1,2])"

lemma q19_rotate_two_three:
  "rotate 2 [a, b, c] = [c, a, b]"
  by (simp add: rotate_def eval_nat_numeral)

theorem q19_mixed_step_rotation:
  assumes "u < 9" "k < 3"
  shows "q19_mixed_rotated_step k growth h u = rotate k (q19_mixed_step growth h u)"
proof -
  have uc: "u=0 \<or> u=1 \<or> u=2 \<or> u=3 \<or> u=4 \<or> u=5 \<or> u=6 \<or> u=7 \<or> u=8"
    using assms by arith
  have kc: "k=0 \<or> k=1 \<or> k=2" using assms by arith
  show ?thesis using uc kc
    by (elim disjE; hypsubst_thin; cases h; cases growth;
      simp_all add: q19_mixed_rotated_step_def q19_mixed_step_def
        q19_mixed_center_def gram_ports_def carry_out_def domain_def
        q19_mixed_bit_def q19_mixed_digit_def Let_def q19_rotate_two_three)
qed

lemma q19_mixed_bit_carry:
  "q19_mixed_bit s b = carry_bit (carry_apply (domain s) b)"
  by (cases b; simp add: q19_mixed_bit_def carry_bit_def domain_def)

lemma q19_mixed_actual_source_cell:
  assumes valid: "valid_pair source" and positive: "0 < i" and bound: "i < length source"
  defines "a \<equiv> carry_out False (take i source)"
      and "b \<equiv> carry_out False (rev (drop (Suc i) source))"
  shows "step source ! i = q19_mixed_digit (source!i) a +
    (if carry_out False source then
       ((source!(i-1)) + q19_mixed_bit (source!i) b) mod 10
     else q19_mixed_digit (source!i) b)"
proof -
  let ?pre = "take i source"
  let ?post = "drop (Suc i) source"
  let ?s = "source!i"
  have all: "\<forall>x\<in>set source. x < 19" using valid by (auto simp: valid_pair_def)
  have pre: "\<forall>x\<in>set ?pre. x<19" using all set_take_subset[of i source] by blast
  have post: "\<forall>x\<in>set ?post. x<19" using all set_drop_subset[of "Suc i" source] by blast
  have cell: "?s<19" using all bound by auto
  have nonempty: "?pre \<noteq> []" using positive bound by auto
  obtain k where ki: "i=Suc k" using positive by (cases i) auto
  have kb: "k<length source" using ki bound by arith
  have last: "last ?pre = source!(i-1)"
    using take_Suc_conv_app_nth[OF kb] ki by simp
  have split: "carry_out (carry_apply (domain ?s) (carry_out False ?pre)) ?post = carry_out False source"
    by (rule carry_out_split_nth[OF bound])
  have scan: "reverse_emit (reverse_left_fold ?pre) ?s (reverse_right_fold ?post) = step source ! i"
    by (rule slab_core_physical_scan[OF valid positive bound])
  show ?thesis
  proof (cases "carry_out False source")
    case False
    have E: "reverse_emit (reverse_left_fold ?pre) ?s (reverse_right_fold ?post) =
      mirror_pair_step ?s (carry_bit a) (carry_bit b)"
      using reverse_emit_no_growth_cell[OF pre post cell] split False by (simp add: a_def b_def)
    show ?thesis using E scan False by (simp add: mirror_pair_step_def q19_mixed_digit_def carry_bit_def)
  next
    case True
    have E: "reverse_emit (reverse_left_fold ?pre) ?s (reverse_right_fold ?post) =
      growth_pair_step ?s (source!(i-1)) (carry_bit a)
        (carry_bit (carry_apply (domain ?s) b))"
      using reverse_emit_growth_interior[OF pre post cell nonempty] split True last
      by (simp add: a_def b_def)
    show ?thesis using E scan True
      by (simp add: growth_pair_step_def q19_mixed_digit_def carry_bit_def q19_mixed_bit_carry)
  qed
qed

lemma q19_mixed_step_selected:
  fixes h :: bool and u :: nat
  assumes "j < 3"
  defines "s \<equiv> q19_mixed_center h u"
  defines "ports \<equiv> gram_ports (\<not>h) h s j"
  shows "q19_mixed_step growth h u ! j = q19_mixed_digit (s!j) (fst ports) +
    (if growth then ((s ! ((j+2) mod 3)) + q19_mixed_bit (s!j) (snd ports)) mod 10
     else q19_mixed_digit (s!j) (snd ports))"
proof -
  have cases: "j=0 \<or> j=1 \<or> j=2" using assms by arith
  show ?thesis using cases
    by (elim disjE; simp add: s_def ports_def q19_mixed_step_def Let_def split: prod.splits)
qed

theorem q19_mixed_selected_source_physical:
  assumes valid: "valid_pair source" and positive: "0<i" and bound: "i<length source"
      and phase: "j<3" "u<9"
      and cell: "source!i = q19_mixed_center h u ! j"
      and predecessor: "source!(i-1) = q19_mixed_center h u ! ((j+2) mod 3)"
      and inlets: "gram_ports False False source i = gram_ports (\<not>h) h (q19_mixed_center h u) j"
  shows "step source ! i = q19_mixed_step (carry_out False source) h u ! j"
    and "length (step source) = length source + (if carry_out False source then 1 else 0)"
proof -
  let ?ports = "gram_ports (\<not>h) h (q19_mixed_center h u) j"
  have low: "carry_out False (take i source) = fst ?ports"
    and high: "carry_out False (rev (drop (Suc i) source)) = snd ?ports"
    using inlets by (simp_all add: gram_ports_def)
  show "step source ! i = q19_mixed_step (carry_out False source) h u ! j"
    using q19_mixed_actual_source_cell[OF valid positive bound]
      q19_mixed_step_selected[OF phase(1), where h=h and u=u and growth="carry_out False source"]
      cell predecessor low high by simp
  show "length (step source) = length source + (if carry_out False source then 1 else 0)"
    by (simp add: length_digits_exact)
qed

theorem q19_mixed_quiet_after_first_quiet:
  fixes h :: bool and u :: nat
  assumes "u < 9"
  defines "x \<equiv> 2 * (u + 1 - (if h then 1 else 0))"
  defines "y \<equiv> 2 * (x mod 10 + 1 - x div 10)"
  shows "(y div 2 + 1) mod 11 = (2 * (x div 2 + 1)) mod 11"
proof -
  have choices: "u=0 \<or> u=1 \<or> u=2 \<or> u=3 \<or> u=4 \<or> u=5 \<or> u=6 \<or> u=7 \<or> u=8"
    using assms(1) by arith
  show ?thesis unfolding y_def x_def using choices
    by (elim disjE; cases h; simp_all)
qed

ML \<open>
  val checked = @{thms q19_mixed_center_ports q19_mixed_rotated_ports q19_mixed_source_selected_ports
    q19_mixed_selected_physical_step q19_mixed_step_rotation q19_mixed_selected_source_physical
    q19_mixed_quiet_after_first_quiet};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "mixed-EQ phase ports depend on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "mixed-EQ phase ports have skipped proofs" else ();
\<close>

end
