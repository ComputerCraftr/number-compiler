theory Mahler_CF_Terminal_8
  imports Mahler_CF_Low_Period
begin

text \<open>The coefficient is the decimal digit plus one. The shear is on
the right because the terminal row is the last ordered letter. The clip
proof retains the exact start and length; a nonterminal clip has no shear.\<close>

definition cf_terminal_shear :: "nat ordered_matrix2" where
  "cf_terminal_shear = Ordered_Matrix2 1 0 5 1"

lemma cf_terminal_letter_shear:
  "mahler_cf_digit (d+5) = ordered_matrix2_multiply (mahler_cf_digit d) cf_terminal_shear"
  by (simp add: mahler_cf_digit_def cf_terminal_shear_def)

definition cf_8_digit where
  "cf_8_digit q t = (q div 2^t) mod 10"

definition cf_8_clip_word where
  "cf_8_clip_word q start count = map (cf_8_digit q) [start..<start+count]"

lemma cf_8_terminal_lift_digit:
  fixes q t :: nat
  assumes q: "q<640" and t: "t<8"
  shows "cf_8_digit (q+640) t = (if t=7 then cf_8_digit q t + 5 else cf_8_digit q t)"
proof (cases "t=7")
  case True
  have bound: "q div 128 < 5" using q by (simp add: div_less_iff_less_mult)
  show ?thesis using True bound by (simp add: cf_8_digit_def)
next
  case False
  have le: "t\<le>6" using t False by arith
  have power: "(2::nat)^t * 2^(6-t) = 64"
    using le by (simp only: power_add[symmetric]) simp
  have factor: "(640::nat) = 2^t * (10*2^(6-t))"
    using power by (simp add: algebra_simps)
  have quo: "(q+640) div 2^t = 10*2^(6-t) + q div 2^t"
    by (subst factor) simp
  show ?thesis using False by (simp add: cf_8_digit_def quo mod_add_eq)
qed

lemma cf_8_admitted_source:
  fixes q :: nat
  shows "q mod 1280 = q mod 640 + 640*((q div 640) mod 2)"
  using mod_mult2_eq[of q 640 2] by (simp add: add.commute)

lemma cf_8_inlet_digit:
  fixes q :: nat
  defines "r \<equiv> q mod 5" and "e \<equiv> q mod 2"
  shows "q mod 10 = r + 5*((r+e) mod 2)"
    and "(q div 2) mod 5 = (3*(r+5-e)) mod 5"
proof -
  let ?d = "q mod 10"
  have bound: "?d<10" by simp
  have c5: "?d mod 5 = q mod 5" by (rule mod_mod_cancel) simp
  have c2: "?d mod 2 = q mod 2" by (rule mod_mod_cancel) simp
  have row: "(?d div 2) mod 5 = (q div 2) mod 5"
    using mahler_cf_observed_remainder[where source=q and divisor=2 and factor=5 and base=5]
    by simp
  have cases: "?d=0 \<or> ?d=1 \<or> ?d=2 \<or> ?d=3 \<or> ?d=4 \<or>
      ?d=5 \<or> ?d=6 \<or> ?d=7 \<or> ?d=8 \<or> ?d=9" using bound by arith
  show "q mod 10 = r + 5*((r+e) mod 2)"
    using cases by (simp only: r_def e_def c5[symmetric] c2[symmetric]; auto)
  show "(q div 2) mod 5 = (3*(r+5-e)) mod 5"
    using cases by (simp only: r_def e_def c5[symmetric] c2[symmetric] row[symmetric]; auto)
qed

theorem cf_8_clip_lift_action:
  fixes q start count :: nat
  assumes q: "q<640" and clip: "start+count\<le>8"
  shows "mahler_cf_word (cf_8_clip_word (q+640) start count) =
    (if count>0 \<and> start+count=8 then
      ordered_matrix2_multiply (mahler_cf_word (cf_8_clip_word q start count)) cf_terminal_shear
     else mahler_cf_word (cf_8_clip_word q start count))"
proof (cases "count>0 \<and> start+count=8")
  case False
  have before: "t<7" if "t\<in>set [start..<start+count]" for t
    using that clip False by auto
  have same: "cf_8_clip_word (q+640) start count = cf_8_clip_word q start count"
    unfolding cf_8_clip_word_def
  proof (rule map_cong[OF refl])
    fix t assume t: "t \<in> set [start..<start+count]"
    have less: "t<7" by (rule before[OF t])
    have within: "t<8" using less by arith
    show "cf_8_digit (q+640) t = cf_8_digit q t"
      using cf_8_terminal_lift_digit[OF q within] less by simp
  qed
  show ?thesis by (simp only: False if_False same)
next
  case True
  then have s: "start\<le>7" and finish: "start+count=8" by arith+
  have seq: "[start..<8] = [start..<7]@[7]"
    using upt_Suc_append[OF s] by simp
  have upto: "[start..<start+count] = [start..<7]@[7]"
    by (simp only: finish seq)
  have same: "map (cf_8_digit (q+640)) [start..<7] = map (cf_8_digit q) [start..<7]"
    by (rule map_cong[OF refl]) (use q in \<open>auto simp: cf_8_terminal_lift_digit\<close>)
  have top: "cf_8_digit (q+640) 7 = cf_8_digit q 7+5"
    using cf_8_terminal_lift_digit[OF q, of 7] by simp
  have eq: "cf_8_clip_word (q+640) start count =
      map (cf_8_digit q) [start..<7] @ [cf_8_digit q 7+5]"
    by (simp add: cf_8_clip_word_def upto same top)
  have orig: "cf_8_clip_word q start count = map (cf_8_digit q) [start..<7] @ [cf_8_digit q 7]"
    by (simp add: cf_8_clip_word_def upto)
  show ?thesis using True
    by (simp add: eq orig mahler_cf_word_append mahler_cf_word_def
      cf_terminal_letter_shear ordered_matrix2_multiply_associative)
qed

lemma cf_8_digit_source_modulus:
  fixes q t :: nat
  assumes "t<8"
  shows "cf_8_digit (q mod 1280) t = cf_8_digit q t"
proof -
  have le: "t\<le>7" using assms by arith
  have power: "(2::nat)^t * 2^(7-t) = 128"
    using le by (simp only: power_add[symmetric]) simp
  have factor: "(1280::nat) = 2^t * (10*2^(7-t))"
    using power by (simp add: algebra_simps)
  have observed: "((q mod (2^t*(10*2^(7-t)))) div 2^t) mod 10 = (q div 2^t) mod 10"
    by (rule mahler_cf_observed_remainder) simp_all
  show ?thesis using observed by (simp only: factor[symmetric] cf_8_digit_def)
qed

lemma cf_8_clip_source_modulus:
  fixes q start count :: nat
  assumes "start+count\<le>8"
  shows "cf_8_clip_word (q mod 1280) start count = cf_8_clip_word q start count"
  unfolding cf_8_clip_word_def
proof (rule map_cong[OF refl])
  fix t assume "t\<in>set [start..<start+count]"
  then have "t<8" using assms by simp
  then show "cf_8_digit (q mod 1280) t = cf_8_digit q t"
    by (rule cf_8_digit_source_modulus)
qed

theorem cf_8_admitted_clip_action:
  fixes q start count :: nat
  assumes clip: "start+count\<le>8"
  defines "q0 \<equiv> q mod 640" and "epsilon \<equiv> (q div 640) mod 2"
  shows "mahler_cf_word (cf_8_clip_word q start count) =
    (if epsilon=1 \<and> count>0 \<and> start+count=8 then
      ordered_matrix2_multiply (mahler_cf_word (cf_8_clip_word q0 start count)) cf_terminal_shear
     else mahler_cf_word (cf_8_clip_word q0 start count))"
proof -
  have bound: "q0<640" by (simp add: q0_def)
  have source: "q mod 1280 = q0+640*epsilon"
    using cf_8_admitted_source[of q] by (simp only: q0_def epsilon_def)
  have eps: "epsilon=0 \<or> epsilon=1" using mod_less_divisor[of 2 "q div 640"]
    by (simp add: epsilon_def; arith)
  have exact: "cf_8_clip_word q start count = cf_8_clip_word (q mod 1280) start count"
    using cf_8_clip_source_modulus[OF clip, of q] by simp
  show ?thesis using eps cf_8_clip_lift_action[OF bound clip]
    by (auto simp: exact source)
qed

lemma cf_8_clip_concatenate:
  "cf_8_clip_word q start (left+right) =
    cf_8_clip_word q start left @ cf_8_clip_word q (start+left) right"
proof -
  have split: "[start..<start+(left+right)] = [start..<start+left] @ [start+left..<start+left+right]"
    using upt_add_eq_append[of start "start+left" right] by (simp only: add.assoc le_add1)
  show ?thesis by (simp only: cf_8_clip_word_def split map_append add.assoc)
qed

theorem cf_8_ordered_clip_composition:
  "mahler_cf_word (cf_8_clip_word q start (left+right)) =
    ordered_matrix2_multiply (mahler_cf_word (cf_8_clip_word q start left))
      (mahler_cf_word (cf_8_clip_word q (start+left) right))"
  by (simp only: cf_8_clip_concatenate mahler_cf_word_append)

theorem cf_five_inlet_source_step:
  fixes q t :: nat
  defines "x \<equiv> q div 2^t" and "r \<equiv> (q div 2^t) mod 5" and "e \<equiv> (q div 2^t) mod 2"
  shows "cf_8_digit q t = r+5*((r+e) mod 2)"
    and "(q div 2^(Suc t)) mod 5 = (3*(r+5-e)) mod 5"
proof -
  show "cf_8_digit q t = r+5*((r+e) mod 2)"
    using cf_8_inlet_digit(1)[of x] by (simp only: x_def r_def e_def cf_8_digit_def)
  have pow: "(2::nat)^(Suc t) = 2^t*2" by simp
  show "(q div 2^(Suc t)) mod 5 = (3*(r+5-e)) mod 5"
    using cf_8_inlet_digit(2)[of x] by (simp only: x_def r_def e_def pow div_mult2_eq)
qed

definition cf5_letter :: "nat \<Rightarrow> nat \<Rightarrow> nat ordered_matrix2 \<times> nat" where
  "cf5_letter r e = (mahler_cf_digit (r+5*((r+e) mod 2)), (3*(r+5-e)) mod 5)"

fun cf5_run :: "nat \<Rightarrow> nat list \<Rightarrow> nat ordered_matrix2 \<times> nat" where
  "cf5_run r [] = (ordered_matrix2_identity, r)"
| "cf5_run r (e#es) =
    (let (a,s) = cf5_letter r e; (b,t) = cf5_run s es
     in (ordered_matrix2_multiply a b,t))"

lemma cf5_run_append:
  "cf5_run r (xs@ys) =
    (let (a,s) = cf5_run r xs; (b,t) = cf5_run s ys in (ordered_matrix2_multiply a b,t))"
  by (induction xs arbitrary: r) (auto simp: Let_def ordered_matrix2_multiply_associative split: prod.splits)

corollary cf5_run_square:
  "cf5_run r (xs@xs) =
    (let (a,s) = cf5_run r xs; (b,t) = cf5_run s xs in (ordered_matrix2_multiply a b,t))"
  by (rule cf5_run_append)

definition cf5_source_bits where
  "cf5_source_bits q start count = map (\<lambda>t. (q div 2^t) mod 2) [start..<start+count]"

lemma cf5_letter_source:
  "cf5_letter ((q div 2^t) mod 5) ((q div 2^t) mod 2) =
    (mahler_cf_digit (cf_8_digit q t), (q div 2^(Suc t)) mod 5)"
  using cf_five_inlet_source_step[of q t]
  by (simp only: cf5_letter_def)

theorem cf5_source_ordered_action:
  "cf5_run ((q div 2^start) mod 5) (cf5_source_bits q start count) =
    (mahler_cf_word (cf_8_clip_word q start count), (q div 2^(start+count)) mod 5)"
proof (induction count arbitrary: start)
  case 0
  then show ?case by (simp add: cf5_source_bits_def cf_8_clip_word_def
      mahler_cf_word_def ordered_matrix2_identity_def)
next
  case (Suc count)
  have interval: "[start..<start+Suc count] = start # [Suc start..<Suc start+count]"
    by (subst upt_conv_Cons) (simp_all add: algebra_simps)
  have tail: "cf5_source_bits q start (Suc count) =
      ((q div 2^start) mod 2) # cf5_source_bits q (Suc start) count"
    by (simp only: cf5_source_bits_def interval list.map)
  have word: "cf_8_clip_word q start (Suc count) =
      cf_8_digit q start # cf_8_clip_word q (Suc start) count"
    by (simp only: cf_8_clip_word_def interval list.map)
  have factor: "mahler_cf_word (d#ds) =
      ordered_matrix2_multiply (mahler_cf_digit d) (mahler_cf_word ds)" for d ds
    using mahler_cf_word_append[of "[d]" ds]
    by (simp add: mahler_cf_word_def; cases "mahler_cf_digit d"; simp add: ordered_matrix2_identity_def)
  show ?case using Suc.IH[of "Suc start"] cf5_letter_source[of q start]
    by (simp only: tail word cf5_run.simps Let_def prod.case factor add_Suc_right add_Suc)
qed

ML \<open>
 val facts = @{thms cf_terminal_letter_shear cf_8_terminal_lift_digit cf_8_admitted_source cf_8_inlet_digit cf_8_clip_lift_action cf_8_admitted_clip_action cf_8_ordered_clip_composition cf_five_inlet_source_step cf5_run_append cf5_run_square cf5_source_ordered_action};
 val _ = if null (Thm_Deps.all_oracles facts) andalso not (Thm_Deps.has_skip_proof facts)
   then () else error "Unverified 8x1 terminal facts";
\<close>
end
