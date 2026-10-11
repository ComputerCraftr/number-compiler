theory Comma_Decade_Orbit_Quotient
  imports Comma_Fast_Control.Comma_Fast_Kernel
    Comma_Decade_Residual_Core.Comma_Decade_Residual_Core
    Comma_Decade_Orbit_Arithmetic
begin

ML \<open>
structure Comma_Decade_Orbit_Quotient_Profile =
struct
  val report = Comma_Proof_Profile.timer "Decade orbit quotient"
end
val _ = Comma_Decade_Orbit_Quotient_Profile.report "entered"
\<close>

definition comma_offset_representatives :: "nat list" where
  "comma_offset_representatives =
    [0,10,20,30,40,50,60,70,80,90,9,19,29,39,49,59,69,79,8,18,28,38,48,58,68,
     7,17,27,37,47,57,6,16,26,36,46,5,15,25,35,4,14,24,3,13,2]"

definition comma_offset_representative :: "nat \<Rightarrow> nat" where
  "comma_offset_representative x=comma_offset_representatives!comma_offset_orbit x"

lemma comma_offset_representatives_checked:
  "list_all (\<lambda>i. comma_offset_representatives!i\<le>90 \<and>
    comma_offset_orbit (comma_offset_representatives!i)=i) [0..<46]"
proof -
  ML_prf \<open>Comma_Decade_Orbit_Quotient_Profile.report "representatives-check entered"\<close>
  show ?thesis by (tactic \<open>
    simp_tac (Comma_Entry_Arithmetic.natural_context @{context} addsimps
      @{thms comma_offset_representatives_def comma_offset_orbit_def comma_digit_orbit_sum_def
        power2_eq_square list_all_Nil_iff list_all_Cons_iff upt_rec nth_Cons'
        of_nat_numeral of_nat_0 of_nat_1 zmod_zminus1_eq_if zmod_zminus2_eq_if}) 1
  \<close>)
qed
ML \<open>
  val _ = Comma_Decade_Orbit_Quotient_Profile.report
    "representatives-check submitted"
\<close>

lemma comma_offset_representative_admitted:
  "comma_offset_representative x\<le>90"
  "comma_offset_orbit (comma_offset_representative x)=comma_offset_orbit x"
  using comma_offset_representatives_checked comma_offset_orbit_bound[of x]
  by (auto simp: list_all_iff comma_offset_representative_def)

lemma comma_sector_one_period:
  assumes "d<10"
  shows "comma_finite_period_fast 1 d=460"
proof -
  have "comma_finite_period_fast 1 d=(replicate 10 460)!d"
    by (simp add: comma_finite_period_fast_def eval_nat_numeral)
  then show ?thesis using assms by simp
qed

lemma comma_sector_one_phase:
  "comma_entry_alphabet_phase 1 r 0 x=(r mod 924+919) mod 22"
proof -
  have period: "comma_finite_period_fast 1 (x mod 10)=460"
    by (rule comma_sector_one_period) simp
  show ?thesis
    by (simp only: comma_entry_alphabet_phase_def period;
      simp add: comma_short_period_def)
qed

definition comma_offset_endpoint_check :: bool where
  "comma_offset_endpoint_check =
    list_all (\<lambda>x. list_all (\<lambda>k.
      comma_entry_alphabet_endpoint 1 x k=
        comma_entry_alphabet_endpoint 1 (comma_offset_representative x) k)
      [0..<22]) [0..<91]"

text \<open>The endpoint depends only on the residue modulo 460. A single
Near-edge transport lemma proves invariance under the canonical sector-one
orbit step; fixed iteration and orbit-key completeness then extend that
equation to all offsets with the same orbit key. The representative list is
used only to select a canonical member of each key class.\<close>

definition comma_offset_endpoint_headroom :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_offset_endpoint_headroom x k =
    2 + nat ((int (comma_power_table 460 ! k)-int x-2) mod (460::int))"

lemma comma_offset_endpoint_headroom_bounds:
  shows "2\<le>comma_offset_endpoint_headroom x k"
    and "comma_offset_endpoint_headroom x k\<le>461"
proof -
  have residue_bound:
    "nat ((int (comma_power_table 460 ! k)-int x-2) mod (460::int))<460"
    by (simp add: nat_less_iff)
  show "2\<le>comma_offset_endpoint_headroom x k"
    and "comma_offset_endpoint_headroom x k\<le>461"
    unfolding comma_offset_endpoint_headroom_def
    using residue_bound by arith+
qed

lemma comma_offset_endpoint_headroom_exact:
  "comma_entry_alphabet_endpoint 1 x k =
    snd (comma_near_closed_germ 1 (comma_offset_endpoint_headroom x k))"
proof -
  have period: "comma_finite_period_fast 1 (x mod 10)=460"
    by (rule comma_sector_one_period) simp
  show ?thesis
    unfolding comma_entry_alphabet_endpoint_def
      comma_offset_endpoint_headroom_def
    by (simp only: Let_def period; simp)
qed
ML \<open>Thm.consolidate @{thms comma_offset_endpoint_headroom_exact}; Comma_Decade_Orbit_Quotient_Profile.report "headroom exact consolidated"\<close>

lemma comma_power_table_460_mod10:
  assumes phase: "k<22"
  shows "comma_power_table 460 ! k mod 10=0"
proof -
  have catalog: "460 \<in> comma_cycle_displacements"
    by (simp add: comma_cycle_displacements_def)
  have short: "k<comma_short_period 460"
    using phase by (simp add: comma_short_period_def)
  have table: "comma_power_table 460 ! k = mod_exp (10::nat) (5+k) 460"
    by (rule comma_power_table_correct[OF catalog short])
  have ten: "(10::nat) dvd 460" by simp
  have exponent: "5+k=Suc (4+k)" by simp
  have power_factor:
    "(10::nat)^(5+k)=10*(10::nat)^(4+k)"
    using exponent by (simp only: power_Suc; simp add: mult.commute)
  have power_dvd: "10 dvd (10::nat)^(5+k)"
    using power_factor unfolding dvd_def by blast
  have power_mod: "(10::nat)^(5+k) mod 10=0"
    using power_dvd by (simp only: dvd_eq_mod_eq_0)
  show ?thesis
    by (simp only: table mod_exp_def; simp add: mod_mod_cancel[OF ten] power_mod)
qed
ML \<open>Thm.consolidate @{thms comma_power_table_460_mod10}; Comma_Decade_Orbit_Quotient_Profile.report "power table phase consolidated"\<close>

lemma comma_offset_endpoint_headroom_aligned:
  fixes v x :: nat
  assumes v_digit: "v mod 10=0"
  shows "(2+nat ((int v-int x-2) mod (460::int))+x mod 10) mod 10=0"
proof -
  let ?z = "int v-int x-2"
  have rem_nonneg: "0 \<le> ?z mod (460::int)" by simp
  have period_divides: "(10::int) dvd 460" by simp
  have rem_mod: "(?z mod (460::int)) mod 10=?z mod 10"
    by (rule mod_mod_cancel[OF period_divides])
  have v_mod: "int v mod (10::int)=0"
  proof -
    have "int (v mod 10)=0" using v_digit by simp
    then show ?thesis
      by (simp only: of_nat_mod of_nat_numeral of_nat_0 of_nat_1)
  qed
  have x_mod: "int x mod (10::int)=int (x mod 10)"
    by (simp only: of_nat_mod of_nat_numeral of_nat_0 of_nat_1)
  have aligned_base:
    "(2+?z+int (x mod 10)) mod (10::int)=0"
  proof -
    have algebra: "2+?z+int (x mod 10)=int v+int (x mod 10)-int x"
      by (simp add: algebra_simps)
    have digit_mod: "int (x mod 10) mod (10::int)=int (x mod 10)"
    proof -
      have "int ((x mod 10) mod 10)=int (x mod 10)" by simp
      then show ?thesis
        by (simp only: of_nat_mod of_nat_numeral of_nat_0 of_nat_1)
    qed
    have digit_residue:
      "int (x mod 10) mod (10::int)=int x mod (10::int)"
      using digit_mod x_mod by simp
    have sum_norm:
      "(int v+int (x mod 10)) mod (10::int)=
        (int v mod (10::int)+int (x mod 10) mod (10::int)) mod (10::int)"
      by (rule mod_add_eq[symmetric])
    have difference_norm:
      "(int v+int (x mod 10)-int x) mod (10::int)=
        ((int v+int (x mod 10)) mod (10::int)-int x mod (10::int)) mod (10::int)"
      by (rule mod_diff_eq[symmetric])
    show ?thesis
      unfolding algebra
      using v_mod digit_residue
      by (simp only: difference_norm sum_norm; simp)
  qed
  have cast:
    "int (2+nat (?z mod (460::int))+x mod 10) =
      2+(?z mod (460::int))+int (x mod 10)"
    using rem_nonneg by simp
  have int_zero:
    "int (2+nat (?z mod (460::int))+x mod 10) mod (10::int)=0"
  proof -
    have replace:
      "(2+(?z mod (460::int))+int (x mod 10)) mod (10::int)=
        (2+?z+int (x mod 10)) mod (10::int)"
    proof -
      have prefix: "(2+(?z mod (460::int))) mod (10::int)=
        (2+?z) mod (10::int)"
        by (rule mod_add_cong[OF refl rem_mod])
      show ?thesis by (rule mod_add_cong[OF prefix refl])
    qed
    show ?thesis
      unfolding cast using replace aligned_base by simp
  qed
  have "int ((2+nat (?z mod (460::int))+x mod 10) mod 10)=0"
    using int_zero by (simp only: of_nat_mod of_nat_numeral of_nat_0 of_nat_1)
  then show ?thesis by simp
qed
ML \<open>Thm.consolidate @{thms comma_offset_endpoint_headroom_aligned}; Comma_Decade_Orbit_Quotient_Profile.report "headroom alignment consolidated"\<close>

lemma comma_offset_headroom_residue_shift:
  fixes v x a :: nat
  assumes a_bound: "a \<le> 91"
  shows "nat ((int v-int (x+a)-2) mod (460::int)) =
    (if nat ((int v-int x-2) mod (460::int))<a
      then 460+nat ((int v-int x-2) mod (460::int))-a
      else nat ((int v-int x-2) mod (460::int))-a)"
proof -
  let ?z = "int v-int x-2"
  let ?B = "nat (?z mod (460::int))"
  have nonneg: "0 \<le> ?z mod (460::int)" by simp
  have rem_bound: "?B<460" by (simp add: nat_less_iff)
  have B_cast: "int ?B=?z mod (460::int)" using nonneg by simp
  have shift: "int v-int (x+a)-2=?z-int a"
    by (simp add: algebra_simps)
  have reduced:
    "(int v-int (x+a)-2) mod (460::int) =
      (int ?B-int a) mod (460::int)"
  proof -
    have "(?z-int a) mod (460::int) =
        (?z mod (460::int)-int a) mod (460::int)"
      by (rule mod_diff_left_eq[symmetric])
    then show ?thesis by (simp only: shift B_cast)
  qed
  have reduced_nat:
    "nat ((int v-int (x+a)-2) mod (460::int))=
      nat ((int ?B-int a) mod (460::int))"
    by (simp only: reduced)
  have normalized:
    "nat ((int ?B-int a) mod (460::int))=
      (if ?B<a then 460+?B-a else ?B-a)"
    by (rule comma_nat_mod460_subtract[OF rem_bound a_bound])
  show ?thesis by (rule trans[OF reduced_nat normalized])
qed

lemma comma_sector_one_displacement:
  assumes digit: "d<10"
  shows "comma_period_displacement 1 d 10=460"
proof -
  have checked: "comma_finite_period 1 d =
      comma_period_displacement 1 d (comma_cycle_length 1)"
  proof -
    have all: "list_all (\<lambda>r. comma_finite_period 1 r =
        comma_period_displacement 1 r (comma_cycle_length 1)) [0..<10]"
      by (rule comma_finite_period_1)
    have member: "d\<in>set [0..<10]" using digit by simp
    show ?thesis using all member by (simp only: list_all_iff; blast)
  qed
  have period: "comma_finite_period 1 d=460"
    unfolding comma_finite_period_def by simp
  have cycle_len: "comma_cycle_length 1=10"
    by (simp add: comma_cycle_length_def)
  show ?thesis using checked period cycle_len by simp
qed
ML \<open>Thm.consolidate @{thms comma_offset_headroom_residue_shift comma_sector_one_displacement}; Comma_Decade_Orbit_Quotient_Profile.report "residue arithmetic consolidated"\<close>

lemma comma_near_germ_one_edge_endpoint:
  assumes move:
    "comma_finite_step 0 (Comma_Near f 0 h) =
      Comma_Next (Comma_Near f 0 j)"
  shows "snd (comma_near_germ f h)=snd (comma_near_germ f j)"
proof -
  obtain n t where tail: "comma_near_germ f j=(n,t)"
    by (cases "comma_near_germ f j") auto
  have source: "comma_near_germ f h=(Suc n,t)"
    using move tail
    by (simp only: comma_near_germ.simps[of f h] move tail
        comma_finite_move.case comma_finite_position.case Let_def prod.case)
  show ?thesis using source tail by simp
qed
ML \<open>Thm.consolidate @{thms comma_near_germ_one_edge_endpoint}; Comma_Decade_Orbit_Quotient_Profile.report "near edge endpoint consolidated"\<close>

lemma comma_sector_one_carry_germ_endpoint:
  fixes d B a h h' :: nat
  assumes digit: "d<10" and B_bound: "B<460" and carry: "B<a"
    and step: "a=10*d+1" and old_headroom: "h=2+B"
    and new_headroom: "h'=2+460+B-a"
    and old_aligned: "(h+d) mod 10=0"
    and new_aligned: "(h'+(d+1) mod 10) mod 10=0"
  shows "snd (comma_near_germ 1 h)=snd (comma_near_germ 1 h')"
proof -
  have sector: "1\<le>(1::nat)" "(1::nat)\<le>9" by simp_all
  have a_bound: "a\<le>91" using digit step by arith
  have a_lower: "1\<le>a" using step by arith
  have a_le: "a\<le>460+B" using a_bound by arith
  have old_initial: "h\<le>540" using old_headroom B_bound by arith
  have new_initial: "h'\<le>540" using new_headroom carry by arith
  have old_safe:
    "comma_period_displacement 1 d 0+1<h"
    using old_headroom by (simp add: comma_period_displacement_def)
  have first: "comma_period_displacement 1 d 1=a"
    using digit step by (simp add: comma_period_displacement_def)
  have first_suc: "comma_period_displacement 1 d (Suc 0)=a"
    using first by simp
  have old_max: "h\<le>comma_period_displacement 1 d (Suc 0)+1"
    using carry old_headroom first_suc by arith
  have old_safe_general:
    "comma_period_displacement 1 d 0+
      (if (1::nat)<9 then 1 else 0)<h"
    using old_safe by simp
  have old_max_general:
    "h\<le>comma_period_displacement 1 d (Suc 0)+
      (if (1::nat)<9 then 1 else 0)"
    using old_max by simp
  have old_germ_raw:
    "comma_near_germ 1 h=(0,h-comma_period_displacement 1 d 0)"
    by (rule comma_near_germ_from_maximal_displacement[OF sector old_initial
      digit old_aligned old_safe_general old_max_general])
  have old_germ: "comma_near_germ 1 h=(0,h)"
    using old_germ_raw by (simp add: comma_period_displacement_def)
  have period: "comma_period_displacement 1 d 10=460"
    by (rule comma_sector_one_displacement[OF digit])
  have tail:
    "comma_period_displacement 1 d 10 = a+
      comma_period_displacement 1 ((d+1) mod 10) 9"
    using comma_near_displacement_tail[OF digit, of 1 9] step by simp
  have a_le_period: "a\<le>460" using period tail by arith
  have suffix:
    "comma_period_displacement 1 ((d+1) mod 10) 9=460-a"
    using period tail by arith
  have next_digit: "(d+1) mod 10<10" by simp
  have next_period:
    "comma_period_displacement 1 ((d+1) mod 10) 10=460"
    by (rule comma_sector_one_displacement[OF next_digit])
  have new_safe:
    "comma_period_displacement 1 ((d+1) mod 10) 9+1<h'"
    using suffix new_headroom carry a_le by arith
  have new_bound: "h'\<le>461"
    using new_headroom carry a_lower by arith
  have new_max:
    "h'\<le>comma_period_displacement 1 ((d+1) mod 10) (Suc 9)+1"
  proof -
    have next_suc:
      "comma_period_displacement 1 ((d+1) mod 10) (Suc 9)=460"
      using next_period by simp
    show ?thesis using next_suc new_bound by arith
  qed
  have new_safe_general:
    "comma_period_displacement 1 ((d+1) mod 10) 9+
      (if (1::nat)<9 then 1 else 0)<h'"
    using new_safe by simp
  have new_max_general:
    "h'\<le>comma_period_displacement 1 ((d+1) mod 10) (Suc 9)+
      (if (1::nat)<9 then 1 else 0)"
    using new_max by simp
  have new_germ:
    "comma_near_germ 1 h'=(9,h'-
      comma_period_displacement 1 ((d+1) mod 10) 9)"
    by (rule comma_near_germ_from_maximal_displacement[OF sector new_initial
      next_digit new_aligned new_safe_general new_max_general])
  have suffix_le:
    "comma_period_displacement 1 ((d+1) mod 10) 9\<le>h'"
    using new_safe by arith
  have headroom_sum:
    "h'=h+comma_period_displacement 1 ((d+1) mod 10) 9"
    using new_headroom suffix old_headroom a_le_period by arith
  have result:
    "h'-comma_period_displacement 1 ((d+1) mod 10) 9=h"
    using suffix_le headroom_sum by arith
  show ?thesis using old_germ new_germ result by simp
qed
ML \<open>Thm.consolidate @{thms comma_sector_one_carry_germ_endpoint}; Comma_Decade_Orbit_Quotient_Profile.report "carry endpoint germ consolidated"\<close>

lemma comma_offset_endpoint_step:
  assumes phase: "k<22"
  shows "comma_entry_alphabet_endpoint 1 x k =
    comma_entry_alphabet_endpoint 1 (x+10*(x mod 10)+1) k"
proof -
  let ?d = "x mod 10"
  let ?a = "10*?d+1"
  let ?v = "comma_power_table 460 ! k"
  let ?B = "nat ((int ?v-int x-2) mod (460::int))"
  let ?h = "comma_offset_endpoint_headroom x k"
  let ?h' = "comma_offset_endpoint_headroom (x+?a) k"
  have digit: "?d<10" by simp
  have a_eq: "?a=10*?d+1" by simp
  have a_bound: "?a\<le>91" using digit by arith
  have power_digit: "?v mod 10=0"
    by (rule comma_power_table_460_mod10[OF phase])
  have h_eq: "?h=2+?B"
    by (simp add: comma_offset_endpoint_headroom_def)
  have shifted:
    "nat ((int ?v-int (x+?a)-2) mod (460::int)) =
      (if ?B<?a then 460+?B-?a else ?B-?a)"
    using comma_offset_headroom_residue_shift[OF a_bound] by simp
  have a_le_460_B: "?a\<le>460+?B" using a_bound by arith
  have h'_eq:
    "?h'=(if ?B<?a then 2+460+?B-?a else ?h-?a)"
  proof (cases "?B<?a")
    case True
    have shifted_value:
      "nat ((int ?v-int (x+?a)-2) mod (460::int))=460+?B-?a"
      using shifted True by simp
    have h'_carry: "?h'=2+(460+?B-?a)"
      unfolding comma_offset_endpoint_headroom_def
      using shifted_value by simp
    have carry_assoc: "2+(460+?B-?a)=2+460+?B-?a"
      by (simp only: add_diff_assoc[OF a_le_460_B] add.assoc)
    show ?thesis using True h'_carry carry_assoc by simp
  next
    case False
    have order: "?a\<le>?B" using False by simp
    have shifted_value:
      "nat ((int ?v-int (x+?a)-2) mod (460::int))=?B-?a"
      using shifted False by simp
    have h'_ordinary: "?h'=2+(?B-?a)"
      unfolding comma_offset_endpoint_headroom_def
      using shifted_value by simp
    have ordinary_assoc: "2+(?B-?a)=2+?B-?a"
      by (rule add_diff_assoc[OF order])
    show ?thesis using False h'_ordinary h_eq ordinary_assoc by simp
  qed
  ML_prf \<open>Thm.consolidate @{thms h'_eq};
    Comma_Decade_Orbit_Quotient_Profile.report "endpoint h-prime checkpoint consolidated"\<close>
  have B_bound: "?B<460" by (simp add: nat_less_iff)
  have h_lower: "2\<le>?h"
    by (rule comma_offset_endpoint_headroom_bounds(1))
  have h_upper: "?h\<le>461"
    by (rule comma_offset_endpoint_headroom_bounds(2))
  have h'_lower: "2\<le>?h'"
    by (rule comma_offset_endpoint_headroom_bounds(1))
  have h'_upper: "?h'\<le>461"
    by (rule comma_offset_endpoint_headroom_bounds(2))
  have aligned: "(?h+?d) mod 10=0"
    unfolding h_eq
    by (rule comma_offset_endpoint_headroom_aligned[OF power_digit])
  have next_digit: "(x+?a) mod 10=(?d+1) mod 10"
    by (simp add: mod_add_left_eq mod_Suc_eq)
  have aligned': "(?h'+(x+?a) mod 10) mod 10=0"
    unfolding comma_offset_endpoint_headroom_def
    by (rule comma_offset_endpoint_headroom_aligned[OF power_digit])
  have aligned_new: "(?h'+(?d+1) mod 10) mod 10=0"
    using aligned' next_digit by simp
  ML_prf \<open>Thm.consolidate @{thms aligned_new};
    Comma_Decade_Orbit_Quotient_Profile.report "endpoint alignment checkpoint consolidated"\<close>
  have sector: "1\<le>(1::nat)" "(1::nat)\<le>9" by simp_all
  have sector_guard: "(if (1::nat)<9 then 1 else 0)=1" by simp
  have h_initial: "?h\<le>540" using h_upper by arith
  have h'_initial: "?h'\<le>540" using h'_upper by arith
  have h_positive: "1\<le>?h" using h_lower by arith
  have h'_positive: "1\<le>?h'" using h'_lower by arith
  have close: "comma_near_closed_germ 1 ?h=comma_near_germ 1 ?h"
    by (rule comma_near_closed_germ_correct[OF sector h_positive h_initial])
  have close': "comma_near_closed_germ 1 ?h'=comma_near_germ 1 ?h'"
    by (rule comma_near_closed_germ_correct[OF sector h'_positive h'_initial])
  ML_prf \<open>Thm.consolidate @{thms close close'};
    Comma_Decade_Orbit_Quotient_Profile.report "endpoint close checkpoint consolidated"\<close>
  have near_same:
    "snd (comma_near_germ 1 ?h)=snd (comma_near_germ 1 ?h')"
  proof (cases "?B<?a")
    case False
    have move:
      "comma_finite_step 0 (Comma_Near 1 0 ?h) =
        Comma_Next (Comma_Near 1 0 (?h-?a))"
    proof -
      have comp:
        "(10-?h mod 10) mod 10=?d"
        using comma_near_complement_digit[OF aligned] digit by simp
      have guard: "?a+1<?h" using False h_eq by arith
      show ?thesis
        using guard comp
        by (simp only: comma_near_internal_iff[OF sector h_positive h_initial]
            comp guard sector_guard)
    qed
    have h_step: "?h'=?h-?a" using h'_eq False by simp
    show ?thesis
      using comma_near_germ_one_edge_endpoint[OF move] h_step by simp
  next
    case True
    have h'_carry: "?h'=2+460+?B-?a"
      using h'_eq True by simp
    show ?thesis
      by (rule comma_sector_one_carry_germ_endpoint[OF digit B_bound True
        a_eq h_eq h'_carry aligned aligned_new])
  qed
  ML_prf \<open>Thm.consolidate @{thms near_same};
    Comma_Decade_Orbit_Quotient_Profile.report "endpoint near checkpoint consolidated"\<close>
  have endpoint: "comma_entry_alphabet_endpoint 1 x k =
      comma_entry_alphabet_endpoint 1 (x+?a) k"
    by (simp only: comma_offset_endpoint_headroom_exact close close' near_same)
  show ?thesis using endpoint by (simp add: algebra_simps)
qed
ML \<open>Thm.consolidate @{thms comma_offset_endpoint_step}; Comma_Decade_Orbit_Quotient_Profile.report "endpoint step consolidated"\<close>

lemma comma_offset_endpoint_fixed_iter:
  assumes phase: "k<22"
  shows "comma_entry_alphabet_endpoint 1 x k =
    comma_entry_alphabet_endpoint 1 (comma_fixed_iter 1 n x) k"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?y = "comma_fixed_iter 1 n x"
  have step:
    "comma_entry_alphabet_endpoint 1 ?y k =
      comma_entry_alphabet_endpoint 1 (?y+10*(?y mod 10)+1) k"
    by (rule comma_offset_endpoint_step[OF phase])
  show ?case using Suc.IH step by simp
qed
ML \<open>Thm.consolidate @{thms comma_offset_endpoint_fixed_iter}; Comma_Decade_Orbit_Quotient_Profile.report "endpoint fixed iteration consolidated"\<close>

lemma comma_offset_orbit_residue_multiple:
  "nat ((int x-comma_digit_orbit_sum (x mod 10)) mod (460::int)) =
    10*comma_offset_orbit x"
proof -
  let ?d = "x mod 10"
  let ?r = "nat ((int x-comma_digit_orbit_sum ?d) mod (460::int))"
  have digit: "?d<10" by simp
  have sum_mod:
    "comma_digit_orbit_sum ?d mod (10::int)=int ?d"
    by (rule comma_digit_orbit_sum_mod10[OF digit])
  have x_mod: "int x mod (10::int)=int ?d"
    by (simp only: of_nat_mod of_nat_numeral of_nat_0 of_nat_1)
  have rem_nonneg:
    "0\<le>(int x-comma_digit_orbit_sum ?d) mod (460::int)" by simp
  have raw_mod:
    "(int x-comma_digit_orbit_sum ?d) mod (10::int)=0"
  proof -
    have difference_norm:
      "(int x-comma_digit_orbit_sum ?d) mod (10::int)=
        (int x mod (10::int)-comma_digit_orbit_sum ?d mod (10::int)) mod (10::int)"
      by (rule mod_diff_eq[symmetric])
    show ?thesis
      by (simp only: difference_norm x_mod sum_mod; simp)
  qed
  ML_prf \<open>Comma_Decade_Orbit_Quotient_Profile.report "orbit raw modulo reached"\<close>
  have divides: "(10::int) dvd 460" by simp
  have reduced:
    "((int x-comma_digit_orbit_sum ?d) mod (460::int)) mod (10::int)=0"
    using raw_mod by (simp only: mod_mod_cancel[OF divides])
  have cast:
    "int ?r=(int x-comma_digit_orbit_sum ?d) mod (460::int)"
    using rem_nonneg by simp
  have int_r_mod: "int ?r mod (10::int)=0"
    by (simp only: cast reduced)
  have r_mod: "?r mod 10=0"
  proof -
    have "int (?r mod 10)=0"
      using int_r_mod by (simp only: of_nat_mod of_nat_numeral of_nat_0 of_nat_1)
    then show ?thesis by simp
  qed
  have decomposition:
    "?r=10*(?r div 10)+?r mod 10"
    using div_mult_mod_eq[of ?r 10] by (simp add: mult.commute)
  have rest: "10*(?r div 10)+?r mod 10=10*(?r div 10)"
    by (simp only: r_mod add_0)
  have residue_quotient: "?r=10*(?r div 10)"
    by (rule trans[OF decomposition rest])
  ML_prf \<open>Comma_Decade_Orbit_Quotient_Profile.report "orbit quotient decomposition reached"\<close>
  show ?thesis unfolding comma_offset_orbit_def
    by (rule residue_quotient)
qed
ML \<open>Thm.consolidate @{thms comma_offset_orbit_residue_multiple}; Comma_Decade_Orbit_Quotient_Profile.report "orbit residue multiple consolidated"\<close>

lemma comma_mod_sub_add:
  fixes a b m :: int
  shows "((a-b) mod m+b) mod m=a mod m"
proof -
  have "((a-b) mod m+b) mod m=(a-b+b) mod m"
    by (rule mod_add_left_eq)
  then show ?thesis by (simp add: algebra_simps)
qed
ML \<open>Thm.consolidate @{thms comma_mod_sub_add}; Comma_Decade_Orbit_Quotient_Profile.report "mod subtraction normalization consolidated"\<close>

lemma comma_offset_orbit_same_digit_mod460:
  assumes same_digit: "x mod 10=y mod 10"
    and same_key: "comma_offset_orbit x=comma_offset_orbit y"
  shows "x mod 460=y mod 460"
proof -
  ML_prf \<open>Comma_Decade_Orbit_Quotient_Profile.report "same-digit proof entered"\<close>
  let ?d = "x mod 10"
  let ?rx = "nat ((int x-comma_digit_orbit_sum ?d) mod (460::int))"
  let ?ry = "nat ((int y-comma_digit_orbit_sum ?d) mod (460::int))"
  have rx: "?rx=10*comma_offset_orbit x"
    by (rule comma_offset_orbit_residue_multiple)
  have ry: "?ry=10*comma_offset_orbit y"
    using comma_offset_orbit_residue_multiple[of y]
    by (simp only: same_digit[symmetric])
  have scaled_key: "10*comma_offset_orbit x=10*comma_offset_orbit y"
    by (rule arg_cong[where f="\<lambda>n::nat. 10*n", OF same_key])
  have residue_eq: "?rx=?ry"
    by (rule trans[OF rx trans[OF scaled_key ry[symmetric]]])
  ML_prf \<open>Comma_Decade_Orbit_Quotient_Profile.report "same-digit key residue reached"\<close>
  have x_nonneg:
    "0\<le>(int x-comma_digit_orbit_sum ?d) mod (460::int)" by simp
  have y_nonneg:
    "0\<le>(int y-comma_digit_orbit_sum ?d) mod (460::int)" by simp
  have x_cast:
    "int ?rx=(int x-comma_digit_orbit_sum ?d) mod (460::int)"
    using x_nonneg by simp
  have y_cast:
    "int ?ry=(int y-comma_digit_orbit_sum ?d) mod (460::int)"
    using y_nonneg by simp
  have raw_eq:
    "(int x-comma_digit_orbit_sum ?d) mod (460::int)=
      (int y-comma_digit_orbit_sum ?d) mod (460::int)"
  proof -
    have cast_eq: "int ?rx=int ?ry"
      by (rule arg_cong[where f="\<lambda>n::nat. int n", OF residue_eq])
    show ?thesis
      by (rule trans[OF trans[OF x_cast[symmetric] cast_eq] y_cast])
  qed
  ML_prf \<open>Comma_Decade_Orbit_Quotient_Profile.report "same-digit raw cast reached"\<close>
  have x_back:
    "((int x-comma_digit_orbit_sum ?d) mod (460::int)+
      comma_digit_orbit_sum ?d) mod (460::int)=int x mod (460::int)"
    by (rule comma_mod_sub_add)
  have transported:
    "((int x-comma_digit_orbit_sum ?d) mod (460::int)+
      comma_digit_orbit_sum ?d) mod (460::int)=
     ((int y-comma_digit_orbit_sum ?d) mod (460::int)+
      comma_digit_orbit_sum ?d) mod (460::int)"
    by (rule arg_cong[where f="\<lambda>n::int.
      (n+comma_digit_orbit_sum ?d) mod (460::int)", OF raw_eq])
  have y_back:
    "((int y-comma_digit_orbit_sum ?d) mod (460::int)+
      comma_digit_orbit_sum ?d) mod (460::int)=int y mod (460::int)"
    by (rule comma_mod_sub_add)
  have int_mod_eq: "int x mod (460::int)=int y mod (460::int)"
    by (rule trans[OF trans[OF x_back[symmetric] transported] y_back])
  ML_prf \<open>Comma_Decade_Orbit_Quotient_Profile.report "same-digit modulo transport reached"\<close>
  have nat_mod_eq: "x mod 460=y mod 460"
  proof -
    have "int (x mod 460)=int (y mod 460)"
      using int_mod_eq
      by (simp only: of_nat_mod of_nat_numeral of_nat_0 of_nat_1)
    then show ?thesis by simp
  qed
  then show ?thesis .
qed
ML \<open>Thm.consolidate @{thms comma_offset_orbit_same_digit_mod460}; Comma_Decade_Orbit_Quotient_Profile.report "same digit orbit key consolidated"\<close>

lemma comma_offset_endpoint_mod460:
  assumes phase: "k<22" and residue: "x mod 460=y mod 460"
  shows "comma_entry_alphabet_endpoint 1 x k=
    comma_entry_alphabet_endpoint 1 y k"
proof -
  have int_residue: "int x mod (460::int)=int y mod (460::int)"
  proof -
    have cast_residue: "int (x mod 460)=int (y mod 460)"
      by (rule arg_cong[where f="\<lambda>n::nat. int n", OF residue])
    show ?thesis using cast_residue
      by (simp only: of_nat_mod of_nat_numeral of_nat_0 of_nat_1)
  qed
  have headroom_residue:
    "(int (comma_power_table 460 ! k)-int x-2) mod (460::int)=
      (int (comma_power_table 460 ! k)-int y-2) mod (460::int)"
  proof -
    let ?power = "int (comma_power_table 460 ! k)"
    have base_residue: "(?power-int x) mod (460::int) =
        (?power-int y) mod (460::int)"
      by (rule mod_diff_cong[OF refl int_residue])
    show ?thesis by (rule mod_diff_cong[OF base_residue refl])
  qed
  have headroom:
    "comma_offset_endpoint_headroom x k=
      comma_offset_endpoint_headroom y k"
    unfolding comma_offset_endpoint_headroom_def
    by (simp only: headroom_residue)
  show ?thesis
    by (simp only: comma_offset_endpoint_headroom_exact headroom)
qed
ML \<open>Thm.consolidate @{thms comma_offset_endpoint_mod460}; Comma_Decade_Orbit_Quotient_Profile.report "endpoint residue transport consolidated"\<close>

lemma comma_offset_orbit_fixed_iter:
  "comma_offset_orbit (comma_fixed_iter 1 n x)=comma_offset_orbit x"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?y = "comma_fixed_iter 1 n x"
  have step:
    "comma_offset_orbit (?y+10*(?y mod 10)+1)=comma_offset_orbit ?y"
    by (rule comma_offset_orbit_step)
  show ?case using Suc.IH step by simp
qed
ML \<open>Thm.consolidate @{thms comma_offset_orbit_fixed_iter}; Comma_Decade_Orbit_Quotient_Profile.report "orbit fixed iteration consolidated"\<close>

lemma comma_offset_endpoint_same_orbit:
  assumes phase: "k<22"
    and same: "comma_offset_orbit x=comma_offset_orbit y"
  shows "comma_entry_alphabet_endpoint 1 x k=
    comma_entry_alphabet_endpoint 1 y k"
proof -
  let ?d = "x mod 10"
  let ?e = "y mod 10"
  let ?n = "(?e+10-?d) mod 10"
  let ?z = "comma_fixed_iter 1 ?n x"
  have d_bound: "?d<10" and e_bound: "?e<10" by simp_all
  have balance: "?d+(?e+10-?d)=?e+10" using d_bound e_bound by arith
  have phase_reduction:
    "(?d+((?e+10-?d) mod 10)) mod 10=
      (?d+(?e+10-?d)) mod 10"
    by (rule mod_add_right_eq)
  have chosen_digit: "(?d+?n) mod 10=?e"
    using phase_reduction balance by simp
  have iterate_digit: "?z mod 10=?e"
    using chosen_digit by (simp only: comma_fixed_iter_phase; simp)
  have iterate_key:
    "comma_offset_orbit ?z=comma_offset_orbit x"
    by (rule comma_offset_orbit_fixed_iter)
  have aligned_key:
    "comma_offset_orbit ?z=comma_offset_orbit y"
    by (rule trans[OF iterate_key same])
  have residue: "?z mod 460=y mod 460"
    by (rule comma_offset_orbit_same_digit_mod460[OF iterate_digit aligned_key])
  have fixed_endpoint:
    "comma_entry_alphabet_endpoint 1 x k=
      comma_entry_alphabet_endpoint 1 ?z k"
    by (rule comma_offset_endpoint_fixed_iter[OF phase])
  have residue_endpoint:
    "comma_entry_alphabet_endpoint 1 ?z k=
      comma_entry_alphabet_endpoint 1 y k"
    by (rule comma_offset_endpoint_mod460[OF phase residue])
  show ?thesis by (rule trans[OF fixed_endpoint residue_endpoint])
qed
ML \<open>Thm.consolidate @{thms comma_offset_endpoint_same_orbit}; Comma_Decade_Orbit_Quotient_Profile.report "same orbit endpoint transport consolidated"\<close>

lemma comma_offset_endpoint_representative:
  assumes x: "x\<le>90" and phase: "k<22"
  shows "comma_entry_alphabet_endpoint 1 x k=
    comma_entry_alphabet_endpoint 1 (comma_offset_representative x) k"
proof -
  have same:
    "comma_offset_orbit x=comma_offset_orbit (comma_offset_representative x)"
    by (rule sym[OF comma_offset_representative_admitted(2)[of x]])
  show ?thesis
    by (rule comma_offset_endpoint_same_orbit[OF phase same])
qed
ML \<open>Thm.consolidate @{thms comma_offset_endpoint_representative}; Comma_Decade_Orbit_Quotient_Profile.report "representative endpoint transport consolidated"\<close>

lemma comma_offset_endpoint_checked: "comma_offset_endpoint_check"
proof -
  ML_prf \<open>Comma_Decade_Orbit_Quotient_Profile.report "endpoint-check entered"\<close>
  have rows:
    "\<forall>x\<in>set [0..<91]. list_all (\<lambda>k.
      comma_entry_alphabet_endpoint 1 x k=
        comma_entry_alphabet_endpoint 1 (comma_offset_representative x) k)
      [0..<22]"
  proof
    fix x
    assume x_member: "x\<in>set [0..<91]"
    have x_less: "x<91" using x_member by simp
    have x_bound: "x\<le>90" using x_less by arith
    have columns:
      "\<forall>k\<in>set [0..<22]. comma_entry_alphabet_endpoint 1 x k=
        comma_entry_alphabet_endpoint 1 (comma_offset_representative x) k"
    proof
      fix k
      assume k_member: "k\<in>set [0..<22]"
      have k_bound: "k<22" using k_member by simp
      show "comma_entry_alphabet_endpoint 1 x k=
        comma_entry_alphabet_endpoint 1 (comma_offset_representative x) k"
        by (rule comma_offset_endpoint_representative[OF x_bound k_bound])
    qed
    show "list_all (\<lambda>k. comma_entry_alphabet_endpoint 1 x k=
        comma_entry_alphabet_endpoint 1 (comma_offset_representative x) k)
        [0..<22]"
      using columns by (simp only: list_all_iff)
  qed
  show ?thesis
    unfolding comma_offset_endpoint_check_def
    using rows by (simp only: list_all_iff)
qed
ML \<open>Thm.consolidate @{thms comma_offset_endpoint_checked}; Comma_Decade_Orbit_Quotient_Profile.report "endpoint checker consolidated"\<close>
ML \<open>
  val _ = Comma_Decade_Orbit_Quotient_Profile.report
    "endpoint-check submitted"
\<close>

lemma comma_sector_one_orbit_congruent:
  assumes x: "x\<le>90" and y: "y\<le>90"
    and same: "comma_offset_orbit x=comma_offset_orbit y"
  shows "comma_fast_sector_target r (Comma_Entry 1 0 x)=
    comma_fast_sector_target r (Comma_Entry 1 0 y)"
proof -
  have representatives: "comma_offset_representative x=comma_offset_representative y"
    using same by (simp only: comma_offset_representative_def)
  have endpoint: "comma_entry_alphabet_endpoint 1 x ((r mod 924+919) mod 22)=
    comma_entry_alphabet_endpoint 1 y ((r mod 924+919) mod 22)"
    using comma_offset_endpoint_representative[OF x, of "(r mod 924+919) mod 22"]
      comma_offset_endpoint_representative[OF y, of "(r mod 924+919) mod 22"]
    by (simp add: representatives)
  show ?thesis using x y
    by (simp only: comma_sector_entry_alphabet comma_sector_one_phase endpoint;
      simp)
qed

lemma comma_fast_decade_control_orbit_congruent:
  assumes "x\<le>90" "y\<le>90" "comma_offset_orbit x=comma_offset_orbit y"
  shows "comma_fast_decade_control (Comma_Decade r x)=
    comma_fast_decade_control (Comma_Decade r y)"
proof -
  have sectors: "comma_fast_sector_target r (Comma_Entry 1 0 x)=
    comma_fast_sector_target r (Comma_Entry 1 0 y)"
    by (rule comma_sector_one_orbit_congruent[OF assms])
  have rounds: "comma_fast_round_aux 9 r (Comma_Entry 1 0 x)=
    comma_fast_round_aux 9 r (Comma_Entry 1 0 y)"
    using comma_fast_round_aux_eval[of 9 r "Comma_Entry 1 0 x"]
      comma_fast_round_aux_eval[of 9 r "Comma_Entry 1 0 y"]
    by (simp only: sectors)
  show ?thesis by (simp only: comma_fast_decade_control.simps rounds)
qed

lemma comma_fast_decade_control_orbit_representative:
  assumes "x\<le>90"
  shows "comma_fast_decade_control (Comma_Decade r x)=
    comma_fast_decade_control (Comma_Decade r (comma_offset_representative x))"
  by (rule comma_fast_decade_control_orbit_congruent[OF assms
    comma_offset_representative_admitted(1)])
    (simp only: comma_offset_representative_admitted(2))

text \<open>The canonical round event observes only the selected sector endpoint.
Its internal prefix length may differ between orbit representatives; after
that endpoint, both control germs follow the same deterministic continuation.\<close>

lemma comma_round_control_germ_event_of_sector_endpoint:
  assumes left: "comma_sector_control r p=(n,t)"
    and right: "comma_sector_control r q=(m,t)"
  shows "snd (snd (comma_round_control_germ r p))=
    snd (snd (comma_round_control_germ r q))"
proof -
  have left_eq:
    "comma_round_control_germ r p =
      (case comma_finite_step (r mod 924) t of
        Comma_Next target \<Rightarrow>
          if comma_round_crossing t target then (n,t,Comma_Round_Cross target)
          else (let (k,u,event)=comma_round_control_germ r target
            in (n+Suc k,u,event))
      | Comma_Fork a d \<Rightarrow> (n,t,Comma_Round_Fork a d)
      | Comma_Landmine d \<Rightarrow> (n,t,Comma_Round_Landmine d)
      | Comma_Invalid \<Rightarrow> (n,t,Comma_Round_Invalid))"
    using left by (subst comma_round_control_germ.simps)
      (simp only: left prod.case)
  have right_eq:
    "comma_round_control_germ r q =
      (case comma_finite_step (r mod 924) t of
        Comma_Next target \<Rightarrow>
          if comma_round_crossing t target then (m,t,Comma_Round_Cross target)
          else (let (k,u,event)=comma_round_control_germ r target
            in (m+Suc k,u,event))
      | Comma_Fork a d \<Rightarrow> (m,t,Comma_Round_Fork a d)
      | Comma_Landmine d \<Rightarrow> (m,t,Comma_Round_Landmine d)
      | Comma_Invalid \<Rightarrow> (m,t,Comma_Round_Invalid))"
    using right by (subst comma_round_control_germ.simps)
      (simp only: right prod.case)
  show ?thesis
    using left_eq right_eq
    by (cases "comma_finite_step (r mod 924) t")
      (auto split: if_splits prod.splits)
qed

theorem comma_decade_control_orbit_congruent:
  assumes x: "x\<le>90" and y: "y\<le>90"
    and same: "comma_offset_orbit x=comma_offset_orbit y"
  shows "comma_decade_control (Comma_Decade r x)=
    comma_decade_control (Comma_Decade r y)"
proof -
  ML_prf \<open>Comma_Decade_Orbit_Quotient_Profile.report "control-congruence entered"\<close>
  let ?p = "Comma_Entry 1 0 x"
  let ?q = "Comma_Entry 1 0 y"
  have p_valid: "comma_round_admitted ?p" using x by simp
  have q_valid: "comma_round_admitted ?q" using y by simp
  obtain nx tx where px: "comma_sector_control r ?p=(nx,tx)"
    by (cases "comma_sector_control r ?p") auto
  obtain ny ty where qy: "comma_sector_control r ?q=(ny,ty)"
    by (cases "comma_sector_control r ?q") auto
  have sector_p: "comma_fast_sector r ?p=(nx,tx)"
    using comma_fast_sector_refines[OF p_valid, of r] px by simp
  have sector_q: "comma_fast_sector r ?q=(ny,ty)"
    using comma_fast_sector_refines[OF q_valid, of r] qy by simp
  have target_p: "comma_fast_sector_target r ?p=tx"
    using comma_fast_sector_target_correct[of r ?p] sector_p by simp
  have target_q: "comma_fast_sector_target r ?q=ty"
    using comma_fast_sector_target_correct[of r ?q] sector_q by simp
  have target_eq: "tx=ty"
    using comma_sector_one_orbit_congruent[where r=r, OF x y same]
    by (simp only: target_p target_q)
  ML_prf \<open>Comma_Decade_Orbit_Quotient_Profile.report "control-congruence target equality reached"\<close>
  have q_endpoint: "comma_sector_control r ?q=(ny,tx)"
    using qy target_eq by simp
  have event_eq:
    "snd (snd (comma_round_control_germ r ?p))=
      snd (snd (comma_round_control_germ r ?q))"
    by (rule comma_round_control_germ_event_of_sector_endpoint[OF px q_endpoint])
  ML_prf \<open>Comma_Decade_Orbit_Quotient_Profile.report "control-congruence event equality reached"\<close>
  have close_event:
    "snd (snd (comma_round_close r ?p))=
      snd (snd (comma_round_close r ?q))"
    using event_eq comma_round_control_germ_refines by simp
  ML_prf \<open>Comma_Decade_Orbit_Quotient_Profile.report "control-congruence close bridge reached"\<close>
  obtain np tp ep where p_close: "comma_round_close r ?p=(np,tp,ep)"
    by (cases "comma_round_close r ?p") auto
  obtain nq tq eq where q_close: "comma_round_close r ?q=(nq,tq,eq)"
    by (cases "comma_round_close r ?q") auto
  have events: "ep=eq" using close_event p_close q_close by simp
  have p_control: "comma_decade_control (Comma_Decade r x)=comma_decade_decode r ep"
    by (simp only: comma_decade_control.simps p_close prod.case)
  have q_control: "comma_decade_control (Comma_Decade r y)=comma_decade_decode r eq"
    by (simp only: comma_decade_control.simps q_close prod.case)
  show ?thesis using p_control q_control events by simp
qed
ML \<open>
  val _ = Comma_Decade_Orbit_Quotient_Profile.report
    "control-congruence submitted"
\<close>

lemma comma_decade_control_orbit_representative:
  assumes "x\<le>90"
  shows "comma_decade_control (Comma_Decade r x)=
    comma_decade_control (Comma_Decade r (comma_offset_representative x))"
  by (rule comma_decade_control_orbit_congruent[OF assms
    comma_offset_representative_admitted(1)])
    (simp only: comma_offset_representative_admitted(2))

text \<open>Candidate summaries may be transported only when both labels agree.
Control equality alone never authenticates a supplied height or terminal table.\<close>
lemma comma_decade_summary_step_orbit_transport:
  assumes offset: "x\<le>90"
    and height: "h (Comma_Decade r x)=h (Comma_Decade r (comma_offset_representative x))"
    and terminal: "t (Comma_Decade r x)=t (Comma_Decade r (comma_offset_representative x))"
  shows "comma_fast_decade_summary_step h t (Comma_Decade r x)=
    comma_fast_decade_summary_step h t (Comma_Decade r (comma_offset_representative x))"
  by (simp only: comma_fast_decade_summary_step_def
    comma_fast_decade_control_orbit_representative[OF offset] height terminal)

ML \<open>
  val _ = Comma_Decade_Orbit_Quotient_Profile.report
    "final-oracle-audit entered"
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_decade_control_orbit_representative
      comma_decade_summary_step_orbit_transport comma_offset_orbit_bound comma_offset_orbit_step
      comma_offset_representatives_checked comma_offset_endpoint_checked
      comma_decade_control_orbit_congruent comma_fast_decade_control_orbit_congruent
      comma_fast_decade_control_orbit_representative})
    then () else error "Decade orbit quotient depends on an oracle";
  val _ = Comma_Decade_Orbit_Quotient_Profile.report
    "final-oracle-audit checked"
\<close>
end
