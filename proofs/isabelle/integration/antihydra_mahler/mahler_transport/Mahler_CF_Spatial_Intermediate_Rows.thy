theory Mahler_CF_Spatial_Intermediate_Rows
  imports Mahler_CF_Fractional_Guard_Compiler
    "HOL-Computational_Algebra.Polynomial" "HOL.Bit_Operations"
begin

unbundle bit_operations_syntax

lemma mahler_cf_quotient_remainder_digit:
  fixes v divisor :: nat
  assumes "0 < divisor"
  shows "(v div divisor) mod 10 = (v mod (divisor*10)) div divisor"
proof -
  have eq: "v mod (divisor*10) =
      divisor * ((v div divisor) mod 10) + v mod divisor"
    by (rule mod_mult2_eq)
  have small: "v mod divisor < divisor" using assms by simp
  show ?thesis using eq small assms by (simp add: div_add1_eq)
qed

lemma mahler_cf_reciprocal_div10:
  fixes v :: nat
  assumes "v \<le> 450"
  shows "(410*v) div 4096 = v div 10"
proof -
  let ?q = "v div 10"
  let ?r = "v mod 10"
  have q: "?q \<le> 45" using div_le_mono[OF assms, of 10] by simp
  have r: "?r < 10" by simp
  have split: "v = 10*?q + ?r" using div_mult_mod_eq[of v 10] by (simp add: mult.commute)
  have small: "4*?q + 410*?r < 4096" using q r by arith
  have eq: "410*v = 4096*?q + (4*?q + 410*?r)"
  proof -
    have "410*v = 410*(10*?q + ?r)"
      by (rule arg_cong[OF split, where f="\<lambda>x. 410*x"])
    also have "... = 4096*?q + (4*?q + 410*?r)"
      by (simp only: algebra_simps arith_simps)
    finally show ?thesis .
  qed
  show ?thesis using small by (simp only: eq div_mult_self2; simp)
qed

lemma mahler_cf_pow5_digit_quotient:
  fixes h t i :: nat
  shows "((5^t*h) div 10^i) mod 10 =
    (((h*10^t) div 10^i) mod (2^t*10)) div 2^t"
proof -
  have factor: "(10::nat)^t = 2^t*5^t"
    by (simp add: power_mult_distrib[symmetric])
  have split: "(h*10^t) div 2^t = 5^t*h"
    by (simp add: factor mult.assoc mult.commute mult.left_commute)
  have reorder: "((h*10^t) div 2^t) div 10^i =
      ((h*10^t) div 10^i) div 2^t"
    by (simp only: div_mult2_eq[symmetric] mult.commute)
  show ?thesis using mahler_cf_quotient_remainder_digit[of "2^t" "(h*10^t) div 10^i"]
    split reorder by simp
qed

lemma mahler_cf_pow5_causal_modulus:
  fixes t :: nat
  shows "2^t*10 dvd (10::nat)^(Suc t)"
proof -
  have "(10::nat)^(Suc t) = (2^t*10)*5^t"
    by (simp add: power_Suc power_mult_distrib[symmetric] algebra_simps)
  then show ?thesis by simp
qed

lemma mahler_cf_pow5_causal_residue:
  fixes v t :: nat
  shows "(v mod 10^(Suc t)) mod (2^t*10) = v mod (2^t*10)"
  by (rule mod_mod_cancel[OF mahler_cf_pow5_causal_modulus])

lemma mahler_cf_fixed_band_placement:
  fixes tick duration width below i kernel_index :: nat
  assumes tick: "1 \<le> tick" "tick \<le> duration" "duration \<le> 4"
    and leaf: "width \<le> 16" "below \<le> duration" "i < width + below"
    and kernel: "kernel_index \<le> tick"
  shows "i + kernel_index < 24"
    "(tick-Suc 0)*24 + i + kernel_index < tick*24"
  using assms by arith+

text \<open>A bounded coefficient is the corresponding radix limb, including a
zero limb beyond the degree. This links packed integer multiplication to
the convolution coefficients without assuming that carries are absent.\<close>

lemma mahler_cf_radix_polynomial_limb:
  fixes base index :: nat and p :: "nat poly"
  assumes base: "0 < base" and small: "\<And>j. coeff p j < base"
  shows "(poly p base div base^index) mod base = coeff p index"
  using small
proof (induction p arbitrary: index rule: pCons_induct)
  case 0
  then show ?case by simp
next
  case (pCons a q)
  have a_bound: "a < base" using pCons.prems[of 0] by simp
  have q_bound: "\<And>j. coeff q j < base"
    using pCons.prems by (metis coeff_pCons_Suc)
  show ?case
  proof (cases index)
    case 0
    then show ?thesis using a_bound by (simp add: mult.commute)
  next
    case (Suc i)
    have quotient: "poly (pCons a q) base div base = poly q base"
      using a_bound base by (simp add: mult.commute)
    have step: "poly (pCons a q) base div base ^ Suc i =
        (poly (pCons a q) base div base) div base^i"
      by (simp only: power_Suc div_mult2_eq)
    show ?thesis using pCons.IH[OF q_bound, of i]
      by (simp only: Suc step quotient coeff_pCons_Suc)
  qed
qed

theorem mahler_cf_radix_polynomial_convolution:
  fixes base index :: nat and p q :: "nat poly"
  assumes "0 < base"
    and "\<And>k. (\<Sum>j\<le>k. coeff p j * coeff q (k-j)) < base"
  shows "((poly p base * poly q base) div base^index) mod base =
    (\<Sum>j\<le>index. coeff p j * coeff q (index-j))"
  using mahler_cf_radix_polynomial_limb[OF assms(1), of "p*q" index] assms(2)
  by (simp only: poly_mult coeff_mult)

lemma mahler_cf_radix_polynomial_shift:
  fixes base divisor index packed :: nat
  assumes divisor: "0 < divisor"
  shows "(packed div divisor div (divisor*base)^index) mod base =
    ((packed div (divisor*base)^index) mod (divisor*base)) div divisor"
proof -
  let ?n = "packed div (divisor*base)^index"
  have swap: "packed div divisor div (divisor*base)^index = ?n div divisor"
    using div_mult2_eq(1)[of packed divisor "(divisor*base)^index"]
      div_mult2_eq(1)[of packed "(divisor*base)^index" divisor]
    by (simp add: mult.commute)
  have mod: "?n mod (divisor*base) = divisor * (?n div divisor mod base) + ?n mod divisor"
    by (rule mod_mult2_eq)
  have "(?n mod (divisor*base)) div divisor = ?n div divisor mod base"
    unfolding mod using divisor by (simp add: add.commute)
  then show ?thesis by (simp only: swap)
qed

definition mahler_cf_spatial_kernel :: "nat \<Rightarrow> nat poly" where
  "mahler_cf_spatial_kernel duration =
    (\<Sum>tick\<in>{1..duration}. \<Sum>j\<le>tick.
      monom ((10^(tick-j) mod (10*2^tick))*2^(duration-tick)) (24*(tick-Suc 0)+j))"

lemma mahler_cf_spatial_kernel_weight:
  fixes duration :: nat
  assumes "duration \<le> 4"
  shows "poly (mahler_cf_spatial_kernel duration) 1 \<le> 45*2^duration"
proof -
  have "duration = 0 \<or> duration = 1 \<or> duration = 2 \<or> duration = 3 \<or> duration = 4"
    using assms by arith
  then show ?thesis
    by (elim disjE) (simp_all add: mahler_cf_spatial_kernel_def poly_sum poly_monom
      sum.atMost_Suc sum.atLeast_Suc_atMost)
qed

lemma mahler_cf_spatial_kernel_product:
  fixes source :: "nat poly" and duration k :: nat
  shows "coeff (mahler_cf_spatial_kernel duration * source) k =
    (\<Sum>r\<in>{1..duration}. \<Sum>j\<le>r.
      if k < 24*(r-Suc 0)+j then 0 else
        (10^(r-j) mod (10*2^r))*2^(duration-r) * coeff source (k-(24*(r-Suc 0)+j)))"
  by (simp add: mahler_cf_spatial_kernel_def sum_distrib_right coeff_sum coeff_monom_mult One_nat_def)

lemma mahler_cf_spatial_product_bound:
  fixes source :: "nat poly" and duration k :: nat
  assumes decimal: "\<And>i. coeff source i \<le> 9" and duration: "duration \<le> 4"
  shows "coeff (mahler_cf_spatial_kernel duration * source) k \<le> 405*2^duration"
proof -
  let ?W = "\<lambda>r j. (10^(r-j) mod (10*2^r))*2^(duration-r)"
  have bounds: "(\<Sum>r\<in>{1..duration}. \<Sum>j\<le>r.
    if k < 24*(r-Suc 0)+j then 0 else ?W r j * coeff source (k-(24*(r-Suc 0)+j)))
      \<le> (\<Sum>r\<in>{1..duration}. \<Sum>j\<le>r. ?W r j * 9)"
    by (intro sum_mono) (auto intro: mult_left_mono decimal)
  have weights: "(\<Sum>r\<in>{1..duration}. \<Sum>j\<le>r. ?W r j * 9) =
      poly (mahler_cf_spatial_kernel duration) 1 * 9"
    by (simp add: mahler_cf_spatial_kernel_def poly_sum poly_monom sum_distrib_right)
  have last: "poly (mahler_cf_spatial_kernel duration) 1 * 9 \<le> 405*2^duration"
    using mult_right_mono[OF mahler_cf_spatial_kernel_weight[OF duration], of 9]
    by (simp add: mult_ac)
  have lifted: "coeff (mahler_cf_spatial_kernel duration * source) k \<le>
      poly (mahler_cf_spatial_kernel duration) 1 * 9"
    using bounds unfolding weights mahler_cf_spatial_kernel_product .
  show ?thesis by (rule order_trans[OF lifted last])
qed

theorem mahler_cf_spatial_selected_coefficient:
  fixes source :: "nat poly" and duration tick index :: nat
  assumes duration: "duration \<le> 4" and tick: "1 \<le> tick" "tick \<le> duration"
    and index: "index < 20" and supported: "\<And>i. 20 \<le> i \<Longrightarrow> coeff source i = 0"
  shows "coeff (mahler_cf_spatial_kernel duration * source) (24*(tick-Suc 0)+index) =
    (\<Sum>j\<le>tick. if index < j then 0 else
      (10^(tick-j) mod (10*2^tick))*2^(duration-tick) * coeff source (index-j))"
proof -
  let ?k = "24*(tick-Suc 0)+index"
  let ?W = "\<lambda>r j. (10^(r-j) mod (10*2^r))*2^(duration-r)"
  let ?U = "\<lambda>r j. if ?k < 24*(r-Suc 0)+j then 0 else
      ?W r j * coeff source (?k-(24*(r-Suc 0)+j))"
  let ?V = "\<Sum>j\<le>tick. if index < j then 0 else ?W tick j * coeff source (index-j)"
  have one: "(\<Sum>r\<in>{1..duration}. \<Sum>j\<le>r. ?U r j) =
      (\<Sum>r\<in>{1..duration}. if r = tick then ?V else 0)"
  proof (rule sum.cong[OF refl])
    fix r assume r: "r \<in> {1..duration}"
    have r_bounds: "1 \<le> r" "r \<le> 4" using r duration by auto
    show "(\<Sum>j\<le>r. ?U r j) = (if r = tick then ?V else 0)"
    proof (cases "r = tick")
      case True
      then show ?thesis by (simp only: True if_P add_less_cancel_left add_diff_cancel_left)
    next
      case False
      note different = False
      have null: "(\<Sum>j\<le>r. ?U r j) = (\<Sum>j\<le>r. 0)"
      proof (rule sum.cong[OF refl])
        fix j assume "j \<in> {..r}"
        then have j: "j \<le> r" by simp
        show "?U r j = 0"
        proof (cases "r < tick")
          case True
          have "20 \<le> ?k-(24*(r-Suc 0)+j)"
            using True tick(1) r_bounds j by arith
          then show ?thesis by (simp add: supported)
        next
          case False
          have "tick < r" using different False by arith
          then have "?k < 24*(r-Suc 0)+j"
            using tick(1) r_bounds index by arith
          then show ?thesis by simp
        qed
      qed
      show ?thesis using null different by simp
    qed
  qed
  show ?thesis unfolding mahler_cf_spatial_kernel_product
    using one tick by simp
qed

lemma mahler_cf_decimal_window_value:
  fixes n nlimbs :: nat
  shows "n mod 10^nlimbs = (\<Sum>j<nlimbs. ((n div 10^j) mod 10)*10^j)"
proof (induction nlimbs arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have mod: "n mod 10^Suc k = n mod 10 + 10*((n div 10) mod 10^k)"
    using mod_mult2_eq[of n 10 "10^k"] by (simp add: power_Suc add.commute)
  have tail: "(\<Sum>j<k. ((n div 10^Suc j) mod 10)*10^Suc j) =
      10 * (\<Sum>j<k. (((n div 10) div 10^j) mod 10)*10^j)"
    by (simp add: power_Suc div_mult2_eq sum_distrib_left mult_ac)
  have split: "(\<Sum>j<Suc k. ((n div 10^j) mod 10)*10^j) =
        n mod 10 + (\<Sum>j<k. ((n div 10^Suc j) mod 10)*10^Suc j)"
    by (subst sum.lessThan_Suc_shift) simp
  show ?case by (simp only: mod split tail Suc.IH)
qed

lemma mahler_cf_spatial_column_window:
  fixes source :: "nat poly" and tick index :: nat
  assumes decimal: "\<And>i. coeff source i < 10"
  shows "((poly source 10 * 10^tick) div 10^index) mod 10^Suc tick =
    (\<Sum>j\<le>tick. if index < j then 0 else 10^(tick-j) * coeff source (index-j))"
proof -
  let ?p = "monom 1 tick * source"
  let ?n = "poly source 10 * 10^tick"
  have n: "poly ?p 10 = ?n" by (simp add: poly_monom mult.commute)
  have limb_bound: "\<And>j. coeff ?p j < 10"
    using decimal by (simp add: coeff_monom_mult)
  have digits: "\<And>j. (((?n div 10^index) div 10^j) mod 10) =
      (if index+j < tick then 0 else coeff source (index+j-tick))"
  proof -
    fix j
    have raw: "poly ?p 10 div 10^(index+j) mod 10 = coeff ?p (index+j)"
      by (rule mahler_cf_radix_polynomial_limb[where base=10, OF _ limb_bound]) simp
    have limb_value: "?n div 10^(index+j) mod 10 = coeff ?p (index+j)"
      using raw by (simp only: n)
    show "(((?n div 10^index) div 10^j) mod 10) =
      (if index+j < tick then 0 else coeff source (index+j-tick))"
      using limb_value by (simp add: coeff_monom_mult power_add div_mult2_eq)
  qed
  have revset: "image (\<lambda>j. tick-j) {..tick} = {..tick}"
  proof
    show "image (\<lambda>j. tick-j) {..tick} \<subseteq> {..tick}" by auto
    show "{..tick} \<subseteq> image (\<lambda>j. tick-j) {..tick}"
    proof
      fix j assume "j \<in> {..tick}"
      then show "j \<in> image (\<lambda>j. tick-j) {..tick}"
        by (intro image_eqI[where x="tick-j"]) simp_all
    qed
  qed
  have inj: "inj_on (\<lambda>j. tick-j) {..tick}" by (auto simp: inj_on_def)
  let ?C = "\<lambda>j. (if index+j < tick then 0 else coeff source (index+j-tick))*10^j"
  have flipped: "(\<Sum>j\<le>tick. ?C j) =
      (\<Sum>j\<le>tick. ?C (tick-j))"
    using sum.reindex[OF inj, of ?C] revset by (simp add: comp_def)
  have source_window: "(?n div 10^index) mod 10^Suc tick =
      (\<Sum>j\<le>tick. ?C j)"
    using mahler_cf_decimal_window_value[of "?n div 10^index" "Suc tick"]
    by (simp only: lessThan_Suc_atMost digits)
  have terms: "(\<Sum>j\<le>tick. ?C (tick-j)) =
      (\<Sum>j\<le>tick. if index < j then 0 else 10^(tick-j)*coeff source (index-j))"
  proof (rule sum.cong[OF refl])
    fix j assume "j \<in> {..tick}"
    then have j: "j \<le> tick" by simp
    have less: "index + (tick-j) < tick \<longleftrightarrow> index < j"
      using j by arith
    have diff: "index + (tick-j) - tick = index-j"
      using j by arith
    show "?C (tick-j) = (if index < j then 0 else 10^(tick-j)*coeff source (index-j))"
      by (simp add: less diff mult.commute)
  qed
  show ?thesis by (simp only: source_window flipped terms)
qed

lemma mahler_cf_sum_mod_congruent:
  fixes f g :: "'a \<Rightarrow> nat"
  assumes finite: "finite A" and same: "\<And>x. x \<in> A \<Longrightarrow> f x mod m = g x mod m"
  shows "sum f A mod m = sum g A mod m"
  using finite same
proof (induction A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x A)
  have head: "f x mod m = g x mod m"
    using insert.prems by simp
  have tail: "sum f A mod m = sum g A mod m"
    using insert.IH insert.prems by simp
  have adds: "(f x + sum f A) mod m = (g x + sum g A) mod m"
  proof -
    have one: "(f x + sum f A) mod m = (f x mod m + sum f A mod m) mod m"
      by (rule mod_add_eq[symmetric])
    have two: "(g x + sum g A) mod m = (g x mod m + sum g A mod m) mod m"
      by (rule mod_add_eq[symmetric])
    show ?thesis by (simp only: one two head tail)
  qed
  show ?case using adds insert.hyps by simp
qed

theorem mahler_cf_spatial_digit_from_quotient:
  fixes source :: "nat poly" and tick index weighted :: nat
  assumes decimal: "\<And>i. coeff source i < 10"
  defines "weighted \<equiv> (\<Sum>j\<le>tick. if index < j then 0 else
        (10^(tick-j) mod (10*2^tick))*coeff source (index-j))"
  shows "(weighted div 2^tick) mod 10 = (5^tick * poly source 10 div 10^index) mod 10"
proof -
  let ?modulus = "(10::nat)*2^tick"
  let ?n = "(poly source 10 * 10^tick) div 10^index"
  have reduced: "weighted mod ?modulus = (?n mod 10^Suc tick) mod ?modulus"
    unfolding weighted_def mahler_cf_spatial_column_window[OF decimal]
  proof (rule mahler_cf_sum_mod_congruent)
    show "finite {..tick}" by simp
    fix j assume "j \<in> {..tick}"
    show "(if index < j then 0 else
          (10^(tick-j) mod ?modulus)*coeff source (index-j)) mod ?modulus =
        (if index < j then 0 else
          10^(tick-j)*coeff source (index-j)) mod ?modulus"
      by (cases "index < j") (simp_all add: mod_mult_left_eq)
  qed
  have residue: "weighted mod (2^tick*10) = ?n mod (2^tick*10)"
    using reduced mahler_cf_pow5_causal_residue[of ?n tick] by (simp add: mult.commute)
  show ?thesis
    using residue mahler_cf_quotient_remainder_digit[where v=weighted and divisor="2^tick"]
      mahler_cf_pow5_digit_quotient[where h="poly source 10" and t=tick and i=index]
    by simp
qed

theorem mahler_cf_spatial_selected_physical_digit:
  fixes source :: "nat poly" and duration tick index :: nat
  assumes duration: "duration \<le> 4" and tick: "1 \<le> tick" "tick \<le> duration"
    and index: "index < 20" and supported: "\<And>i. 20 \<le> i \<Longrightarrow> coeff source i = 0"
    and decimal: "\<And>i. coeff source i < 10"
  shows "(coeff (mahler_cf_spatial_kernel duration * source) (24*(tick-Suc 0)+index)
      div 2^duration) mod 10 = (5^tick * poly source 10 div 10^index) mod 10"
proof -
  let ?w = "\<Sum>j\<le>tick. if index < j then 0 else
    (10^(tick-j) mod (10*2^tick))*coeff source (index-j)"
  have selected: "coeff (mahler_cf_spatial_kernel duration * source) (24*(tick-Suc 0)+index) =
      2^(duration-tick) * ?w"
    using mahler_cf_spatial_selected_coefficient[OF duration tick index supported]
    by (simp only: sum_distrib_left) (intro sum.cong refl; split if_splits; simp add: algebra_simps)
  have power: "(2::nat)^duration = 2^(duration-tick) * 2^tick"
    using tick(2) by (simp flip: power_add)
  have "(2^(duration-tick) * ?w) div 2^duration = ?w div 2^tick"
    by (simp add: power)
  then show ?thesis using selected mahler_cf_spatial_digit_from_quotient[OF decimal, of index tick]
    by simp
qed

definition mahler_cf_limb_mask :: "nat \<Rightarrow> nat" where
  "mahler_cf_limb_mask nlimbs = poly (Poly (replicate nlimbs 1023)) (2^24)"

lemma mahler_cf_limb_mask_field:
  assumes "index < nlimbs"
  shows "take_bit 24 (drop_bit (24*index) (mahler_cf_limb_mask nlimbs)) = (1023::nat)"
proof -
  have bounded: "\<And>j. coeff (Poly (replicate nlimbs 1023) :: nat poly) j < 2^24"
    by (simp add: coeff_Poly_eq nth_default_def)
  have limb: "poly (Poly (replicate nlimbs 1023) :: nat poly) (2^24)
        div (2^24)^index mod 2^24 = 1023"
    using mahler_cf_radix_polynomial_limb[where base="2^24"
      and p="Poly (replicate nlimbs 1023)" and index=index, OF _ bounded] assms
    by (simp add: coeff_Poly_eq nth_default_def)
  show ?thesis using limb
    by (simp add: mahler_cf_limb_mask_def take_bit_eq_mod drop_bit_eq_div power_mult)
qed

lemma mahler_cf_masked_field:
  fixes packed :: nat
  assumes "index < nlimbs"
  shows "take_bit 24 (drop_bit (24*index) (packed AND mahler_cf_limb_mask nlimbs)) =
    take_bit 10 (drop_bit (24*index) packed)"
proof -
  have field: "take_bit 24 (drop_bit (24*index) (mahler_cf_limb_mask nlimbs)) = mask 10"
    using mahler_cf_limb_mask_field[OF assms] by (simp add: mask_eq_exp_minus_1)
  show ?thesis
    by (simp only: drop_bit_and take_bit_and field take_bit_eq_mask[symmetric]
        take_bit_take_bit min_def; simp)
qed

lemma mahler_cf_radix24_shift_field:
  fixes raw shift index :: nat
  assumes shift: "shift \<le> 14"
    and small: "(raw div (2^24)^index mod 2^24) div 2^shift < 1024"
  shows "(raw div 2^shift div (2^24)^index) mod 1024 =
    (raw div (2^24)^index mod 2^24) div 2^shift"
proof -
  have factored: "(2::nat)^24 = 2^shift * 2^(24-shift)"
    using shift by (simp flip: power_add)
  have divisibility: "(1024::nat) dvd 2^(24-shift)"
  proof -
    have "(10::nat) \<le> 24-shift" using shift by arith
    then show ?thesis using le_imp_power_dvd[of 10 "24-shift" "2::nat"] by simp
  qed
  have residue: "raw div 2^shift div (2^24)^index mod 2^(24-shift) =
      (raw div (2^24)^index mod 2^24) div 2^shift"
    using mahler_cf_radix_polynomial_shift[where divisor="2^shift"
        and base="2^(24-shift)" and index=index and packed=raw] factored
    by simp
  have collapse: "(raw div 2^shift div (2^24)^index mod 2^(24-shift)) mod 1024 =
      (raw div 2^shift div (2^24)^index) mod 1024"
    by (rule mod_mod_cancel[OF divisibility])
  show ?thesis using residue collapse small by simp
qed

lemma mahler_cf_masked_radix24_shift_field:
  fixes raw shift index nlimbs :: nat
  assumes "index < nlimbs" "shift \<le> 14"
    and "(raw div (2^24)^index mod 2^24) div 2^shift < 1024"
  shows "(raw div 2^shift AND mahler_cf_limb_mask nlimbs) div (2^24)^index mod 2^24 =
    (raw div (2^24)^index mod 2^24) div 2^shift"
  using mahler_cf_masked_field[where index=index and nlimbs=nlimbs and packed="raw div 2^shift", OF assms(1)]
    mahler_cf_radix24_shift_field[OF assms(2,3)]
  by (simp add: take_bit_eq_mod drop_bit_eq_div power_mult)

theorem mahler_cf_packed_reciprocal_field:
  fixes p :: "nat poly" and index nlimbs :: nat
  assumes bounded: "\<And>j. coeff p j \<le> 450" and index: "index < nlimbs"
  shows "((410 * poly p (2^24) div 4096) AND mahler_cf_limb_mask nlimbs)
        div (2^24)^index mod 2^24 = coeff p index div 10"
proof -
  let ?q = "monom 410 0 * p"
  let ?raw = "410 * poly p (2^24)"
  have eval: "poly ?q (2^24) = ?raw" by (simp add: poly_monom)
  have bound: "\<And>j. coeff ?q j < 2^24"
  proof -
    fix j
    have "410 * coeff p j \<le> 410 * 450" by (rule mult_left_mono[OF bounded]; simp)
    then show "coeff ?q j < 2^24" by (simp add: coeff_monom_mult)
  qed
  have extracted: "poly ?q (2^24) div (2^24)^index mod 2^24 = coeff ?q index"
    by (rule mahler_cf_radix_polynomial_limb[OF _ bound]) simp
  have raw: "?raw div (2^24)^index mod 2^24 = 410 * coeff p index"
    using extracted by (simp only: eval coeff_monom_mult; simp)
  have qbound: "coeff p index div 10 \<le> 45"
    using div_le_mono[OF bounded[of index], of 10] by simp
  have reciprocal: "(410 * coeff p index) div 4096 = coeff p index div 10"
    by (rule mahler_cf_reciprocal_div10[OF bounded])
  have small: "(?raw div (2^24)^index mod 2^24) div 2^12 < 1024"
    using qbound by (simp only: raw reciprocal; simp)
  have field: "(?raw div 2^12 AND mahler_cf_limb_mask nlimbs)
      div (2^24)^index mod 2^24 = (?raw div (2^24)^index mod 2^24) div 2^12"
    using index small by (intro mahler_cf_masked_radix24_shift_field) simp_all
  show ?thesis using field raw mahler_cf_reciprocal_div10[OF bounded[of index]] by simp
qed

lemma mahler_cf_radix_equal_from_fields:
  fixes x y base n :: nat
  assumes base: "0 < base" and x: "x < base^n" and y: "y < base^n"
    and field: "\<And>i. i < n \<Longrightarrow> x div base^i mod base = y div base^i mod base"
  shows "x = y"
  using x y field
proof (induction n arbitrary: x y)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have xd: "x div base < base^n"
    by (rule less_mult_imp_div_less) (use Suc.prems(1) in \<open>simp add: power_Suc mult.commute\<close>)
  have yd: "y div base < base^n"
    by (rule less_mult_imp_div_less) (use Suc.prems(2) in \<open>simp add: power_Suc mult.commute\<close>)
  have eq: "x div base = y div base"
  proof (rule Suc.IH[OF xd yd])
    fix i assume "i < n"
    then have "x div base^(Suc i) mod base = y div base^(Suc i) mod base"
      by (intro Suc.prems(3)) simp
    then show "x div base div base^i mod base = y div base div base^i mod base"
      by (simp only: power_Suc div_mult2_eq)
  qed
  have r: "x mod base = y mod base" using Suc.prems(3)[of 0] by simp
  have "x div base * base + x mod base = y div base * base + y mod base"
    by (simp only: eq r)
  then show ?case by simp
qed

lemma mahler_cf_poly_split_div10:
  fixes p :: "nat poly" and base :: nat
  shows "poly p base = 10 * poly (map_poly (\<lambda>x. x div 10) p) base +
                     poly (map_poly (\<lambda>x. x mod 10) p) base"
proof -
  let ?q = "map_poly (\<lambda>(x::nat). x div 10) p"
  let ?r = "map_poly (\<lambda>(x::nat). x mod 10) p"
  have "p = monom 10 0 * ?q + ?r"
  proof (rule poly_eqI)
    fix i show "coeff p i = coeff (monom 10 0 * ?q + ?r) i"
      by (simp add: coeff_map_poly coeff_monom_mult mult.commute)
  qed
  then have "poly p base = poly (monom 10 0 * ?q + ?r) base"
    by (rule arg_cong)
  then show ?thesis by (simp add: poly_add poly_mult poly_monom)
qed

definition mahler_cf_spatial_values :: "nat poly \<Rightarrow> nat \<Rightarrow> nat" where
  "mahler_cf_spatial_values p duration =
    ((poly p (2^24) * poly (mahler_cf_spatial_kernel duration) (2^24)) div 2^duration)
      AND mahler_cf_limb_mask (24*duration)"

lemma mahler_cf_spatial_values_field:
  fixes p :: "nat poly" and duration i v q :: nat
  assumes duration: "duration \<le> 4" and i: "i < 24*duration"
    and decimal: "\<And>j. coeff p j < 10"
  shows "mahler_cf_spatial_values p duration div (2^24)^i mod 2^24 =
      coeff (mahler_cf_spatial_kernel duration * p) i div 2^duration"
proof -
  let ?q = "mahler_cf_spatial_kernel duration * p"
  let ?raw = "poly p (2^24) * poly (mahler_cf_spatial_kernel duration) (2^24)"
  have p9: "\<And>j. coeff p j \<le> 9"
  proof -
    fix j show "coeff p j \<le> 9" using decimal[of j] by arith
  qed
  have bounds: "\<And>j. coeff ?q j \<le> 405*2^duration"
    by (rule mahler_cf_spatial_product_bound[OF p9 duration])
  have powers: "(2::nat)^duration \<le> 2^4"
    by (rule power_increasing[OF duration]) simp
  have B: "405*2^duration < (2::nat)^24" using powers by simp
  have C: "\<And>j. coeff ?q j < (2::nat)^24" using bounds B by (meson le_less_trans)
  have digit: "?raw div (2^24)^i mod 2^24 = coeff ?q i"
    using mahler_cf_radix_polynomial_limb[where base="2^24" and p="?q" and index=i,
      OF _ C] by (simp add: mult.commute)
  have reduced: "coeff ?q i div 2^duration \<le> 405"
    using div_le_mono[OF bounds[of i], of "2^duration"] by simp
  have small: "(?raw div (2^24)^i mod 2^24) div 2^duration < 1024"
    using reduced by (simp only: digit; arith)
  have d14: "duration \<le> 14" using duration by arith
  show ?thesis unfolding mahler_cf_spatial_values_def
    using mahler_cf_masked_radix24_shift_field[where raw="?raw" and shift=duration
      and index=i and nlimbs="24*duration", OF i d14 small]
    by (simp only: digit)
qed

lemma mahler_cf_radix_list_fits:
  fixes base :: nat and xs :: "nat list"
  assumes "0 < base" "list_all (\<lambda>x. x < base) xs"
  shows "poly (Poly xs) base < base^length xs"
  using assms(2)
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have a: "a < base" and xs: "list_all (\<lambda>x. x < base) xs"
    using Cons.prems by simp_all
  have "poly (Poly (a#xs)) base = a + base * poly (Poly xs) base"
    by simp
  also have "... < base + base * poly (Poly xs) base" using a by simp
  also have "... = base * (Suc (poly (Poly xs) base))" by simp
  also have "... \<le> base * base^length xs"
    using Cons.IH[OF xs] by (intro mult_left_mono) simp_all
  finally show ?case by (simp only: length_Cons power_Suc)
qed

lemma mahler_cf_masked_fits:
  fixes x nlimbs :: nat
  shows "(x AND mahler_cf_limb_mask nlimbs) < (2^24)^nlimbs"
proof -
  have mask: "mahler_cf_limb_mask nlimbs < (2^24)^nlimbs"
  proof -
    have fits: "poly (Poly (replicate nlimbs (1023::nat))) (2^24) < (2^24)^length (replicate nlimbs (1023::nat))"
      by (rule mahler_cf_radix_list_fits) (simp_all add: list_all_iff)
    show ?thesis using fits by (simp only: mahler_cf_limb_mask_def length_replicate)
  qed
  have zero: "drop_bit (24*nlimbs) (mahler_cf_limb_mask nlimbs) = 0"
    using mask by (simp add: drop_bit_eq_div power_mult)
  have "drop_bit (24*nlimbs) (x AND mahler_cf_limb_mask nlimbs) = 0"
    by (simp add: zero)
  then have quotient: "(x AND mahler_cf_limb_mask nlimbs) div (2^(24*nlimbs)) = 0"
    by (simp only: drop_bit_eq_div)
  have "x AND mahler_cf_limb_mask nlimbs < 2^(24*nlimbs)"
    using quotient by (simp add: div_eq_0_iff)
  then show ?thesis by (simp only: power_mult)
qed

definition mahler_cf_spatial_value_poly :: "nat poly \<Rightarrow> nat \<Rightarrow> nat poly" where
  "mahler_cf_spatial_value_poly p duration = Poly
    (map (\<lambda>i. coeff (mahler_cf_spatial_kernel duration * p) i div 2^duration)
      [0..<24*duration])"

theorem mahler_cf_spatial_no_borrow:
  fixes p :: "nat poly" and duration i v q :: nat
  assumes duration: "duration \<le> 4" and i: "i < 24*duration"
    and digits: "\<And>j. coeff p j < 10"
  defines "v \<equiv> mahler_cf_spatial_values p duration"
    and "q \<equiv> (410*v div 4096) AND mahler_cf_limb_mask (24*duration)"
  shows "((v - 10*q) div (2^24)^i) mod 2^24 =
    (coeff (mahler_cf_spatial_kernel duration * p) i div 2^duration) mod 10"
proof -
  let ?P = "mahler_cf_spatial_value_poly p duration"
  let ?Q = "map_poly (\<lambda>x. x div 10) ?P"
  let ?R = "map_poly (\<lambda>x. x mod 10) ?P"
  let ?f = "\<lambda>i. coeff (mahler_cf_spatial_kernel duration * p) i div 2^duration"
  let ?r = "(2::nat)^24"
  let ?n = "24*duration"
  have fmax: "\<And>j. ?f j \<le> 405"
  proof -
    fix j
    have digit9: "\<And>k. coeff p k \<le> 9"
    proof -
      fix k show "coeff p k \<le> 9" using digits[of k] by arith
    qed
    show "?f j \<le> 405"
      using div_le_mono[OF mahler_cf_spatial_product_bound[OF digit9 duration, of j],
         of "2^duration"] by simp
  qed
  have coeff_P: "\<And>j. coeff ?P j = (if j < ?n then ?f j else 0)"
    by (simp add: mahler_cf_spatial_value_poly_def nth_default_def)
  have Pmax: "\<And>j. coeff ?P j \<le> 450"
  proof -
    fix j
    have "?f j \<le> 405" by (rule fmax)
    then show "coeff ?P j \<le> 450" by (simp only: coeff_P; split if_splits; arith)
  qed
  have B: "\<And>j. coeff ?P j < ?r"
  proof -
    fix j
    have limit: "450 < ?r" by simp
    show "coeff ?P j < ?r" by (rule le_less_trans[OF Pmax limit])
  qed
  have vfit: "v < ?r^?n"
    unfolding v_def mahler_cf_spatial_values_def by (rule mahler_cf_masked_fits)
  have allf: "\<And>j. ?f j < ?r"
  proof -
    fix j have "?f j \<le> 405" by (rule fmax)
    moreover have "405 < ?r" by simp
    ultimately show "?f j < ?r" by (rule le_less_trans)
  qed
  have all_small: "list_all (\<lambda>x. x < ?r) (map ?f [0..<?n])"
    using allf by (simp add: list_all_iff)
  have fits: "poly (Poly (map ?f [0..<?n])) ?r < ?r^length (map ?f [0..<?n])"
    by (rule mahler_cf_radix_list_fits[OF _ all_small]) simp
  have Pfit: "poly ?P ?r < ?r^?n"
    using fits by (simp only: mahler_cf_spatial_value_poly_def length_map length_upt diff_zero)
  have veq: "v = poly ?P ?r"
  proof (rule mahler_cf_radix_equal_from_fields[OF _ vfit Pfit])
    show "0 < ?r" by simp
    fix j assume j: "j < ?n"
    show "v div ?r^j mod ?r = poly ?P ?r div ?r^j mod ?r"
      using mahler_cf_spatial_values_field[OF duration j digits]
        mahler_cf_radix_polynomial_limb[where p="?P" and base="?r" and index=j, OF _ B]
      by (simp add: v_def coeff_P j)
  qed
  have qfit: "q < ?r^?n" unfolding q_def by (rule mahler_cf_masked_fits)
  have Qpoly: "?Q = Poly (map (\<lambda>j. ?f j div 10) [0..<?n])"
    by (rule poly_eqI) (simp add: coeff_map_poly coeff_P nth_default_def)
  have allq: "\<And>j. ?f j div 10 < ?r"
  proof -
    fix j
    have "?f j div 10 \<le> ?f j" by simp
    then show "?f j div 10 < ?r" by (rule le_less_trans[OF _ allf])
  qed
  have qlist: "list_all (\<lambda>x. x < ?r) (map (\<lambda>j. ?f j div 10) [0..<?n])"
    using allq by (simp add: list_all_iff)
  have qfits: "poly (Poly (map (\<lambda>j. ?f j div 10) [0..<?n])) ?r <
      ?r^length (map (\<lambda>j. ?f j div 10) [0..<?n])"
    by (rule mahler_cf_radix_list_fits[OF _ qlist]) simp
  have Qfit: "poly ?Q ?r < ?r^?n"
    using qfits by (simp only: Qpoly length_map length_upt diff_zero)
  have Qsmall: "\<And>j. coeff ?Q j < ?r"
  proof -
    fix j
    have bound: "coeff ?P j \<le> 450" by (rule Pmax)
    have quotient: "coeff ?P j div 10 \<le> coeff ?P j" by simp
    have limit: "450 < ?r" by simp
    have "coeff ?P j div 10 < ?r" using quotient bound limit by arith
    then show "coeff ?Q j < ?r" by (simp only: coeff_map_poly)
  qed
  have qeq: "q = poly ?Q ?r"
  proof (rule mahler_cf_radix_equal_from_fields[OF _ qfit Qfit])
    show "0 < ?r" by simp
    fix j assume j: "j < ?n"
    show "q div ?r^j mod ?r = poly ?Q ?r div ?r^j mod ?r"
      using mahler_cf_packed_reciprocal_field[OF Pmax j]
        mahler_cf_radix_polynomial_limb[where p="?Q" and base="?r" and index=j, OF _ Qsmall]
      by (simp add: q_def veq coeff_map_poly)
  qed
  have req: "v - 10*q = poly ?R ?r"
    using mahler_cf_poly_split_div10[of "?P" "?r"] by (simp add: veq qeq)
  have Rsmall: "\<And>j. coeff ?R j < ?r"
    by (simp add: coeff_map_poly)
  show ?thesis
    using mahler_cf_radix_polynomial_limb[where p="?R" and base="?r" and index=i, OF _ Rsmall] i
    by (simp add: req coeff_map_poly coeff_P)
qed

definition mahler_cf_cut_poly :: "nat poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat poly" where
  "mahler_cf_cut_poly source start width = Poly
    (map (\<lambda>i. coeff source (start+i)) [0..<width])"

lemma mahler_cf_cut_poly_coeff:
  "coeff (mahler_cf_cut_poly source start width) i =
    (if i < width then coeff source (start+i) else 0)"
  by (simp add: mahler_cf_cut_poly_def nth_default_def)

theorem mahler_cf_cut_lower_halo_digit:
  fixes source :: "nat poly" and start width index tick :: nat
  assumes index: "index < width" and halo: "start = 0 \<or> tick \<le> index"
    and decimal: "\<And>i. coeff source i < 10"
  shows "(5^tick * poly (mahler_cf_cut_poly source start width) 10 div 10^index) mod 10 =
    (5^tick * poly source 10 div 10^(start+index)) mod 10"
proof -
  let ?cut = "mahler_cf_cut_poly source start width"
  let ?w = "\<lambda>p i. \<Sum>j\<le>tick. if i < j then 0 else
    (10^(tick-j) mod (10*2^tick))*coeff p (i-j)"
  have cut_digits: "\<And>i. coeff ?cut i < 10"
    by (simp add: mahler_cf_cut_poly_coeff decimal)
  have same: "?w ?cut index = ?w source (start+index)"
  proof (rule sum.cong[OF refl])
    fix j assume j: "j \<in> {..tick}"
    have relation: "index < j \<longleftrightarrow> start+index < j"
      using j halo by auto
    show "(if index < j then 0 else
           (10^(tick-j) mod (10*2^tick))*coeff ?cut (index-j)) =
          (if start+index < j then 0 else
           (10^(tick-j) mod (10*2^tick))*coeff source (start+index-j))"
    proof (cases "index < j")
      case True
      thus ?thesis by (simp add: relation)
    next
      case False
      have small: "index-j < width" using index by arith
      have order: "start+index-j = start+(index-j)" using False by arith
      show ?thesis
        by (simp only: relation[symmetric] False if_False order
              mahler_cf_cut_poly_coeff small if_True)
    qed
  qed
  have a: "(?w ?cut index div 2^tick) mod 10 =
      (5^tick * poly ?cut 10 div 10^index) mod 10"
    using mahler_cf_spatial_digit_from_quotient[OF cut_digits, of index tick] by simp
  have b: "(?w source (start+index) div 2^tick) mod 10 =
      (5^tick * poly source 10 div 10^(start+index)) mod 10"
    using mahler_cf_spatial_digit_from_quotient[OF decimal, of "start+index" tick] by simp
  show ?thesis using a b same by metis
qed

lemma mahler_cf_spatial_join_radix_lanes:
  fixes low high width :: nat
  assumes fits: "low < (2^24)^width"
  shows "low OR push_bit (24*width) high = low + (2^24)^width * high"
proof -
  have width: "low < 2^(24*width)" using fits by (simp add: power_mult)
  have mask: "take_bit (24*width) low = low"
    using take_bit_nat_eq_self_iff width by blast
  have "take_bit (24*width) low AND push_bit (24*width) high = 0"
    by (simp add: bit_eq_iff bit_simps)
  then have "low AND push_bit (24*width) high = 0"
    by (simp only: mask)
  then have join: "low + push_bit (24*width) high = low OR push_bit (24*width) high"
    by (rule disjunctive_add_eq_or)
  have exponent: "(2::nat)^(24*width) = (2^24)^width"
    by (simp only: power_mult)
  have shifted: "push_bit (24*width) high = (2^24)^width * high"
    by (simp only: push_bit_eq_mult exponent; rule mult.commute)
  show ?thesis using join[symmetric] by (simp only: shifted)
qed

ML \<open>
  val checked = @{thms
    mahler_cf_quotient_remainder_digit mahler_cf_reciprocal_div10
    mahler_cf_pow5_digit_quotient mahler_cf_pow5_causal_residue
    mahler_cf_fixed_band_placement mahler_cf_radix_polynomial_convolution
    mahler_cf_radix_polynomial_shift mahler_cf_spatial_kernel_weight
    mahler_cf_spatial_product_bound mahler_cf_spatial_selected_coefficient
    mahler_cf_spatial_selected_physical_digit
    mahler_cf_limb_mask_field mahler_cf_masked_field
    mahler_cf_masked_radix24_shift_field mahler_cf_packed_reciprocal_field};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "CF spatial row oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "CF spatial row skipped proof" else ();
\<close>

end
