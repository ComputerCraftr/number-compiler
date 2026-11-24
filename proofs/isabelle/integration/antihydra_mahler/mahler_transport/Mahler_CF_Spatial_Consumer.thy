theory Mahler_CF_Spatial_Consumer
  imports Mahler_CF_Spatial_Intermediate_Rows
begin

unbundle bit_operations_syntax

text \<open>The consumer evaluates every requested physical time from the same
decimal inlet. Its spatial children crop their complete lower support before
evaluation. Low and high children are combined at the same physical time.\<close>

definition mahler_cf_spatial_leaf :: "nat poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mahler_cf_spatial_leaf p duration tick width below =
    (let v = mahler_cf_spatial_values p duration;
         q = (410*v div 4096) AND mahler_cf_limb_mask (24*duration)
     in ((v - 10*q) div (2^24)^(24*(tick-Suc 0)+below)) mod (2^24)^width)"

lemma mahler_cf_radix_cropped_field:
  fixes packed base start width j :: nat
  assumes "0 < base" "j < width"
  shows "(packed div base^start mod base^width) div base^j mod base =
    packed div base^(start+j) mod base"
proof -
  let ?v = "packed div base^start"
  have W: "base^width = base^j * base^(width-j)" using assms(2)
    by (simp flip: power_add)
  have B: "0 < base^j" using assms by simp
  have mod: "(?v mod base^width) div base^j = (?v div base^j) mod base^(width-j)"
  proof -
    have split: "?v mod base^width = base^j * (?v div base^j mod base^(width-j)) + ?v mod base^j"
      unfolding W by (rule mod_mult2_eq)
    show ?thesis unfolding split using B by (simp add: div_add1_eq)
  qed
  have "base^1 dvd base^(width-j)" using assms(2)
    by (intro le_imp_power_dvd) simp
  then have dvd: "base dvd base^(width-j)" by simp
  have "(?v mod base^width) div base^j mod base = ?v div base^j mod base"
    by (simp only: mod mod_mod_cancel[OF dvd])
  also have "... = packed div base^(start+j) mod base"
    by (simp only: div_mult2_eq power_add)
  finally show ?thesis .
qed

theorem mahler_cf_spatial_leaf_selected_digit:
  fixes source :: "nat poly" and duration tick lo width j :: nat
  assumes dur: "duration \<le> 4" and tick: "1 \<le> tick" "tick \<le> duration"
    and width: "width \<le> 16" and column: "j < width"
    and digits: "\<And>k. coeff source k < 10"
  shows "mahler_cf_spatial_leaf
      (mahler_cf_cut_poly source (lo-min lo duration) (width+min lo duration))
      duration tick width (min lo duration) div (2^24)^j mod 2^24 =
    ((5^tick * poly source 10) div 10^(lo+j)) mod 10"
proof -
  let ?below = "min lo duration"
  let ?p = "mahler_cf_cut_poly source (lo - ?below) (width + ?below)"
  let ?b = "?below+j"
  let ?k = "24*(tick-Suc 0)+?b"
  let ?v = "mahler_cf_spatial_values ?p duration"
  let ?q = "(410*?v div 4096) AND mahler_cf_limb_mask (24*duration)"
  have B: "?b < 20" using dur width column by arith
  have K: "?k < 24*duration" using B tick by arith
  have src_digits: "\<And>k. coeff ?p k < 10"
    by (simp add: mahler_cf_cut_poly_coeff digits)
  have supported: "\<And>k. 20 \<le> k \<Longrightarrow> coeff ?p k = 0"
  proof -
    fix k :: nat
    assume "20 \<le> k"
    then have "\<not> k < width + ?below" using dur width by arith
    then show "coeff ?p k = 0" by (simp only: mahler_cf_cut_poly_coeff if_False)
  qed
  have L: "mahler_cf_spatial_leaf ?p duration tick width ?below div (2^24)^j mod 2^24 =
      ((?v - 10*?q) div (2^24)^?k) mod 2^24"
    unfolding mahler_cf_spatial_leaf_def Let_def
    by (simp add: mahler_cf_radix_cropped_field[OF _ column] add.assoc)
  have V: "((?v - 10*?q) div (2^24)^?k) mod 2^24 =
      (5^tick * poly ?p 10 div 10^?b) mod 10"
    using mahler_cf_spatial_no_borrow[OF dur K src_digits]
      mahler_cf_spatial_selected_physical_digit[OF dur tick B supported src_digits]
    by simp
  have within: "?b < width + ?below" using column by simp
  have halo: "lo - ?below = 0 \<or> tick \<le> ?b"
    using tick by arith
  have index: "(lo - ?below) + ?b = lo+j" by simp
  have H: "(5^tick * poly ?p 10 div 10^?b) mod 10 =
      ((5^tick * poly source 10) div 10^(lo+j)) mod 10"
    using mahler_cf_cut_lower_halo_digit[OF within halo digits] index by simp
  show ?thesis by (simp only: L V H)
qed

function mahler_cf_spatial_visit :: "nat poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mahler_cf_spatial_visit source duration tick lo width =
    (if width \<le> 16 then
       mahler_cf_spatial_leaf
         (mahler_cf_cut_poly source (lo-min lo duration) (width+min lo duration))
         duration tick width (min lo duration)
     else
       (let half = width div 2;
            low = mahler_cf_spatial_visit source duration tick lo half;
            high = mahler_cf_spatial_visit source duration tick (lo+half) (width-half)
        in low OR push_bit (24*half) high))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(source,duration,tick,lo,width). width)") auto

declare mahler_cf_spatial_visit.simps[simp del]

lemma mahler_cf_radix_join_field:
  fixes l h base mid j :: nat
  assumes pos: "0 < base" and fits: "l < base^mid"
  shows "(l + base^mid * h) div base^j mod base =
    (if j < mid then l div base^j mod base else h div base^(j-mid) mod base)"
proof (cases "j < mid")
  case True
  then have d: "Suc j \<le> mid" by simp
  have divisibility: "base^Suc j dvd base^mid" by (rule le_imp_power_dvd[OF d])
  obtain k where factor: "base^mid = base^Suc j * k"
    using divisibility by (rule dvdE)
  have M: "(l + base^mid*h) mod base^Suc j = l mod base^Suc j"
    unfolding factor mult.assoc by (rule mod_mult_self2)
  have digit: "\<And>n. (n div base^j) mod base =
       (n mod (base^j*base)) div base^j"
  proof -
    fix n show "(n div base^j) mod base = (n mod (base^j*base)) div base^j"
      using mahler_cf_radix_polynomial_shift[where divisor="base^j" and base=base and index=0
        and packed=n] pos by simp
  qed
  have suc: "base^Suc j = base^j*base" by (simp add: power_Suc mult.commute)
  show ?thesis
    by (simp only: True if_True digit suc[symmetric] M)
next
  case False
  have j: "j = mid + (j-mid)" using False by arith
  have Q: "(l + base^mid*h) div base^mid = h" using fits pos by (simp add: div_add1_eq)
  have "(l + base^mid*h) div base^j = h div base^(j-mid)"
    using arg_cong[OF j, where f="\<lambda>k. (l + base^mid*h) div base^k"]
    by (simp only: power_add div_mult2_eq Q)
  then show ?thesis using False by simp
qed

theorem mahler_cf_spatial_visit_exact:
  fixes source :: "nat poly" and duration tick lo width :: nat
  assumes dur: "duration \<le> 4" and tick: "1 \<le> tick" "tick \<le> duration"
    and digits: "\<And>k. coeff source k < 10"
  shows "mahler_cf_spatial_visit source duration tick lo width < (2^24)^width \<and>
    (\<forall>j<width. mahler_cf_spatial_visit source duration tick lo width div (2^24)^j mod 2^24 =
      ((5^tick * poly source 10) div 10^(lo+j)) mod 10)"
proof (induction width arbitrary: lo rule: less_induct)
  case (less width)
  let ?B = "(2::nat)^24"
  let ?v = "mahler_cf_spatial_visit source duration tick"
  let ?value = "5^tick * poly source 10"
  show ?case
  proof (cases "width \<le> 16")
    case True
    let ?p = "mahler_cf_cut_poly source (lo-min lo duration) (width+min lo duration)"
    have v: "?v lo width = mahler_cf_spatial_leaf ?p duration tick width (min lo duration)"
      by (simp only: mahler_cf_spatial_visit.simps[of source duration tick lo width] True if_True)
    have fits: "?v lo width < ?B^width"
      unfolding v mahler_cf_spatial_leaf_def Let_def
      by (rule mod_less_divisor) simp
    moreover have "\<forall>j<width. ?v lo width div ?B^j mod ?B = (?value div 10^(lo+j)) mod 10"
    proof (intro allI impI)
      fix j assume j: "j < width"
      show "?v lo width div ?B^j mod ?B = (?value div 10^(lo+j)) mod 10"
        unfolding v by (rule mahler_cf_spatial_leaf_selected_digit[OF dur tick True j digits])
    qed
    ultimately show ?thesis by blast
  next
    case False
    let ?half = "width div 2"
    let ?tail = "width-?half"
    let ?l = "?v lo ?half"
    let ?r = "?v (lo+?half) ?tail"
    have h: "?half < width" "?tail < width" "?half+?tail = width" using False by arith+
    have low: "?l < ?B^?half" "\<And>j. j < ?half \<Longrightarrow>
        ?l div ?B^j mod ?B = (?value div 10^(lo+j)) mod 10"
      using less.IH[OF h(1), of lo] by blast+
    have high: "?r < ?B^?tail" "\<And>j. j < ?tail \<Longrightarrow>
        ?r div ?B^j mod ?B = (?value div 10^((lo+?half)+j)) mod 10"
      using less.IH[OF h(2), of "lo+?half"] by blast+
    have join: "?v lo width = ?l + ?B^?half * ?r"
      using mahler_cf_spatial_join_radix_lanes[OF low(1), of ?r]
      by (simp only: mahler_cf_spatial_visit.simps[of source duration tick lo width]
        False if_False Let_def)
    have fits: "?v lo width < ?B^width"
    proof -
      have "?v lo width < ?B^?half + ?B^?half * ?r"
        using low(1) by (simp only: join add_less_cancel_right)
      also have "... = ?B^?half * Suc ?r" by simp
      also have "... \<le> ?B^?half * ?B^?tail"
      proof -
        have "Suc ?r \<le> ?B^?tail" using high(1) by arith
        then show ?thesis by (rule mult_le_mono2)
      qed
      also have "... = ?B^width" by (simp only: power_add[symmetric] h(3))
      finally show ?thesis .
    qed
    moreover have "\<forall>j<width. ?v lo width div ?B^j mod ?B = (?value div 10^(lo+j)) mod 10"
    proof (intro allI impI)
      fix j assume j: "j < width"
      have field: "?v lo width div ?B^j mod ?B =
        (if j < ?half then ?l div ?B^j mod ?B else ?r div ?B^(j-?half) mod ?B)"
        unfolding join by (rule mahler_cf_radix_join_field[OF _ low(1)]) simp
      show "?v lo width div ?B^j mod ?B = (?value div 10^(lo+j)) mod 10"
      proof (cases "j < ?half")
        case True
        show ?thesis using low(2)[OF True] by (simp only: field True if_True)
      next
        case False
        have rest: "j-?half < ?tail" and index: "(lo+?half)+(j-?half) = lo+j"
          using j h(3) False by arith+
        show ?thesis using high(2)[OF rest]
          by (simp only: field False if_False index)
      qed
    qed
    ultimately show ?thesis by blast
  qed
qed

text \<open>The direct leaf avoids constructing a crop when its source already
fits the requested width. The extra zero lanes are part of the same inlet.\<close>

lemma mahler_cf_complete_source_crop:
  fixes p :: "nat poly" and width duration :: nat
  assumes digit: "\<And>j. coeff p j < 10" and fit: "poly p 10 < 10^width"
  shows "mahler_cf_cut_poly p 0 (width+duration) = p"
proof (rule poly_eqI)
  fix j
  show "coeff (mahler_cf_cut_poly p 0 (width+duration)) j = coeff p j"
  proof (cases "j < width+duration")
    case True then show ?thesis by (simp only: mahler_cf_cut_poly_coeff if_True add_0_left)
  next
    case False
    have width: "width \<le> j" using False by arith
    have "(10::nat)^width \<le> 10^j" by (rule power_increasing[OF width]) simp
    then have small: "poly p 10 < 10^j" using fit by arith
    have "coeff p j = 0"
      using mahler_cf_radix_polynomial_limb[where p=p and base=10 and index=j, OF _ digit]
        small by simp
    with False show ?thesis by (simp only: mahler_cf_cut_poly_coeff if_False)
  qed
qed

theorem mahler_cf_spatial_direct_leaf:
  fixes p :: "nat poly" and width duration tick :: nat
  assumes bound: "width+duration \<le> 16"
    and digit: "\<And>j. coeff p j < 10" and fit: "poly p 10 < 10^width"
  shows "mahler_cf_spatial_visit p duration tick 0 (width+duration) =
      mahler_cf_spatial_leaf p duration tick (width+duration) 0"
  by (simp only: mahler_cf_spatial_visit.simps[of p duration tick 0 "width+duration"] bound
      if_True min_0L diff_zero add_0_right mahler_cf_complete_source_crop[OF digit fit])

definition mahler_cf_spatial_decode :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "mahler_cf_spatial_decode width packed =
    dropWhile ((=) 0) (rev (map (\<lambda>j. packed div (2^24)^j mod 2^24) [0..<width]))"

definition mahler_cf_spatial_packed_stream ::
    "nat poly \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "mahler_cf_spatial_packed_stream source width duration =
    concat (map (\<lambda>i. mahler_cf_spatial_decode (width+duration)
      (mahler_cf_spatial_visit source duration (Suc i) 0 (width+duration))) [0..<duration])"

lemma mahler_cf_poly_decimal_word:
  "poly (Poly digits) (10::nat) = decimal_lsd_value digits"
  by (induction digits) (simp_all add: Poly.simps mult.commute)

theorem mahler_cf_spatial_packed_stream_exact:
  fixes n width duration :: nat
  assumes dur: "duration \<le> 4" and source_fits: "(5::nat)^n < 10^width"
  shows "mahler_cf_spatial_packed_stream (Poly (mahler_cf_pow5_word n)) width duration =
    concat (map (\<lambda>i. rev (reflected_trim_high (mahler_cf_pow5_word (n+Suc i))))
      [0..<duration])"
proof -
  let ?source = "Poly (mahler_cf_pow5_word n)"
  let ?width = "width+duration"
  let ?row = "\<lambda>tick. mahler_cf_spatial_visit ?source duration tick 0 ?width"
  let ?published = "\<lambda>i. mahler_cf_spatial_decode ?width (?row (Suc i))"
  let ?physical = "\<lambda>i. rev (reflected_trim_high (mahler_cf_pow5_word (n+Suc i)))"
  have source_digits: "\<And>j. coeff ?source j < 10"
  proof -
    fix j
    show "coeff ?source j < 10"
    proof (cases "j < length (mahler_cf_pow5_word n)")
      case True
      then have "mahler_cf_pow5_word n ! j \<in> set (mahler_cf_pow5_word n)"
        by (rule nth_mem)
      then have "mahler_cf_pow5_word n ! j < 10"
        using mahler_cf_pow5_word_consumer(2)[of n] unfolding list_all_iff by blast
      then show ?thesis using True by (simp add: nth_default_def)
    next
      case False
      then show ?thesis by (simp add: nth_default_def)
    qed
  qed
  have source_value: "poly ?source 10 = 5^n"
    using mahler_cf_pow5_word_consumer(1) by (simp only: mahler_cf_poly_decimal_word)
  have growth: "(5::nat)^duration * 5^n < 10^?width"
    by (rule mahler_cf_packed_runtime_width[OF source_fits])
  have rows: "map ?published [0..<duration] = map ?physical [0..<duration]"
  proof (rule map_cong[OF refl])
    fix i assume member: "i \<in> set [0..<duration]"
    have tick: "1 \<le> Suc i" "Suc i \<le> duration" using member by simp_all
    let ?v = "(5::nat)^(Suc i)*5^n"
    let ?digits = "mahler_cf_pow5_word (n+Suc i)"
    have physical: "\<And>j. j < ?width \<Longrightarrow>
      ?row (Suc i) div (2^24)^j mod 2^24 = (?v div 10^j) mod 10"
      using mahler_cf_spatial_visit_exact[OF dur tick source_digits, of 0 ?width]
      by (auto simp only: add_0_left source_value)
    have canonical: "?v = decimal_lsd_value ?digits"
      by (simp only: mahler_cf_pow5_word_consumer(1) power_add mult.commute)
    have fits: "?v < 10^?width"
    proof -
      have "(5::nat)^(Suc i) \<le> 5^duration"
        by (intro power_increasing[OF tick(2)]) simp
      then have "?v \<le> 5^duration * 5^n" by (rule mult_le_mono1)
      thus ?thesis by (rule le_less_trans[OF _ growth])
    qed
    have decode: "map (\<lambda>j. ?row (Suc i) div (2^24)^j mod 2^24) [0..<?width] =
        rev (mahler_cf_decimal_digits ?width (decimal_lsd_value ?digits))"
      unfolding mahler_cf_padded_digits_lsd[OF mahler_cf_pow5_word_consumer(2)]
    proof (rule map_cong[OF refl])
      fix j assume j: "j \<in> set [0..<?width]"
      have column: "j < ?width" using j by simp
      have "?row (Suc i) div (2^24)^j mod 2^24 = (?v div 10^j) mod 10"
        by (rule physical[OF column])
      also have "... = (decimal_lsd_value ?digits div 10^j) mod 10"
        by (simp only: canonical)
      also have "... = (if j < length ?digits then ?digits!j else 0)"
        by (rule mahler_cf_decimal_lsd_digit[OF mahler_cf_pow5_word_consumer(2)])
      finally show "?row (Suc i) div (2^24)^j mod 2^24 =
        (if j < length ?digits then ?digits!j else 0)" .
    qed
    have row_fits: "decimal_lsd_value ?digits < 10^?width"
      using fits by (simp only: canonical[symmetric])
    show "?published i = ?physical i"
      unfolding mahler_cf_spatial_decode_def decode rev_rev_ident
      by (rule mahler_cf_decimal_padded_physical[OF mahler_cf_pow5_word_consumer(2) row_fits])
  qed
  show ?thesis unfolding mahler_cf_spatial_packed_stream_def
    by (simp only: rows)
qed

theorem mahler_cf_spatial_packed_first_prefix:
  fixes n width duration cap index :: nat and emitted prefix :: "nat list"
    and decision :: "nat \<Rightarrow> bool" and low_bound high_bound :: real
  defines "emitted \<equiv> take cap
      (mahler_cf_spatial_packed_stream (Poly (mahler_cf_pow5_word n)) width duration)"
    and "decision \<equiv> (\<lambda>i. mahler_cf_guard_contains_prefix low_bound high_bound
      (prefix @ take i emitted))"
    and "index \<equiv> mahler_cf_binary_decisive decision 1 (length emitted)"
  assumes dur: "duration \<le> 4" and source: "(5::nat)^n < 10^width"
    and old: "\<not> mahler_cf_guard_contains_prefix low_bound high_bound prefix"
    and nonempty: "emitted \<noteq> []" and last: "decision (length emitted)"
  shows "mahler_cf_guard_contains_prefix low_bound high_bound
      (take (length prefix + index) (prefix @ emitted))"
    "\<And>j. j < length prefix + index \<Longrightarrow>
      \<not> mahler_cf_guard_contains_prefix low_bound high_bound
        (take j (prefix @ emitted))"
    "mahler_cf_word (take index emitted) = mahler_cf_word
      (take index (take cap (concat (map (\<lambda>i.
        rev (reflected_trim_high (mahler_cf_pow5_word (n+Suc i)))) [0..<duration]))))"
proof -
  have geometric: "emitted \<equiv> take cap
      (mahler_cf_packed_stream (5^n) (10^(width+duration)) (width+duration) duration)"
    by (simp only: emitted_def mahler_cf_spatial_packed_stream_exact[OF dur source]
        mahler_cf_packed_physical_source[OF source])
  note first = mahler_cf_runtime_physical_first_prefix[
    where n=n and width=width and rows=duration and cap=cap and prefix=prefix
      and low_bound=low_bound and high_bound=high_bound,
    folded geometric, OF source old nonempty last[unfolded decision_def]]
  show "mahler_cf_guard_contains_prefix low_bound high_bound
      (take (length prefix + index) (prefix @ emitted))"
    unfolding index_def decision_def by (rule first(1))
  show "\<And>j. j < length prefix + index \<Longrightarrow>
      \<not> mahler_cf_guard_contains_prefix low_bound high_bound
        (take j (prefix @ emitted))"
    unfolding index_def decision_def by (rule first(2))
  show "mahler_cf_word (take index emitted) = mahler_cf_word
      (take index (take cap (concat (map (\<lambda>i.
        rev (reflected_trim_high (mahler_cf_pow5_word (n+Suc i)))) [0..<duration]))))"
    unfolding index_def decision_def by (rule first(3))
qed

text \<open>A clipped block consumes the remaining coefficient budget. The
cylinder can continue only after an emitted block without a clipped row.\<close>

lemma mahler_cf_spatial_clip_exhausts:
  fixes prior budget :: nat and rows :: "nat list"
  assumes "prior \<le> budget" "budget-prior < length rows"
  shows "prior + length (take (budget-prior) rows) = budget"
  using assms by simp

theorem mahler_cf_spatial_prefix_continuant:
  fixes n width duration cap cut :: nat
  assumes dur: "duration \<le> 4" and source: "(5::nat)^n < 10^width"
  shows "mahler_cf_prefix (take cut (take cap
        (mahler_cf_spatial_packed_stream (Poly (mahler_cf_pow5_word n)) width duration))) =
    mahler_cf_matrix_coordinates (mahler_cf_word (take cut (take cap
      (concat (map (\<lambda>i. rev (reflected_trim_high (mahler_cf_pow5_word (n+Suc i))))
        [0..<duration])))))"
  by (simp only: mahler_cf_spatial_packed_stream_exact[OF dur source]
      mahler_cf_prefix_is_ordered_continuant)

text \<open>The old prefix is ruled out by a stalled compiled guard. A later
admitted continuation fixes the guard, and the selected continuant is the
least inside prefix of the physical rows that satisfies its bounds.\<close>

theorem mahler_cf_spatial_compiled_first_prefix:
  fixes n width duration cap :: nat and prefix :: "nat list"
    and pre post :: "mahler_cf_guard_batch list"
    and before finished :: mahler_cf_compiled_guard and F :: "real \<Rightarrow> real"
    and emitted :: "nat list" and decision :: "nat \<Rightarrow> bool" and index :: nat
  defines "before \<equiv> mahler_cf_guard_compile pre"
    and "finished \<equiv> mahler_cf_guard_compile (pre @ post)"
    and "F \<equiv> (\<lambda>x. (cf_gain before*x-cf_innovation before)/cf_modulus before)"
    and "emitted \<equiv> take cap
      (mahler_cf_spatial_packed_stream (Poly (mahler_cf_pow5_word n)) width duration)"
    and "decision \<equiv> (\<lambda>i. mahler_cf_guard_contains_prefix
      (cf_lower finished) (cf_upper finished) (prefix @ take i emitted))"
    and "index \<equiv> mahler_cf_binary_decisive decision 1 (length emitted)"
  assumes dur: "duration \<le> 4" and source: "(5::nat)^n < 10^width"
    and prefix: "mahler_cf_prefix prefix = (q,r,p,s)"
    and stall: "\<not> (0 \<le> F (mahler_cf_low q r p s) \<and>
      F (mahler_cf_high q r p s) \<le> 1/2 \<and>
      (F (mahler_cf_high q r p s) \<le> 1/3 \<or>
       1/3 \<le> F (mahler_cf_low q r p s)))"
    and later: "cf_ticks before < cf_ticks finished"
    and nonempty: "emitted \<noteq> []" and contains: "decision (length emitted)"
  shows "mahler_cf_guard_contains_prefix (cf_lower finished) (cf_upper finished)
      (take (length prefix+index) (prefix @ emitted))"
    "\<And>j. j < length prefix+index \<Longrightarrow>
      \<not> mahler_cf_guard_contains_prefix (cf_lower finished) (cf_upper finished)
        (take j (prefix @ emitted))"
proof -
  have added: "concat (map mahler_cf_batch_word post) \<noteq> []"
    using later unfolding before_def finished_def by (rule mahler_cf_compiled_later_ticks)
  have old: "\<not> mahler_cf_guard_contains_prefix (cf_lower finished) (cf_upper finished) prefix"
    unfolding finished_def
    by (rule mahler_cf_compiled_stall_not_guarded[
        where pre=pre and post=post, OF prefix stall[unfolded F_def before_def] added])
  note least = mahler_cf_spatial_packed_first_prefix[
    where n=n and width=width and duration=duration and cap=cap and prefix=prefix
      and low_bound="cf_lower finished" and high_bound="cf_upper finished",
    folded emitted_def, OF dur source old nonempty contains[unfolded decision_def]]
  show "mahler_cf_guard_contains_prefix (cf_lower finished) (cf_upper finished)
      (take (length prefix+index) (prefix @ emitted))"
    unfolding index_def decision_def by (rule least(1))
  fix j assume earlier: "j < length prefix+index"
  show "\<not> mahler_cf_guard_contains_prefix (cf_lower finished) (cf_upper finished)
        (take j (prefix @ emitted))"
    unfolding index_def decision_def
    by (rule least(2)[OF earlier[unfolded index_def decision_def]])
qed

ML \<open>
  val checked = @{thms mahler_cf_spatial_leaf_selected_digit
    mahler_cf_spatial_visit_exact mahler_cf_spatial_direct_leaf
    mahler_cf_spatial_packed_stream_exact
    mahler_cf_spatial_packed_first_prefix mahler_cf_spatial_clip_exhausts
    mahler_cf_spatial_prefix_continuant mahler_cf_spatial_compiled_first_prefix};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "CF spatial consumer oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "CF spatial consumer skipped proof" else ();
\<close>

end
