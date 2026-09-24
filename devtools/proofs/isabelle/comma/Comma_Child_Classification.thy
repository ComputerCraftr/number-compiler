theory Comma_Child_Classification
  imports Comma_Boundary_Quotient
begin

text \<open>These are the decade facts needed to lift the two local
tropical seam candidates to the complete literal child relation.\<close>

lemma comma_sector_decade_bounds:
  assumes sector: "comma_sector e p k"
  shows "10 ^ p \<le> k" "k < 10 ^ (Suc p)"
proof -
  have digit: "1 \<le> e" "e \<le> 9"
    using sector by (auto simp: comma_sector_def)
  have lower: "(10::nat) ^ p \<le> e * 10 ^ p"
    using digit(1) by (simp add: mult_right_mono)
  have upper: "(e + 1) * (10::nat) ^ p \<le> 10 * 10 ^ p"
    using digit(2) by (intro mult_right_mono; simp)
  have admitted_lower: "e * 10 ^ p \<le> k"
    using sector by (simp add: comma_sector_def)
  show "10 ^ p \<le> k"
    by (rule order_trans[OF lower admitted_lower])
  have admitted_upper: "k < (e + 1) * 10 ^ p"
    using sector by (simp add: comma_sector_def)
  have "k < 10 * (10::nat) ^ p"
    by (rule less_le_trans[OF admitted_upper upper])
  then show "k < 10 ^ (Suc p)"
    by (simp add: power_Suc)
qed

lemma comma_decade_exponent_unique:
  fixes k :: nat
  assumes p_lo: "10 ^ p \<le> k" and p_hi: "k < 10 ^ (Suc p)"
    and q_lo: "10 ^ q \<le> k" and q_hi: "k < 10 ^ (Suc q)"
  shows "p = q"
proof (rule ccontr)
  assume "p \<noteq> q"
  then consider "p < q" | "q < p" by linarith
  then show False
  proof cases
    case 1
    have order: "Suc p \<le> q" using 1 by simp
    have powers: "(10::nat) ^ (Suc p) \<le> 10 ^ q"
      by (rule power_increasing[OF order]) simp
    show False using p_hi q_lo powers by linarith
  next
    case 2
    have order: "Suc q \<le> p" using 2 by simp
    have powers: "(10::nat) ^ (Suc q) \<le> 10 ^ p"
      by (rule power_increasing[OF order]) simp
    show False using q_hi p_lo powers by linarith
  qed
qed

lemma comma_sector_exponent_unique:
  assumes "comma_sector e p k" "comma_sector f q k"
  shows "p = q"
  using comma_decade_exponent_unique
    [OF comma_sector_decade_bounds(1)[OF assms(1)]
        comma_sector_decade_bounds(2)[OF assms(1)]
        comma_sector_decade_bounds(1)[OF assms(2)]
        comma_sector_decade_bounds(2)[OF assms(2)]] .

lemma comma_sector_leading_unique:
  assumes first: "comma_sector e p k"
    and second: "comma_sector f p k"
  shows "e = f"
proof (rule ccontr)
  assume "e \<noteq> f"
  then consider "e < f" | "f < e" by linarith
  then show False
  proof cases
    case 1
    have order: "e + 1 \<le> f" using 1 by simp
    have scaled: "(e + 1) * 10 ^ p \<le> f * (10::nat) ^ p"
      by (rule mult_right_mono[OF order]; simp)
    show False using first second scaled
      by (auto simp: comma_sector_def; linarith)
  next
    case 2
    have order: "f + 1 \<le> e" using 2 by simp
    have scaled: "(f + 1) * 10 ^ p \<le> e * (10::nat) ^ p"
      by (rule mult_right_mono[OF order]; simp)
    show False using first second scaled
      by (auto simp: comma_sector_def; linarith)
  qed
qed

lemma comma_child_witness:
  assumes "comma_child k target"
  obtains e p where "comma_sector e p target"
    "target = k + 10 * (k mod 10) + e"
    "1 \<le> e" "e \<le> 9"
  using assms unfolding comma_child_def comma_sector_def by blast

lemma comma_below_nine_candidate_bounds:
  assumes source: "comma_sector f p k"
    and below_nine: "f < 9"
    and exponent: "2 \<le> p"
    and digit: "1 \<le> e" "e \<le> 9"
    and target: "target = k + 10 * (k mod 10) + e"
  shows "10 ^ p \<le> target"
    "target < 10 ^ (Suc p)"
    "target < (f + 2) * 10 ^ p"
proof -
  let ?scale = "(10::nat) ^ p"
  have scale: "100 \<le> ?scale"
  proof -
    have "(10::nat) ^ 2 \<le> 10 ^ p"
      by (rule power_increasing[OF exponent]) simp
    then show ?thesis by simp
  qed
  have last: "k mod 10 \<le> 9" by simp
  have increment: "10 * (k mod 10) + e \<le> 99"
    using digit last by linarith
  have source_lo: "f * ?scale \<le> k"
    and source_hi: "k < (f + 1) * ?scale"
    using source by (auto simp: comma_sector_def)
  have first: "?scale \<le> target"
    using comma_sector_decade_bounds(1)[OF source] target by linarith
  then show "10 ^ p \<le> target" .
  have nine: "(f + 1) * ?scale \<le> 9 * ?scale"
    using below_nine by (intro mult_right_mono; simp)
  have decade: "target < 10 * ?scale"
    using source_hi nine increment scale target by linarith
  then show "target < 10 ^ (Suc p)"
    by (simp add: power_Suc)
  have radial: "(f + 2) * ?scale = (f + 1) * ?scale + ?scale"
    by (simp add: algebra_simps)
  show "target < (f + 2) * 10 ^ p"
    using source_hi increment scale target radial by linarith
qed

lemma comma_below_nine_child_alternatives:
  assumes source: "comma_sector f p k"
    and below_nine: "f < 9"
    and exponent: "2 \<le> p"
    and child: "comma_child k target"
  shows "(comma_sector f p target \<and>
      target = k + 10 * (k mod 10) + f) \<or>
    (comma_sector (f + 1) p target \<and>
      target = k + 10 * (k mod 10) + f + 1)"
proof -
  obtain e q where admitted: "comma_sector e q target"
    and step_value: "target = k + 10 * (k mod 10) + e"
    and e_bounds: "1 \<le> e" "e \<le> 9"
    using comma_child_witness[OF child] by blast
  have bounds: "10 ^ p \<le> target" "target < 10 ^ (Suc p)"
    "target < (f + 2) * 10 ^ p"
    using comma_below_nine_candidate_bounds
      [OF source below_nine exponent e_bounds step_value] by auto
  have q: "q = p"
    using comma_decade_exponent_unique
      [OF bounds(1,2) comma_sector_decade_bounds(1)[OF admitted]
        comma_sector_decade_bounds(2)[OF admitted]] by simp
  have source_lo: "f * 10 ^ p \<le> target"
    using source step_value by (auto simp: comma_sector_def)
  have admitted_lo: "e * 10 ^ p \<le> target"
    and admitted_hi: "target < (e + 1) * 10 ^ p"
    using admitted q by (auto simp: comma_sector_def)
  have not_smaller: "\<not> e < f"
  proof
    assume "e < f"
    then have order: "e + 1 \<le> f" by simp
    have scaled: "(e + 1) * 10 ^ p \<le> f * (10::nat) ^ p"
      by (rule mult_right_mono[OF order]; simp)
    show False using admitted_hi source_lo scaled by linarith
  qed
  have not_larger: "\<not> f + 1 < e"
  proof
    assume "f + 1 < e"
    then have order: "f + 2 \<le> e" by simp
    have scaled: "(f + 2) * 10 ^ p \<le> e * (10::nat) ^ p"
      by (rule mult_right_mono[OF order]; simp)
    show False using admitted_lo bounds(3) scaled by linarith
  qed
  have "e = f \<or> e = f + 1"
    using not_smaller not_larger by linarith
  then show ?thesis using admitted step_value q by auto
qed

lemma comma_below_nine_next_sector_candidate:
  assumes source: "comma_sector f p k"
    and below_nine: "f < 9"
    and exponent: "2 \<le> p"
  shows "comma_sector (f + 1) p
      (k + 10 * (k mod 10) + f + 1) \<longleftrightarrow>
    comma_headroom f p k \<le> 10 * (k mod 10) + f + 1"
proof -
  let ?target = "k + 10 * (k mod 10) + f + 1"
  have f_bounds: "1 \<le> f + 1" "f + 1 \<le> 9"
    using below_nine by auto
  have upper: "?target < (f + 2) * 10 ^ p"
    using comma_below_nine_candidate_bounds
      [OF source below_nine exponent f_bounds] by simp
  have sum: "k + comma_headroom f p k = (f + 1) * 10 ^ p"
    using comma_sector_headroom[OF source] .
  have lower: "((f + 1) * 10 ^ p \<le> ?target) \<longleftrightarrow>
      comma_headroom f p k \<le> 10 * (k mod 10) + f + 1"
    using sum by arith
  show ?thesis using f_bounds upper lower
    by (simp add: comma_sector_def)
qed

lemma comma_nine_child_alternatives:
  assumes source: "comma_sector 9 p k"
    and exponent: "2 \<le> p"
    and child: "comma_child k target"
  shows "(comma_sector 9 p target \<and>
      target = k + 10 * (k mod 10) + 9) \<or>
    (comma_sector 1 (Suc p) target \<and>
      target = k + 10 * (k mod 10) + 1)"
proof -
  obtain e q where admitted: "comma_sector e q target"
    and step_value: "target = k + 10 * (k mod 10) + e"
    and e_bounds: "1 \<le> e" "e \<le> 9"
    using comma_child_witness[OF child] by blast
  let ?scale = "(10::nat) ^ p"
  have scale: "100 \<le> ?scale"
  proof -
    have "(10::nat) ^ 2 \<le> 10 ^ p"
      by (rule power_increasing[OF exponent]) simp
    then show ?thesis by simp
  qed
  have increment: "10 * (k mod 10) + e \<le> 99"
  proof -
    have "k mod 10 \<le> 9" by simp
    then show ?thesis using e_bounds by linarith
  qed
  have source_lo: "9 * ?scale \<le> k"
    and source_hi: "k < 10 * ?scale"
    using source by (auto simp: comma_sector_def)
  have target_lo: "?scale \<le> target"
    using source_lo step_value by linarith
  have target_hi: "target < 10 ^ (Suc (Suc p))"
  proof -
    have "target < 20 * ?scale"
      using source_hi increment scale step_value by linarith
    also have "... \<le> 100 * ?scale" by simp
    also have "... = 10 ^ (Suc (Suc p))"
      by (simp add: power_Suc)
    finally show ?thesis .
  qed
  have bounds_q: "10 ^ q \<le> target" "target < 10 ^ (Suc q)"
    using comma_sector_decade_bounds[OF admitted] by auto
  have q_lower: "p \<le> q"
  proof (rule ccontr)
    assume "\<not> p \<le> q"
    then have order: "Suc q \<le> p" by simp
    have powers: "(10::nat) ^ (Suc q) \<le> 10 ^ p"
      by (rule power_increasing[OF order]) simp
    show False using bounds_q(2) target_lo powers by linarith
  qed
  have q_upper: "q \<le> Suc p"
  proof (rule ccontr)
    assume "\<not> q \<le> Suc p"
    then have order: "Suc (Suc p) \<le> q" by simp
    have powers: "(10::nat) ^ (Suc (Suc p)) \<le> 10 ^ q"
      by (rule power_increasing[OF order]) simp
    show False using target_hi bounds_q(1) powers by linarith
  qed
  have cases: "q = p \<or> q = Suc p"
    using q_lower q_upper by linarith
  then show ?thesis
  proof
    assume q: "q = p"
    have target_upper: "target < (e + 1) * ?scale"
      using admitted q by (simp add: comma_sector_def)
    have "e = 9"
    proof (rule ccontr)
      assume "e \<noteq> 9"
      then have "e + 1 \<le> 9" using e_bounds by linarith
      then have "(e + 1) * ?scale \<le> 9 * ?scale"
        by (rule mult_right_mono; simp)
      then show False using target_upper source_lo step_value by linarith
    qed
    then show ?thesis using admitted step_value q by simp
  next
    assume q: "q = Suc p"
    have lower: "e * (10 * ?scale) \<le> target"
      using admitted q by (simp add: comma_sector_def power_Suc)
    have upper: "target < 2 * (10 * ?scale)"
      using source_hi increment scale step_value by linarith
    have "e = 1"
    proof (rule ccontr)
      assume "e \<noteq> 1"
      then have "2 \<le> e" using e_bounds by linarith
      then have "2 * (10 * ?scale) \<le> e * (10 * ?scale)"
        by (rule mult_right_mono; simp)
      then show False using lower upper by linarith
    qed
    then show ?thesis using admitted step_value q by simp
  qed
qed

lemma comma_nine_same_sector_candidate:
  assumes source: "comma_sector 9 p k"
  shows "comma_sector 9 p (k + 10 * (k mod 10) + 9) \<longleftrightarrow>
    10 * (k mod 10) + 9 < comma_headroom 9 p k"
  using source
  by (auto simp: comma_sector_def comma_headroom_def; linarith)

lemma comma_nine_power_crossing_candidate:
  assumes source: "comma_sector 9 p k"
    and exponent: "2 \<le> p"
  shows "comma_sector 1 (Suc p) (k + 10 * (k mod 10) + 1) \<longleftrightarrow>
    comma_headroom 9 p k \<le> 10 * (k mod 10) + 1"
proof -
  let ?target = "k + 10 * (k mod 10) + 1"
  let ?boundary = "10 * (10::nat) ^ p"
  have scale: "100 \<le> (10::nat) ^ p"
  proof -
    have "(10::nat) ^ 2 \<le> 10 ^ p"
      by (rule power_increasing[OF exponent]) simp
    then show ?thesis by simp
  qed
  have increment: "10 * (k mod 10) + 1 \<le> 91"
  proof -
    have "k mod 10 \<le> 9" by simp
    then show ?thesis by linarith
  qed
  have source_hi: "k < ?boundary"
    using source by (simp add: comma_sector_def)
  have upper: "?target < 2 * ?boundary"
    using source_hi increment scale by linarith
  have sum: "k + comma_headroom 9 p k = ?boundary"
    using comma_sector_headroom[OF source] by simp
  have lower: "(?boundary \<le> ?target) \<longleftrightarrow>
      comma_headroom 9 p k \<le> 10 * (k mod 10) + 1"
    using sum by arith
  show ?thesis using upper lower
    by (simp add: comma_sector_def power_Suc)
qed

theorem comma_below_nine_complete_children:
  assumes source: "comma_sector f p k"
    and below_nine: "f < 9"
    and exponent: "2 \<le> p"
  shows "comma_child k target \<longleftrightarrow>
    (target = k + 10 * (k mod 10) + f \<and>
      10 * (k mod 10) + f < comma_headroom f p k) \<or>
    (target = k + 10 * (k mod 10) + f + 1 \<and>
      comma_headroom f p k \<le> 10 * (k mod 10) + f + 1)"
proof -
  have same: "comma_sector f p
      (k + 10 * (k mod 10) + f) \<longleftrightarrow>
      10 * (k mod 10) + f < comma_headroom f p k"
    by (rule comma_current_sector_candidate[OF source below_nine])
  have next_sector: "comma_sector (f + 1) p
      (k + 10 * (k mod 10) + f + 1) \<longleftrightarrow>
      comma_headroom f p k \<le> 10 * (k mod 10) + f + 1"
    by (rule comma_below_nine_next_sector_candidate
      [OF source below_nine exponent])
  show ?thesis
  proof (rule iffI)
    assume edge: "comma_child k target"
    show "(target = k + 10 * (k mod 10) + f \<and>
        10 * (k mod 10) + f < comma_headroom f p k) \<or>
      (target = k + 10 * (k mod 10) + f + 1 \<and>
        comma_headroom f p k \<le> 10 * (k mod 10) + f + 1)"
      using comma_below_nine_child_alternatives
        [OF source below_nine exponent edge] same next_sector by auto
  next
    assume admitted: "(target = k + 10 * (k mod 10) + f \<and>
        10 * (k mod 10) + f < comma_headroom f p k) \<or>
      (target = k + 10 * (k mod 10) + f + 1 \<and>
        comma_headroom f p k \<le> 10 * (k mod 10) + f + 1)"
    then show "comma_child k target"
    proof
      assume branch: "target = k + 10 * (k mod 10) + f \<and>
          10 * (k mod 10) + f < comma_headroom f p k"
      have sector: "comma_sector f p target"
        using same branch by simp
      have step: "target = k + 10 * (k mod 10) + f"
        using branch by simp
      show ?thesis unfolding comma_child_def
        by (rule exI[where x=f], rule exI[where x=p],
            rule conjI[OF sector step])
    next
      assume branch: "target = k + 10 * (k mod 10) + f + 1 \<and>
          comma_headroom f p k \<le> 10 * (k mod 10) + f + 1"
      have sector: "comma_sector (f + 1) p target"
        using next_sector branch by simp
      have step: "target = k + 10 * (k mod 10) + (f + 1)"
        using branch by simp
      show ?thesis unfolding comma_child_def
        by (rule exI[where x="f + 1"], rule exI[where x=p],
            rule conjI[OF sector step])
    qed
  qed
qed

theorem comma_nine_complete_children:
  assumes source: "comma_sector 9 p k" and exponent: "2 \<le> p"
  shows "comma_child k target \<longleftrightarrow>
    (target = k + 10 * (k mod 10) + 9 \<and>
      10 * (k mod 10) + 9 < comma_headroom 9 p k) \<or>
    (target = k + 10 * (k mod 10) + 1 \<and>
      comma_headroom 9 p k \<le> 10 * (k mod 10) + 1)"
proof -
  have same: "comma_sector 9 p
      (k + 10 * (k mod 10) + 9) \<longleftrightarrow>
      10 * (k mod 10) + 9 < comma_headroom 9 p k"
    by (rule comma_nine_same_sector_candidate[OF source])
  have next_sector: "comma_sector 1 (Suc p)
      (k + 10 * (k mod 10) + 1) \<longleftrightarrow>
      comma_headroom 9 p k \<le> 10 * (k mod 10) + 1"
    by (rule comma_nine_power_crossing_candidate[OF source exponent])
  show ?thesis
  proof (rule iffI)
    assume edge: "comma_child k target"
    show "(target = k + 10 * (k mod 10) + 9 \<and>
        10 * (k mod 10) + 9 < comma_headroom 9 p k) \<or>
      (target = k + 10 * (k mod 10) + 1 \<and>
        comma_headroom 9 p k \<le> 10 * (k mod 10) + 1)"
      using comma_nine_child_alternatives[OF source exponent edge]
        same next_sector by auto
  next
    assume admitted: "(target = k + 10 * (k mod 10) + 9 \<and>
        10 * (k mod 10) + 9 < comma_headroom 9 p k) \<or>
      (target = k + 10 * (k mod 10) + 1 \<and>
        comma_headroom 9 p k \<le> 10 * (k mod 10) + 1)"
    then show "comma_child k target"
    proof
      assume branch: "target = k + 10 * (k mod 10) + 9 \<and>
          10 * (k mod 10) + 9 < comma_headroom 9 p k"
      have sector: "comma_sector 9 p target"
        using same branch by simp
      have step: "target = k + 10 * (k mod 10) + 9"
        using branch by simp
      show ?thesis unfolding comma_child_def
        by (rule exI[where x=9], rule exI[where x=p],
            rule conjI[OF sector step])
    next
      assume branch: "target = k + 10 * (k mod 10) + 1 \<and>
          comma_headroom 9 p k \<le> 10 * (k mod 10) + 1"
      have sector: "comma_sector 1 (Suc p) target"
        using next_sector branch by simp
      have step: "target = k + 10 * (k mod 10) + 1"
        using branch by simp
      show ?thesis unfolding comma_child_def
        by (rule exI[where x=1], rule exI[where x="Suc p"],
            rule conjI[OF sector step])
    qed
  qed
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_sector_decade_bounds comma_decade_exponent_unique
      comma_sector_exponent_unique comma_sector_leading_unique
      comma_child_witness comma_below_nine_candidate_bounds
      comma_below_nine_child_alternatives
      comma_below_nine_next_sector_candidate
      comma_nine_child_alternatives comma_nine_same_sector_candidate
      comma_nine_power_crossing_candidate
      comma_below_nine_complete_children comma_nine_complete_children})
    then () else error "Comma child classification proof depends on an oracle";
\<close>
end
