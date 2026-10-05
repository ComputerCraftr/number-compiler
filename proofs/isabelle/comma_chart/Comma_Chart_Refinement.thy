theory Comma_Chart_Refinement
  imports Comma_Cylinder.Comma_Finite_Transition
begin

text \<open>The finite Near chart stores headroom, not a guessed next
digit.  The chart equation determines the actual last decimal digit.\<close>

lemma comma_near_chart_digit:
  fixes k H f n :: nat
  assumes chart: "k + H = (f + 1) * 10 ^ n"
    and exponent: "0 < n"
  shows "k mod 10 = (10 - H mod 10) mod 10"
proof -
  have divisible: "((f + 1) * 10 ^ n) mod 10 = 0"
    using exponent by (cases n) simp_all
  have congruence: "(k + H) mod 10 = 0"
    using chart divisible by simp
  define x where "x = k mod 10"
  define y where "y = H mod 10"
  have x_bound: "x < 10" by (simp add: x_def)
  have y_bound: "y < 10" by (simp add: y_def)
  have remainder: "(x + y) mod 10 = 0"
    using congruence by (simp add: x_def y_def mod_add_eq)
  have small: "x + y < 20"
    by (simp add: x_def y_def)
  define q where "q = (x + y) div 10"
  have division: "x + y = q * 10"
  proof -
    have "x + y = ((x + y) div 10) * 10 + (x + y) mod 10"
      by (simp add: div_mult_mod_eq)
    then show ?thesis using remainder by (simp add: q_def)
  qed
  have quotient: "q \<le> 1"
    using division small by linarith
  have qcases: "q = 0 \<or> q = 1"
    using quotient by auto
  have cases: "x + y = 0 \<or> x + y = 10"
    using division qcases by auto
  have digit: "x = (10 - y) mod 10"
  proof (cases "y = 0")
    case True
    then have "x = 0" using cases x_bound by arith
    then show ?thesis using True by simp
  next
    case False
    then have sum: "x + y = 10" using cases by linarith
    have "x = 10 - y" using sum by linarith
    then show ?thesis using False y_bound by simp
  qed
  show ?thesis using digit by (simp add: x_def y_def)
qed

lemma comma_entry_chart_checked_sector:
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and offset: "offset \<le> 98"
  shows "comma_sector f (p + delta)
    (comma_chart_value p (Comma_Entry f delta offset))"
proof -
  have scale: "100000 \<le> (10::nat) ^ (p + delta)"
  proof -
    have "(10::nat) ^ 5 \<le> 10 ^ (p + delta)"
      by (rule power_increasing) (use exponent in auto)
    then show ?thesis by simp
  qed
  show ?thesis using f offset scale
    by (auto simp: comma_sector_def comma_chart_value_def; arith)
qed

lemma comma_near_chart_checked_sector:
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and headroom: "1 \<le> H" "H \<le> 540"
  shows "comma_sector f (p + delta)
    (comma_chart_value p (Comma_Near f delta H))"
proof -
  let ?scale = "(10::nat) ^ (p + delta)"
  have scale: "540 \<le> ?scale"
  proof -
    have "(10::nat) ^ 5 \<le> ?scale"
      by (rule power_increasing) (use exponent in auto)
    then show ?thesis by simp
  qed
  have product: "(f + 1) * ?scale = f * ?scale + ?scale"
    by (simp add: algebra_simps)
  have bound: "H \<le> (f + 1) * ?scale"
    using scale headroom product by arith
  have lower: "f * ?scale \<le> (f + 1) * ?scale - H"
    using scale headroom product by arith
  have upper: "(f + 1) * ?scale - H < (f + 1) * ?scale"
    using headroom bound by arith
  show ?thesis using f lower upper
    by (simp add: comma_sector_def comma_chart_value_def)
qed

lemma comma_near_chart_headroom:
  assumes sector: "comma_sector f n k"
    and chart: "k = comma_chart_value p (Comma_Near f delta H)"
    and exponent: "n = p + delta"
  shows "comma_headroom f n k = H"
proof -
  have upper: "k + comma_headroom f n k = (f + 1) * 10 ^ n"
    using comma_sector_headroom[OF sector] .
  have fpositive: "0 < f"
    using sector by (simp add: comma_sector_def)
  have product_positive: "0 < f * (10::nat) ^ n"
    using fpositive by simp
  have chart_lower: "f * (10::nat) ^ n \<le> k"
    using sector by (simp add: comma_sector_def)
  have positive: "0 < k"
    by (rule less_le_trans[OF product_positive chart_lower])
  have bound: "H \<le> (f + 1) * 10 ^ n"
    using chart positive exponent
    by (auto simp: comma_chart_value_def; arith)
  have chart_sum: "k + H = (f + 1) * 10 ^ n"
    using chart bound exponent by (simp add: comma_chart_value_def)
  show ?thesis using upper chart_sum by simp
qed

lemma comma_entry_control_formula:
  "comma_finite_step r (Comma_Entry f delta entry_offset) =
    (if f < 1 \<or> 9 < f \<or> 98 < entry_offset \<or>
        comma_finite_period f (entry_offset mod 10) = 0
     then Comma_Invalid
     else Comma_Next (Comma_Near f delta
       (comma_finite_headroom f r delta entry_offset)))"
  by (simp add: comma_finite_step_def Let_def)

lemma comma_near_control_formula:
  "comma_finite_step residue (Comma_Near f delta H) =
    (if f < 1 \<or> 9 < f \<or> H = 0 \<or> 540 < H then Comma_Invalid
     else let d = (10 - H mod 10) mod 10 in
       if f < 9 then
         let low = 10 * d + f in
           if H > low + 1 then
             Comma_Next (Comma_Near f delta (H - low))
           else if H = low + 1 then Comma_Fork (f + 1) delta
           else Comma_Next
             (Comma_Entry (f + 1) delta (low + 1 - H))
       else let same = 10 * d + 9; cross = 10 * d + 1 in
         if H > same then Comma_Next (Comma_Near 9 delta (H - same))
         else if H \<le> cross then
           Comma_Next (Comma_Entry 1 (Suc delta) (cross - H))
         else Comma_Landmine delta)"
  by (simp add: comma_finite_step_def comma_weighted_step_def Let_def)

lemma comma_near_success_admissible:
  assumes "comma_finite_step residue (Comma_Near f delta H) \<noteq>
    Comma_Invalid"
  shows "1 \<le> f" "f \<le> 9" "0 < H" "H \<le> 540"
  using assms by (auto simp: comma_near_control_formula split: if_splits)

lemma comma_near_chart_next_below_nine:
  fixes n p delta f H k :: nat
  assumes sector: "comma_sector f n k" and exponent: "2 \<le> n"
    and n: "n = p + delta"
    and chart: "k = comma_chart_value p (Comma_Near f delta H)"
    and below: "f < 9"
    and step: "comma_finite_step (p mod 924) (Comma_Near f delta H) =
      Comma_Next next"
  shows "comma_large_children f n k = [comma_chart_value p next]"
    "comma_child k (comma_chart_value p next)"
    "comma_finite_next_weight p (Comma_Near f delta H) = 1"
proof -
  let ?d = "k mod 10"
  let ?low = "10 * ?d + f"
  have head: "comma_headroom f n k = H"
    using comma_near_chart_headroom[OF sector chart n] .
  have sum: "k + H = (f + 1) * 10 ^ n"
    using comma_sector_headroom[OF sector] head by simp
  have digit: "?d = (10 - H mod 10) mod 10"
    using comma_near_chart_digit[OF sum] exponent by simp
  have f: "1 \<le> f" using sector by (simp add: comma_sector_def)
  have allowed: "0 < H" "H \<le> 540"
    using comma_near_success_admissible[of "p mod 924" f delta H]
      step by auto
  have split: "H > ?low + 1 \<or> H \<le> ?low"
    using step below f digit allowed
    by (auto simp: comma_near_control_formula Let_def split: if_splits)
  show children: "comma_large_children f n k = [comma_chart_value p next]"
  proof (cases "H > ?low + 1")
    case True
    have next_eq: "next = Comma_Near f delta (H - ?low)"
      using step below f digit True allowed
      by (simp add: comma_near_control_formula Let_def)
    have value_eq: "comma_chart_value p next = k + ?low"
      using sum True n by (simp add: next_eq comma_chart_value_def; arith)
    show ?thesis using head below True value_eq
      by (simp add: comma_large_children_def Let_def)
  next
    case False
    have short: "H \<le> ?low" using split False by simp
    have next_eq: "next = Comma_Entry (f + 1) delta (?low + 1 - H)"
      using step below f digit False short allowed
      by (simp add: comma_near_control_formula Let_def)
    have value_eq: "comma_chart_value p next = k + ?low + 1"
      using sum short n by (simp add: next_eq comma_chart_value_def; arith)
    show ?thesis using head below False short value_eq
      by (simp add: comma_large_children_def Let_def)
  qed
  show "comma_child k (comma_chart_value p next)"
    using comma_large_children_complete
      [OF sector exponent, of "comma_chart_value p next"] children
    by simp
  show "comma_finite_next_weight p (Comma_Near f delta H) = 1"
    using step by (rule comma_finite_near_next_weight)
qed

lemma comma_near_chart_next_nine:
  fixes n p delta H k :: nat
  assumes sector: "comma_sector 9 n k" and exponent: "2 \<le> n"
    and n: "n = p + delta"
    and chart: "k = comma_chart_value p (Comma_Near 9 delta H)"
    and step: "comma_finite_step (p mod 924) (Comma_Near 9 delta H) =
      Comma_Next next"
  shows "comma_large_children 9 n k = [comma_chart_value p next]"
    "comma_child k (comma_chart_value p next)"
    "comma_finite_next_weight p (Comma_Near 9 delta H) = 1"
proof -
  let ?d = "k mod 10"
  let ?same = "10 * ?d + 9"
  let ?cross = "10 * ?d + 1"
  have head: "comma_headroom 9 n k = H"
    using comma_near_chart_headroom[OF sector chart n] .
  have sum: "k + H = (9 + 1) * 10 ^ n"
    using comma_sector_headroom[OF sector] head by simp
  have digit: "?d = (10 - H mod 10) mod 10"
    using comma_near_chart_digit[OF sum] exponent by simp
  have allowed: "0 < H" "H \<le> 540"
    using comma_near_success_admissible[of "p mod 924" 9 delta H]
      step by auto
  have split: "H > ?same \<or> H \<le> ?cross"
    using step digit allowed
    by (auto simp: comma_near_control_formula Let_def split: if_splits)
  show children: "comma_large_children 9 n k = [comma_chart_value p next]"
  proof (cases "H > ?same")
    case True
    have next_eq: "next = Comma_Near 9 delta (H - ?same)"
      using step digit True allowed
      by (simp add: comma_near_control_formula Let_def)
    have value_eq: "comma_chart_value p next = k + ?same"
      using sum True n by (simp add: next_eq comma_chart_value_def; arith)
    show ?thesis using head True value_eq
      by (simp add: comma_large_children_def Let_def)
  next
    case False
    have short: "H \<le> ?cross" using split False by simp
    have next_eq: "next = Comma_Entry 1 (Suc delta) (?cross - H)"
      using step digit False short allowed
      by (simp add: comma_near_control_formula Let_def)
    have value_eq: "comma_chart_value p next = k + ?cross"
      using sum short n
      by (simp add: next_eq comma_chart_value_def power_Suc; arith)
    show ?thesis using head False short value_eq
      by (simp add: comma_large_children_def Let_def)
  qed
  show "comma_child k (comma_chart_value p next)"
    using comma_large_children_complete
      [OF sector exponent, of "comma_chart_value p next"] children
    by simp
  show "comma_finite_next_weight p (Comma_Near 9 delta H) = 1"
    using step by (rule comma_finite_near_next_weight)
qed

lemma comma_near_chart_next_literal:
  fixes f p delta H k :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and headroom: "1 \<le> H" "H \<le> 540"
    and step: "comma_finite_step (p mod 924) (Comma_Near f delta H) =
      Comma_Next next"
  defines "k \<equiv> comma_chart_value p (Comma_Near f delta H)"
  shows "comma_literal_path 1 k (comma_chart_value p next)"
    "comma_finite_next_weight p (Comma_Near f delta H) = 1"
    "comma_large_children f (p + delta) k =
      [comma_chart_value p next]"
proof -
  have sector: "comma_sector f (p + delta) k"
    using comma_near_chart_checked_sector[OF f exponent headroom,
      of delta] by (simp add: k_def)
  have large: "2 \<le> p + delta" using exponent by simp
  have chart: "k = comma_chart_value p (Comma_Near f delta H)"
    by (simp add: k_def)
  have parts_conj: "comma_large_children f (p + delta) k =
        [comma_chart_value p next] \<and>
      comma_child k (comma_chart_value p next) \<and>
      comma_finite_next_weight p (Comma_Near f delta H) = 1"
  proof (cases "f < 9")
    case True
    have same_extent: "p + delta = p + delta" by simp
    note below_parts = comma_near_chart_next_below_nine
      [OF sector large same_extent chart True step]
    show ?thesis using below_parts by blast
  next
    case False
    have nine: "f = 9" using f False by arith
    have sector9: "comma_sector 9 (p + delta) k"
      using sector nine by simp
    have chart9: "k = comma_chart_value p (Comma_Near 9 delta H)"
      using chart nine by simp
    have step9: "comma_finite_step (p mod 924)
        (Comma_Near 9 delta H) = Comma_Next next"
      using step nine by simp
    have same_extent: "p + delta = p + delta" by simp
    note nine_parts = comma_near_chart_next_nine
      [OF sector9 large same_extent chart9 step9]
    show ?thesis using nine_parts nine by simp
  qed
  have parts: "comma_large_children f (p + delta) k =
        [comma_chart_value p next]"
      "comma_child k (comma_chart_value p next)"
      "comma_finite_next_weight p (Comma_Near f delta H) = 1"
    using parts_conj by auto
  show "comma_literal_path 1 k (comma_chart_value p next)"
    using parts(2) by (auto intro: comma_literal_path.intros)
  show "comma_finite_next_weight p (Comma_Near f delta H) = 1"
    by (rule parts(3))
  show "comma_large_children f (p + delta) k =
      [comma_chart_value p next]"
    by (rule parts(1))
qed

lemma comma_near_chart_fork:
  assumes sector: "comma_sector f n k" and exponent: "2 \<le> n"
    and n: "n = p + delta"
    and chart: "k = comma_chart_value p (Comma_Near f delta H)"
    and step: "comma_finite_step (p mod 924) (Comma_Near f delta H) =
      Comma_Fork a delta"
  shows "a = f + 1" "f < 9"
    "comma_large_children f n k =
      [comma_near_boundary a n, comma_zero_boundary a n]"
proof -
  have head: "comma_headroom f n k = H"
    using comma_near_chart_headroom[OF sector chart n] .
  have sum: "k + H = (f + 1) * 10 ^ n"
    using comma_sector_headroom[OF sector] head by simp
  have digit: "k mod 10 = (10 - H mod 10) mod 10"
    using comma_near_chart_digit[OF sum] exponent by simp
  have f: "1 \<le> f" "f \<le> 9"
    using sector by (auto simp: comma_sector_def)
  have allowed: "0 < H" "H \<le> 540"
    using comma_near_success_admissible[of "p mod 924" f delta H]
      step by auto
  have below: "f < 9"
  proof (rule ccontr)
    assume "\<not> f < 9"
    then have nine: "f = 9" using f by arith
    show False using step allowed nine
      by (auto simp: comma_near_control_formula Let_def
        split: if_splits)
  qed
  have a: "a = f + 1"
    and threshold: "H = 10 * (k mod 10) + f + 1"
    using step digit f allowed below
    by (auto simp: comma_near_control_formula Let_def
      split: if_splits)
  have two: "length (comma_large_children f n k) = 2"
    using below threshold head
    by (simp add: comma_large_children_def Let_def)
  show "a = f + 1" by (rule a)
  show "f < 9" by (rule below)
  show "comma_large_children f n k =
      [comma_near_boundary a n, comma_zero_boundary a n]"
    using comma_large_children_fork[OF sector exponent two] a by simp
qed

lemma comma_near_chart_landmine:
  assumes sector: "comma_sector f n k" and exponent: "2 \<le> n"
    and n: "n = p + delta"
    and chart: "k = comma_chart_value p (Comma_Near f delta H)"
    and step: "comma_finite_step (p mod 924) (Comma_Near f delta H) =
      Comma_Landmine delta"
  shows "comma_large_children f n k = []"
    "\<nexists>target. comma_child k target"
proof -
  have head: "comma_headroom f n k = H"
    using comma_near_chart_headroom[OF sector chart n] .
  have sum: "k + H = (f + 1) * 10 ^ n"
    using comma_sector_headroom[OF sector] head by simp
  have digit: "k mod 10 = (10 - H mod 10) mod 10"
    using comma_near_chart_digit[OF sum] exponent by simp
  have allowed: "0 < H" "H \<le> 540"
    using comma_near_success_admissible[of "p mod 924" f delta H]
      step by auto
  have f: "f = 9"
  proof (rule ccontr)
    assume "f \<noteq> 9"
    then have below: "f < 9"
      using comma_near_success_admissible[of "p mod 924" f delta H]
        step by auto
    show False using step allowed below
      by (auto simp: comma_near_control_formula Let_def
        split: if_splits)
  qed
  have low: "10 * (k mod 10) + 1 < H"
    and high: "H \<le> 10 * (k mod 10) + 9"
    using step digit allowed f
    by (auto simp: comma_near_control_formula Let_def split: if_splits)
  show empty: "comma_large_children f n k = []"
    using f low high head by (simp add: comma_large_children_def Let_def)
  show "\<nexists>target. comma_child k target"
  proof
    assume "\<exists>target. comma_child k target"
    then obtain target where child: "comma_child k target" by blast
    have "target \<in> set (comma_large_children f n k)"
      using comma_large_children_complete[OF sector exponent, of target]
        child by simp
    then show False using empty by simp
  qed
qed

lemma comma_entry_chart_digit:
  assumes exponent: "0 < p"
  shows "comma_chart_value p (Comma_Entry f delta offset) mod 10 =
    offset mod 10"
proof -
  have positive: "0 < p + delta" using exponent by simp
  have divisible: "10 dvd (10::nat) ^ (p + delta)"
    using positive by (cases "p + delta") simp_all
  have radial: "10 dvd f * (10::nat) ^ (p + delta)"
    using divisible by simp
  have radial_mod: "(f * (10::nat) ^ (p + delta)) mod 10 = 0"
    using radial by (simp add: dvd_eq_mod_eq_0)
  have digit: "(f * 10 ^ (p + delta) + offset) mod 10 =
      offset mod 10"
  proof -
    have "(f * 10 ^ (p + delta) + offset) mod 10 =
        ((f * 10 ^ (p + delta)) mod 10 + offset mod 10) mod 10"
      by (simp add: mod_add_eq)
    then show ?thesis using radial_mod by simp
  qed
  show ?thesis using digit by (simp add: comma_chart_value_def)
qed

lemma comma_finite_period_guard_bound:
  assumes f: "1 \<le> f" "f \<le> 9" and digit: "d < 10"
  shows "comma_finite_period f d + comma_finite_guard_extra f \<le> 540"
proof -
  have two: "d mod 2 \<le> 1" by simp
  have five: "d mod 5 \<le> 4" by simp
  have one: "comma_finite_period 1 d +
      comma_finite_guard_extra 1 \<le> 540"
    by (simp add: comma_finite_period_def
      comma_finite_guard_extra_def Let_def gcd_nat.simps)
  have two_sector: "comma_finite_period 2 d +
      comma_finite_guard_extra 2 \<le> 540"
    using two by (simp add: comma_finite_period_def
      comma_finite_guard_extra_def Let_def gcd_nat.simps; arith)
  have three: "comma_finite_period 3 d +
      comma_finite_guard_extra 3 \<le> 540"
    by (simp add: comma_finite_period_def
      comma_finite_guard_extra_def Let_def gcd_nat.simps)
  have four: "comma_finite_period 4 d +
      comma_finite_guard_extra 4 \<le> 540"
    using two by (simp add: comma_finite_period_def
      comma_finite_guard_extra_def Let_def gcd_nat.simps; arith)
  have five_sector: "comma_finite_period 5 d +
      comma_finite_guard_extra 5 \<le> 540"
    using five by (simp add: comma_finite_period_def
      comma_finite_guard_extra_def Let_def gcd_nat.simps; arith)
  have six: "comma_finite_period 6 d +
      comma_finite_guard_extra 6 \<le> 540"
    using two by (simp add: comma_finite_period_def
      comma_finite_guard_extra_def Let_def gcd_nat.simps; arith)
  have seven: "comma_finite_period 7 d +
      comma_finite_guard_extra 7 \<le> 540"
    by (simp add: comma_finite_period_def
      comma_finite_guard_extra_def Let_def gcd_nat.simps)
  have eight: "comma_finite_period 8 d +
      comma_finite_guard_extra 8 \<le> 540"
    using two by (simp add: comma_finite_period_def
      comma_finite_guard_extra_def Let_def gcd_nat.simps; arith)
  have nine: "comma_finite_period 9 d +
      comma_finite_guard_extra 9 \<le> 540"
    by (simp add: comma_finite_period_def
      comma_finite_guard_extra_def Let_def gcd_nat.simps)
  have cases: "f = 1 \<or> f = 2 \<or> f = 3 \<or> f = 4 \<or>
      f = 5 \<or> f = 6 \<or> f = 7 \<or> f = 8 \<or> f = 9"
    using f by arith
  show ?thesis
    using cases one two_sector three four five_sector six seven eight nine
    by blast
qed

lemma comma_finite_entry_headroom_admitted:
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and offset: "offset \<le> 98"
  shows "1 \<le> comma_finite_headroom f (p mod 924) delta offset"
    "comma_finite_headroom f (p mod 924) delta offset \<le> 540"
proof -
  let ?P = "comma_finite_period f (offset mod 10)"
  let ?e = "comma_finite_guard_extra f"
  let ?H = "10 ^ (p + delta) - offset"
  let ?h = "comma_finite_headroom f (p mod 924) delta offset"
  have fpositive: "0 < f" using f by simp
  have length: "0 < comma_cycle_length f"
    using comma_cycle_length_admitted[OF f] by simp
  have positive: "0 < ?P"
    using comma_finite_period_refines[OF f, of "offset mod 10"]
      comma_period_displacement_admitted
        [OF fpositive length, of "offset mod 10"]
    by simp
  have reduced: "?h = 1 + ?e + (?H - (1 + ?e)) mod ?P"
    using comma_finite_headroom_reduced[OF f exponent offset, of delta]
    by (simp add: Let_def)
  have bound: "?P + ?e \<le> 540"
    using comma_finite_period_guard_bound[OF f, of "offset mod 10"]
    by simp
  have remainder: "(?H - (1 + ?e)) mod ?P < ?P"
    using positive by simp
  show "1 \<le> ?h" using reduced by simp
  show "?h \<le> 540" using reduced bound remainder by arith
qed

theorem comma_entry_chart_exact_literal_path:
  fixes f p delta offset k H P h L c :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and offset: "offset \<le> 98"
  defines "k \<equiv> comma_chart_value p (Comma_Entry f delta offset)"
    and "H \<equiv> 10 ^ (p + delta) - offset"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "L \<equiv> comma_cycle_length f"
    and "c \<equiv> (H - h) div P"
  shows "comma_finite_step (p mod 924) (Comma_Entry f delta offset) =
      Comma_Next (Comma_Near f delta h)"
    "comma_finite_next_weight p (Comma_Entry f delta offset) = c * L"
    "comma_chart_value p (Comma_Near f delta h) = k + c * P"
    "comma_literal_path (c * L) k
      (comma_chart_value p (Comma_Near f delta h))"
    "\<forall>j<c * L.
      comma_child (comma_fixed_iter f j k)
        (comma_fixed_iter f (Suc j) k) \<and>
      (\<forall>v. comma_child (comma_fixed_iter f j k) v \<longrightarrow>
        v = comma_fixed_iter f (Suc j) k)"
    "\<forall>j<c * L. \<exists>!target.
      comma_child (comma_fixed_iter f j k) target"
    "comma_weighted_step (p mod 924) (Comma_Entry f delta offset) =
      Comma_WNext (Comma_Near f delta h)
        (Comma_Chart_Weight L delta
          (- int (L * (offset + h))) P)"
    "P dvd H - h"
    "0 \<le> int (L * 10 ^ (p + delta)) - int (L * (offset + h))"
    "int P dvd
      int (L * 10 ^ (p + delta)) - int (L * (offset + h))"
proof -
  let ?e = "comma_finite_guard_extra f"
  let ?G = "comma_phase_max_guard f (offset mod 10) L"
  have sector: "comma_sector f (p + delta) k"
    using comma_entry_chart_checked_sector[OF f exponent offset,
      of delta] by (simp add: k_def)
  have length: "0 < L" and closes: "10 dvd L * f"
    using comma_cycle_length_admitted[OF f] by (simp_all add: L_def)
  have fpositive: "0 < f" using f by simp
  have positive: "0 < P"
    using comma_period_displacement_admitted[OF fpositive length,
      of "offset mod 10"]
      comma_finite_period_refines[OF f, of "offset mod 10"]
    by (simp add: P_def L_def)
  have digit: "k mod 10 = offset mod 10"
    using comma_entry_chart_digit[of p f delta offset] exponent
    by (simp add: k_def)
  have headroom: "comma_headroom f (p + delta) k = H"
    using exponent offset
    by (simp add: H_def k_def comma_chart_value_def
      comma_headroom_def algebra_simps)
  have refines: "h = 1 + ?e + (H - (1 + ?e)) mod P"
    using comma_finite_headroom_reduced[OF f exponent offset,
      of delta]
    by (simp add: h_def H_def P_def Let_def)
  have scale: "100000 \<le> (10::nat) ^ (p + delta)"
  proof -
    have "(10::nat) ^ 5 \<le> 10 ^ (p + delta)"
      by (rule power_increasing) (use exponent in auto)
    then show ?thesis by simp
  qed
  have H_two: "2 \<le> H"
    using scale offset by (simp add: H_def; arith)
  have e_bound: "?e \<le> 1"
    by (simp add: comma_finite_guard_extra_def)
  have lower: "1 + ?e \<le> H"
    using H_two e_bound by arith
  have cycles: "c = comma_safe_cycle_count H (P + ?e) P (H + 1)"
    using comma_reduced_headroom_weight[OF positive lower] refines
    by (simp add: c_def)
  have guard: "?G = P + ?e"
    using comma_finite_entry_guard_refines[OF f, of "offset mod 10"]
    by (simp add: P_def L_def)
  have displacement: "comma_period_displacement f (k mod 10) L = P"
    using comma_finite_period_refines[OF f, of "offset mod 10"]
      digit by (simp add: P_def L_def)
  have guard_source:
      "comma_phase_max_guard f (k mod 10) L = P + ?e"
    using guard digit by simp
  have displacement_positive:
      "0 < comma_period_displacement f (k mod 10) L"
    using displacement positive by simp
  let ?x = "H - (1 + ?e)"
  have Hform: "H = 1 + ?e + ?x"
    using lower by arith
  have hform: "h = 1 + ?e + ?x mod P"
    using refines by simp
  have euclidean: "?x = (?x div P) * P + ?x mod P"
    by (simp add: div_mult_mod_eq)
  have Hq: "H = h + (?x div P) * P"
    using Hform hform euclidean by (simp add: algebra_simps)
  have difference: "H - h = (?x div P) * P"
    using Hq by arith
  have c_eq: "c = ?x div P"
    using difference positive by (simp add: c_def)
  have decomposition: "H = h + c * P"
    using Hq c_eq by simp
  have offset_bound: "offset \<le> 10 ^ (p + delta)"
    using offset scale by arith
  have full: "10 ^ (p + delta) = offset + h + c * P"
    using decomposition offset_bound by (simp add: H_def; arith)
  have numerator: "int (L * 10 ^ (p + delta)) -
      int (L * (offset + h)) = int (L * c * P)"
    using full by (simp add: algebra_simps)
  have weighted_step: "comma_weighted_step (p mod 924)
      (Comma_Entry f delta offset) =
      Comma_WNext (Comma_Near f delta h)
        (Comma_Chart_Weight L delta
          (- int (L * (offset + h))) P)"
    using f offset positive by (simp add: comma_weighted_step_def
      P_def h_def L_def Let_def)
  have descriptor_bound: "offset + h \<le> 10 ^ (p + delta)"
    using full by arith
  have descriptor_displacement:
      "10 ^ (p + delta) - offset - h = c * P"
    using full by arith
  have descriptor_weight: "comma_chart_weight_value p
      (Comma_Chart_Weight L delta
        (- int (L * (offset + h))) P) = c * L"
    using comma_chart_weight_entry_exact
      [OF positive descriptor_bound descriptor_displacement] by simp
  have chart_sum: "k + H = (f + 1) * 10 ^ (p + delta)"
    using comma_sector_headroom[OF sector] headroom by simp
  have endpoint: "comma_chart_value p (Comma_Near f delta h) =
      k + c * P"
    using decomposition chart_sum
    by (simp add: comma_chart_value_def; arith)
  show step: "comma_finite_step (p mod 924)
      (Comma_Entry f delta offset) =
      Comma_Next (Comma_Near f delta h)"
    using weighted_step by (simp add: comma_finite_step_def)
  show weight: "comma_finite_next_weight p
      (Comma_Entry f delta offset) = c * L"
    using weighted_step descriptor_weight
    by (simp add: comma_finite_next_weight_def)
  show "comma_chart_value p (Comma_Near f delta h) = k + c * P"
    by (rule endpoint)
  have path: "comma_literal_path (c * L) k (k + c * P)"
    using comma_safe_cycles_literal_path(1)
      [OF sector _ closes length displacement_positive,
        where target="H + 1"]
      cycles guard_source displacement headroom exponent
    by simp
  show "comma_literal_path (c * L) k
      (comma_chart_value p (Comma_Near f delta h))"
    using path endpoint by simp
  have unique: "\<forall>j<c * L.
      comma_child (comma_fixed_iter f j k)
        (comma_fixed_iter f (Suc j) k) \<and>
      (\<forall>v. comma_child (comma_fixed_iter f j k) v \<longrightarrow>
        v = comma_fixed_iter f (Suc j) k)"
    using comma_safe_complete_cycles_refine(3)
      [OF sector _ closes length displacement_positive,
        where target="H + 1"]
      cycles guard_source displacement headroom exponent
    by simp
  show "\<forall>j<c * L.
      comma_child (comma_fixed_iter f j k)
        (comma_fixed_iter f (Suc j) k) \<and>
      (\<forall>v. comma_child (comma_fixed_iter f j k) v \<longrightarrow>
        v = comma_fixed_iter f (Suc j) k)"
    by (rule unique)
  show "\<forall>j<c * L. \<exists>!target.
      comma_child (comma_fixed_iter f j k) target"
    using unique by blast
  show "comma_weighted_step (p mod 924)
      (Comma_Entry f delta offset) =
      Comma_WNext (Comma_Near f delta h)
        (Comma_Chart_Weight L delta
          (- int (L * (offset + h))) P)"
    by (rule weighted_step)
  show "P dvd H - h"
    using difference by simp
  show "0 \<le> int (L * 10 ^ (p + delta)) -
      int (L * (offset + h))"
    using numerator by simp
  show "int P dvd
      int (L * 10 ^ (p + delta)) - int (L * (offset + h))"
    using numerator by (simp add: algebra_simps)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_near_chart_digit comma_near_chart_headroom
      comma_entry_chart_checked_sector comma_near_chart_checked_sector
      comma_near_chart_next_below_nine comma_near_chart_next_nine
      comma_near_chart_next_literal
      comma_near_control_formula comma_near_success_admissible
      comma_near_chart_fork comma_near_chart_landmine
      comma_entry_chart_digit comma_finite_period_guard_bound
      comma_finite_entry_headroom_admitted
      comma_entry_chart_exact_literal_path})
    then () else error "Comma Near-chart refinement depends on an oracle";
\<close>

end
