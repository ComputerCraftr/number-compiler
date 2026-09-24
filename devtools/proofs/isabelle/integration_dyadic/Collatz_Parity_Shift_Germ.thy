theory Collatz_Parity_Shift_Germ
  imports Collatz_Reduced_Precision
begin

text \<open>The normalized map consumes one parity symbol per step.  The
physical map is its two-phase suspension: an even symbol costs one physical
step, whereas an odd symbol has a forced intermediate even state and costs
two.  All statements below concern finite prefixes of an authenticated
source.  A cursor without its source binding or an exterior threshold does
not certify a public point observation.\<close>

definition collatz_normalized_step :: "nat \<Rightarrow> nat" where
  "collatz_normalized_step x =
    (if even x then x div 2 else (3*x+1) div 2)"

definition collatz_normalized_gain :: "bool \<Rightarrow> nat" where
  "collatz_normalized_gain branch = (if branch then 3 else 1)"

lemma normalized_step_even:
  "even x \<Longrightarrow> collatz_normalized_step x = x div 2"
  by (simp add: collatz_normalized_step_def)

lemma normalized_step_odd:
  "odd x \<Longrightarrow> 2 * collatz_normalized_step x = 3*x+1"
  by (auto simp: collatz_normalized_step_def)

lemma normalized_step_translation:
  "collatz_normalized_step (x + 2*k) =
    collatz_normalized_step x + collatz_normalized_gain (odd x)*k"
  by (cases "even x")
    (simp_all add: collatz_normalized_step_def
      collatz_normalized_gain_def algebra_simps)

interpretation collatz_normalized_source: dyadic_source_action
    collatz_normalized_step odd collatz_normalized_gain
proof
  show "\<And>x k. odd (x + 2*k) = odd x" by simp
  show "\<And>x k. collatz_normalized_step (x + 2*k) =
      collatz_normalized_step x + collatz_normalized_gain (odd x)*k"
    by (rule normalized_step_translation)
qed

definition collatz_qprefix :: "nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "collatz_qprefix width source =
    dyadic_source_word collatz_normalized_step odd source width"

lemma collatz_qprefix_length [simp]:
  "length (collatz_qprefix width source) = width"
  by (simp add: collatz_qprefix_def)

lemma collatz_qprefix_snoc:
  "collatz_qprefix (Suc width) source =
    collatz_qprefix width source @
      [odd (dyadic_source_orbit collatz_normalized_step source width)]"
proof -
  have append: "dyadic_source_word collatz_normalized_step odd source
      (width+1) =
      dyadic_source_word collatz_normalized_step odd source width @
      dyadic_source_word collatz_normalized_step odd
        (dyadic_source_orbit collatz_normalized_step source width) 1"
    by (rule dyadic_source_word_append)
  show ?thesis using append
    by (simp add: collatz_qprefix_def)
qed

lemma collatz_qprefix_shift:
  "tl (collatz_qprefix (Suc width) source) =
    collatz_qprefix width (collatz_normalized_step source)"
  by (simp add: collatz_qprefix_def)

lemma collatz_qprefix_low:
  "collatz_qprefix width (source mod 2^width) =
    collatz_qprefix width source"
  using collatz_normalized_source.source_residue_lift[of source width]
  by (simp add: collatz_qprefix_def)

lemma collatz_normalized_gain_odd [simp]:
  "odd (collatz_normalized_gain branch)"
  by (simp add: collatz_normalized_gain_def)

lemma collatz_qprefix_gain_odd:
  "odd (dyadic_gain_product collatz_normalized_gain
      (collatz_qprefix width source))"
proof -
  have every_word: "odd (dyadic_gain_product collatz_normalized_gain bits)"
    for bits :: "bool list"
    by (induction bits) (simp_all add: dyadic_gain_product_def)
  show ?thesis by (rule every_word)
qed

lemma collatz_qprefix_topbit_flip:
  "odd (dyadic_source_orbit collatz_normalized_step
      (source + 2^width) width) \<noteq>
   odd (dyadic_source_orbit collatz_normalized_step source width)"
  using collatz_normalized_source.exact_precision_source_lift
    [of source width 1] collatz_qprefix_gain_odd[of width source]
  by (simp add: collatz_qprefix_def)

lemma collatz_qprefix_topbit_prefix:
  "collatz_qprefix width (source + 2^width) =
    collatz_qprefix width source"
  using collatz_normalized_source.exact_precision_source_lift
    [of source width 1]
  by (simp add: collatz_qprefix_def)

theorem collatz_qprefix_injective_mod:
  assumes "collatz_qprefix width left = collatz_qprefix width right"
  shows "left mod 2^width = right mod 2^width"
  using assms
proof (induction width arbitrary: left right)
  case 0
  then show ?case by simp
next
  case (Suc width)
  let ?m = "(2::nat)^width"
  let ?r = "left mod ?m"
  let ?bl = "left div ?m mod 2"
  let ?br = "right div ?m mod 2"
  have prior: "collatz_qprefix width left = collatz_qprefix width right"
    using Suc.prems by (simp add: collatz_qprefix_snoc)
  have low: "left mod ?m = right mod ?m"
    by (rule Suc.IH[OF prior])
  have left_split: "left mod 2^Suc width = ?r + ?m * ?bl"
  proof -
    have "left mod (?m * 2) = ?m * ?bl + ?r"
      by (rule mod_mult2_eq)
    then show ?thesis by (simp add: power_Suc algebra_simps)
  qed
  have right_split: "right mod 2^Suc width = ?r + ?m * ?br"
  proof -
    have "right mod (?m * 2) = ?m * ?br + right mod ?m"
      by (rule mod_mult2_eq)
    with low show ?thesis by (simp add: power_Suc algebra_simps)
  qed
  have left_bit: "odd (dyadic_source_orbit collatz_normalized_step
      (left mod 2^Suc width) width) =
      odd (dyadic_source_orbit collatz_normalized_step left width)"
    using collatz_qprefix_low[of "Suc width" left]
    by (simp add: collatz_qprefix_snoc)
  have right_bit: "odd (dyadic_source_orbit collatz_normalized_step
      (right mod 2^Suc width) width) =
      odd (dyadic_source_orbit collatz_normalized_step right width)"
    using collatz_qprefix_low[of "Suc width" right]
    by (simp add: collatz_qprefix_snoc)
  have equal_bit: "odd (dyadic_source_orbit collatz_normalized_step left width) =
      odd (dyadic_source_orbit collatz_normalized_step right width)"
    using Suc.prems by (simp add: collatz_qprefix_snoc)
  have bounds: "?bl < 2" "?br < 2" by simp_all
  have "?bl = ?br"
  proof (rule ccontr)
    assume "?bl \<noteq> ?br"
    with bounds have cases:
      "(?bl = 0 \<and> ?br = 1) \<or> (?bl = 1 \<and> ?br = 0)"
      by arith
    have flip: "odd (dyadic_source_orbit collatz_normalized_step
        (?r + ?m) width) \<noteq>
        odd (dyadic_source_orbit collatz_normalized_step ?r width)"
      by (rule collatz_qprefix_topbit_flip)
    show False
      using cases flip left_bit right_bit equal_bit left_split right_split
      by auto
  qed
  with left_split right_split show ?case by simp
qed

text \<open>This is a mathematical finite inverse on source-reachable
prefixes.  Its Hilbert-choice definition is not the executable modular
inverse loop in arithmetic/fields/two_adic.py; that loop needs a separate
refinement proof before a production claim can cite it.\<close>

definition collatz_qinverse :: "nat \<Rightarrow> bool list \<Rightarrow> nat" where
  "collatz_qinverse width bits =
    (SOME residue. residue < 2^width \<and>
      collatz_qprefix width residue = bits)"

theorem collatz_qinverse_actual_source:
  "collatz_qinverse width (collatz_qprefix width source) =
    source mod 2^width"
proof -
  have witness: "source mod 2^width < 2^width \<and>
      collatz_qprefix width (source mod 2^width) =
        collatz_qprefix width source"
    by (simp add: collatz_qprefix_low)
  have exists: "\<exists>residue. residue < 2^width \<and>
      collatz_qprefix width residue = collatz_qprefix width source"
    using witness by blast
  have chosen: "collatz_qinverse width (collatz_qprefix width source) <
      2^width \<and>
      collatz_qprefix width
        (collatz_qinverse width (collatz_qprefix width source)) =
        collatz_qprefix width source"
    using someI_ex[OF exists] unfolding collatz_qinverse_def .
  have same: "collatz_qinverse width (collatz_qprefix width source)
      mod 2^width = source mod 2^width"
    using collatz_qprefix_injective_mod chosen by blast
  with chosen show ?thesis by simp
qed

lemma collatz_qinverse_zero [simp]: "collatz_qinverse 0 [] = 0"
  using collatz_qinverse_actual_source[of 0 0]
  by (simp add: collatz_qprefix_def)

theorem collatz_qprefix_bit_minimal:
  "collatz_qprefix position 0 = collatz_qprefix position (2^position)"
  "(0::nat) mod 2^Suc position \<noteq>
    (2^position) mod 2^Suc position"
  using collatz_qprefix_topbit_prefix[of position 0]
  by (simp_all add: power_Suc)

corollary collatz_qprefix_bit_minimal_explicit:
  "collatz_qprefix position 0 = collatz_qprefix position (2^position)"
  "((0::nat) div 2^position) mod 2 \<noteq>
    ((2^position) div 2^position) mod 2"
  using collatz_qprefix_bit_minimal(1) by simp_all

lemma physical_collatz_normalized_even:
  "even source \<Longrightarrow> physical_collatz source =
    collatz_normalized_step source"
  by (simp add: physical_collatz_def collatz_normalized_step_def)

lemma physical_collatz_normalized_odd:
  "odd source \<Longrightarrow> physical_collatz source =
    2 * collatz_normalized_step source"
  using normalized_step_odd[of source]
  by (simp add: physical_collatz_def)

lemma physical_collatz_pending_division:
  "odd source \<Longrightarrow>
    physical_collatz (physical_collatz source) =
      collatz_normalized_step source"
  using physical_collatz_normalized_odd[of source]
  by (simp add: physical_collatz_def)

definition collatz_shifted_q_residue ::
    "bool \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_shifted_q_residue pending bits width =
    (if width = 0 then 0
     else if pending then
       (2 * collatz_qinverse (width-1) (tl bits)) mod 2^width
     else collatz_qinverse width bits)"

theorem collatz_phase0_shifted_q_residue:
  "collatz_shifted_q_residue False
      (collatz_qprefix width source) width = source mod 2^width"
  by (cases width)
    (simp_all add: collatz_shifted_q_residue_def
      collatz_qinverse_actual_source)

theorem collatz_phase1_shifted_q_residue:
  assumes "0 < width" "odd source"
  shows "collatz_shifted_q_residue True
      (collatz_qprefix width source) width =
    physical_collatz source mod 2^width"
proof -
  obtain rest where width: "width = Suc rest"
    using assms(1) by (cases width) auto
  have shifted: "tl (collatz_qprefix width source) =
      collatz_qprefix rest (collatz_normalized_step source)"
    using collatz_qprefix_shift[of rest source]
    by (simp only: width)
  have inverse_tail:
      "collatz_qinverse rest (tl (collatz_qprefix width source)) =
        collatz_normalized_step source mod 2^rest"
    by (simp only: shifted collatz_qinverse_actual_source)
  have "collatz_shifted_q_residue True
      (collatz_qprefix width source) width =
      (2 * (collatz_normalized_step source mod 2^rest)) mod 2^width"
    using inverse_tail
    by (simp add: collatz_shifted_q_residue_def width)
  also have "... = (2 * collatz_normalized_step source) mod 2^width"
    by (simp add: width power_Suc mod_mult2_eq)
  also have "... = physical_collatz source mod 2^width"
    using physical_collatz_normalized_odd[OF assms(2)] by simp
  finally show ?thesis .
qed

lemma collatz_phase1_low_bit_forced_zero:
  "collatz_shifted_q_residue True bits 1 = 0"
  by (simp add: collatz_shifted_q_residue_def)

lemma collatz_phase1_positive_bit_minimal:
  assumes "odd source" "0 < position"
  shows "collatz_qprefix position source =
      collatz_qprefix position (source + 2^position)"
    "((2 * collatz_normalized_step source) div 2^position) mod 2 \<noteq>
      ((2 * collatz_normalized_step (source + 2^position))
        div 2^position) mod 2"
proof -
  obtain k where pos: "position = Suc k"
    using assms(2) by (cases position) auto
  show "collatz_qprefix position source =
      collatz_qprefix position (source + 2^position)"
    by (rule collatz_qprefix_topbit_prefix[symmetric])
  have shifted: "collatz_normalized_step (source + 2^position) =
      collatz_normalized_step source + 3 * 2^k"
    using normalized_step_translation[of source "2^k"] assms(1)
    by (simp add: pos power_Suc collatz_normalized_gain_def)
  have doubled: "2 * collatz_normalized_step (source + 2^position) =
      2 * collatz_normalized_step source + 3 * 2^position"
    using shifted by (simp add: pos power_Suc algebra_simps)
  have quotient: "(2 * collatz_normalized_step (source + 2^position))
      div 2^position =
      3 + (2 * collatz_normalized_step source) div 2^position"
    using doubled by simp
  have flip: "n mod 2 \<noteq> (3 + n) mod 2" for n :: nat
    by presburger
  show "((2 * collatz_normalized_step source) div 2^position) mod 2 \<noteq>
      ((2 * collatz_normalized_step (source + 2^position))
        div 2^position) mod 2"
    using quotient flip[of "(2 * collatz_normalized_step source)
      div 2^position"] by simp
qed

definition collatz_exterior_guard :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "collatz_exterior_guard position endpoint \<longleftrightarrow>
    endpoint < 2^position"

lemma collatz_q_germ_does_not_decide_exterior:
  "collatz_qprefix (Suc position) 0 =
    collatz_qprefix (Suc position) (2^Suc position)"
  "collatz_exterior_guard position 0"
  "\<not> collatz_exterior_guard position (2^Suc position)"
  using collatz_qprefix_topbit_prefix[of "Suc position" 0]
  by (simp_all add: collatz_exterior_guard_def)

lemma collatz_q_germ_positive_exterior_witness:
  assumes "0 < position"
  shows "collatz_qprefix (Suc position) 1 =
    collatz_qprefix (Suc position) (1 + 2^Suc position)"
    "collatz_exterior_guard position 1"
    "\<not> collatz_exterior_guard position (1 + 2^Suc position)"
proof -
  show "collatz_qprefix (Suc position) 1 =
      collatz_qprefix (Suc position) (1 + 2^Suc position)"
    by (rule collatz_qprefix_topbit_prefix[symmetric])
  show "collatz_exterior_guard position 1"
  proof -
    obtain k where pos: "position = Suc k"
      using assms by (cases position) auto
    have positive: "0 < (2::nat)^k" by simp
    show ?thesis
      using positive by (simp add: pos collatz_exterior_guard_def
        power_Suc; linarith)
  qed
  show "\<not> collatz_exterior_guard position (1 + 2^Suc position)"
    by (simp add: collatz_exterior_guard_def power_Suc)
qed

definition collatz_cursor_valid :: "nat \<times> bool \<Rightarrow> bool" where
  "collatz_cursor_valid cursor \<longleftrightarrow>
    (case cursor of (source,pending) \<Rightarrow> pending \<longrightarrow> odd source)"

definition collatz_cursor_value :: "nat \<times> bool \<Rightarrow> nat" where
  "collatz_cursor_value cursor =
    (case cursor of (source,pending) \<Rightarrow>
      if pending then 2 * collatz_normalized_step source else source)"

definition collatz_cursor_step :: "nat \<times> bool \<Rightarrow> nat \<times> bool" where
  "collatz_cursor_step cursor =
    (case cursor of (source,pending) \<Rightarrow>
      if pending then (collatz_normalized_step source,False)
      else if odd source then (source,True)
      else (collatz_normalized_step source,False))"

lemma collatz_cursor_valid_step:
  "collatz_cursor_valid cursor \<Longrightarrow>
    collatz_cursor_valid (collatz_cursor_step cursor)"
  by (cases cursor) (auto simp: collatz_cursor_valid_def
      collatz_cursor_step_def)

theorem collatz_cursor_physical_step:
  assumes "collatz_cursor_valid cursor"
  shows "collatz_cursor_value (collatz_cursor_step cursor) =
    physical_collatz (collatz_cursor_value cursor)"
  using assms physical_collatz_normalized_even[of "fst cursor"]
    physical_collatz_normalized_odd[of "fst cursor"]
    physical_collatz_pending_division[of "fst cursor"]
  by (cases cursor) (auto simp: collatz_cursor_valid_def
      collatz_cursor_value_def collatz_cursor_step_def)

theorem collatz_cursor_physical_run:
  assumes "collatz_cursor_valid cursor"
  shows "collatz_cursor_value ((collatz_cursor_step ^^ steps) cursor) =
    (physical_collatz ^^ steps) (collatz_cursor_value cursor)"
  using assms
proof (induction steps arbitrary: cursor)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  have valid: "collatz_cursor_valid (collatz_cursor_step cursor)"
    by (rule collatz_cursor_valid_step[OF Suc.prems])
  have "collatz_cursor_value
      ((collatz_cursor_step ^^ Suc steps) cursor) =
      collatz_cursor_value
        ((collatz_cursor_step ^^ steps) (collatz_cursor_step cursor))"
    by (simp only: funpow_Suc_right o_apply)
  also have "... = (physical_collatz ^^ steps)
      (collatz_cursor_value (collatz_cursor_step cursor))"
    using Suc.IH[OF valid] .
  also have "... = (physical_collatz ^^ Suc steps)
      (collatz_cursor_value cursor)"
    using collatz_cursor_physical_step[OF Suc.prems]
    by (simp only: funpow_Suc_right o_apply
        collatz_cursor_physical_step[OF Suc.prems])
  finally show ?case .
qed

theorem collatz_cursor_q_residue:
  assumes "collatz_cursor_valid cursor"
  shows "collatz_shifted_q_residue (snd cursor)
      (collatz_qprefix width (fst cursor)) width =
    collatz_cursor_value cursor mod 2^width"
proof (cases cursor)
  case (Pair source pending)
  show ?thesis
  proof (cases pending)
    case False
    then show ?thesis
      by (simp add: Pair collatz_cursor_value_def
          collatz_phase0_shifted_q_residue)
  next
    case True
    then have odd_source: "odd source"
      using assms by (simp add: Pair collatz_cursor_valid_def)
    show ?thesis
    proof (cases width)
      case 0
      then show ?thesis
        by (simp add: Pair collatz_shifted_q_residue_def)
    next
      case (Suc rest)
      with collatz_phase1_shifted_q_residue[OF _ odd_source]
      show ?thesis
        by (simp add: Pair True collatz_cursor_value_def
            physical_collatz_normalized_odd[OF odd_source])
    qed
  qed
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms normalized_step_even normalized_step_odd
      normalized_step_translation collatz_qprefix_length
      collatz_qprefix_snoc collatz_qprefix_shift collatz_qprefix_low
      collatz_normalized_gain_odd collatz_qprefix_gain_odd
      collatz_qprefix_topbit_flip collatz_qprefix_topbit_prefix
      collatz_qprefix_injective_mod collatz_qinverse_actual_source
      collatz_qinverse_zero collatz_qprefix_bit_minimal
      collatz_qprefix_bit_minimal_explicit
      physical_collatz_normalized_even
      physical_collatz_normalized_odd physical_collatz_pending_division
      collatz_phase0_shifted_q_residue collatz_phase1_shifted_q_residue
      collatz_phase1_low_bit_forced_zero
      collatz_phase1_positive_bit_minimal
      collatz_q_germ_positive_exterior_witness
      collatz_q_germ_does_not_decide_exterior
      collatz_cursor_valid_step collatz_cursor_physical_step
      collatz_cursor_physical_run collatz_cursor_q_residue})
    then () else error "Collatz parity germ proof depends on an oracle";
\<close>

end
