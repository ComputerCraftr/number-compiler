theory Shared_Carry_Tape
  imports Shared_Carry_Domain
begin

text \<open>Family-independent finite carry and phase actions over ordered domain
words.  Recurrence-specific thresholds and interpretation remain with each
family.\<close>

fun carry_finish :: "bool \<Rightarrow> carry_domain list \<Rightarrow> bool" where
  "carry_finish c [] = c"
| "carry_finish c (d # ds) = carry_finish (carry_apply d c) ds"

fun advance_phase :: "bool \<Rightarrow> carry_domain list \<Rightarrow> bool" where
  "advance_phase p [] = p"
| "advance_phase p (_ # ds) = advance_phase (\<not> p) ds"

lemma carry_finish_fold:
  "carry_finish c ds = fold carry_apply ds c"
  by (induction ds arbitrary: c) simp_all

lemma carry_finish_append [simp]:
  "carry_finish c (xs @ ys) = carry_finish (carry_finish c xs) ys"
  by (simp only: carry_finish_fold fold_append comp_apply)

lemma advance_phase_append [simp]:
  "advance_phase p (xs @ ys) = advance_phase (advance_phase p xs) ys"
  by (induction xs arbitrary: p) simp_all

lemma advance_phase_by_length:
  "advance_phase p xs = (if even (length xs) then p else \<not> p)"
  by (induction xs arbitrary: p) simp_all

lemma carry_finish_equal_prefix [simp]:
  "carry_finish c (replicate n Equal @ ds) = carry_finish c ds"
  by (induction n arbitrary: c) simp_all

theorem first_decisive_carry_coalesces:
  assumes "d \<noteq> Equal"
  shows "carry_finish False (replicate j Equal @ d # ds) =
    carry_finish True (replicate j Equal @ d # ds)"
  using assms by (cases d) simp_all

lemma all_equal_carry [simp]:
  "carry_finish c (replicate n Equal) = c"
  by (induction n arbitrary: c) simp_all


definition domain_prefix_carry ::
    "carry_domain list \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool" where
  "domain_prefix_carry geometry i incoming =
    carry_finish incoming (take i geometry)"

theorem domain_prefix_carry_composition:
  "domain_prefix_carry geometry (i+j) incoming =
    carry_finish (domain_prefix_carry geometry i incoming)
      (take j (drop i geometry))"
  by (simp add: domain_prefix_carry_def take_add)

theorem all_equal_prefix_preserves_incoming:
  assumes "take i geometry = replicate i Equal"
  shows "domain_prefix_carry geometry i incoming = incoming"
  using assms by (simp add: domain_prefix_carry_def)

theorem last_decisive_domain_determines_prefix_carry:
  assumes prefix: "take i geometry = before @ d # replicate tail Equal"
      and decisive: "d \<noteq> Equal"
  shows "domain_prefix_carry geometry i incoming = (d = Above)"
  using decisive prefix
  by (cases d; simp_all add: domain_prefix_carry_def)

corollary last_below_resets_prefix_carry:
  assumes "take i geometry = before @ Below # replicate tail Equal"
  shows "domain_prefix_carry geometry i incoming = False"
proof -
  have "domain_prefix_carry geometry i incoming = (Below = Above)"
    by (rule last_decisive_domain_determines_prefix_carry[OF assms]) simp
  then show ?thesis by simp
qed

corollary last_above_sets_prefix_carry:
  assumes "take i geometry = before @ Above # replicate tail Equal"
  shows "domain_prefix_carry geometry i incoming = True"
proof -
  have "domain_prefix_carry geometry i incoming = (Above = Above)"
    by (rule last_decisive_domain_determines_prefix_carry[OF assms]) simp
  then show ?thesis by simp
qed

text \<open>Thus each pointwise Boolean carry boundary is a prefix query on the
same domain word.  The theorem introduces no independent carry-state field.\<close>

type_synonym carry_wires = "(bool \<Rightarrow> bool) \<times> (bool \<Rightarrow> bool)"

definition carry_bits :: "nat \<Rightarrow> bool \<times> bool" where
  "carry_bits c = (1 \<le> c, c = 2)"

definition staircase_port :: "bool \<times> bool \<Rightarrow> bool" where
  "staircase_port p \<longleftrightarrow> (snd p \<longrightarrow> fst p)"

definition carry_from_bits :: "bool \<times> bool \<Rightarrow> nat" where
  "carry_from_bits p = (if fst p then 1 else 0) + (if snd p then 1 else 0)"

definition apply_wires :: "carry_wires \<Rightarrow> nat \<Rightarrow> nat" where
  "apply_wires w c = carry_from_bits
    (fst w (fst (carry_bits c)), snd w (snd (carry_bits c)))"

definition compose_wires :: "carry_wires \<Rightarrow> carry_wires \<Rightarrow> carry_wires" where
  "compose_wires left right =
    (fst right \<circ> fst left, snd right \<circ> snd left)"

definition valid_wires :: "carry_wires \<Rightarrow> bool" where
  "valid_wires w \<longleftrightarrow>
    (\<forall>p. staircase_port p \<longrightarrow>
      staircase_port (fst w (fst p), snd w (snd p)))"

lemma three_reachable_carry_ports:
  assumes "c < 3"
  shows "staircase_port (carry_bits c)"
    and "carry_from_bits (carry_bits c) = c"
proof -
  have cases: "c = 0 \<or> c = 1 \<or> c = 2" using assms by arith
  then show "staircase_port (carry_bits c)"
    by (auto simp: carry_bits_def staircase_port_def)
  from cases show "carry_from_bits (carry_bits c) = c"
    by (auto simp: carry_bits_def carry_from_bits_def)
qed

lemma valid_wires_stay_reachable:
  assumes "valid_wires w" "c < 3"
  shows "apply_wires w c < 3"
proof -
  have source: "staircase_port (carry_bits c)"
    using assms(2) by (rule three_reachable_carry_ports)
  have target: "staircase_port
      (fst w (fst (carry_bits c)), snd w (snd (carry_bits c)))"
    using assms(1) source by (auto simp: valid_wires_def)
  show ?thesis
    using target by (cases "fst w (fst (carry_bits c))";
        cases "snd w (snd (carry_bits c))";
        simp_all add: apply_wires_def carry_from_bits_def staircase_port_def)
qed

lemma valid_wires_compose:
  assumes "valid_wires left" "valid_wires right"
  shows "valid_wires (compose_wires left right)"
  using assms
  by (auto simp: valid_wires_def compose_wires_def staircase_port_def)

theorem carry_projection_spatial_composition:
  assumes "valid_wires left" "valid_wires right" "c < 3"
  shows "apply_wires (compose_wires left right) c =
    apply_wires right (apply_wires left c)"
proof -
  let ?p = "(fst left (fst (carry_bits c)),
      snd left (snd (carry_bits c)))"
  have source: "staircase_port (carry_bits c)"
    using assms(3) by (rule three_reachable_carry_ports)
  have middle: "staircase_port ?p"
    using assms(1) source by (auto simp: valid_wires_def)
  have middle_bound: "carry_from_bits ?p < 3"
    using middle by (cases "fst ?p"; cases "snd ?p";
        simp_all add: carry_from_bits_def staircase_port_def)
  have encode_middle: "carry_bits (carry_from_bits ?p) = ?p"
    using middle by (cases "fst ?p"; cases "snd ?p";
        simp_all add: carry_bits_def carry_from_bits_def staircase_port_def)
  show ?thesis
    using encode_middle
    by (simp add: apply_wires_def compose_wires_def comp_def)
qed

record 'a emitting_carry_action =
  action_wires :: carry_wires
  action_emission :: "nat \<Rightarrow> 'a"

definition compose_emitting ::
    "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a emitting_carry_action \<Rightarrow>
      'a emitting_carry_action \<Rightarrow> 'a emitting_carry_action" where
  "compose_emitting add left right = \<lparr>
    action_wires = compose_wires (action_wires left) (action_wires right),
    action_emission = (\<lambda>c. add (action_emission left c)
      (action_emission right (apply_wires (action_wires left) c))) \<rparr>"

definition carry_projection :: "'a emitting_carry_action \<Rightarrow> carry_wires" where
  "carry_projection action = action_wires action"

theorem emitting_action_projects_to_carry_composition:
  "carry_projection (compose_emitting add left right) =
    compose_wires (carry_projection left) (carry_projection right)"
  by (simp add: carry_projection_def compose_emitting_def)

corollary emitting_projection_application:
  assumes "valid_wires (carry_projection left)"
      and "valid_wires (carry_projection right)" "c < 3"
  shows "apply_wires
      (carry_projection (compose_emitting add left right)) c =
    apply_wires (carry_projection right)
      (apply_wires (carry_projection left) c)"
  using assms emitting_action_projects_to_carry_composition
    carry_projection_spatial_composition by metis


definition identity_carry_wires :: carry_wires where
  "identity_carry_wires = (id, id)"

definition carry_domain_wires :: "carry_domain \<Rightarrow> carry_wires" where
  "carry_domain_wires d =
    (case d of
       Below \<Rightarrow> (\<lambda>_. False, \<lambda>_. False)
     | Equal \<Rightarrow> identity_carry_wires
     | Above \<Rightarrow> (\<lambda>_. True, \<lambda>_. False))"

lemma carry_domain_wires_valid:
  "valid_wires (carry_domain_wires d)"
  by (cases d; auto simp: carry_domain_wires_def identity_carry_wires_def
      valid_wires_def staircase_port_def)

lemma carry_domain_wires_apply:
  assumes "c < 3"
  shows "apply_wires (carry_domain_wires d) c =
    (case d of Below \<Rightarrow> 0 | Equal \<Rightarrow> c | Above \<Rightarrow> 1)"
  using assms three_reachable_carry_ports(2)[OF assms]
  by (cases d; cases c; simp add: carry_domain_wires_def
      identity_carry_wires_def apply_wires_def carry_bits_def
      carry_from_bits_def)

lemma carry_domain_wires_bool_exact:
  "apply_wires (carry_domain_wires d) (if c then 1 else 0) =
    (if carry_apply d c then 1 else 0)"
  by (cases d; cases c; simp add: carry_domain_wires_def
      identity_carry_wires_def apply_wires_def carry_bits_def
      carry_from_bits_def)

theorem carry_domain_wires_compose:
  "carry_domain_wires (carry_then after before) =
    compose_wires (carry_domain_wires before) (carry_domain_wires after)"
  by (cases after; cases before; simp add: carry_domain_wires_def
      carry_then_def compose_wires_def identity_carry_wires_def fun_eq_iff)

fun wire_word_action :: "carry_wires list \<Rightarrow> carry_wires" where
  "wire_word_action [] = identity_carry_wires"
| "wire_word_action (wire # wires) =
    compose_wires wire (wire_word_action wires)"

fun wire_word_scan :: "nat \<Rightarrow> carry_wires list \<Rightarrow> nat" where
  "wire_word_scan c [] = c"
| "wire_word_scan c (wire # wires) =
    wire_word_scan (apply_wires wire c) wires"

lemma identity_wires_valid [simp]:
  "valid_wires identity_carry_wires"
  by (simp add: valid_wires_def identity_carry_wires_def staircase_port_def)

lemma identity_wires_apply [simp]:
  assumes "c < 3"
  shows "apply_wires identity_carry_wires c = c"
  using assms three_reachable_carry_ports(2)[of c]
  by (simp add: apply_wires_def identity_carry_wires_def)

lemma wire_word_action_valid:
  assumes "\<forall>wire \<in> set wires. valid_wires wire"
  shows "valid_wires (wire_word_action wires)"
  using assms
  by (induction wires) (simp_all add: valid_wires_compose)

theorem wire_word_action_exact:
  assumes valid: "\<forall>wire \<in> set wires. valid_wires wire"
      and incoming: "c < 3"
  shows "apply_wires (wire_word_action wires) c = wire_word_scan c wires"
  using valid incoming
proof (induction wires arbitrary: c)
  case Nil
  then show ?case by simp
next
  case (Cons wire wires)
  have wire_valid: "valid_wires wire" using Cons.prems by simp
  have rest_valid: "\<forall>w \<in> set wires. valid_wires w"
    using Cons.prems by simp
  have next_bound: "apply_wires wire c < 3"
    using wire_valid Cons.prems(2) by (rule valid_wires_stay_reachable)
  have rest_action_valid: "valid_wires (wire_word_action wires)"
    using rest_valid by (rule wire_word_action_valid)
  have composed:
      "apply_wires (wire_word_action (wire # wires)) c =
        apply_wires (wire_word_action wires) (apply_wires wire c)"
    using carry_projection_spatial_composition[OF wire_valid rest_action_valid
        Cons.prems(2)]
    by simp
  also have "... = wire_word_scan (apply_wires wire c) wires"
    using Cons.IH[OF rest_valid next_bound] .
  finally show ?case by simp
qed

theorem carry_domain_wire_word_exact:
  "apply_wires (wire_word_action (map carry_domain_wires ds))
      (if incoming then 1 else 0) =
    (if carry_finish incoming ds then 1 else 0)"
proof (induction ds arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  have valid: "\<forall>wire \<in> set (map carry_domain_wires (d # ds)).
      valid_wires wire"
    by (auto intro: carry_domain_wires_valid)
  have bound: "(if incoming then (1::nat) else 0) < 3"
    by (cases incoming) simp_all
  have mapped: "map carry_domain_wires (d # ds) =
      carry_domain_wires d # map carry_domain_wires ds"
    by simp
  have action:
    "apply_wires (wire_word_action (map carry_domain_wires (d # ds)))
        (if incoming then 1 else 0) =
      wire_word_scan (if incoming then 1 else 0)
        (map carry_domain_wires (d # ds))"
    by (rule wire_word_action_exact[OF valid bound])
  also have "... = wire_word_scan
      (if carry_apply d incoming then 1 else 0)
      (map carry_domain_wires ds)"
  proof -
    show ?thesis
      unfolding mapped wire_word_scan.simps
      by (simp only: carry_domain_wires_bool_exact)
  qed
  also have "... = apply_wires (wire_word_action (map carry_domain_wires ds))
      (if carry_apply d incoming then 1 else 0)"
  proof -
    have tail_valid: "\<forall>wire \<in> set (map carry_domain_wires ds).
        valid_wires wire"
      by (auto intro: carry_domain_wires_valid)
    have tail_bound: "(if carry_apply d incoming then (1::nat) else 0) < 3"
      by (cases "carry_apply d incoming") simp_all
    show ?thesis
      using wire_word_action_exact[OF tail_valid tail_bound] by simp
  qed
  also have "... =
      (if carry_finish incoming (d # ds) then 1 else 0)"
    using Cons.IH[of "carry_apply d incoming"] by simp
  finally show ?case .
qed

lemma wire_word_scan_append [simp]:
  "wire_word_scan c (left @ right) =
    wire_word_scan (wire_word_scan c left) right"
  by (induction left arbitrary: c) simp_all

theorem binary_boolean_add_block_composition:
  fixes low_left low_right high_left high_right incoming low_width high_width :: nat
  shows "((low_left + 2^low_width * high_left) +
      (low_right + 2^low_width * high_right) + incoming) mod
        2^(low_width + high_width) =
    (low_left + low_right + incoming) mod 2^low_width +
      2^low_width * ((high_left + high_right +
        ((low_left + low_right + incoming) div 2^low_width)) mod
          2^high_width)"
proof -
  let ?base = "2^low_width"
  let ?top = "2^high_width"
  let ?low_sum = "low_left + low_right + incoming"
  let ?low = "?low_sum mod ?base"
  let ?high = "high_left + high_right + (?low_sum div ?base)"
  let ?whole = "(low_left + ?base * high_left) +
      (low_right + ?base * high_right) + incoming"
  have split_low: "?low_sum mod ?base + ?base * (?low_sum div ?base) = ?low_sum"
    by (simp add: mod_mult_div_eq mult.commute)
  have split_whole: "?whole = ?low + ?base * ?high"
    using split_low by (simp add: algebra_simps)
  have low_bound: "?low < ?base"
    by (simp add: mod_less)
  have high_quotient: "(?low + ?base * ?high) div ?base = ?high"
    using low_bound by (simp add: div_mult_self2)
  have high_remainder: "(?low + ?base * ?high) mod ?base = ?low"
    using low_bound by simp
  have joined_remainder:
    "(?low + ?base * ?high) mod (?base * ?top) =
      ?base * (?high mod ?top) + ?low"
  proof -
    have "(?low + ?base * ?high) mod (?base * ?top) =
        ?base * (((?low + ?base * ?high) div ?base) mod ?top) +
          ((?low + ?base * ?high) mod ?base)"
      by (rule mod_mult2_eq)
    then show ?thesis using high_quotient high_remainder by simp
  qed
  have modulus: "(2::nat)^(low_width + high_width) = ?base * ?top"
    by (simp add: power_add mult.commute)
  show ?thesis
    using split_whole joined_remainder modulus by simp
qed

theorem binary_boolean_signed_fold_composition:
  "(int (low_output + base * high_output) -
      int (low_source + base * high_source)) mod int modulus =
    ((int low_output - int low_source) +
      int base * (int high_output - int high_source)) mod int modulus"
  by (simp add: algebra_simps)


lemma decimal_double_digit_carry:
  fixes a carry :: nat
  assumes digit: "a < 10" and carry: "carry \<le> 1"
  shows "2*a + carry = (2*a + carry) mod 10 +
    10*(if 5 \<le> a then 1 else 0)"
proof (cases "5 \<le> a")
  case True
  have small: "2*(a-5) + carry < 10" using digit carry True by arith
  have expanded: "2*a + carry = 10 + (2*(a-5) + carry)"
    using True by arith
  show ?thesis using True small by (simp add: expanded)
next
  case False
  have small: "2*a + carry < 10" using digit carry False by arith
  show ?thesis using False small by simp
qed

lemma decimal_double_three_digits:
  fixes a b c :: nat
  assumes ab: "a < 10" and bb: "b < 10"
  shows "(2 * (100*c + 10*b + a)) mod 1000 =
    100*((2*c + (if 5 \<le> b then 1 else 0)) mod 10) +
    10*((2*b + (if 5 \<le> a then 1 else 0)) mod 10) + (2*a mod 10)"
proof -
  let ?ca = "if 5 \<le> a then (1::nat) else 0"
  let ?cb = "if 5 \<le> b then (1::nat) else 0"
  let ?ra = "2*a mod 10"
  let ?rb = "(2*b + ?ca) mod 10"
  let ?rc = "(2*c + ?cb) mod 10"
  let ?carry = "(2*c + ?cb) div 10"
  have ca: "2*a = ?ra + 10*?ca"
    using decimal_double_digit_carry[OF ab, of 0] by simp
  have carry_bound: "?ca \<le> 1" by simp
  have cb: "2*b + ?ca = ?rb + 10*?cb"
    by (rule decimal_double_digit_carry[OF bb carry_bound])
  have cc: "2*c + ?cb = ?rc + 10*?carry"
    by (simp add: mod_mult_div_eq mult.commute)
  have combine: "\<And>a b c u v x y z q::nat.
      2*a = x+10*u \<Longrightarrow> 2*b+u = y+10*v \<Longrightarrow>
      2*c+v = z+10*q \<Longrightarrow>
      2*(100*c+10*b+a) = 100*z+10*y+x+1000*q"
    by (simp only: algebra_simps; linarith)
  have decomposition:
    "2*(100*c + 10*b + a) = 100*?rc + 10*?rb + ?ra + 1000*?carry"
    by (rule combine[OF ca cb cc])
  have bounds: "?ra < 10" "?rb < 10" "?rc < 10"
    using mod_less_divisor[of "2*a" 10]
      mod_less_divisor[of "2*b + ?ca" 10]
      mod_less_divisor[of "2*c + ?cb" 10] by arith+
  have bound: "100*?rc + 10*?rb + ?ra < 1000" using bounds by arith
  show ?thesis using decomposition bound by simp
qed


ML \<open>
  val checked = @{thms carry_finish_fold carry_finish_append
    advance_phase_append advance_phase_by_length carry_finish_equal_prefix
    first_decisive_carry_coalesces all_equal_carry
    domain_prefix_carry_composition all_equal_prefix_preserves_incoming
    last_decisive_domain_determines_prefix_carry
    last_below_resets_prefix_carry last_above_sets_prefix_carry
    three_reachable_carry_ports valid_wires_stay_reachable valid_wires_compose
    carry_projection_spatial_composition
    emitting_action_projects_to_carry_composition emitting_projection_application
    carry_domain_wires_valid carry_domain_wires_apply
    carry_domain_wires_bool_exact carry_domain_wires_compose
    carry_domain_wire_word_exact
    identity_wires_valid identity_wires_apply wire_word_action_valid
    wire_word_action_exact wire_word_scan_append
    binary_boolean_add_block_composition
    binary_boolean_signed_fold_composition decimal_double_three_digits};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Shared carry-tape proof depends on an oracle";
\<close>

end
