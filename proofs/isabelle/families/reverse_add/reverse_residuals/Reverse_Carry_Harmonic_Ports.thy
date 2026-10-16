theory Reverse_Carry_Harmonic_Ports
  imports Reverse_Residuals Shared_Carry_Dynamics.Shared_Carry_Tape
    Shared_Carry_Dynamics.Port_Valued_Mealy Mirror_Pair_Step
    Shared_S_Arithmetic.S_Arithmetic_Skew
begin

text \<open>Port-conditioned carry harmonics for the alternating 2,3 radix over
F5.  This is a spatial emitting carry action.  The theory proves its exact
composition and the first-decisive-domain coalescence law.  It does not assert
that the action is closed under a temporal reverse-and-add successor.\<close>

datatype harmonic_channel = Radix2 | Radix3

fun harmonic_weight :: "harmonic_channel \<Rightarrow> bool \<Rightarrow> nat" where
  "harmonic_weight Radix2 False = 1"
| "harmonic_weight Radix2 True = 2"
| "harmonic_weight Radix3 False = 1"
| "harmonic_weight Radix3 True = 3"

lemma harmonic_weight_mod_five [simp]:
  "harmonic_weight k p mod 5 = harmonic_weight k p"
  by (cases k; cases p) simp_all

fun harmonic_emit ::
    "harmonic_channel \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>
      carry_domain list \<Rightarrow> nat" where
  "harmonic_emit k p c [] = 0"
| "harmonic_emit k p c (d # ds) =
    ((if c then harmonic_weight k p else 0) +
      harmonic_emit k (\<not> p) (carry_apply d c) ds) mod 5"

fun harmonic_emit_raw ::
    "harmonic_channel \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>
      carry_domain list \<Rightarrow> nat" where
  "harmonic_emit_raw k p c [] = 0"
| "harmonic_emit_raw k p c (d # ds) =
    (if c then harmonic_weight k p else 0) +
      harmonic_emit_raw k (\<not> p) (carry_apply d c) ds"

lemma harmonic_emit_raw_mod_five:
  "harmonic_emit k p c ds = harmonic_emit_raw k p c ds mod 5"
  by (induction ds arbitrary: p c)
    (simp_all add: mod_add_eq mod_add_left_eq mod_add_right_eq add.assoc)

definition port_action ::
    "bool \<Rightarrow> carry_domain list \<Rightarrow> bool \<Rightarrow> bool \<times> nat \<times> nat" where
  "port_action p ds c =
    (carry_finish c ds, harmonic_emit Radix2 p c ds,
      harmonic_emit Radix3 p c ds)"

lemma harmonic_emit_less_five:
  "harmonic_emit k p c ds < 5"
  by (cases ds) simp_all

lemma harmonic_emit_mod_five [simp]:
  "harmonic_emit k p c ds mod 5 = harmonic_emit k p c ds"
  using harmonic_emit_less_five by simp

theorem harmonic_emit_append:
  "harmonic_emit k p c (xs @ ys) =
    (harmonic_emit k p c xs +
      harmonic_emit k (advance_phase p xs) (carry_finish c xs) ys) mod 5"
  by (induction xs arbitrary: p c)
    (simp_all add: mod_add_eq mod_add_left_eq mod_add_right_eq add.assoc)

lemma harmonic_emit_raw_append:
  "harmonic_emit_raw k p c (xs @ ys) =
    harmonic_emit_raw k p c xs +
      harmonic_emit_raw k (advance_phase p xs) (carry_finish c xs) ys"
  by (induction xs arbitrary: p c) (simp_all add: add.assoc)

interpretation identity_nat_emission_shift:
    additive_shift_action "\<lambda>(_ :: nat) (emission :: nat). emission"
  by unfold_locales simp_all

text \<open>Do not export the identity instance's generic simp rules into the
remainder of this theory: doing so makes unrelated recursive definitions
normalize through the whole Mealy algebra.  The bridge below names only the
identity laws it uses.\<close>

declare identity_nat_emission_shift.shift_zero[simp del]
  identity_nat_emission_shift.shift_zero_value[simp del]
  identity_nat_emission_shift.identity_mealy_left[simp del]
  identity_nat_emission_shift.identity_mealy_right[simp del]

definition harmonic_emitting_mealy ::
    "harmonic_channel \<Rightarrow> carry_domain list \<Rightarrow>
      (bool \<times> bool, nat) port_mealy" where
  "harmonic_emitting_mealy k ds = \<lparr>
    mealy_span = length ds,
    mealy_endpoint = (\<lambda>(p,c). (advance_phase p ds, carry_finish c ds)),
    mealy_emission = (\<lambda>(p,c). harmonic_emit_raw k p c ds)\<rparr>"

lemma harmonic_emitting_mealy_empty:
  "harmonic_emitting_mealy k [] = identity_nat_emission_shift.identity_mealy"
proof (rule port_mealy.equality)
  show "mealy_span (harmonic_emitting_mealy k []) =
      mealy_span identity_nat_emission_shift.identity_mealy"
    by (simp add: harmonic_emitting_mealy_def
        identity_nat_emission_shift.identity_mealy_def)
  show "mealy_endpoint (harmonic_emitting_mealy k []) =
      mealy_endpoint identity_nat_emission_shift.identity_mealy"
    by (rule ext; case_tac x;
        simp add: harmonic_emitting_mealy_def
          identity_nat_emission_shift.identity_mealy_def)
  show "mealy_emission (harmonic_emitting_mealy k []) =
      mealy_emission identity_nat_emission_shift.identity_mealy"
    by (rule ext; simp add: harmonic_emitting_mealy_def
        identity_nat_emission_shift.identity_mealy_def)
  show "port_mealy.more (harmonic_emitting_mealy k []) =
      port_mealy.more identity_nat_emission_shift.identity_mealy"
    by simp
qed

theorem harmonic_emitting_mealy_append:
  "identity_nat_emission_shift.compose_mealy
      (harmonic_emitting_mealy k xs) (harmonic_emitting_mealy k ys) =
    harmonic_emitting_mealy k (xs @ ys)"
proof (rule port_mealy.equality)
  show "mealy_span
      (identity_nat_emission_shift.compose_mealy
        (harmonic_emitting_mealy k xs) (harmonic_emitting_mealy k ys)) =
      mealy_span (harmonic_emitting_mealy k (xs @ ys))"
    by (simp add: identity_nat_emission_shift.compose_mealy_def
        harmonic_emitting_mealy_def)
  show "mealy_endpoint
      (identity_nat_emission_shift.compose_mealy
        (harmonic_emitting_mealy k xs) (harmonic_emitting_mealy k ys)) =
      mealy_endpoint (harmonic_emitting_mealy k (xs @ ys))"
    by (rule ext; case_tac x;
        simp add: identity_nat_emission_shift.compose_mealy_def
          harmonic_emitting_mealy_def advance_phase_append carry_finish_append)
  show "mealy_emission
      (identity_nat_emission_shift.compose_mealy
        (harmonic_emitting_mealy k xs) (harmonic_emitting_mealy k ys)) =
      mealy_emission (harmonic_emitting_mealy k (xs @ ys))"
    by (rule ext; case_tac x;
        simp add: identity_nat_emission_shift.compose_mealy_def
          harmonic_emitting_mealy_def harmonic_emit_raw_append)
  show "port_mealy.more
      (identity_nat_emission_shift.compose_mealy
        (harmonic_emitting_mealy k xs) (harmonic_emitting_mealy k ys)) =
      port_mealy.more (harmonic_emitting_mealy k (xs @ ys))"
    by simp
qed

definition harmonic_repeat_word :: "nat \<Rightarrow> carry_domain list \<Rightarrow> carry_domain list" where
  "harmonic_repeat_word n word = concat (replicate n word)"

lemma harmonic_repeat_word_Suc:
  "harmonic_repeat_word (Suc n) word = harmonic_repeat_word n word @ word"
proof -
  have replicate:
    "replicate (Suc n) word = replicate n word @ [word]"
    using replicate_Suc[of n word] replicate_append_same[of n word]
    by simp
  show ?thesis
    using replicate by (simp add: harmonic_repeat_word_def)
qed

theorem harmonic_emitting_mealy_repeat:
  "identity_nat_emission_shift.compose_mealy_power n
      (harmonic_emitting_mealy k word) =
    harmonic_emitting_mealy k (harmonic_repeat_word n word)"
proof (induction n)
  case 0
  have empty_word: "harmonic_repeat_word 0 word = []"
    by (simp add: harmonic_repeat_word_def)
  show ?case
    by (simp only: identity_nat_emission_shift.compose_mealy_power.simps
        empty_word harmonic_emitting_mealy_empty)
next
  case (Suc n)
  then show ?case
    by (simp only: identity_nat_emission_shift.compose_mealy_power.simps
        harmonic_repeat_word_Suc Suc.IH harmonic_emitting_mealy_append)
qed

theorem harmonic_emitting_mealy_observes_mod_five:
  "mealy_emission (harmonic_emitting_mealy k ds) (p,c) mod 5 =
    harmonic_emit k p c ds"
  by (simp add: harmonic_emitting_mealy_def harmonic_emit_raw_mod_five)

theorem port_action_spatial_composition:
  "port_action p (xs @ ys) c =
    (carry_finish (carry_finish c xs) ys,
      (harmonic_emit Radix2 p c xs +
        harmonic_emit Radix2 (advance_phase p xs)
          (carry_finish c xs) ys) mod 5,
      (harmonic_emit Radix3 p c xs +
        harmonic_emit Radix3 (advance_phase p xs)
          (carry_finish c xs) ys) mod 5)"
  by (simp add: port_action_def harmonic_emit_append)

fun prefix_harmonic :: "harmonic_channel \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat" where
  "prefix_harmonic k p 0 = 0"
| "prefix_harmonic k p (Suc n) =
    (harmonic_weight k p + prefix_harmonic k (\<not> p) n) mod 5"

lemma prefix_harmonic_ten_period:
  "prefix_harmonic k p (n + 10) = prefix_harmonic k p n"
proof (induction n arbitrary: p)
  case 0
  have ten: "(10 :: nat) =
      Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))"
    by simp
  then show ?case
    by (cases k; cases p;
        simp only: prefix_harmonic.simps harmonic_weight.simps ten;
        simp)
next
  case (Suc n)
  have length_step: "Suc n + 10 = Suc (n + 10)" by simp
  show ?case
    using Suc.IH[of "\<not> p"]
    by (simp only: length_step prefix_harmonic.simps)
qed

lemma prefix_harmonic_add_tens:
  "prefix_harmonic k p (n + 10 * q) = prefix_harmonic k p n"
proof (induction q)
  case 0
  then show ?case by simp
next
  case (Suc q)
  have arithmetic: "n + 10 * Suc q = (n + 10 * q) + 10" by simp
  show ?case
  proof (subst arithmetic)
    show "prefix_harmonic k p (n + 10 * q + 10) =
        prefix_harmonic k p n"
      using Suc.IH prefix_harmonic_ten_period by metis
  qed
qed

theorem first_decisive_harmonic_difference:
  assumes "d \<noteq> Equal"
  shows "harmonic_emit k p True (replicate j Equal @ d # ds) =
    (prefix_harmonic k p (Suc j) +
      harmonic_emit k p False (replicate j Equal @ d # ds)) mod 5"
  using assms
proof (induction j arbitrary: p)
  case 0
  then show ?case
    by (cases d;
        simp add: mod_add_eq mod_add_left_eq mod_add_right_eq add.assoc)
next
  case (Suc j)
  then show ?case
    by (simp add: mod_add_eq mod_add_left_eq mod_add_right_eq add.assoc)
qed

text \<open>The two incoming-carry trajectories differ exactly on the incoming
positions zero through j, hence on a prefix of length j+1.  The preceding two
lemmas show why only j modulo ten is visible to these emissions.\<close>

fun even_population :: "bool \<Rightarrow> bool \<Rightarrow> carry_domain list \<Rightarrow> nat" where
  "even_population p c [] = 0"
| "even_population p c (d # ds) =
    (if \<not> p \<and> c then 1 else 0) +
      even_population (\<not> p) (carry_apply d c) ds"

fun odd_population :: "bool \<Rightarrow> bool \<Rightarrow> carry_domain list \<Rightarrow> nat" where
  "odd_population p c [] = 0"
| "odd_population p c (d # ds) =
    (if p \<and> c then 1 else 0) +
      odd_population (\<not> p) (carry_apply d c) ds"

theorem radix2_population:
  "harmonic_emit Radix2 p c ds =
    (even_population p c ds + 2 * odd_population p c ds) mod 5"
  by (induction ds arbitrary: p c)
    (simp_all add: mod_add_eq mod_add_left_eq mod_add_right_eq
      add.assoc algebra_simps)

theorem radix3_population:
  "harmonic_emit Radix3 p c ds =
    (even_population p c ds + 3 * odd_population p c ds) mod 5"
  by (induction ds arbitrary: p c)
    (simp_all add: mod_add_eq mod_add_left_eq mod_add_right_eq
      add.assoc algebra_simps)

lemma even_odd_linear_inversion:
  fixes ev od :: int
  shows "((ev + 3 * od) - (ev + 2 * od)) mod 5 = od mod 5"
    and "(3 * (ev + 2 * od) - 2 * (ev + 3 * od)) mod 5 = ev mod 5"
  by simp_all

text \<open>The following cardinalities concern length-indexed reduced-code
spaces.  At one fixed length, the unique all-Equal word contributes one code.
It must not be identified with all-Equal words at other lengths because its
incoming-one emissions depend on the length modulo ten.\<close>

definition nonidentity_occupancy_codes ::
    "(bool \<times> nat \<times> nat \<times> nat) set" where
  "nonidentity_occupancy_codes = UNIV \<times> {0..<10} \<times> {0..<5} \<times> {0..<5}"

definition fixed_length_occupancy_codes ::
    "(bool \<times> nat \<times> nat \<times> nat) option set" where
  "fixed_length_occupancy_codes =
    insert None (Some ` nonidentity_occupancy_codes)"

theorem occupancy_code_capacity:
  "card nonidentity_occupancy_codes = 500"
  "card fixed_length_occupancy_codes = 501"
  by (simp_all add: nonidentity_occupancy_codes_def
      fixed_length_occupancy_codes_def card_image)

definition nonidentity_border_codes :: "(bool \<times> bool \<times> nat) set" where
  "nonidentity_border_codes = UNIV \<times> UNIV \<times> {0..<5}"

definition fixed_length_border_codes :: "(bool \<times> bool \<times> nat) option set" where
  "fixed_length_border_codes = insert None (Some ` nonidentity_border_codes)"

theorem border_code_capacity:
  "card nonidentity_border_codes = 20"
  "card fixed_length_border_codes = 21"
  by (simp_all add: nonidentity_border_codes_def fixed_length_border_codes_def
      card_image)

lemma all_equal_false_emission [simp]:
  "harmonic_emit k p False (replicate n Equal) = 0"
  by (induction n arbitrary: p) simp_all

lemma all_equal_true_emission:
  "harmonic_emit k p True (replicate n Equal) = prefix_harmonic k p n"
  by (induction n arbitrary: p) simp_all

theorem all_equal_actions_are_length_indexed:
  "port_action False [] True \<noteq> port_action False [Equal] True"
  by (simp add: port_action_def)

theorem all_equal_action_ten_period:
  "port_action p (replicate (n + 10) Equal) c =
    port_action p (replicate n Equal) c"
  by (cases c; simp add: port_action_def all_equal_true_emission
      prefix_harmonic_ten_period)

text \<open>The Q19 pair-field producer uses the same three carry actions as the
shared tape.  A coefficient sum below nine resets to zero, nine transmits the
ingress, and a sum above nine resets to one.  The following bridge makes the
source coefficient and its two ingress ports the input to the harmonic bank;
it does not infer an unavailable ingress from a finite spectral observation.\<close>

definition reverse_q19_pair_carry :: "nat \<Rightarrow> bool \<Rightarrow> bool" where
  "reverse_q19_pair_carry s c = carry_apply (domain s) c"

definition reverse_q19_carry_bit :: "bool \<Rightarrow> nat" where
  "reverse_q19_carry_bit c = (if c then 1 else 0)"

lemma reverse_q19_pair_carry_reset:
  "reverse_q19_pair_carry s c =
    (if s < 9 then False else if s = 9 then c else True)"
  by (cases c; simp add: reverse_q19_pair_carry_def domain_def)

definition reverse_q19_no_growth_target ::
    "nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat" where
  "reverse_q19_no_growth_target s low reflected =
    2*s + reverse_q19_carry_bit low + reverse_q19_carry_bit reflected -
      10*(reverse_q19_carry_bit (reverse_q19_pair_carry s low) +
        reverse_q19_carry_bit (reverse_q19_pair_carry s reflected))"

lemma reverse_q19_no_growth_target_range:
  assumes "s \<le> 18"
  shows "reverse_q19_no_growth_target s low reflected \<le> 18"
  using assms
  unfolding reverse_q19_no_growth_target_def reverse_q19_carry_bit_def
    reverse_q19_pair_carry_def
  by (cases low; cases reflected; cases "s < 9"; cases "s = 9";
      simp_all add: domain_def; arith)

lemma reverse_q19_no_growth_target_addback:
  assumes "s \<le> 18"
  shows "reverse_q19_no_growth_target s low reflected +
      10*(reverse_q19_carry_bit (reverse_q19_pair_carry s low) +
        reverse_q19_carry_bit (reverse_q19_pair_carry s reflected)) =
      2*s + reverse_q19_carry_bit low + reverse_q19_carry_bit reflected"
proof -
  have nonnegative:
    "10*(reverse_q19_carry_bit (reverse_q19_pair_carry s low) +
        reverse_q19_carry_bit (reverse_q19_pair_carry s reflected)) \<le>
      2*s + reverse_q19_carry_bit low + reverse_q19_carry_bit reflected"
    using assms
    unfolding reverse_q19_pair_carry_reset reverse_q19_carry_bit_def
    by (cases low; cases reflected; cases "s < 9"; cases "s = 9";
        simp_all; arith)
  show ?thesis
    unfolding reverse_q19_no_growth_target_def
    using nonnegative by arith
qed

lemma reverse_q19_no_growth_target_normalized_pair:
  assumes "s \<le> 18"
  shows "reverse_q19_no_growth_target s low reflected =
      normalized_pair_digit s (reverse_q19_carry_bit low) +
      normalized_pair_digit s (reverse_q19_carry_bit reflected)"
  using assms
  unfolding reverse_q19_no_growth_target_def reverse_q19_carry_bit_def
    reverse_q19_pair_carry_def normalized_pair_digit_def domain_def
  by (cases low; cases reflected; cases "s < 9"; cases "s = 9";
      simp_all; arith)

theorem reverse_q19_no_growth_harmonic_coordinates:
  assumes source: "s \<le> 18"
  shows "reverse_q19_no_growth_target s low reflected mod 5 =
      (2*s + reverse_q19_carry_bit low +
        reverse_q19_carry_bit reflected) mod 5"
    and "reverse_q19_no_growth_target s low reflected mod 2 =
      (reverse_q19_carry_bit low +
        reverse_q19_carry_bit reflected) mod 2"
proof -
  let ?lo = "reverse_q19_carry_bit (reverse_q19_pair_carry s low)"
  let ?hi = "reverse_q19_carry_bit (reverse_q19_pair_carry s reflected)"
  have equation:
    "reverse_q19_no_growth_target s low reflected + 10*(?lo + ?hi) =
      2*s + reverse_q19_carry_bit low + reverse_q19_carry_bit reflected"
    by (rule reverse_q19_no_growth_target_addback[OF source])
  have mod5:
    "(reverse_q19_no_growth_target s low reflected + 10*(?lo + ?hi)) mod 5 =
      reverse_q19_no_growth_target s low reflected mod 5"
  proof -
    have factor: "10*(?lo + ?hi) = 5*(2*(?lo + ?hi))"
      by (simp add: algebra_simps)
    have zero: "(10*(?lo + ?hi)) mod 5 = 0"
      by (simp only: factor mod_mult_self1_is_0)
    have split:
      "(reverse_q19_no_growth_target s low reflected +
          10*(?lo + ?hi)) mod 5 =
        (reverse_q19_no_growth_target s low reflected mod 5 +
          (10*(?lo + ?hi)) mod 5) mod 5"
      by (rule mod_add_eq[symmetric])
    show ?thesis using split zero by simp
  qed
  have mod2:
    "(reverse_q19_no_growth_target s low reflected + 10*(?lo + ?hi)) mod 2 =
      reverse_q19_no_growth_target s low reflected mod 2"
  proof -
    have factor: "10*(?lo + ?hi) = 2*(5*(?lo + ?hi))"
      by (simp add: algebra_simps)
    have zero: "(10*(?lo + ?hi)) mod 2 = 0"
      by (simp only: factor mod_mult_self1_is_0)
    have split:
      "(reverse_q19_no_growth_target s low reflected +
          10*(?lo + ?hi)) mod 2 =
        (reverse_q19_no_growth_target s low reflected mod 2 +
          (10*(?lo + ?hi)) mod 2) mod 2"
      by (rule mod_add_eq[symmetric])
    show ?thesis using split zero by simp
  qed
  have even: "(2*s) mod 2 = 0"
    by (simp only: mod_mult_self1_is_0)
  have pair_sum_mod:
    "(2*s + (reverse_q19_carry_bit low +
        reverse_q19_carry_bit reflected)) mod 2 =
      (reverse_q19_carry_bit low +
        reverse_q19_carry_bit reflected) mod 2"
  proof -
    have split:
      "(2*s + (reverse_q19_carry_bit low +
          reverse_q19_carry_bit reflected)) mod 2 =
        ((2*s) mod 2 +
          (reverse_q19_carry_bit low +
            reverse_q19_carry_bit reflected) mod 2) mod 2"
      by (rule mod_add_eq[symmetric])
    show ?thesis using split even by simp
  qed
  show "reverse_q19_no_growth_target s low reflected mod 5 =
      (2*s + reverse_q19_carry_bit low +
        reverse_q19_carry_bit reflected) mod 5"
    using mod5 equation by simp
  show "reverse_q19_no_growth_target s low reflected mod 2 =
      (reverse_q19_carry_bit low +
        reverse_q19_carry_bit reflected) mod 2"
    using mod2 equation pair_sum_mod by (simp add: add.assoc)
qed

lemma reverse_q19_small_residue_characterization:
  fixes n :: nat
  assumes "n \<le> 18"
  shows "n = 9 \<longleftrightarrow> n mod 5 = 4 \<and> n mod 2 = 1"
  using assms by presburger

corollary reverse_q19_no_growth_eq_birth:
  assumes source: "s \<le> 18"
  shows "reverse_q19_no_growth_target s low reflected = 9 \<longleftrightarrow>
    (2*s + reverse_q19_carry_bit low +
      reverse_q19_carry_bit reflected) mod 5 = 4 \<and>
    (reverse_q19_carry_bit low +
      reverse_q19_carry_bit reflected) mod 2 = 1"
proof -
  have range: "reverse_q19_no_growth_target s low reflected \<le> 18"
    by (rule reverse_q19_no_growth_target_range[OF source])
  have criterion:
    "reverse_q19_no_growth_target s low reflected = 9 \<longleftrightarrow>
      reverse_q19_no_growth_target s low reflected mod 5 = 4 \<and>
      reverse_q19_no_growth_target s low reflected mod 2 = 1"
    by (rule reverse_q19_small_residue_characterization[OF range])
  show ?thesis
    using reverse_q19_no_growth_harmonic_coordinates(1)[OF source]
      reverse_q19_no_growth_harmonic_coordinates(2)[OF source] criterion
    by simp
qed

definition reverse_q19_pair_domain_word :: "nat list \<Rightarrow> carry_domain list" where
  "reverse_q19_pair_domain_word coefficients = map domain coefficients"

definition reverse_q19_pair_port_action ::
    "bool \<Rightarrow> nat list \<Rightarrow> bool \<Rightarrow>
      bool \<times> nat \<times> nat" where
  "reverse_q19_pair_port_action phase coefficients ingress =
    port_action phase (reverse_q19_pair_domain_word coefficients) ingress"

theorem reverse_q19_pair_port_action_append:
  "reverse_q19_pair_port_action phase (left @ right) ingress =
    (carry_finish (carry_finish ingress (reverse_q19_pair_domain_word left))
        (reverse_q19_pair_domain_word right),
      (harmonic_emit Radix2 phase ingress
          (reverse_q19_pair_domain_word left) +
        harmonic_emit Radix2
          (advance_phase phase (reverse_q19_pair_domain_word left))
          (carry_finish ingress (reverse_q19_pair_domain_word left))
          (reverse_q19_pair_domain_word right)) mod 5,
      (harmonic_emit Radix3 phase ingress
          (reverse_q19_pair_domain_word left) +
        harmonic_emit Radix3
          (advance_phase phase (reverse_q19_pair_domain_word left))
          (carry_finish ingress (reverse_q19_pair_domain_word left))
          (reverse_q19_pair_domain_word right)) mod 5)"
  by (simp add: reverse_q19_pair_port_action_def
      reverse_q19_pair_domain_word_def port_action_spatial_composition)

text \<open>A source-certified Q19 macro supplies an exact finite word of growth
bits and forced F5 innovations.  This affine tape consumes that word in
chronological order.  Quiet and growth multipliers are respectively 2 and
1+z; `shared_skew_then` owns their composition law.  The theorem below does
not select the word, predict a future source, or turn the source guard into a
phase-only authorization.\<close>

definition reverse_q19_f5_tick :: "nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow>
    nat skew_transfer" where
  "reverse_q19_f5_tick z growth forcing =
    \<lparr>upper = (if growth then 1+z else 2),
      offset = forcing mod 5, lower = 1\<rparr>"

fun reverse_q19_f5_tape :: "nat \<Rightarrow> (bool \<times> nat) list \<Rightarrow>
    nat skew_transfer" where
  "reverse_q19_f5_tape z [] = shared_skew_identity"
| "reverse_q19_f5_tape z ((growth,forcing)#events) =
    shared_skew_then (reverse_q19_f5_tick z growth forcing)
      (reverse_q19_f5_tape z events)"

fun reverse_q19_f5_apply :: "nat \<Rightarrow> (bool \<times> nat) list \<Rightarrow>
    nat \<Rightarrow> nat" where
  "reverse_q19_f5_apply z [] value = value mod 5"
| "reverse_q19_f5_apply z ((growth,forcing)#events) value =
    reverse_q19_f5_apply z events
      (((if growth then 1+z else 2)*value + forcing) mod 5)"

lemma reverse_q19_mod5_affine_step:
  fixes a b c d x :: nat
  shows "(a * ((b*x+c) mod 5) + d) mod 5 =
    (a*b*x + a*(c mod 5) + d) mod 5"
proof -
  have input: "((b*x+c) mod 5) mod 5 = (b*x+c) mod 5"
    by simp
  have scaled_input:
    "(a * ((b*x+c) mod 5)) mod 5 = (a * (b*x+c)) mod 5"
    by (rule mod_mult_cong[OF refl input])
  have first_add:
    "(a * ((b*x+c) mod 5) + d) mod 5 =
      (a * (b*x+c) + d) mod 5"
    by (rule mod_add_cong[OF scaled_input refl])
  have forcing:
    "(a*c) mod 5 = (a * (c mod 5)) mod 5"
    by (rule mod_mult_cong[OF refl]; simp)
  have inner_add:
    "(a*b*x + a*c) mod 5 = (a*b*x + a*(c mod 5)) mod 5"
    by (rule mod_add_cong[OF refl forcing])
  have final_add:
    "((a*b*x + a*c) + d) mod 5 =
      ((a*b*x + a*(c mod 5)) + d) mod 5"
    by (rule mod_add_cong[OF inner_add refl])
  have polynomial: "a*(b*x+c)+d = (a*b*x+a*c)+d"
    by (simp add: algebra_simps)
  have normalized:
    "(a*(b*x+c)+d) mod 5 =
      (a*b*x+a*(c mod 5)+d) mod 5"
    by (simp only: polynomial final_add)
  show ?thesis by (rule trans[OF first_add normalized])
qed

theorem reverse_q19_f5_tape_append:
  "reverse_q19_f5_tape z (left @ right) =
    shared_skew_then (reverse_q19_f5_tape z left)
      (reverse_q19_f5_tape z right)"
proof (induction left)
  case Nil
  then show ?case by simp
next
  case (Cons event events)
  obtain growth forcing where event: "event = (growth,forcing)"
    by (cases event)
  show ?case
    using Cons.IH event
    by (simp add: shared_skew_associative)
qed

theorem reverse_q19_f5_apply_tape:
  "reverse_q19_f5_apply z events x =
    (upper (reverse_q19_f5_tape z events)*x +
      offset (reverse_q19_f5_tape z events)) mod 5"
proof (induction events arbitrary: x)
  case Nil
  then show ?case
    by (simp add: shared_skew_identity_def)
next
  case (Cons event events)
  obtain growth forcing where event: "event = (growth,forcing)"
    by (cases event)
  let ?tail = "reverse_q19_f5_tape z events"
  let ?scale = "if growth then 1+z else 2"
  have affine:
    "(upper ?tail * ((?scale*x+forcing) mod 5) + offset ?tail) mod 5 =
      (upper ?tail * ?scale*x +
        upper ?tail * (forcing mod 5) + offset ?tail) mod 5"
    using reverse_q19_mod5_affine_step
      [where a = "upper ?tail" and b = "?scale" and c = "forcing"
        and d = "offset ?tail" and x = "x"] .
  have applied:
    "reverse_q19_f5_apply z (event#events) x =
      (upper ?tail * ((?scale*x+forcing) mod 5) + offset ?tail) mod 5"
    using Cons.IH[of "(?scale*x+forcing) mod 5"] event
    by simp
  have composed:
    "(upper (reverse_q19_f5_tape z (event#events))*x +
      offset (reverse_q19_f5_tape z (event#events))) mod 5 =
      (upper ?tail * ?scale*x +
        upper ?tail * (forcing mod 5) + offset ?tail) mod 5"
    using event
    by (simp add: shared_skew_then_def reverse_q19_f5_tick_def
        algebra_simps)
  show ?case using applied composed affine event by simp
qed

ML \<open>
  val checked = @{thms harmonic_emit_append port_action_spatial_composition
    harmonic_emit_raw_mod_five harmonic_emit_raw_append
    harmonic_emitting_mealy_empty harmonic_emitting_mealy_append
    harmonic_emitting_mealy_repeat harmonic_emitting_mealy_observes_mod_five
    prefix_harmonic_ten_period
    first_decisive_harmonic_difference radix2_population radix3_population
    even_odd_linear_inversion occupancy_code_capacity border_code_capacity
    all_equal_actions_are_length_indexed all_equal_action_ten_period
    reverse_q19_pair_carry_reset reverse_q19_no_growth_target_range
    reverse_q19_no_growth_target_addback
    reverse_q19_no_growth_target_normalized_pair
    reverse_q19_no_growth_harmonic_coordinates
    reverse_q19_no_growth_eq_birth reverse_q19_pair_port_action_append
    reverse_q19_f5_tape_append reverse_q19_mod5_affine_step
    reverse_q19_f5_apply_tape};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Carry harmonic port proof depends on an oracle";
\<close>

end
