theory Collatz_Boundary_Macros
  imports Collatz_Physical_Cylinder_Lift
    Shared_Carry_Dynamics.Port_Valued_Mealy
begin

text \<open>Exact guard lemmas for the four finite boundary templates used by the
Collatz production macro selector.  The divisibility assumptions state only
that the selected finite word is admissible; this theory does not assert that
the repetition count is maximal or prove any convergence property.\<close>

lemma collatz_guarded_false_step_exact:
  assumes even_source: "even x"
  shows "collatz_guarded_normalized_source_step False x = x div 2"
  using even_source
  by (simp add: collatz_guarded_normalized_source_step_def
      physical_collatz_def)

lemma collatz_guarded_true_step_exact:
  assumes odd_source: "odd x"
  shows "collatz_guarded_normalized_source_step True x = (3*x+1) div 2"
proof -
  have first_tick: "physical_collatz x = 3*x+1"
    using odd_source by (simp add: physical_collatz_def)
  have even_after: "even (3*x+1)"
    using odd_source by simp
  have second_tick:
      "physical_collatz (3*x+1) = (3*x+1) div 2"
    using even_after by (simp add: physical_collatz_def)
  have two: "2 = Suc (Suc 0)" by simp
  have iterate_two:
      "(physical_collatz ^^ 2) x =
        physical_collatz (physical_collatz x)"
    by (simp only: two funpow.simps comp_apply id_apply)
  show ?thesis
    unfolding collatz_guarded_normalized_source_step_def
    using iterate_two first_tick second_tick by simp
qed

lemma collatz_guarded_true_step_plus_one:
  assumes odd_source: "odd x"
  shows "collatz_guarded_normalized_source_step True x + 1 =
      3 * ((x+1) div 2)"
proof -
  obtain k where x: "x = 2*k+1"
    using odd_source by (rule oddE)
  show ?thesis
    using x odd_source
    by (simp add: collatz_guarded_true_step_exact algebra_simps)
qed

lemma collatz_guarded_step_double_exact:
  assumes branch: "branch = odd source"
  shows "2 * collatz_guarded_normalized_source_step branch source =
    (if branch then 3 * source + 1 else source)"
proof (cases branch)
  case False
  have even_source: "even source"
    using branch False by simp
  obtain k where source: "source = 2*k"
    using even_source by (rule evenE)
  show ?thesis
    using False even_source source
      collatz_guarded_false_step_exact[OF even_source]
    by simp
next
  case True
  have odd_source: "odd source"
    using branch True by simp
  obtain k where source: "source = 2*k+1"
    using odd_source by (rule oddE)
  show ?thesis
    using True odd_source source
      collatz_guarded_true_step_exact[OF odd_source]
    by (simp add: algebra_simps)
qed

definition collatz_modular_half_inverse :: "nat \<Rightarrow> nat" where
  "collatz_modular_half_inverse m = (m+1) div 2"

lemma collatz_modular_half_inverse_exact:
  assumes odd_modulus: "odd m"
  shows "2 * collatz_modular_half_inverse m = m+1"
proof -
  obtain k where modulus: "m=2*k+1"
    using odd_modulus by (rule oddE)
  show ?thesis
    using modulus by (simp add: collatz_modular_half_inverse_def)
qed

lemma collatz_modular_half_transport:
  assumes odd_modulus: "odd m"
  shows "((2*q mod m) * collatz_modular_half_inverse m) mod m = q mod m"
proof -
  have inverse: "2 * collatz_modular_half_inverse m = m+1"
    by (rule collatz_modular_half_inverse_exact[OF odd_modulus])
  have "((2*q mod m) * collatz_modular_half_inverse m) mod m =
        (2*q*collatz_modular_half_inverse m) mod m"
      by (simp only: mod_mult_left_eq)
  also have "... = (q * (2 * collatz_modular_half_inverse m)) mod m"
    by (simp add: algebra_simps)
  also have "... = (q * (m+1)) mod m"
    using inverse by simp
  also have "... = (q*m + q) mod m"
    by (simp add: algebra_simps)
  also have "... = q mod m"
    by (simp add: mult.commute)
  finally show ?thesis .
qed

lemma collatz_modular_numerator_residue:
  fixes source m s :: nat and branch :: bool
  assumes residue: "source mod m = s"
    and positive_modulus: "0 < m"
  shows "(if branch then 3*source+1 else source) mod m =
    (if branch then 3*s+1 else s) mod m"
proof (cases branch)
  case False
  have source_remainder: "source mod m < m"
    by (rule mod_less_divisor[OF positive_modulus])
  have s_lt_m: "s < m" using source_remainder residue by simp
  show ?thesis using False residue s_lt_m by simp
next
  case True
  have product: "(3*source) mod m = (3*s) mod m"
  proof -
    have "(3*source) mod m = (3*(source mod m)) mod m"
      by (simp only: mod_mult_right_eq)
    also have "... = (3*s) mod m"
      using residue by simp
    finally show ?thesis .
  qed
  have numerator: "(3*source+1) mod m = (3*s+1) mod m"
    by (rule mod_add_cong[OF product refl])
  show ?thesis using True numerator by simp
qed

definition collatz_modular_port_transition ::
    "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> nat \<times> bool" where
  "collatz_modular_port_transition m s branch next_bit =
    (((if branch then 3*s+1 else s) * collatz_modular_half_inverse m) mod m,
      next_bit)"

text \<open>This is the input-driven residue transition used by the global port
observer.  The parity input is authenticated by the exact normalized source
step; the theorem does not make either parity choice autonomous or use an
observer class as an endpoint identity.\<close>

theorem collatz_modular_port_transition_exact:
  fixes m source s :: nat and branch next_bit :: bool
  assumes odd_modulus: "odd m"
    and source_residue: "source mod m = s"
    and source_branch: "branch = odd source"
    and next_parity:
      "next_bit = odd (collatz_guarded_normalized_source_step branch source)"
  shows "collatz_modular_port_transition m s branch next_bit =
    (collatz_guarded_normalized_source_step branch source mod m,
      odd (collatz_guarded_normalized_source_step branch source))"
proof -
  let ?endpoint = "collatz_guarded_normalized_source_step branch source"
  have doubled:
    "2*?endpoint = (if branch then 3*source+1 else source)"
    by (rule collatz_guarded_step_double_exact[OF source_branch])
  have numerator_residue:
    "(if branch then 3*source+1 else source) mod m =
      (if branch then 3*s+1 else s) mod m"
  proof (rule collatz_modular_numerator_residue[OF source_residue])
    show "0 < m" using odd_modulus by (cases m) simp_all
  qed
  have doubled_residue:
    "(2*?endpoint) mod m =
      (if branch then 3*s+1 else s) mod m"
    using doubled numerator_residue by simp
  have transport:
    "(((if branch then 3*s+1 else s) mod m) *
        collatz_modular_half_inverse m) mod m = ?endpoint mod m"
  proof -
    have half: "((2*?endpoint mod m) * collatz_modular_half_inverse m) mod m =
        ?endpoint mod m"
      by (rule collatz_modular_half_transport[OF odd_modulus])
    show ?thesis using half doubled_residue by simp
  qed
  have transition_residue:
    "((if branch then 3*s+1 else s) *
        collatz_modular_half_inverse m) mod m = ?endpoint mod m"
  proof -
    have normalize:
      "((if branch then 3*s+1 else s) *
          collatz_modular_half_inverse m) mod m =
        (((if branch then 3*s+1 else s) mod m) *
          collatz_modular_half_inverse m) mod m"
      by (rule mod_mult_left_eq[symmetric])
    show ?thesis by (rule trans[OF normalize transport])
  qed
  show ?thesis
    unfolding collatz_modular_port_transition_def
    using transition_residue next_parity by simp
qed

text \<open>The physical decimal boundary observation is a small total classifier.
Its twenty input guards are the two possible quotient parities and ten
present digits.  The emitted digit is the low decimal digit of one physical
Collatz step.  This is a one-step observation contract; it does not claim that
the twenty guards form a closed future-state machine (the next quotient
parity needs more source information).\<close>

definition collatz_decimal_boundary_output :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz_decimal_boundary_output quotient_parity digit =
    (if even digit then digit div 2 + 5 * quotient_parity
     else (3 * digit + 1) mod 10)"

definition collatz_decimal_boundary_mealy :: "(nat \<times> nat, nat) port_mealy" where
  "collatz_decimal_boundary_mealy = \<lparr>
    mealy_span = 1,
    mealy_endpoint = id,
    mealy_emission = (\<lambda>(quotient_parity, digit).
      collatz_decimal_boundary_output quotient_parity digit)\<rparr>"

definition collatz_decimal_boundary_guard :: "nat \<Rightarrow> nat \<times> nat" where
  "collatz_decimal_boundary_guard index = (index div 10, index mod 10)"

lemma collatz_decimal_boundary_guard_bounds:
  assumes index: "index < 20"
  shows "fst (collatz_decimal_boundary_guard index) < 2 \<and>
    snd (collatz_decimal_boundary_guard index) < 10"
proof -
  have remainder: "index mod 10 < 10" by simp
  have decomposition: "(index div 10) * 10 + index mod 10 = index"
    by (rule div_mult_mod_eq)
  show ?thesis
    using index remainder decomposition
    by (simp add: collatz_decimal_boundary_guard_def; arith)
qed

lemma collatz_decimal_boundary_guard_reconstruct:
  assumes index: "index < 20"
  shows "10 * fst (collatz_decimal_boundary_guard index) +
      snd (collatz_decimal_boundary_guard index) = index"
  using index by (simp add: collatz_decimal_boundary_guard_def div_mult_mod_eq)

lemma collatz_decimal_boundary_guard_injective:
  assumes left: "left < 20" and right: "right < 20"
    and same: "collatz_decimal_boundary_guard left =
      collatz_decimal_boundary_guard right"
  shows "left = right"
proof -
  have left_reconstruct:
    "10 * fst (collatz_decimal_boundary_guard left) +
       snd (collatz_decimal_boundary_guard left) = left"
    by (rule collatz_decimal_boundary_guard_reconstruct[OF left])
  have right_reconstruct:
    "10 * fst (collatz_decimal_boundary_guard right) +
       snd (collatz_decimal_boundary_guard right) = right"
    by (rule collatz_decimal_boundary_guard_reconstruct[OF right])
  have equal_fst:
    "fst (collatz_decimal_boundary_guard left) =
       fst (collatz_decimal_boundary_guard right)"
    using same by (rule arg_cong[where f=fst])
  have equal_snd:
    "snd (collatz_decimal_boundary_guard left) =
       snd (collatz_decimal_boundary_guard right)"
    using same by (rule arg_cong[where f=snd])
  have left_value:
    "left = 10 * fst (collatz_decimal_boundary_guard left) +
      snd (collatz_decimal_boundary_guard left)"
    by (rule sym[OF left_reconstruct])
  also have
    "10 * fst (collatz_decimal_boundary_guard left) +
        snd (collatz_decimal_boundary_guard left) =
      10 * fst (collatz_decimal_boundary_guard right) +
        snd (collatz_decimal_boundary_guard right)"
    by (simp only: equal_fst equal_snd)
  also have
    "10 * fst (collatz_decimal_boundary_guard right) +
        snd (collatz_decimal_boundary_guard right) = right"
    by (rule right_reconstruct)
  finally show ?thesis .
qed

lemma collatz_decimal_boundary_guard_covers:
  assumes quotient_parity: "quotient_parity < 2" and digit: "digit < 10"
  shows "collatz_decimal_boundary_guard (10 * quotient_parity + digit) =
    (quotient_parity, digit)"
proof -
  have index: "10 * quotient_parity + digit < 20"
    using quotient_parity digit by arith
  have remainder: "(10 * quotient_parity + digit) mod 10 < 10"
    by simp
  have decomposition:
    "((10 * quotient_parity + digit) div 10) * 10 +
       (10 * quotient_parity + digit) mod 10 =
       10 * quotient_parity + digit"
    by (rule div_mult_mod_eq)
  show ?thesis
    using quotient_parity digit decomposition index remainder
    by (simp add: collatz_decimal_boundary_guard_def; arith)
qed

lemma collatz_decimal_boundary_output_range:
  assumes quotient_parity: "quotient_parity < 2" and digit: "digit < 10"
  shows "collatz_decimal_boundary_output quotient_parity digit < 10"
proof (cases "even digit")
  case True
  obtain half where digit_even: "digit = 2 * half"
    using True by (elim evenE)
  have half_bound: "half < 5"
    using digit digit_even by arith
  have digit_half: "digit div 2 = half"
    using digit_even by simp
  show ?thesis
    using quotient_parity half_bound digit_half True
    by (simp add: collatz_decimal_boundary_output_def; arith)
next
  case False
  show ?thesis
    using False by (simp add: collatz_decimal_boundary_output_def)
qed

lemma collatz_decimal_boundary_output_covers_digit:
  assumes target: "target < 10"
  shows "\<exists>quotient_parity<2. \<exists>digit<10.
    collatz_decimal_boundary_output quotient_parity digit = target"
proof -
  let ?quotient_parity = "target div 5"
  let ?digit = "2 * (target mod 5)"
  have parity: "?quotient_parity < 2"
    using target by simp
  have digit_bound: "?digit < 10"
    using target by simp
  have even_digit: "even ?digit" by simp
  have division: "?digit div 2 = target mod 5" by simp
  have reconstruction: "5 * ?quotient_parity + target mod 5 = target"
    using target by (simp add: div_mult_mod_eq)
  have emitted_digit:
    "collatz_decimal_boundary_output ?quotient_parity ?digit = target"
    using even_digit division reconstruction
    by (simp add: collatz_decimal_boundary_output_def)
  show ?thesis using parity digit_bound emitted_digit by blast
qed

lemma collatz_decimal_boundary_output_exact:
  assumes digit: "digit < 10"
  shows "collatz_decimal_boundary_output (source_quotient mod 2) digit =
      physical_collatz (10 * source_quotient + digit) mod 10"
proof (cases "even digit")
  case True
  obtain half where digit_even: "digit = 2 * half"
    using True by (elim evenE) (auto simp: mult.commute)
  have half_bound: "half < 5"
    using digit digit_even by arith
  have quotient_decomposition:
    "source_quotient =
      (source_quotient div 2) * 2 + source_quotient mod 2"
    by (simp add: div_mult_mod_eq)
  have source_even:
    "10 * source_quotient + digit =
      2 * (5 * source_quotient + half)"
    using digit_even by (simp add: algebra_simps)
  have quotient_value:
    "(10 * source_quotient + digit) div 2 =
      5 * source_quotient + half"
    using source_even by simp
  have low_digit:
    "5 * (source_quotient mod 2) + half < 10"
  proof -
    have residue_bound: "source_quotient mod 2 < 2" by simp
    show ?thesis using residue_bound half_bound by arith
  qed
  have expanded:
    "5 * source_quotient + half =
      10 * (source_quotient div 2) +
        (5 * (source_quotient mod 2) + half)"
    using quotient_decomposition by arith
  have modulo:
    "(5 * source_quotient + half) mod 10 =
      5 * (source_quotient mod 2) + half"
  proof -
    have expanded_mod:
      "(5 * source_quotient + half) mod 10 =
        (10 * (source_quotient div 2) +
          (5 * (source_quotient mod 2) + half)) mod 10"
      by (simp only: expanded)
    also have
      "(10 * (source_quotient div 2) +
          (5 * (source_quotient mod 2) + half)) mod 10 =
        ((10 * (source_quotient div 2)) mod 10 +
          (5 * (source_quotient mod 2) + half) mod 10) mod 10"
      by (rule mod_add_eq[symmetric])
    also have
      "((10 * (source_quotient div 2)) mod 10 +
          (5 * (source_quotient mod 2) + half) mod 10) mod 10 =
        5 * (source_quotient mod 2) + half"
      using low_digit by simp
    finally show ?thesis .
  qed
  show ?thesis
    using True digit_even quotient_value modulo
    by (simp add: collatz_decimal_boundary_output_def physical_collatz_def
        algebra_simps)
next
  case False
  have source_odd: "odd (10 * source_quotient + digit)"
    using False by simp
  have numerator:
    "(3 * (10 * source_quotient + digit) + 1) mod 10 =
      (3 * digit + 1) mod 10"
  proof -
    have regroup:
      "3 * (10 * source_quotient + digit) + 1 =
        (3 * digit + 1) + 10 * (3 * source_quotient)"
      by (simp add: algebra_simps)
    have split:
      "((3 * digit + 1) + 10 * (3 * source_quotient)) mod 10 =
        (((3 * digit + 1) mod 10) +
          (10 * (3 * source_quotient)) mod 10) mod 10"
      by (rule mod_add_eq[symmetric])
    show ?thesis using regroup split by (simp add: add.commute)
  qed
  show ?thesis
    using False source_odd numerator
    by (simp add: collatz_decimal_boundary_output_def physical_collatz_def)
qed

theorem collatz_decimal_boundary_mealy_exact:
  assumes digit: "digit < 10"
  shows "mealy_response collatz_decimal_boundary_mealy
      (q mod 2, digit) =
    ((q mod 2, digit), physical_collatz (10 * q + digit) mod 10)"
  using collatz_decimal_boundary_output_exact[OF digit, of q]
  by (simp add: mealy_response_def collatz_decimal_boundary_mealy_def
      collatz_decimal_boundary_output_def)

theorem collatz_decimal_boundary_twenty_guards_ten_outputs:
  "(\<forall>index<20. let guard = collatz_decimal_boundary_guard index
      in fst guard < 2 \<and> snd guard < 10 \<and>
        collatz_decimal_boundary_output (fst guard) (snd guard) < 10) \<and>
   (\<forall>left<20. \<forall>right<20.
      collatz_decimal_boundary_guard left =
        collatz_decimal_boundary_guard right \<longrightarrow> left = right) \<and>
   (\<forall>quotient_parity<2. \<forall>digit<10.
      collatz_decimal_boundary_guard (10 * quotient_parity + digit) =
        (quotient_parity, digit)) \<and>
   (\<forall>target<10. \<exists>quotient_parity<2. \<exists>digit<10.
      collatz_decimal_boundary_output quotient_parity digit = target)"
proof (intro conjI)
  show "\<forall>index<20. let guard = collatz_decimal_boundary_guard index
      in fst guard < 2 \<and> snd guard < 10 \<and>
        collatz_decimal_boundary_output (fst guard) (snd guard) < 10"
  proof (intro allI impI)
    fix index :: nat
    assume index: "index < 20"
    have bounds: "fst (collatz_decimal_boundary_guard index) < 2 \<and>
        snd (collatz_decimal_boundary_guard index) < 10"
      by (rule collatz_decimal_boundary_guard_bounds[OF index])
    have quotient_parity:
      "fst (collatz_decimal_boundary_guard index) < 2"
      by (rule conjunct1[OF bounds])
    have digit: "snd (collatz_decimal_boundary_guard index) < 10"
      by (rule conjunct2[OF bounds])
    have emitted_bound:
      "collatz_decimal_boundary_output
        (fst (collatz_decimal_boundary_guard index))
        (snd (collatz_decimal_boundary_guard index)) < 10"
      by (rule collatz_decimal_boundary_output_range[OF quotient_parity digit])
    show "let guard = collatz_decimal_boundary_guard index
        in fst guard < 2 \<and> snd guard < 10 \<and>
          collatz_decimal_boundary_output (fst guard) (snd guard) < 10"
      using bounds emitted_bound by simp
  qed
  show "\<forall>left<20. \<forall>right<20.
      collatz_decimal_boundary_guard left =
        collatz_decimal_boundary_guard right \<longrightarrow> left = right"
    by (blast intro: collatz_decimal_boundary_guard_injective)
  show "\<forall>quotient_parity<2. \<forall>digit<10.
      collatz_decimal_boundary_guard (10 * quotient_parity + digit) =
        (quotient_parity, digit)"
  proof (intro allI impI)
    fix quotient_parity digit :: nat
    assume quotient_parity: "quotient_parity < 2"
      and digit: "digit < 10"
    show "collatz_decimal_boundary_guard (10 * quotient_parity + digit) =
        (quotient_parity, digit)"
      by (rule collatz_decimal_boundary_guard_covers[OF quotient_parity digit])
  qed
  show "\<forall>target<10. \<exists>quotient_parity<2. \<exists>digit<10.
      collatz_decimal_boundary_output quotient_parity digit = target"
  proof (intro allI impI)
    fix target :: nat
    assume target: "target < 10"
    show "\<exists>quotient_parity<2. \<exists>digit<10.
        collatz_decimal_boundary_output quotient_parity digit = target"
      by (rule collatz_decimal_boundary_output_covers_digit[OF target])
  qed
qed

lemma collatz_guarded_normalized_word_admitted_append:
  "collatz_guarded_normalized_word_admitted (left @ right) x \<longleftrightarrow>
    collatz_guarded_normalized_word_admitted left x \<and>
    collatz_guarded_normalized_word_admitted right
      (collatz_guarded_normalized_word_endpoint left x)"
  by (induction left arbitrary: x) simp_all

lemma collatz_guarded_normalized_word_endpoint_append:
  "collatz_guarded_normalized_word_endpoint (left @ right) x =
    collatz_guarded_normalized_word_endpoint right
      (collatz_guarded_normalized_word_endpoint left x)"
  by (induction left arbitrary: x) simp_all

lemma collatz_guarded_false_run_exact:
  assumes divisible: "2^n dvd x"
  shows "collatz_guarded_normalized_word_admitted (replicate n False) x \<and>
    collatz_guarded_normalized_word_endpoint (replicate n False) x =
      x div 2^n"
  using divisible
proof (induction n arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain k where x: "x = 2^(Suc n)*k"
    using Suc.prems unfolding dvd_def by blast
  have even_x: "even x"
    using x by simp
  have first_step:
      "collatz_guarded_normalized_source_step False x = 2^n*k"
    using collatz_guarded_false_step_exact[OF even_x] x
    by (simp add: power_Suc algebra_simps)
  have tail_divisible: "2^n dvd 2^n*k"
    unfolding dvd_def by blast
  have tail:
      "collatz_guarded_normalized_word_admitted (replicate n False) (2^n*k) \<and>
       collatz_guarded_normalized_word_endpoint (replicate n False) (2^n*k) =
         (2^n*k) div 2^n"
    by (rule Suc.IH[OF tail_divisible])
  have first_guard: "False = odd x"
    using even_x by simp
  have endpoint:
      "collatz_guarded_normalized_word_endpoint (replicate (Suc n) False) x = k"
    using tail first_step
    by (simp add: first_guard collatz_guarded_normalized_word_endpoint.simps)
  have quotient: "x div 2^(Suc n) = k"
    using x by (simp add: power_Suc mult.assoc)
  show ?case
    using tail first_step first_guard endpoint quotient
    by (simp add: collatz_guarded_normalized_word_admitted.simps
        collatz_guarded_normalized_word_endpoint.simps)
qed

lemma collatz_guarded_true_run_admitted:
  assumes divisible: "2^n dvd x+1"
  shows "collatz_guarded_normalized_word_admitted (replicate n True) x"
  using divisible
proof (induction n arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain k where x_plus: "x+1 = 2^(Suc n)*k"
    using Suc.prems unfolding dvd_def by blast
  let ?half = "2^n*k"
  have x_plus_two: "x+1 = 2*?half"
    using x_plus by (simp add: power_Suc mult.assoc)
  have even_successor: "even (Suc x)"
    using x_plus_two by simp
  have odd_x: "odd x"
    using even_successor by (simp add: even_Suc)
  have half: "(x+1) div 2 = ?half"
    using x_plus_two by simp
  have next_plus: "collatz_guarded_normalized_source_step True x + 1 =
      2^n*(3*k)"
    using collatz_guarded_true_step_plus_one[OF odd_x] half
    by (simp add: mult.assoc)
  have tail_divisible:
      "2^n dvd collatz_guarded_normalized_source_step True x + 1"
    using next_plus unfolding dvd_def by blast
  have tail:
      "collatz_guarded_normalized_word_admitted (replicate n True)
        (collatz_guarded_normalized_source_step True x)"
    by (rule Suc.IH[OF tail_divisible])
  show ?case
    using odd_x tail
    by (simp add: collatz_guarded_normalized_word_admitted.simps)
qed

lemma collatz_guarded_one_zero_pair:
  assumes exponent: "2 \<le> n"
  shows
    "collatz_guarded_normalized_word_admitted [True,False]
       (1+2^n*k) \<and>
     collatz_guarded_normalized_word_endpoint [True,False]
       (1+2^n*k) = 1+3*2^(n-2)*k"
proof -
  obtain e where n: "n = 2+e"
    using exponent by (metis le_iff_add add.commute)
  let ?x = "1+2^n*k"
  have odd_x: "odd ?x"
    by (simp add: n power_add)
  have first_numerator:
      "3*(1+2^(2+e)*k)+1 = 2*(2*(1+3*2^e*k))"
    by (simp add: power_add algebra_simps)
  have first_value:
      "collatz_guarded_normalized_source_step True ?x =
        2*(1+3*2^e*k)"
    using collatz_guarded_true_step_exact[OF odd_x] first_numerator n
    by simp
  have even_first:
      "even (collatz_guarded_normalized_source_step True ?x)"
    using first_value by simp
  have second_value:
      "collatz_guarded_normalized_source_step False
        (collatz_guarded_normalized_source_step True ?x) =
        1+3*2^e*k"
    using collatz_guarded_false_step_exact[OF even_first] first_value
    by simp
  show ?thesis
    using odd_x even_first first_value second_value n
    by (simp add: collatz_guarded_normalized_word_admitted.simps
        collatz_guarded_normalized_word_endpoint.simps)
qed

fun collatz_421_tail :: "nat \<Rightarrow> bool list" where
  "collatz_421_tail 0 = [True]"
| "collatz_421_tail (Suc n) = [True,False] @ collatz_421_tail n"

definition collatz_421_word :: "nat \<Rightarrow> bool list" where
  "collatz_421_word r = [False,False] @ collatz_421_tail (r-1)"

lemma collatz_421_tail_admitted:
  "collatz_guarded_normalized_word_admitted (collatz_421_tail n)
    (1+2^(2*n+1)*k)"
proof (induction n arbitrary: k)
  case 0
  have divisible: "2^1 dvd (1+2^1*k)+1"
    unfolding dvd_def by (rule exI[where x="1+k"]) simp
  show ?case
    using collatz_guarded_true_run_admitted[OF divisible] by simp
next
  case (Suc n)
  have pair_result:
      "collatz_guarded_normalized_word_admitted [True,False]
        (1+2^(2*(Suc n)+1)*k) \<and>
       collatz_guarded_normalized_word_endpoint [True,False]
        (1+2^(2*(Suc n)+1)*k) =
          1+3*2^(2*(Suc n)+1-2)*k"
    by (rule collatz_guarded_one_zero_pair) arith
  have pair:
      "collatz_guarded_normalized_word_admitted [True,False]
        (1+2^(2*(Suc n)+1)*k)"
    using pair_result by simp
  have pair_exponent: "2*(Suc n)+1-2=2*n+1"
    by arith
  have pair_endpoint:
      "collatz_guarded_normalized_word_endpoint [True,False]
        (1+2^(2*(Suc n)+1)*k) = 1+2^(2*n+1)*(3*k)"
    using pair_result pair_exponent by (simp add: algebra_simps)
  have tail:
      "collatz_guarded_normalized_word_admitted (collatz_421_tail n)
        (1+2^(2*n+1)*(3*k))"
    by (rule Suc.IH)
  show ?case
    using pair pair_endpoint tail
    by (simp add: collatz_421_tail.simps
        collatz_guarded_normalized_word_admitted_append)
qed

lemma collatz_421_tail_length:
  "length (collatz_421_tail n) = 2*n+1"
  by (induction n) simp_all

lemma collatz_421_tail_true_count:
  "count_list (collatz_421_tail n) True = n+1"
  by (induction n) simp_all

theorem collatz_421_macro_guard:
  assumes positive: "0 < r"
    and source: "source mod 40 = 4"
    and source_large: "4 < source"
    and divisor: "2^(2*r+1) dvd source-4"
  shows "collatz_guarded_normalized_word_admitted
      (collatz_421_word r) source"
proof -
  obtain n where r: "r = Suc n"
    using positive by (cases r) auto
  obtain k where difference: "source-4 = 2^(2*r+1)*k"
    using divisor unfolding dvd_def by blast
  have source_form: "source = 4+2^(2*r+1)*k"
    using difference source_large by arith
  have exponent: "2*r+1 = 2+(2*n+1)"
    using r by arith
  have source_factor: "source = 4*(1+2^(2*n+1)*k)"
    using source_form r exponent
    by (simp add: power_add algebra_simps)
  have prefix_divisible: "2^2 dvd source"
    unfolding source_factor dvd_def
    by (rule exI[where x="1+2^(2*n+1)*k"]) simp
  have prefix_result:
      "collatz_guarded_normalized_word_admitted (replicate 2 False) source \<and>
       collatz_guarded_normalized_word_endpoint (replicate 2 False) source =
         source div 2^2"
    using collatz_guarded_false_run_exact[OF prefix_divisible] .
  have prefix_admitted:
      "collatz_guarded_normalized_word_admitted [False,False] source"
  proof -
    have two: "(2::nat) = Suc (Suc 0)" by simp
    have list: "replicate 2 False = [False,False]"
      unfolding two by (simp only: replicate.simps)
    show ?thesis
      using prefix_result list by (metis conjunct1)
  qed
  have prefix_endpoint:
      "collatz_guarded_normalized_word_endpoint [False,False] source =
        1+2^(2*n+1)*k"
  proof -
    have two: "(2::nat) = Suc (Suc 0)" by simp
    have list: "replicate 2 False = [False,False]"
      unfolding two by (simp only: replicate.simps)
    have run_endpoint:
        "collatz_guarded_normalized_word_endpoint (replicate 2 False) source =
          source div 2^2"
      using prefix_result by blast
    have quotient: "source div 2^2 = 1+2^(2*n+1)*k"
      using source_factor by (simp add: power_add algebra_simps)
    show ?thesis using run_endpoint quotient list by simp
  qed
  have tail: "collatz_guarded_normalized_word_admitted
      (collatz_421_tail n) (1+2^(2*n+1)*k)"
    by (rule collatz_421_tail_admitted)
  have admitted:
    "collatz_guarded_normalized_word_admitted
       ([False,False] @ collatz_421_tail n) source"
    using prefix_admitted tail prefix_endpoint
    by (simp add: collatz_guarded_normalized_word_admitted_append)
  show ?thesis
    using admitted r
    by (simp add: collatz_421_word_def)
qed

lemma collatz_421_macro_duration:
  assumes positive: "0 < r"
  shows "length (collatz_421_word r) +
    count_list (collatz_421_word r) True = 3*r+1"
proof -
  obtain n where r: "r = Suc n"
    using positive by (cases r) auto
  show ?thesis
    using r collatz_421_tail_length[of n]
      collatz_421_tail_true_count[of n]
    by (simp add: collatz_421_word_def)
qed

definition collatz_4721_word :: "nat \<Rightarrow> bool list" where
  "collatz_4721_word r = False # replicate (2*r) True"

theorem collatz_4721_macro_guard:
  assumes positive: "0 < r"
    and source: "source mod 40 = 14"
    and divisor: "2^(2*r+1) dvd source+2"
  shows "collatz_guarded_normalized_word_admitted
      (collatz_4721_word r) source"
proof -
  have source_split: "(source div 40)*40 + source mod 40 = source"
    by (rule div_mult_mod_eq)
  have source_decomp: "source = 40*(source div 40)+14"
    using source_split source by (simp add: algebra_simps)
  have source_twice:
      "source = 2*(20*(source div 40)+7)"
    using source_decomp by arith
  have even_source: "even source"
    by (subst source_twice) simp
  obtain m where source_form: "source=2*m"
    using even_source by (rule evenE)
  obtain k where quotient:
      "source+2=2^(2*r+1)*k"
    using divisor unfolding dvd_def by blast
  have half_plus_one: "source div 2+1=2^(2*r)*k"
  proof -
    have "2*(m+1)=2*(2^(2*r)*k)"
      using quotient source_form by (simp add: power_Suc algebra_simps)
    then have "m+1=2^(2*r)*k"
      by arith
    then show ?thesis using source_form by simp
  qed
  have tail_divisible: "2^(2*r) dvd (source div 2)+1"
    unfolding half_plus_one dvd_def by blast
  have tail:
      "collatz_guarded_normalized_word_admitted (replicate (2*r) True)
        (source div 2)"
    by (rule collatz_guarded_true_run_admitted[OF tail_divisible])
  have first: "False=odd source"
    using even_source by simp
  have admitted:
      "collatz_guarded_normalized_word_admitted
         (False # replicate (2*r) True) source"
    using first tail
    by (simp add: collatz_guarded_normalized_word_admitted.simps
        collatz_guarded_normalized_source_step_def physical_collatz_def)
  show ?thesis
    using admitted by (simp add: collatz_4721_word_def)
qed

lemma collatz_count_list_replicate_true:
  "count_list (replicate n True) True = n"
  by (induction n) simp_all

lemma collatz_count_list_replicate_false:
  "count_list (replicate n False) True = 0"
  by (induction n) simp_all

lemma collatz_4721_macro_duration:
  "length (collatz_4721_word r) +
    count_list (collatz_4721_word r) True = 4*r+1"
  by (simp add: collatz_4721_word_def collatz_count_list_replicate_true)

definition collatz_630_word :: "nat \<Rightarrow> bool list" where
  "collatz_630_word r = [False,True] @ replicate r False"

lemma collatz_630_prefix_exact:
  "collatz_guarded_normalized_word_admitted [False,True] (20*k+6) \<and>
   collatz_guarded_normalized_word_endpoint [False,True] (20*k+6) =
     5*(3*k+1)"
proof -
  have even_source: "even (20*k+6)" by simp
  have after_even:
      "collatz_guarded_normalized_source_step False (20*k+6)=10*k+3"
    using collatz_guarded_false_step_exact[OF even_source] by simp
  have odd_after: "odd (10*k+3)" by simp
  have odd_numerator:
      "3*(10*k+3)+1=2*(5*(3*k+1))"
    by (simp add: algebra_simps)
  have after_odd:
      "collatz_guarded_normalized_source_step True (10*k+3)=5*(3*k+1)"
    using collatz_guarded_true_step_exact[OF odd_after] odd_numerator
    by simp
  show ?thesis
    using even_source after_even odd_after after_odd
    by (simp add: collatz_guarded_normalized_word_admitted.simps
        collatz_guarded_normalized_word_endpoint.simps)
qed

theorem collatz_630_macro_guard:
  assumes positive: "0 < r"
    and source: "source=20*k+6"
    and divisor: "2^r dvd 3*k+1"
  shows "collatz_guarded_normalized_word_admitted
      (collatz_630_word r) source"
proof -
  obtain t where t: "3*k+1=2^r*t"
    using divisor unfolding dvd_def by blast
  have tail_divisible: "2^r dvd 5*(3*k+1)"
    unfolding t dvd_def
    by (rule exI[where x="5*t"])
       (simp add: mult.assoc mult.commute mult.left_commute)
  have tail:
      "collatz_guarded_normalized_word_admitted (replicate r False)
        (5*(3*k+1))"
    by (rule collatz_guarded_false_run_exact[OF tail_divisible, THEN conjunct1])
  have prefix:
      "collatz_guarded_normalized_word_admitted [False,True] (20*k+6) \<and>
       collatz_guarded_normalized_word_endpoint [False,True] (20*k+6) =
         5*(3*k+1)"
    by (rule collatz_630_prefix_exact)
  have admitted:
      "collatz_guarded_normalized_word_admitted
        ([False,True] @ replicate r False) (20*k+6)"
    using prefix tail
    by (simp add: collatz_guarded_normalized_word_admitted_append)
  show ?thesis using admitted source
    by (simp add: collatz_630_word_def collatz_count_list_replicate_false)
qed

lemma collatz_630_macro_duration:
  "length (collatz_630_word r) +
    count_list (collatz_630_word r) True = r+3"
  by (simp add: collatz_630_word_def)

definition collatz_989_word :: "nat \<Rightarrow> bool list" where
  "collatz_989_word r = replicate r True"

theorem collatz_989_macro_guard:
  assumes positive: "0 < r"
    and source: "source mod 10 = 9"
    and divisor: "2^r dvd source+1"
  shows "collatz_guarded_normalized_word_admitted
      (collatz_989_word r) source"
  using collatz_guarded_true_run_admitted[OF divisor]
  by (simp add: collatz_989_word_def collatz_count_list_replicate_true)

lemma collatz_989_macro_duration:
  "length (collatz_989_word r) +
    count_list (collatz_989_word r) True = 2*r"
  by (simp add: collatz_989_word_def collatz_count_list_replicate_true)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms collatz_guarded_false_step_exact collatz_guarded_true_step_exact
      collatz_guarded_true_step_plus_one
      collatz_guarded_step_double_exact
      collatz_modular_half_inverse_exact collatz_modular_half_transport
      collatz_modular_numerator_residue collatz_modular_port_transition_exact
      collatz_guarded_normalized_word_admitted_append
      collatz_guarded_normalized_word_endpoint_append
      collatz_guarded_false_run_exact collatz_guarded_true_run_admitted
      collatz_guarded_one_zero_pair collatz_421_tail_admitted
      collatz_421_tail_length collatz_421_tail_true_count
      collatz_421_macro_guard collatz_421_macro_duration
      collatz_4721_macro_guard collatz_4721_macro_duration
      collatz_630_prefix_exact collatz_630_macro_guard collatz_630_macro_duration
      collatz_989_macro_guard collatz_989_macro_duration})
    then () else error "Collatz boundary macro refinement depends on an oracle";
\<close>

end
