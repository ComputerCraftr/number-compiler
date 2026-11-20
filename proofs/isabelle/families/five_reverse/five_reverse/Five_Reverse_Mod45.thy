theory Five_Reverse_Mod45
  imports Five_Reverse
begin

text \<open>
The mod-45 observation is derived from the exact decimal recurrence through
the mod-9 reversal invariant.  It is a residue observer, not a source-period
certificate for the full integer orbit.
\<close>

(* Keep the recursive equations local to their explicit one-step uses.  A
   global simp rewrite on a variable decimal count/reversal can keep peeling
   symbolic quotients and is unnecessary for the residue transport below. *)
declare decimal_digit_count.simps [simp del]
declare decimal_reverse.simps [simp del]

lemma decimal_ten_power_mod_nine:
  "(10::nat)^k mod 9 = 1"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have step:
    "(10::nat)^Suc k mod 9 =
      (((10::nat)^k mod 9) * (10 mod 9)) mod 9"
  proof -
    have power: "(10::nat)^Suc k = (10::nat)^k * 10"
      by (simp only: power_Suc)
    show ?thesis unfolding power by (rule mod_mult_eq[symmetric])
  qed
  show ?case using step Suc.IH by simp
qed

lemma decimal_reverse_mod_nine:
  "decimal_reverse n mod 9 = n mod 9"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 10")
    case True
    then show ?thesis by (simp add: decimal_reverse.simps)
  next
    case False
    let ?q = "n div 10"
    let ?r = "n mod 10"
    let ?k = "decimal_digit_count n - 1"
    have q_less: "?q < n" using False by simp
    have reverse_quotient:
      "decimal_reverse ?q mod 9 = ?q mod 9"
      by (rule less.IH[OF q_less])
    have power: "(10::nat)^?k mod 9 = 1"
      by (rule decimal_ten_power_mod_nine)
    have count_unfolded:
      "decimal_digit_count n =
        (if n < 10 then 1 else Suc (decimal_digit_count ?q))"
      by (rule decimal_digit_count.simps)
    have count_step:
      "decimal_digit_count n = Suc (decimal_digit_count ?q)"
      using count_unfolded False by simp
    have exponent:
      "?k = decimal_digit_count ?q"
      using count_step by simp
    have reverse_unfolded:
      "decimal_reverse n =
        (if n < 10 then n else
          n mod 10 * 10^(decimal_digit_count n - 1) +
            decimal_reverse (n div 10))"
      by (rule decimal_reverse.simps)
    have reverse_step:
      "decimal_reverse n = ?r * 10^?k + decimal_reverse ?q"
      using reverse_unfolded False exponent by simp
    have source_step: "n = 10 * ?q + ?r"
      by (simp add: div_mult_mod_eq mult.commute)
    have reversed_residue:
      "decimal_reverse n mod 9 = (?r + ?q) mod 9"
    proof -
      have product:
        "(?r * 10^?k) mod 9 = (?r mod 9)"
      proof -
        have factor:
          "(?r * 10^?k) mod 9 =
            ((?r mod 9) * ((10::nat)^?k mod 9)) mod 9"
          by (rule mod_mult_eq[symmetric])
        show ?thesis
          using factor power
          by (simp only: factor power mult_1_right mod_mod_trivial)
      qed
      have sum:
        "(?r * 10^?k + decimal_reverse ?q) mod 9 =
          ((?r * 10^?k) mod 9 +
            (decimal_reverse ?q mod 9)) mod 9"
        by (rule mod_add_eq[symmetric])
      have reverse_mod_step:
        "decimal_reverse n mod 9 =
          (?r * 10^?k + decimal_reverse ?q) mod 9"
        by (rule arg_cong[where f="\<lambda>value. value mod 9"])
          (rule reverse_step)
      have reduced_sum:
        "(?r * 10^?k + decimal_reverse ?q) mod 9 = (?r + ?q) mod 9"
      proof -
        have "(?r * 10^?k + decimal_reverse ?q) mod 9 =
            ((?r * 10^?k) mod 9 +
              (decimal_reverse ?q mod 9)) mod 9"
          by (rule sum)
        also have "... = ((?r mod 9) + (?q mod 9)) mod 9"
          by (simp only: product reverse_quotient)
        also have "... = (?r + ?q) mod 9"
          by (rule mod_add_eq)
        finally show ?thesis .
      qed
      show ?thesis by (rule trans[OF reverse_mod_step reduced_sum])
    qed
    have source_residue:
      "n mod 9 = (?r + ?q) mod 9"
    proof -
      have product: "(10 * ?q) mod 9 = ?q mod 9"
      proof -
        have factor:
          "(10 * ?q) mod 9 = ((10 mod 9) * (?q mod 9)) mod 9"
          by (rule mod_mult_eq[symmetric])
        have ten: "10 mod 9 = (1::nat)" by simp
        have reduced:
          "((10 mod 9) * (?q mod 9)) mod 9 = ?q mod 9"
          using ten by (simp only: ten mult_1_left mod_mod_trivial)
        show ?thesis by (rule trans[OF factor reduced])
      qed
      have sum: "(10 * ?q + ?r) mod 9 =
          ((10 * ?q) mod 9 + ?r mod 9) mod 9"
        by (rule mod_add_eq[symmetric])
      have source_mod_step:
        "n mod 9 = (10 * ?q + ?r) mod 9"
        by (rule arg_cong[where f="\<lambda>value. value mod 9"])
          (rule source_step)
      have reduced_sum:
        "(10 * ?q + ?r) mod 9 = (?r + ?q) mod 9"
      proof -
        have "(10 * ?q + ?r) mod 9 =
            ((10 * ?q) mod 9 + ?r mod 9) mod 9"
          by (rule sum)
        also have "... = (?q mod 9 + ?r mod 9) mod 9"
          by (simp only: product)
        also have "... = (?q + ?r) mod 9"
          by (rule mod_add_eq)
        also have "... = (?r + ?q) mod 9"
          by (simp add: add.commute)
        finally show ?thesis .
      qed
      show ?thesis by (rule trans[OF source_mod_step reduced_sum])
    qed
    show ?thesis
      by (rule trans[OF reversed_residue source_residue[symmetric]])
  qed
qed

lemma five_mod45_determined_by_mod_nine:
  fixes n :: nat
  shows
  "(5 * n) mod 45 = (5 * (n mod 9)) mod 45"
proof -
  let ?q = "n div 9"
  let ?r = "n mod 9"
  have decomposition: "n = 9 * ?q + ?r"
    by presburger
  have product:
    "5 * n = 5 * (9 * ?q + ?r)"
    by (rule arg_cong[where f="\<lambda>value. 5 * value"]) (rule decomposition)
  have modulo:
    "(5 * n) mod 45 = (5 * (9 * ?q + ?r)) mod 45"
    by (rule arg_cong[where f="\<lambda>value. value mod 45"]) (rule product)
  have expanded: "5 * (9 * ?q + ?r) = 45 * ?q + 5 * ?r"
    using decomposition by presburger
  show ?thesis
    using modulo expanded
    by (simp only: modulo expanded mod_mult_self4)
qed

lemma five_mod_nine_determined_by_mod_nine:
  fixes n :: nat
  shows
  "(5 * n) mod 9 = (5 * (n mod 9)) mod 9"
proof -
  let ?q = "n div 9"
  let ?r = "n mod 9"
  have decomposition: "n = 9 * ?q + ?r"
    by presburger
  have product:
    "5 * n = 5 * (9 * ?q + ?r)"
    by (rule arg_cong[where f="\<lambda>value. 5 * value"]) (rule decomposition)
  have modulo:
    "(5 * n) mod 9 = (5 * (9 * ?q + ?r)) mod 9"
    by (rule arg_cong[where f="\<lambda>value. value mod 9"]) (rule product)
  have expanded: "5 * (9 * ?q + ?r) = 9 * (5 * ?q) + 5 * ?r"
    using decomposition by presburger
  show ?thesis
    using modulo expanded
    by (simp only: modulo expanded mod_mult_self4)
qed

lemma five_mod45_clock_residue:
  fixes r :: nat
  assumes "r < 9"
  shows "(5 * r) mod 45 = (10 * ((5 * r) mod 9)) mod 45"
proof -
  have residue_cases:
    "r = 0 \<or> r = 1 \<or> r = 2 \<or> r = 3 \<or> r = 4 \<or>
     r = 5 \<or> r = 6 \<or> r = 7 \<or> r = 8"
    using assms by presburger
  show ?thesis using residue_cases by auto
qed

lemma five_reverse_step_mod_nine:
  "five_reverse_step n mod 9 = (5 * n) mod 9"
proof -
  have product:
    "(5 * decimal_reverse n) mod 9 =
      ((5 mod 9) * (decimal_reverse n mod 9)) mod 9"
    by (rule mod_mult_eq[symmetric])
  have reverse_product:
    "(5 * decimal_reverse n) mod 9 =
      ((5 mod 9) * (n mod 9)) mod 9"
    using product decimal_reverse_mod_nine[of n]
    by (simp only: product decimal_reverse_mod_nine[of n])
  have source_product:
    "(5 * n) mod 9 = ((5 mod 9) * (n mod 9)) mod 9"
    by (rule mod_mult_eq[symmetric])
  show ?thesis
    using reverse_product source_product
    by (simp only: five_reverse_step_def reverse_product source_product)
qed

lemma five_reverse_step_mod45:
  "five_reverse_step n mod 45 =
    (10 * ((5 * n) mod 9)) mod 45"
proof -
  have exact_five:
    "five_reverse_step n mod 45 =
      (5 * (decimal_reverse n mod 9)) mod 45"
    unfolding five_reverse_step_def
    by (rule five_mod45_determined_by_mod_nine)
  have source_residue:
    "(5 * n) mod 9 = (5 * (n mod 9)) mod 9"
    by (rule five_mod_nine_determined_by_mod_nine)
  have clock:
    "(5 * (n mod 9)) mod 45 =
      (10 * ((5 * (n mod 9)) mod 9)) mod 45"
    by (rule five_mod45_clock_residue) simp
  have reverse_residue: "decimal_reverse n mod 9 = n mod 9"
    by (rule decimal_reverse_mod_nine)
  have exact_source:
    "five_reverse_step n mod 45 = (5 * (n mod 9)) mod 45"
    using exact_five reverse_residue
    by (simp only: exact_five reverse_residue)
  have transported_clock:
    "(10 * ((5 * n) mod 9)) mod 45 =
      (10 * ((5 * (n mod 9)) mod 9)) mod 45"
    using source_residue by (simp only: source_residue)
  show ?thesis
    using exact_source clock transported_clock
    by (simp only: exact_source clock transported_clock)
qed

lemma five_reverse_orbit_mod_nine:
  "five_reverse_orbit n seed mod 9 = (seed * 5^n) mod 9"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have step:
    "five_reverse_step (five_reverse_orbit n seed) mod 9 =
      (5 * five_reverse_orbit n seed) mod 9"
    by (rule five_reverse_step_mod_nine)
  have power: "(seed * 5^Suc n) mod 9 =
      (5 * (seed * 5^n)) mod 9"
    by (simp only: power_Suc; simp add: algebra_simps)
  have product_transport:
    "(5 * five_reverse_orbit n seed) mod 9 =
      (5 * (seed * 5^n)) mod 9"
  proof -
    have left:
      "(5 * five_reverse_orbit n seed) mod 9 =
        ((5 mod 9) * (five_reverse_orbit n seed mod 9)) mod 9"
      by (rule mod_mult_eq[symmetric])
    have right:
      "(5 * (seed * 5^n)) mod 9 =
        ((5 mod 9) * ((seed * 5^n) mod 9)) mod 9"
      by (rule mod_mult_eq[symmetric])
    show ?thesis using left right Suc.IH
      by (simp only: left right Suc.IH)
  qed
  show ?case
    unfolding five_reverse_orbit.simps(2)
    using step product_transport power
    by (simp only: step product_transport power)
qed

theorem five_reverse_orbit_mod45:
  assumes "0 < n"
  shows "five_reverse_orbit n seed mod 45 =
    (10 * ((seed * 5^n) mod 9)) mod 45"
proof -
  obtain k where n: "n = Suc k" using assms by (cases n) auto
  have step:
    "five_reverse_orbit n seed mod 45 =
      (10 * ((5 * five_reverse_orbit k seed) mod 9)) mod 45"
    unfolding n five_reverse_orbit.simps
    by (rule five_reverse_step_mod45)
  have orbit_mod_nine:
    "five_reverse_orbit k seed mod 9 = (seed * 5^k) mod 9"
    by (rule five_reverse_orbit_mod_nine)
  have exponent:
    "(5 * (seed * 5^k)) mod 9 = (seed * 5^n) mod 9"
    unfolding n by (simp only: power_Suc; simp add: algebra_simps)
  have reduced:
    "(5 * five_reverse_orbit k seed) mod 9 =
      (5 * (five_reverse_orbit k seed mod 9)) mod 9"
    by (rule five_mod_nine_determined_by_mod_nine)
  have orbit_product:
    "(5 * five_reverse_orbit k seed) mod 9 =
      (5 * (seed * 5^k)) mod 9"
  proof -
    have prefix:
      "(5 * (five_reverse_orbit k seed mod 9)) mod 9 =
        (5 * ((seed * 5^k) mod 9)) mod 9"
      by (simp only: orbit_mod_nine)
    have suffix:
      "(5 * ((seed * 5^k) mod 9)) mod 9 =
        (5 * (seed * 5^k)) mod 9"
      by (rule mod_mult_right_eq)
    have joined:
      "(5 * five_reverse_orbit k seed) mod 9 =
        (5 * ((seed * 5^k) mod 9)) mod 9"
      by (rule trans[OF reduced prefix])
    show ?thesis by (rule trans[OF joined suffix])
  qed
  have clock_transport:
    "(10 * ((5 * five_reverse_orbit k seed) mod 9)) mod 45 =
      (10 * ((5 * (seed * 5^k)) mod 9)) mod 45"
    by (rule arg_cong[where f="\<lambda>value. (10 * value) mod 45"])
      (rule orbit_product)
  show ?thesis using step clock_transport exponent by simp
qed

ML \<open>
  val checked = @{thms decimal_ten_power_mod_nine decimal_reverse_mod_nine
    five_mod45_determined_by_mod_nine
    five_mod_nine_determined_by_mod_nine five_mod45_clock_residue
    five_reverse_step_mod_nine five_reverse_step_mod45
    five_reverse_orbit_mod_nine five_reverse_orbit_mod45};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Five-reverse modular proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped five-reverse modular proof" else ();
\<close>

end
