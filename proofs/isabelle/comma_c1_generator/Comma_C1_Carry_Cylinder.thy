theory Comma_C1_Carry_Cylinder
  imports Comma_C1_Return
begin

text \<open>Only a finite high-prefix residue is retained at any requested
precision. Successive precisions commute with reduction, giving compatible
finite views of the same additive c1 return. The carry lookup below is for
one represented fixed-sector segment. It does not select a legal comma child
at a fork, prove harmonic or Entry-phase safety, or establish future native
round safety.\<close>

definition comma_c1_apply_cylinder ::
  "nat \<Rightarrow> comma_c1_return \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_apply_cylinder r R h = (h + c1_count R) mod 10 ^ r"

lemma comma_c1_cylinder_power_exact:
  "comma_c1_apply_cylinder r (comma_c1_return C n) (H mod 10 ^ r) =
    (H + comma_c1_count C n) mod 10 ^ r"
proof -
  let ?M = "10 ^ r"
  have head: "(H mod ?M) mod ?M = H mod ?M" by simp
  have sum: "(H mod ?M + comma_c1_count C n) mod ?M =
      (H + comma_c1_count C n) mod ?M"
    by (rule mod_add_cong[OF head refl])
  show ?thesis
    unfolding comma_c1_apply_cylinder_def comma_c1_return_def
    using sum by simp
qed

lemma comma_c1_cylinder_projection:
  "comma_c1_apply_cylinder r R (H mod 10 ^ r) =
    comma_c1_apply_cylinder (Suc r) R (H mod 10 ^ Suc r) mod 10 ^ r"
proof -
  have divides: "(10::nat) ^ r dvd 10 ^ Suc r"
    by (simp add: power_Suc)
  have head: "(H mod 10 ^ Suc r) mod 10 ^ r = H mod 10 ^ r"
    by (rule mod_mod_cancel[OF divides])
  have head_same:
    "(H mod 10 ^ Suc r) mod 10 ^ r =
      (H mod 10 ^ r) mod 10 ^ r"
    using head by simp
  have sum:
    "(H mod 10 ^ Suc r + c1_count R) mod 10 ^ r =
      (H mod 10 ^ r + c1_count R) mod 10 ^ r"
    by (rule mod_add_cong[OF head_same refl])
  show ?thesis
    unfolding comma_c1_apply_cylinder_def
    using divides sum by (simp only: mod_mod_cancel[OF divides])
qed

definition comma_carry_wire ::
  "nat \<Rightarrow> comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_carry_wire j C H n =
    (if j = 0 then comma_c0 (c1_target (comma_c1_return C n))
     else if j = 1 then comma_c1 (c1_target (comma_c1_return C n))
     else comma_c1 (c1_target (comma_c1_return C n)) \<and>
       (H + c1_count (comma_c1_return C n) + 1) mod 10 ^ (j - 1) = 0)"

lemma comma_carry_wire_powered:
  "comma_carry_wire j C H n =
    (if j = 0 then comma_c0 (comma_c1_iter n C)
     else if j = 1 then comma_c1 (comma_c1_iter n C)
     else comma_c1 (comma_c1_iter n C) \<and>
       (H + comma_c1_count C n + 1) mod 10 ^ (j - 1) = 0)"
  by (simp add: comma_carry_wire_def comma_c1_return_def)

text \<open>A carry into the high prefix propagates through exactly those
literal decimal columns of H whose digits are all nine. This recursive
column test is the physical addition view; the modular cylinder is its finite
closed-form projection.\<close>

fun comma_literal_prefix_nines :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_literal_prefix_nines 0 H = True"
| "comma_literal_prefix_nines (Suc r) H =
     (H mod 10 = 9 \<and> comma_literal_prefix_nines r (H div 10))"

lemma comma_literal_increment_mod_split:
  fixes H r :: nat
  shows "(H + 1) mod 10 ^ Suc r = 0 \<longleftrightarrow>
    H mod 10 = 9 \<and> (H div 10 + 1) mod 10 ^ r = 0"
proof -
  let ?q = "H div 10"
  let ?d = "H mod 10"
  have split: "H = 10 * ?q + ?d" by (simp add: mult.commute)
  have d_bound: "?d < 10" by simp
  have modulus: "(10::nat) ^ Suc r = 10 * 10 ^ r"
    by (simp add: power_Suc mult.commute)
  show ?thesis
  proof (cases "?d = 9")
    case True
    have increment: "H + 1 = 10 * (?q + 1)"
      using split True by arith
    have scaled_mod:
      "(10 * (?q + 1)) mod (10 * 10 ^ r) =
        10 * ((?q + 1) mod 10 ^ r)"
      by (simp add: mod_mult2_eq)
    show ?thesis
      using True increment scaled_mod modulus
      by (simp only: modulus increment scaled_mod True; simp)
  next
    case False
    have d_inc_bound: "?d + 1 < 10"
      using d_bound False by arith
    have increment: "H + 1 = 10 * ?q + (?d + 1)"
      using split by arith
    have low_digit: "(H + 1) mod 10 = ?d + 1"
      by (simp only: increment mod_mult_self4;
          rule mod_less[OF d_inc_bound])
    have full_split:
      "(H + 1) mod (10 * 10 ^ r) =
        10 * ((H + 1) div 10 mod 10 ^ r) + (H + 1) mod 10"
      by (rule mod_mult2_eq)
    have nonzero: "(H + 1) mod (10 * 10 ^ r) \<noteq> 0"
      using full_split low_digit d_inc_bound by arith
    show ?thesis
      using False nonzero modulus
      by (simp only: modulus False nonzero; simp)
  qed
qed

lemma comma_literal_prefix_nines_iff:
  "comma_literal_prefix_nines r H \<longleftrightarrow>
    (H + 1) mod 10 ^ r = 0"
proof (induction r arbitrary: H)
  case 0
  then show ?case by simp
next
  case (Suc r)
  have increment:
    "(H + 1) mod 10 ^ Suc r = 0 \<longleftrightarrow>
      H mod 10 = 9 \<and> (H div 10 + 1) mod 10 ^ r = 0"
    by (rule comma_literal_increment_mod_split)
  have induction:
    "comma_literal_prefix_nines r (H div 10) \<longleftrightarrow>
      (H div 10 + 1) mod 10 ^ r = 0"
    using Suc.IH[of "H div 10"] .
  show ?case
    by (simp only: comma_literal_prefix_nines.simps(2) increment induction)
qed

definition comma_literal_carry_wire ::
  "nat \<Rightarrow> comma_c1_phase \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_literal_carry_wire j C H =
    (let f = c1_sector C;
         x = comma_c1_decode (c1_mod4 C) (c1_mod25 C);
         d = x mod 10;
         t = x div 10;
         c0 = (10 \<le> d + f);
         c1 = (10 \<le> t + d + (if c0 then 1 else 0))
     in if j = 0 then c0
        else if j = 1 then c1
        else c1 \<and> comma_literal_prefix_nines (j - 1) H)"

definition comma_literal_column_sum_carry ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_literal_column_sum_carry j source increment =
    ((source mod 10 ^ Suc j + increment mod 10 ^ Suc j) div
      10 ^ Suc j = 1)"

lemma comma_literal_carry_wire_phase:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_literal_carry_wire j C H =
    (if j = 0 then comma_c0 C
     else if j = 1 then comma_c1 C
     else comma_c1 C \<and> (H + 1) mod 10 ^ (j - 1) = 0)"
proof -
  let ?f = "c1_sector C"
  let ?x = "comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
  have x_bound: "?x < 100"
    by (simp add: comma_c1_decode_def)
  have phase: "C = comma_c1_phase_of ?f ?x"
    using comma_c1_phase_of_decode[OF admitted] by simp
  have c0: "comma_c0 C \<longleftrightarrow> 10 \<le> ?x mod 10 + ?f"
    by (rule comma_c0_exact[OF x_bound phase])
  have c1: "comma_c1 C \<longleftrightarrow>
      10 \<le> ?x div 10 + ?x mod 10 +
        (if 10 \<le> ?x mod 10 + ?f then 1 else 0)"
    by (rule comma_c1_exact[OF x_bound phase])
  show ?thesis
  proof (cases "j = 0")
    case True
    then show ?thesis
      unfolding comma_literal_carry_wire_def
      using c0 by (simp add: Let_def)
  next
    case not_zero: False
    show ?thesis
    proof (cases "j = 1")
      case True
      then show ?thesis
        unfolding comma_literal_carry_wire_def
        using c0 c1 by (simp add: Let_def)
    next
      case not_one: False
      have nines:
        "comma_literal_prefix_nines (j - 1) H =
          ((H + 1) mod 10 ^ (j - 1) = 0)"
        by (rule comma_literal_prefix_nines_iff)
      show ?thesis
        unfolding comma_literal_carry_wire_def
        using c0 c1 nines not_zero not_one
        by (simp add: Let_def)
    qed
  qed
qed

lemma comma_literal_carry_wire_column_sum:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_literal_carry_wire j C H =
    comma_literal_column_sum_carry j
      (100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C))
      (10 * ((100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C)) mod 10) +
        c1_sector C)"
proof -
  let ?f = "c1_sector C"
  let ?x = "comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
  let ?k = "100 * H + ?x"
  let ?a = "10 * (?k mod 10) + ?f"
  have x_bound: "?x < 100"
    by (simp add: comma_c1_decode_def)
  have f_bound: "?f \<le> 9"
    using admitted by (simp add: comma_c1_phase_admitted_def)
  have d_bound: "?x mod 10 < 10" by simp
  have f_lt: "?f < 10" using f_bound by arith
  have increment: "?a = 10 * (?x mod 10) + ?f"
    by (simp add: comma_decimal_high_mod10)
  have increment_bound: "?a < 100"
    using d_bound f_bound increment by arith
  have k_unit: "?k mod 10 = ?x mod 10"
    by (simp add: comma_decimal_high_mod10)
  have k_low2: "?k mod 100 = ?x"
  proof -
    have "?k mod 100 =
        ((100 * H) mod 100 + ?x mod 100) mod 100"
      by (rule mod_add_eq[symmetric])
    also have "... = ?x" using x_bound by simp
    finally show ?thesis .
  qed
  have phase: "C = comma_c1_phase_of ?f ?x"
    using comma_c1_phase_of_decode[OF admitted] by simp
  have c0_exact: "comma_c0 C \<longleftrightarrow> 10 \<le> ?x mod 10 + ?f"
    by (rule comma_c0_exact[OF x_bound phase])
  show ?thesis
  proof (cases "j = 0")
    case zero: True
    have q0:
      "(?k mod 10 + ?a mod 10) div 10 =
        (if 10 \<le> ?x mod 10 + ?f then 1 else 0)"
    proof -
      have a_unit: "?a mod 10 = ?f"
        using increment f_lt by simp
      have sum_bound: "?x mod 10 + ?f < 20"
        using d_bound f_bound by arith
      have quotient:
        "(?x mod 10 + ?f) div 10 =
          (if 10 \<le> ?x mod 10 + ?f then 1 else 0)"
        by (rule comma_nat_div10_lt20[OF sum_bound])
      show ?thesis using k_unit a_unit quotient by simp
    qed
    show ?thesis
      using zero c0_exact q0
      by (simp add: comma_literal_carry_wire_def
          comma_literal_column_sum_carry_def Let_def)
  next
    case not_zero: False
    show ?thesis
    proof (cases "j = 1")
      case one: True
      have next_low: "comma_c1_decode
          (c1_mod4 (comma_c1_step C)) (c1_mod25 (comma_c1_step C)) < 100"
        by (simp add: comma_c1_decode_def)
      have local:
        "?x + 10 * (?x mod 10) + ?f =
          100 * (if comma_c1 C then 1 else 0) +
            comma_c1_decode (c1_mod4 (comma_c1_step C))
              (c1_mod25 (comma_c1_step C))"
        by (rule comma_c1_spatiotemporal_step[OF x_bound phase f_bound])
      have quotient:
        "(?x + ?a) div 100 = (if comma_c1 C then 1 else 0)"
      proof -
        have exact_sum:
          "?x + ?a = 100 * (if comma_c1 C then 1 else 0) +
            comma_c1_decode (c1_mod4 (comma_c1_step C))
              (c1_mod25 (comma_c1_step C))"
          using local increment by (simp add: algebra_simps)
        show ?thesis using exact_sum next_low by simp
      qed
      have a_low2: "?a mod 100 = ?a"
        by (rule mod_less[OF increment_bound])
      have column_one:
        "comma_literal_column_sum_carry 1 ?k ?a = comma_c1 C"
        using quotient k_low2 a_low2
        by (simp add: comma_literal_column_sum_carry_def)
      have phase_projection:
        "comma_literal_carry_wire 1 C H = comma_c1 C"
        using comma_literal_carry_wire_phase[OF admitted, of 1 H]
        by simp
      show ?thesis using one column_one phase_projection by simp
    next
      case not_one: False
      obtain j' where j_suc: "j = Suc j'"
        using not_zero by (cases j) auto
      have j'_nonzero: "j' \<noteq> 0"
        using not_one j_suc by auto
      obtain r where j_value: "j = Suc (Suc r)"
        using j_suc j'_nonzero by (cases j') auto
      let ?M = "(10::nat) ^ Suc r"
      let ?c = "if comma_c1 C then (1::nat) else 0"
      have exponent: "Suc j = 2 + Suc r"
        using j_value by simp
      have modulus: "(10::nat) ^ Suc j = 100 * ?M"
      proof -
        have "(10::nat) ^ Suc j = (10::nat) ^ (2 + Suc r)"
          by (simp only: exponent)
        also have "... = (10::nat) ^ 2 * (10::nat) ^ Suc r"
          by (simp only: power_add)
        also have "... = 100 * ?M" by simp
        finally show ?thesis .
      qed
      have k_split:
        "?k mod (100 * ?M) = 100 * (H mod ?M) + ?x"
      proof -
        have split:
          "?k mod (100 * ?M) =
            100 * (?k div 100 mod ?M) + ?k mod 100"
          by (rule mod_mult2_eq)
        have quotient: "?k div 100 = H"
          using x_bound by simp
        show ?thesis using split quotient k_low2 by simp
      qed
      have modulus_large: "100 \<le> 100 * ?M" by simp
      have a_residue: "?a mod (100 * ?M) = ?a"
        by (rule mod_less) (use increment_bound modulus_large in arith)
      have local:
        "?x + 10 * (?x mod 10) + ?f =
          100 * ?c +
            comma_c1_decode (c1_mod4 (comma_c1_step C))
              (c1_mod25 (comma_c1_step C))"
        by (rule comma_c1_spatiotemporal_step[OF x_bound phase f_bound])
      have next_low:
        "comma_c1_decode (c1_mod4 (comma_c1_step C))
           (c1_mod25 (comma_c1_step C)) < 100"
        by (simp add: comma_c1_decode_def)
      have sum_split:
        "?k mod (100 * ?M) + ?a mod (100 * ?M) =
          100 * (H mod ?M + ?c) +
            comma_c1_decode (c1_mod4 (comma_c1_step C))
              (c1_mod25 (comma_c1_step C))"
        using k_split a_residue local increment by (simp add: algebra_simps)
      have sum_quotient:
        "(100 * (H mod ?M + ?c) +
            comma_c1_decode (c1_mod4 (comma_c1_step C))
              (c1_mod25 (comma_c1_step C))) div (100 * ?M) =
          (H mod ?M + ?c) div ?M"
      proof -
        have low_quotient:
          "(100 * (H mod ?M + ?c) +
              comma_c1_decode (c1_mod4 (comma_c1_step C))
                (c1_mod25 (comma_c1_step C))) div 100 = H mod ?M + ?c"
          using next_low by simp
        show ?thesis by (simp only: div_mult2_eq low_quotient)
      qed
      have h_bound: "H mod ?M < ?M" by simp
      have residue_link:
        "(H mod ?M + 1) mod ?M = (H + 1) mod ?M"
      proof -
        have residue: "(H mod ?M) mod ?M = H mod ?M" by simp
        show ?thesis by (rule mod_add_cong[OF residue refl])
      qed
      have high_quotient:
        "(H mod ?M + ?c) div ?M =
          (if comma_c1 C \<and> (H + 1) mod ?M = 0 then 1 else 0)"
      proof (cases "comma_c1 C")
        case False
        then show ?thesis using h_bound by simp
      next
        case c1_true: True
        show ?thesis
        proof (cases "H mod ?M + 1 = ?M")
          case full_prefix: True
          then show ?thesis using c1_true residue_link by simp
        next
          case partial_prefix: False
          have lower: "H mod ?M + 1 < ?M"
            using h_bound partial_prefix by arith
          have residue: "(H + 1) mod ?M = H mod ?M + 1"
            using residue_link lower by simp
          show ?thesis using c1_true partial_prefix lower residue by simp
        qed
      qed
      have literal_formula:
        "comma_literal_carry_wire j C H =
          (comma_c1 C \<and> (H + 1) mod ?M = 0)"
        using comma_literal_carry_wire_phase[OF admitted, of j H] j_value
        by simp
      show ?thesis
        using j_value modulus sum_split sum_quotient high_quotient
          literal_formula
        by (simp add: comma_literal_column_sum_carry_def)
    qed
  qed
qed

lemma comma_carry_wire_literal_return:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_carry_wire j C H n =
    comma_literal_carry_wire j
      (c1_target (comma_c1_return C n))
      (H + c1_count (comma_c1_return C n))"
proof -
  have target_admitted:
    "comma_c1_phase_admitted (c1_target (comma_c1_return C n))"
    using comma_c1_iter_closed[OF admitted, of n]
    by (simp add: comma_c1_return_def)
  note literal = comma_literal_carry_wire_phase
    [OF target_admitted, of j "H + c1_count (comma_c1_return C n)"]
  show ?thesis
    using literal
    by (simp add: comma_carry_wire_powered comma_c1_return_def)
qed

lemma comma_carry_wire_column_sum_return:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_carry_wire j C H n =
    comma_literal_column_sum_carry j
      (100 * (H + c1_count (comma_c1_return C n)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return C n)))
          (c1_mod25 (c1_target (comma_c1_return C n))))
      (10 * ((100 * (H + c1_count (comma_c1_return C n)) +
          comma_c1_decode
            (c1_mod4 (c1_target (comma_c1_return C n)))
            (c1_mod25 (c1_target (comma_c1_return C n)))) mod 10) +
        c1_sector (c1_target (comma_c1_return C n)))"
proof -
  have target_admitted:
    "comma_c1_phase_admitted (c1_target (comma_c1_return C n))"
    using comma_c1_iter_closed[OF admitted, of n]
    by (simp add: comma_c1_return_def)
  note local = comma_literal_carry_wire_column_sum
    [OF target_admitted, of j
      "H + c1_count (comma_c1_return C n)"]
  note powered = comma_carry_wire_literal_return[OF admitted, of j H n]
  show ?thesis using local powered by simp
qed

lemma comma_carry_wire_literal_iter:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_carry_wire j C H n =
    comma_literal_carry_wire j (comma_c1_iter n C)
      (H + comma_c1_count C n)"
  using comma_carry_wire_literal_return[OF admitted, of j H n]
  by (simp add: comma_c1_return_def)

lemma comma_carry_prefix_extensional:
  assumes "H1 mod 10 ^ r = H2 mod 10 ^ r"
  shows "\<forall>j \<le> r + 1.
      comma_carry_wire j C H1 n = comma_carry_wire j C H2 n"
proof (intro allI impI)
  fix j
  assume j: "j \<le> r + 1"
  show "comma_carry_wire j C H1 n = comma_carry_wire j C H2 n"
  proof (cases "j < 2")
    case True
    then have "j = 0 \<or> j = 1" by arith
    then show ?thesis by (elim disjE) (simp_all add: comma_carry_wire_powered)
  next
    case False
    have exponent: "j - 1 \<le> r" using j False by arith
    have exp_split: "r = (j - 1) + (r - (j - 1))"
      using exponent by arith
    have modulus_divides: "(10::nat) ^ (j - 1) dvd 10 ^ r"
    proof -
      have factor:
        "(10::nat) ^ r = (10::nat) ^ (j - 1) * (10::nat) ^ (r - (j - 1))"
      proof -
        have exponent:
          "(10::nat) ^ r =
            (10::nat) ^ ((j - 1) + (r - (j - 1)))"
          by (rule arg_cong[where f="\<lambda>e. (10::nat) ^ e", OF exp_split])
        have power_split:
          "(10::nat) ^ ((j - 1) + (r - (j - 1))) =
            (10::nat) ^ (j - 1) * (10::nat) ^ (r - (j - 1))"
          by (rule power_add)
        show ?thesis by (rule trans[OF exponent power_split])
      qed
      show ?thesis unfolding dvd_def using factor by blast
    qed
    have high_residue: "H1 mod 10 ^ (j - 1) = H2 mod 10 ^ (j - 1)"
    proof -
      have "(H1 mod 10 ^ r) mod 10 ^ (j - 1) =
          (H2 mod 10 ^ r) mod 10 ^ (j - 1)"
        using assms by (rule arg_cong[where f="\<lambda>z. z mod 10 ^ (j - 1)"])
      then show ?thesis
        by (simp only: mod_mod_cancel[OF modulus_divides])
    qed
    have shifted_first:
      "(H1 + comma_c1_count C n) mod 10 ^ (j - 1) =
       (H2 + comma_c1_count C n) mod 10 ^ (j - 1)"
      by (rule mod_add_cong[OF high_residue refl])
    have shifted:
      "(H1 + comma_c1_count C n + 1) mod 10 ^ (j - 1) =
       (H2 + comma_c1_count C n + 1) mod 10 ^ (j - 1)"
      using shifted_first by (rule mod_add_cong[OF _ refl])
    have j0: "j \<noteq> 0" and j1: "j \<noteq> 1"
      using False by arith+
    show ?thesis
      using shifted j0 j1
      by (simp add: comma_carry_wire_powered)
  qed
qed

ML \<open>
  val checked = @{thms comma_c1_cylinder_power_exact
    comma_c1_cylinder_projection comma_carry_wire_powered
    comma_literal_increment_mod_split comma_literal_prefix_nines_iff
    comma_literal_carry_wire_phase comma_carry_wire_literal_return
    comma_literal_carry_wire_column_sum
    comma_carry_wire_column_sum_return comma_carry_wire_literal_iter
    comma_carry_prefix_extensional};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "C1 carry-cylinder proof depends on an oracle";
\<close>
end
