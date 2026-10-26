theory Comma_C1_Source_Coefficients
  imports Shared_Carry_Dynamics.Shared_Decimal_Cocycle_Core
    Comma_C1_Occurrence
    Comma_C1_Carry_Generator.Comma_C1_Boundary_Carry
begin

text \<open>
The fixed-sector source coefficient view is a producer-owned normalization
morphism. Temporal recurrence is used only inside the proof of the defect;
consumers see a closed powered endpoint, exact carry columns, and the explicit
source-admission guard. Spatial digit index, physical duration, and the
independent 924-phase selector remain distinct coordinates.
\<close>

definition comma_c1_source_integer :: "comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_source_integer C H =
    100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C)"

definition comma_c1_source_integer_at ::
    "comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_source_integer_at C H t =
    comma_fixed_iter (c1_sector C) t (comma_c1_source_integer C H)"

definition comma_c1_source_increment ::
    "comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_source_increment C H t =
    10 * (comma_c1_source_integer_at C H t mod 10) + c1_sector C"

definition comma_c1_source_closed_endpoint ::
    "comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_source_closed_endpoint C H n =
    100 * (H + c1_count (comma_c1_powered_return C n)) +
      comma_c1_decode
        (c1_mod4 (c1_target (comma_c1_powered_return C n)))
        (c1_mod25 (c1_target (comma_c1_powered_return C n)))"

definition comma_c1_source_driver_mass ::
    "nat \<Rightarrow> comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_source_driver_mass j C H n =
    (if j=0 then n * c1_sector C
     else if j=1 then
       (comma_c1_source_closed_endpoint C H n -
          comma_c1_source_integer C H - n * c1_sector C) div 10
     else 0)"

definition comma_c1_source_carry_coefficient ::
    "nat \<Rightarrow> comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_source_carry_coefficient j C H n =
    (if j=0 then
       (comma_c1_source_integer C H mod 10 + n * c1_sector C) div 10
     else if j=1 then c1_count (comma_c1_powered_return C n)
     else (H mod 10^(j-1) + c1_count (comma_c1_powered_return C n)) div
       10^(j-1))"

definition comma_c1_source_raw_coefficient ::
    "nat \<Rightarrow> comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_source_raw_coefficient j C H n =
    decimal_base10_digit j (comma_c1_source_integer C H) +
      comma_c1_source_driver_mass j C H n"

lemma comma_c1_source_closed_endpoint_exact:
  assumes phase: "comma_c1_phase_admitted C"
  shows "comma_c1_source_integer_at C H n =
    comma_c1_source_closed_endpoint C H n"
proof -
  have physical:
    "comma_fixed_iter (c1_sector C) n
        (100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C)) =
      100 * (H + comma_c1_count C n) +
        comma_c1_decode (c1_mod4 (comma_c1_iter n C))
          (c1_mod25 (comma_c1_iter n C))"
    by (rule comma_c1_iter_physical[OF phase, where H=H and n=n])
  have powered:
    "comma_c1_powered_return C n = comma_c1_return C n"
    by (rule comma_c1_powered_return_exact[OF phase])
  show ?thesis
    using physical powered
    by (simp add: comma_c1_source_integer_at_def comma_c1_source_integer_def
        comma_c1_source_closed_endpoint_def comma_c1_return_def)
qed

definition comma_c1_source_normalized_coefficient ::
    "nat \<Rightarrow> comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_source_normalized_coefficient j C H n =
    decimal_base10_digit j (comma_c1_source_closed_endpoint C H n)"

definition comma_c1_source_prior_carry_coefficient ::
    "nat \<Rightarrow> comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_source_prior_carry_coefficient j C H n =
    (if j=0 then 0 else comma_c1_source_carry_coefficient (j-1) C H n)"

lemma comma_c1_phase_return_summary_compose:
  "(comma_c1_iter (m+n) C, comma_c1_count C (m+n)) =
    (comma_c1_iter n (comma_c1_iter m C),
      comma_c1_count C m + comma_c1_count (comma_c1_iter m C) n)"
  by (simp add: comma_c1_iter_add comma_c1_count_add)

definition comma_c1_prior_wire_total ::
    "nat \<Rightarrow> comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_prior_wire_total j C H n =
    (if j=0 then 0 else comma_c1_carry_wire_total (j-1) C H n)"

lemma comma_c1_wire_total_as_sum:
  "comma_c1_carry_wire_total j C H n =
    (\<Sum>t<n. if comma_carry_wire j C H t then 1 else 0)"
  by (induction n) (simp_all add: sum.lessThan_Suc)

lemma comma_c1_source_wire_column_action:
  assumes phase: "comma_c1_phase_admitted C"
  shows "comma_carry_wire j C H t =
      decimal_base10_column_carry j
        (comma_c1_source_integer_at C H t)
        (comma_c1_source_increment C H t)"
proof -
  have physical:
    "comma_c1_source_integer_at C H t =
      100 * (H + c1_count (comma_c1_return C t)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return C t)))
          (c1_mod25 (c1_target (comma_c1_return C t)))"
    using comma_c1_iter_physical[OF phase, where H=H and n=t]
    by (simp add: comma_c1_source_integer_at_def comma_c1_source_integer_def
        comma_c1_return_def)
  have column:
    "comma_carry_wire j C H t =
      decimal_base10_column_carry j
        (100 * (H + c1_count (comma_c1_return C t)) +
          comma_c1_decode
            (c1_mod4 (c1_target (comma_c1_return C t)))
            (c1_mod25 (c1_target (comma_c1_return C t))) )
        (10 * ((100 * (H + c1_count (comma_c1_return C t)) +
          comma_c1_decode
            (c1_mod4 (c1_target (comma_c1_return C t)))
            (c1_mod25 (c1_target (comma_c1_return C t))) ) mod 10) +
          c1_sector (c1_target (comma_c1_return C t)))"
    by (rule comma_carry_wire_column_sum_return[OF phase])
  show ?thesis using physical column
    by (simp add: decimal_base10_column_carry_def
        comma_c1_source_increment_def
        comma_c1_source_integer_at_def comma_c1_return_def
        comma_c1_iter_sector)
qed

lemma comma_c1_source_wire_sum_exact:
  assumes phase: "comma_c1_phase_admitted C"
  shows "(\<Sum>t<n. int
      (if decimal_base10_column_carry j
        (comma_c1_source_integer_at C H t)
        (comma_c1_source_increment C H t) then 1 else 0)) =
    int (comma_c1_carry_wire_total j C H n)"
proof -
  have point:
    "(if decimal_base10_column_carry j
        (comma_c1_source_integer_at C H t)
        (comma_c1_source_increment C H t) then 1 else 0) =
      (if comma_carry_wire j C H t then 1 else 0)" for t
    using comma_c1_source_wire_column_action[OF phase]
    by simp
  have summands:
    "(\<Sum>t<n. int (if decimal_base10_column_carry j
        (comma_c1_source_integer_at C H t)
        (comma_c1_source_increment C H t) then 1 else 0)) =
      (\<Sum>t<n. int (if comma_carry_wire j C H t then 1 else 0))"
    by (rule sum.cong) (auto simp: point)
  have total:
    "comma_c1_carry_wire_total j C H n =
      (\<Sum>t<n. if comma_carry_wire j C H t then 1 else 0)"
    by (rule comma_c1_wire_total_as_sum)
  show ?thesis using summands total by simp
qed

lemma comma_c1_source_driver_mass_exact:
  assumes phase: "comma_c1_phase_admitted C"
  shows "(\<Sum>t<n. int (decimal_base10_digit j
      (comma_c1_source_increment C H t))) =
    int (comma_c1_source_driver_mass j C H n)"
proof -
  have sector_bound: "c1_sector C < 10"
    using phase by (simp add: comma_c1_phase_admitted_def; arith)
  have source_phase:
    "comma_c1_source_integer_at C H t mod 10 =
      (comma_c1_source_integer C H mod 10 + t * c1_sector C) mod 10"
    for t
    by (simp add: comma_c1_source_integer_at_def comma_fixed_iter_phase)
  have increment_bound:
    "comma_c1_source_increment C H t < 100" for t
  proof -
    have digit: "comma_c1_source_integer_at C H t mod 10 < 10" by simp
    show ?thesis using digit sector_bound
      by (simp add: comma_c1_source_increment_def; arith)
  qed
  have displacement_split:
    "comma_period_displacement (c1_sector C)
       (comma_c1_source_integer C H mod 10) n =
      10 * (\<Sum>t<n.
          (comma_c1_source_integer C H mod 10 + t * c1_sector C) mod 10) +
        n * c1_sector C"
  proof (induction n)
    case 0
    then show ?case by (simp add: comma_period_displacement_def)
  next
    case (Suc n)
    then show ?case
      by (simp add: comma_period_displacement_def sum.lessThan_Suc
          algebra_simps)
  qed
  have iteration_displacement:
    "comma_c1_source_integer_at C H n =
      comma_c1_source_integer C H +
        comma_period_displacement (c1_sector C)
          (comma_c1_source_integer C H mod 10) n"
    by (simp add: comma_c1_source_integer_at_def comma_fixed_iter_displacement)
  have endpoint_displacement:
    "comma_c1_source_closed_endpoint C H n =
      comma_c1_source_integer C H +
        comma_period_displacement (c1_sector C)
          (comma_c1_source_integer C H mod 10) n"
    using iteration_displacement comma_c1_source_closed_endpoint_exact[OF phase]
    by simp
  have displacement_endpoint:
    "comma_period_displacement (c1_sector C)
        (comma_c1_source_integer C H mod 10) n =
      comma_c1_source_closed_endpoint C H n - comma_c1_source_integer C H"
    using endpoint_displacement by (simp add: add.commute)
  show ?thesis
  proof (cases j)
    case 0
    have each:
      "decimal_base10_digit 0 (comma_c1_source_increment C H t) =
        c1_sector C" for t
      using sector_bound
      by (simp add: decimal_base10_digit_def comma_c1_source_increment_def)
    have sum:
      "(\<Sum>t<n. int (decimal_base10_digit 0
          (comma_c1_source_increment C H t))) = int (n * c1_sector C)"
      using each by (induction n) (simp_all add: sum.lessThan_Suc algebra_simps)
    show ?thesis using sum 0
      by (simp add: comma_c1_source_driver_mass_def)
  next
    case (Suc j')
    note outer = Suc
    show ?thesis
    proof (cases j')
      case 0
      have each:
        "decimal_base10_digit 1 (comma_c1_source_increment C H t) =
          (comma_c1_source_integer C H mod 10 + t * c1_sector C) mod 10"
        for t
        using source_phase[of t] sector_bound
        by (simp add: decimal_base10_digit_def comma_c1_source_increment_def)
      have driver:
        "(\<Sum>t<n. (comma_c1_source_integer C H mod 10 +
            t * c1_sector C) mod 10) =
          (comma_period_displacement (c1_sector C)
            (comma_c1_source_integer C H mod 10) n -
            n * c1_sector C) div 10"
        using displacement_split by simp
      have driver_closed:
        "(\<Sum>t<n. (comma_c1_source_integer C H mod 10 +
            t * c1_sector C) mod 10) =
          (comma_c1_source_closed_endpoint C H n -
            comma_c1_source_integer C H - n * c1_sector C) div 10"
        using driver displacement_endpoint by simp
      have sum:
        "(\<Sum>t<n. int (decimal_base10_digit 1
            (comma_c1_source_increment C H t))) =
          int ((comma_c1_source_closed_endpoint C H n -
            comma_c1_source_integer C H - n * c1_sector C) div 10)"
        using arg_cong[OF driver_closed, of int]
        by (simp only: of_nat_sum each)
      show ?thesis using sum outer 0
        by (simp add: comma_c1_source_driver_mass_def)
    next
      case (Suc r)
      have exponent_bound: "10 ^ 2 \<le> (10::nat) ^ (Suc (Suc r))"
        by (rule power_increasing; simp)
      have each:
        "decimal_base10_digit (Suc (Suc r))
           (comma_c1_source_increment C H t) = 0" for t
      proof -
        have hundred: "100 \<le> (10::nat) ^ (Suc (Suc r))"
          using exponent_bound by simp
        have small: "comma_c1_source_increment C H t <
            10 ^ (Suc (Suc r))"
          by (rule less_le_trans[OF increment_bound[of t] hundred])
        show ?thesis using small
          by (simp add: decimal_base10_digit_def div_less_iff_less_mult)
      qed
      have sum:
        "(\<Sum>t<n. int (decimal_base10_digit (Suc (Suc r))
            (comma_c1_source_increment C H t))) = 0"
        using each by simp
      show ?thesis using sum outer Suc
        by (simp add: comma_c1_source_driver_mass_def)
    qed
  qed
qed

lemma comma_c1_phase_source_base_z_coefficient_defect_wire:
  assumes phase: "comma_c1_phase_admitted C"
  shows "int (comma_c1_source_raw_coefficient j C H n) -
      int (comma_c1_source_normalized_coefficient j C H n) =
    10 * int (comma_c1_carry_wire_total j C H n) -
      int (comma_c1_prior_wire_total j C H n)"
proof -
  have source_step:
    "comma_c1_source_integer_at C H (Suc t) =
      comma_c1_source_integer_at C H t + comma_c1_source_increment C H t"
    for t
    by (simp add: comma_c1_source_integer_at_def comma_c1_source_increment_def)
  have stream:
    "int (decimal_base10_digit j (comma_c1_source_integer_at C H 0)) +
       (\<Sum>t<n. int (decimal_base10_digit j
          (comma_c1_source_increment C H t))) -
       int (decimal_base10_digit j (comma_c1_source_integer_at C H n)) =
     10 * (\<Sum>t<n. int (if decimal_base10_column_carry j
          (comma_c1_source_integer_at C H t)
          (comma_c1_source_increment C H t) then 1 else 0)) -
       (if j=0 then 0 else
         (\<Sum>t<n. int (if decimal_base10_column_carry (j-1)
          (comma_c1_source_integer_at C H t)
          (comma_c1_source_increment C H t) then 1 else 0)))"
  proof (rule decimal_base10_column_defect_telescope)
    fix t
    assume "t<n"
    show "comma_c1_source_integer_at C H (Suc t) =
        comma_c1_source_integer_at C H t + comma_c1_source_increment C H t"
      by (rule source_step)
  qed
  have wire_j:
    "(\<Sum>t<n. int (if decimal_base10_column_carry j
        (comma_c1_source_integer_at C H t)
        (comma_c1_source_increment C H t) then 1 else 0)) =
      int (comma_c1_carry_wire_total j C H n)"
    by (rule comma_c1_source_wire_sum_exact[OF phase])
  have wire_prev:
    "(if j=0 then 0 else
        (\<Sum>t<n. int (if decimal_base10_column_carry (j-1)
          (comma_c1_source_integer_at C H t)
          (comma_c1_source_increment C H t) then 1 else 0))) =
      int (comma_c1_prior_wire_total j C H n)"
  proof (cases j)
    case 0
    then show ?thesis by (simp add: comma_c1_prior_wire_total_def)
  next
    case (Suc k)
    have sum:
      "(\<Sum>t<n. int (if decimal_base10_column_carry k
          (comma_c1_source_integer_at C H t)
          (comma_c1_source_increment C H t) then 1 else 0)) =
        int (comma_c1_carry_wire_total k C H n)"
      by (rule comma_c1_source_wire_sum_exact[OF phase])
    show ?thesis using Suc sum
      by (simp add: comma_c1_prior_wire_total_def)
  qed
  have raw_start:
    "comma_c1_source_integer_at C H 0 = comma_c1_source_integer C H"
    by (simp add: comma_c1_source_integer_at_def)
  have mass:
    "(\<Sum>t<n. int (decimal_base10_digit j
        (comma_c1_source_increment C H t))) =
      int (comma_c1_source_driver_mass j C H n)"
    by (rule comma_c1_source_driver_mass_exact[OF phase])
  have normalized:
    "comma_c1_source_normalized_coefficient j C H n =
      decimal_base10_digit j (comma_c1_source_integer_at C H n)"
    using comma_c1_source_closed_endpoint_exact[OF phase]
    by (simp add: comma_c1_source_normalized_coefficient_def)
  show "int (comma_c1_source_raw_coefficient j C H n) -
      int (comma_c1_source_normalized_coefficient j C H n) =
    10 * int (comma_c1_carry_wire_total j C H n) -
      int (comma_c1_prior_wire_total j C H n)"
    using stream wire_j wire_prev raw_start mass normalized
    by (simp add: comma_c1_source_raw_coefficient_def
        comma_c1_source_normalized_coefficient_def)
qed

theorem comma_c1_source_base_z_coefficient_defect_wire:
  assumes admitted: "comma_c1_source_admitted C H p n"
  shows "int (comma_c1_source_raw_coefficient j C H n) -
      int (comma_c1_source_normalized_coefficient j C H n) =
    10 * int (comma_c1_carry_wire_total j C H n) -
      int (comma_c1_prior_wire_total j C H n)"
    and "comma_literal_path n (comma_c1_source_integer C H)
      (comma_c1_source_closed_endpoint C H n)"
proof -
  have phase: "comma_c1_phase_admitted C"
    using admitted by (simp add: comma_c1_source_admitted_def)
  show "int (comma_c1_source_raw_coefficient j C H n) -
      int (comma_c1_source_normalized_coefficient j C H n) =
    10 * int (comma_c1_carry_wire_total j C H n) -
      int (comma_c1_prior_wire_total j C H n)"
    by (rule comma_c1_phase_source_base_z_coefficient_defect_wire[OF phase])
  show "comma_literal_path n (comma_c1_source_integer C H)
      (comma_c1_source_closed_endpoint C H n)"
    using comma_c1_fixed_sector_powered_occurrence_path(1)[OF admitted]
    by (simp only: comma_c1_source_integer_def comma_c1_source_closed_endpoint_def)
qed



lemma comma_c1_phase_source_carry_coefficient_exact:
  assumes phase: "comma_c1_phase_admitted C"
  shows "comma_c1_carry_wire_total j C H n =
    comma_c1_source_carry_coefficient j C H n"
proof -
  show ?thesis
  proof (cases j)
    case 0
    have defect:
      "int (comma_c1_source_raw_coefficient 0 C H n) -
          int (comma_c1_source_normalized_coefficient 0 C H n) =
        10 * int (comma_c1_carry_wire_total 0 C H n)"
      using comma_c1_phase_source_base_z_coefficient_defect_wire
        [OF phase, where j=0]
      by (simp add: comma_c1_prior_wire_total_def)
    have raw:
      "comma_c1_source_raw_coefficient 0 C H n =
        comma_c1_source_integer C H mod 10 + n * c1_sector C"
      by (simp add: comma_c1_source_raw_coefficient_def
          comma_c1_source_driver_mass_def decimal_base10_digit_def)
    have normalized:
      "comma_c1_source_normalized_coefficient 0 C H n =
        comma_c1_source_closed_endpoint C H n mod 10"
      by (simp add: comma_c1_source_normalized_coefficient_def
          decimal_base10_digit_def)
    have balance_int:
      "int (comma_c1_source_integer C H mod 10 + n * c1_sector C) =
        int (10 * comma_c1_carry_wire_total 0 C H n +
          comma_c1_source_closed_endpoint C H n mod 10)"
      using defect raw normalized by (simp; linarith)
    have balance:
      "comma_c1_source_integer C H mod 10 + n * c1_sector C =
        10 * comma_c1_carry_wire_total 0 C H n +
          comma_c1_source_closed_endpoint C H n mod 10"
      using balance_int by (simp only: of_nat_eq_iff)
    have remainder:
      "comma_c1_source_closed_endpoint C H n mod 10 < 10" by simp
    have quotient:
      "(comma_c1_source_integer C H mod 10 + n * c1_sector C) div 10 =
        comma_c1_carry_wire_total 0 C H n"
      using balance remainder by (simp add: mult.commute)
    show ?thesis using 0 quotient
      by (simp add: comma_c1_source_carry_coefficient_def)
  next
    case (Suc j')
    note outer = Suc
    show ?thesis
    proof (cases j')
      case 0
      have wire_count:
        "comma_c1_carry_wire_total 1 C H n = comma_c1_count C n"
        by (induction n)
          (simp_all add: comma_carry_wire_powered comma_c1_count_suc)
      have powered:
        "comma_c1_powered_return C n = comma_c1_return C n"
        by (rule comma_c1_powered_return_exact[OF phase])
      show ?thesis using outer 0 wire_count powered
        by (simp add: comma_c1_source_carry_coefficient_def
            comma_c1_return_def)
    next
      case (Suc r)
      have width: "2 \<le> Suc (Suc r)" by simp
      have higher:
        "comma_c1_carry_wire_total (Suc (Suc r)) C H n =
          (H mod 10^(Suc (Suc r)-1) + comma_c1_count C n) div
            10^(Suc (Suc r)-1)"
        by (rule comma_c1_carry_wire_total_exact[OF width])
      have powered:
        "comma_c1_powered_return C n = comma_c1_return C n"
        by (rule comma_c1_powered_return_exact[OF phase])
      show ?thesis using outer Suc higher powered
        by (simp add: comma_c1_source_carry_coefficient_def
            comma_c1_return_def)
    qed
  qed
qed

lemma comma_c1_source_carry_coefficient_exact:
  assumes admitted: "comma_c1_source_admitted C H p n"
  shows "comma_c1_carry_wire_total j C H n =
    comma_c1_source_carry_coefficient j C H n"
proof -
  have phase: "comma_c1_phase_admitted C"
    using admitted by (simp add: comma_c1_source_admitted_def)
  show ?thesis
    by (rule comma_c1_phase_source_carry_coefficient_exact[OF phase])
qed

theorem comma_c1_phase_source_base_z_coefficient_defect:
  assumes phase: "comma_c1_phase_admitted C"
  shows "int (comma_c1_source_raw_coefficient j C H n) -
      int (comma_c1_source_normalized_coefficient j C H n) =
    10 * int (comma_c1_source_carry_coefficient j C H n) -
      int (comma_c1_source_prior_carry_coefficient j C H n)"
proof -
  have wire_defect:
    "int (comma_c1_source_raw_coefficient j C H n) -
        int (comma_c1_source_normalized_coefficient j C H n) =
      10 * int (comma_c1_carry_wire_total j C H n) -
        int (comma_c1_prior_wire_total j C H n)"
    by (rule comma_c1_phase_source_base_z_coefficient_defect_wire[OF phase])
  have wire_current:
    "comma_c1_carry_wire_total j C H n =
      comma_c1_source_carry_coefficient j C H n"
    by (rule comma_c1_phase_source_carry_coefficient_exact[OF phase])
  have wire_prior:
    "comma_c1_prior_wire_total j C H n =
      comma_c1_source_prior_carry_coefficient j C H n"
  proof (cases j)
    case 0
    then show ?thesis
      by (simp add: comma_c1_prior_wire_total_def
          comma_c1_source_prior_carry_coefficient_def)
  next
    case (Suc k)
    have previous:
      "comma_c1_carry_wire_total k C H n =
        comma_c1_source_carry_coefficient k C H n"
      by (rule comma_c1_phase_source_carry_coefficient_exact[OF phase])
    show ?thesis using Suc previous
      by (simp add: comma_c1_prior_wire_total_def
          comma_c1_source_prior_carry_coefficient_def)
  qed
  show "int (comma_c1_source_raw_coefficient j C H n) -
      int (comma_c1_source_normalized_coefficient j C H n) =
    10 * int (comma_c1_source_carry_coefficient j C H n) -
      int (comma_c1_source_prior_carry_coefficient j C H n)"
    using wire_defect wire_current wire_prior by simp
qed

theorem comma_c1_source_base_z_coefficient_defect:
  assumes admitted: "comma_c1_source_admitted C H p n"
  shows "int (comma_c1_source_raw_coefficient j C H n) -
      int (comma_c1_source_normalized_coefficient j C H n) =
    10 * int (comma_c1_source_carry_coefficient j C H n) -
      int (comma_c1_source_prior_carry_coefficient j C H n)"
    and "comma_literal_path n (comma_c1_source_integer C H)
      (comma_c1_source_closed_endpoint C H n)"
proof -
  have phase: "comma_c1_phase_admitted C"
    using admitted by (simp add: comma_c1_source_admitted_def)
  show "int (comma_c1_source_raw_coefficient j C H n) -
      int (comma_c1_source_normalized_coefficient j C H n) =
    10 * int (comma_c1_source_carry_coefficient j C H n) -
      int (comma_c1_source_prior_carry_coefficient j C H n)"
    by (rule comma_c1_phase_source_base_z_coefficient_defect[OF phase])
  show "comma_literal_path n (comma_c1_source_integer C H)
      (comma_c1_source_closed_endpoint C H n)"
    by (rule comma_c1_source_base_z_coefficient_defect_wire(2)[OF admitted])
qed


ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms comma_c1_phase_return_summary_compose
        comma_c1_source_closed_endpoint_exact
        comma_c1_source_wire_column_action
        comma_c1_source_wire_sum_exact
        comma_c1_source_driver_mass_exact
        comma_c1_phase_source_base_z_coefficient_defect_wire
        comma_c1_phase_source_carry_coefficient_exact
        comma_c1_phase_source_base_z_coefficient_defect
        comma_c1_source_carry_coefficient_exact
        comma_c1_source_base_z_coefficient_defect_wire
        comma_c1_source_base_z_coefficient_defect}) then ()
    else error "C1 source coefficients depend on an oracle";
\<close>

end
