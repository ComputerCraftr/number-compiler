theory Antihydra_Diagonal_Carry_Refinement
  imports Antihydra_Exact_Run_Candidate_Refinement
    Shared_Carry_Dynamics.Decimal_Normalization_Morphism
begin

text \<open>The physical integer recurrence, the centered source innovation,
and the raw radix-15 moving cut are related through one authenticated family
orbit.  A raw rational floor is not identified with repeated physical
integer flooring.\<close>

fun antihydra_physical_floor_correction :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "antihydra_physical_floor_correction h 0 = 0"
| "antihydra_physical_floor_correction h (Suc n) =
    (3::int)^n * int (h mod 2) +
      2 * antihydra_physical_floor_correction
        (antihydra_family_step h) n"

definition antihydra_centered_innovation :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "antihydra_centered_innovation h n =
    (3::int)^n - (2::int)^n -
      antihydra_physical_floor_correction h n"

definition antihydra_raw_three_halves_quotient :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "antihydra_raw_three_halves_quotient h n = (3^n*h) div 2^n"

definition antihydra_raw_three_halves_remainder :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "antihydra_raw_three_halves_remainder h n = (3^n*h) mod 2^n"

theorem antihydra_physical_carry_tower_exact:
  "(2::int)^n * int (antihydra_family_orbit h n) =
    (3::int)^n * int h - antihydra_physical_floor_correction h n"
proof (induction n arbitrary: h)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?next = "antihydra_family_step h"
  have step:
    "2 * int ?next = 3 * int h - int (h mod 2)"
    by (rule antihydra_family_step_skew_equation)
  have rest:
    "(2::int)^n * int (antihydra_family_orbit ?next n) =
      (3::int)^n * int ?next -
        antihydra_physical_floor_correction ?next n"
    by (rule Suc.IH)
  have recurrence:
    "2 * ((3::int)^n * int ?next -
        antihydra_physical_floor_correction ?next n) =
      (3::int)^(Suc n) * int h -
        antihydra_physical_floor_correction h (Suc n)"
  proof -
    have first:
      "2 * ((3::int)^n * int ?next -
          antihydra_physical_floor_correction ?next n) =
        (3::int)^n * (2 * int ?next) -
          2 * antihydra_physical_floor_correction ?next n"
      by (simp add: algebra_simps)
    also have "... = (3::int)^n * (3 * int h - int (h mod 2)) -
        2 * antihydra_physical_floor_correction ?next n"
      by (simp only: step)
    also have "... = (3::int)^(Suc n) * int h -
        antihydra_physical_floor_correction h (Suc n)"
      by (simp add: antihydra_physical_floor_correction.simps
          power_Suc algebra_simps)
    finally show ?thesis .
  qed
  show ?case
  proof -
    have lift_step:
      "(2::int)^Suc n * int (antihydra_family_orbit h (Suc n)) =
        2 * ((2::int)^n *
          int (antihydra_family_orbit ?next n))"
      by (simp add: power_Suc algebra_simps)
    also have "... = 2 * ((3::int)^n * int ?next -
        antihydra_physical_floor_correction ?next n)"
      using rest by simp
    also have "... = (3::int)^Suc n * int h -
        antihydra_physical_floor_correction h (Suc n)"
      using recurrence by simp
    finally show ?thesis .
  qed
qed

theorem antihydra_physical_decimal_x15_identity:
  "(10::int)^n * int (antihydra_family_orbit h n) =
    (15::int)^n * int h - (5::int)^n *
      antihydra_physical_floor_correction h n"
proof -
  have physical: "(2::int)^n * int (antihydra_family_orbit h n) =
      (3::int)^n * int h - antihydra_physical_floor_correction h n"
    by (rule antihydra_physical_carry_tower_exact)
  have scaled:
    "(5::int)^n * ((2::int)^n *
        int (antihydra_family_orbit h n)) =
      (5::int)^n * ((3::int)^n * int h -
        antihydra_physical_floor_correction h n)"
    by (rule arg_cong[OF physical, of "\<lambda>x. (5::int)^n*x"])
  have power10: "(5::int)^n * (2::int)^n = (10::int)^n"
    using power_mult_distrib[of "5::int" 2 n] by simp
  have power15: "(5::int)^n * (3::int)^n = (15::int)^n"
    using power_mult_distrib[of "5::int" 3 n] by simp
  show ?thesis
    using scaled power10 power15
    by (simp add: power10 power15 algebra_simps)
qed

theorem antihydra_coupled_raw_cut_exact:
  "antihydra_physical_floor_correction h n =
    int (antihydra_raw_three_halves_remainder h n) +
      (2::int)^n *
        (int (antihydra_raw_three_halves_quotient h n) -
          int (antihydra_family_orbit h n))"
proof -
  let ?numerator = "(3::nat)^n*h"
  let ?denominator = "(2::nat)^n"
  let ?quotient = "?numerator div ?denominator"
  let ?remainder = "?numerator mod ?denominator"
  let ?D = "int ?denominator"
  let ?Q = "int ?quotient"
  let ?R = "int ?remainder"
  let ?X = "int (antihydra_family_orbit h n)"
  let ?C = "antihydra_physical_floor_correction h n"
  have quotient_remainder_nat:
    "?numerator = ?denominator * ?quotient + ?remainder"
    using div_mult_mod_eq[of ?numerator ?denominator]
    by (simp add: mult.commute)
  have quotient_remainder:
    "int ?numerator = int ?denominator * int ?quotient + int ?remainder"
    using arg_cong[OF quotient_remainder_nat, of int]
    by (simp only: of_nat_add of_nat_mult)
  have physical:
    "?D * ?X = int ?numerator - ?C"
    using antihydra_physical_carry_tower_exact[of n h]
    by (simp add: algebra_simps)
  have physical_cancel: "?D * ?X + ?C = int ?numerator"
    using physical by (simp add: add.commute)
  have joined: "?D * ?Q + ?R = ?D * ?X + ?C"
  proof -
    have quotient_reverse: "?D * ?Q + ?R = int ?numerator"
      using quotient_remainder by (rule sym)
    have physical_forward: "int ?numerator = ?D * ?X + ?C"
      using physical_cancel by (rule sym)
    show ?thesis by (rule trans[OF quotient_reverse physical_forward])
  qed
  have subtract_shared:
    "?D * ?Q + ?R - ?D * ?X = ?D * ?X + ?C - ?D * ?X"
    by (rule arg_cong[OF joined, of "\<lambda>value. value - ?D * ?X"])
  have cancel_right: "?D * ?X + ?C - ?D * ?X = ?C"
    by (simp add: algebra_simps)
  have quotient_form_reverse: "?D * ?Q + ?R - ?D * ?X = ?C"
    using subtract_shared cancel_right by simp
  have quotient_form: "?C = ?D * ?Q + ?R - ?D * ?X"
    using quotient_form_reverse by (rule sym)
  have correction:
    "?C = ?R + ?D * (?Q - ?X)"
  proof -
    show ?thesis using quotient_form by (simp add: algebra_simps)
  qed
  show ?thesis
    using correction
    by (simp add: antihydra_raw_three_halves_quotient_def
        antihydra_raw_three_halves_remainder_def)
qed

theorem antihydra_centered_x15_innovation_exact:
  "(2::int)^n * (int (antihydra_family_orbit h n) - 1) =
    (3::int)^n * (int h - 1) + antihydra_centered_innovation h n"
  using antihydra_physical_carry_tower_exact[of n h]
  by (simp add: antihydra_centered_innovation_def algebra_simps)

theorem antihydra_skew_offset_is_negative_physical_correction:
  "sk_J (antihydra_arithmetic_block h n) =
    - antihydra_physical_floor_correction h n"
proof -
  have fields:
    "antihydra_exact_run_offset h n =
      sk_J (antihydra_arithmetic_block h n)"
    using antihydra_exact_run_candidate_fields[of
      "antihydra_family_orbit h n" h n] by simp
  show ?thesis
    using fields antihydra_physical_carry_tower_exact[of n h]
    by (simp add: antihydra_exact_run_offset_def algebra_simps)
qed

theorem antihydra_centered_innovation_from_skew_action:
  "antihydra_centered_innovation h n =
    (3::int)^n - (2::int)^n + sk_J (antihydra_arithmetic_block h n)"
  by (simp add: antihydra_centered_innovation_def
      antihydra_skew_offset_is_negative_physical_correction)

text \<open>A low-eight-bit row determines the complete eight-step source word,
endpoint offset, carry correction, and ordered ledger summary.  The high
fiber changes the endpoint by the exact multiplier 3^8, while it cannot
change any of the eight consumed parity symbols.\<close>

lemma antihydra_source_low_eight_split:
  "(h::nat) = h mod 256 + 256 * (h div 256)"
  using mod_div_mult_eq[of h 256] by (simp add: mult.commute)

theorem antihydra_eight_tick_endpoint_from_low_row:
  "antihydra_family_orbit h 8 =
    antihydra_family_orbit (h mod 256) 8 + 6561 * (h div 256)"
proof -
  have lifted:
    "antihydra_family_orbit
        ((h mod 256) + 2^8 * (h div 256)) 8 =
      antihydra_family_orbit (h mod 256) 8 + 3^8 * (h div 256)"
    by (rule antihydra_family_orbit_cylinder_transport)
  show ?thesis
    using lifted antihydra_source_low_eight_split[of h]
    by simp
qed

theorem antihydra_eight_tick_word_from_low_row:
  "antihydra_family_bits h 8 = antihydra_family_bits (h mod 256) 8"
proof -
  have lifted:
    "antihydra_family_bits
        ((h mod 256) + 2^8 * (h div 256)) 8 =
      antihydra_family_bits (h mod 256) 8"
    by (rule antihydra_family_bits_cylinder_transport)
  show ?thesis
    using lifted antihydra_source_low_eight_split[of h]
    by simp
qed

corollary antihydra_eight_tick_skew_action_from_low_row:
  "antihydra_arithmetic_block h 8 =
    antihydra_arithmetic_block (h mod 256) 8"
  using antihydra_eight_tick_word_from_low_row[of h]
  by (simp add: antihydra_arithmetic_block_def)

corollary antihydra_eight_tick_ledger_from_low_row:
  "antihydra_family_balance h initial 8 =
      antihydra_family_balance (h mod 256) initial 8"
  "antihydra_family_minimum h initial 8 =
      antihydra_family_minimum (h mod 256) initial 8"
  using antihydra_eight_tick_word_from_low_row[of h]
  by (simp_all add: antihydra_family_balance_def
      antihydra_family_minimum_def)

fun antihydra_eight_tick_chunks :: "nat \<Rightarrow> nat \<Rightarrow> antihydra_skew" where
  "antihydra_eight_tick_chunks h 0 = skew_identity"
| "antihydra_eight_tick_chunks h (Suc k) = skew_then
    (antihydra_eight_tick_chunks h k)
    (antihydra_arithmetic_block (antihydra_family_orbit h (8*k)) 8)"

theorem antihydra_eight_tick_chunks_are_chronological:
  "antihydra_arithmetic_block h (8*k) =
    antihydra_eight_tick_chunks h k"
proof (induction k)
  case 0
  then show ?case
    by (simp add: antihydra_arithmetic_block_def skew_word.simps
        skew_identity_def)
next
  case (Suc k)
  have extent: "8 * Suc k = 8*k + 8" by simp
  have joined:
    "antihydra_arithmetic_block h (8*k+8) =
      skew_then (antihydra_arithmetic_block h (8*k))
        (antihydra_arithmetic_block
          (antihydra_family_orbit h (8*k)) 8)"
    by (rule antihydra_arithmetic_block_composition)
  show ?case
    using Suc.IH joined extent
    by (simp only: extent joined antihydra_eight_tick_chunks.simps)
qed

theorem antihydra_eight_tick_chunks_join_remainder:
  "antihydra_arithmetic_block h (8*k + tail_steps) =
    skew_then (antihydra_eight_tick_chunks h k)
      (antihydra_arithmetic_block
        (antihydra_family_orbit h (8*k)) tail_steps)"
proof -
  have joined:
    "antihydra_arithmetic_block h (8*k + tail_steps) =
      skew_then (antihydra_arithmetic_block h (8*k))
        (antihydra_arithmetic_block
          (antihydra_family_orbit h (8*k)) tail_steps)"
    by (rule antihydra_arithmetic_block_composition)
  show ?thesis
    using joined antihydra_eight_tick_chunks_are_chronological[of h k]
    by simp
qed

text \<open>The decimal borrow between the multipliers 225 and 210+15, and
between 15 and 14+1, is determined by the exact low prefix modulo
\(10^w\).  The shared column-carry theorem supplies the finite 0/1 range;
these family corollaries connect that carry to the production multiplier
differences without enumerating source integers.\<close>

definition antihydra_decimal_prefix_floor ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "antihydra_decimal_prefix_floor multiplier source width =
    (multiplier * (source mod 10^width)) div 10^width"

definition antihydra_decimal_prefix_carry ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "antihydra_decimal_prefix_carry left right source width =
    (((left * (source mod 10^width)) mod 10^width +
      (right * (source mod 10^width)) mod 10^width) div 10^width)"

lemma antihydra_decimal_prefix_floor_split:
  fixes left right source width :: nat
  shows
  "antihydra_decimal_prefix_floor (left+right) source width =
    antihydra_decimal_prefix_floor left source width +
    antihydra_decimal_prefix_floor right source width +
    antihydra_decimal_prefix_carry left right source width"
proof -
  let ?m = "10^width"
  let ?low = "source mod ?m"
  have split:
    "((left*?low)+(right*?low)) div ?m =
      (left*?low) div ?m + (right*?low) div ?m +
        ((left*?low) mod ?m + (right*?low) mod ?m) div ?m"
    by (rule div_add1_eq)
  have distribute: "(left+right)*?low = left*?low + right*?low"
    by (simp add: algebra_simps)
  show ?thesis
    using split distribute
    by (simp add: antihydra_decimal_prefix_floor_def
        antihydra_decimal_prefix_carry_def)
qed

lemma antihydra_decimal_prefix_carry_bound:
  fixes left right source width :: nat
  shows
  "antihydra_decimal_prefix_carry left right source width \<le> 1"
proof (cases width)
  case 0
  then show ?thesis
    by (simp add: antihydra_decimal_prefix_carry_def)
next
  case (Suc j)
  let ?m = "(10::nat)^Suc j"
  let ?a = "left * (source mod ?m)"
  let ?b = "right * (source mod ?m)"
  have column:
    "(if decimal_base10_column_carry j ?a ?b then 1 else 0) =
      (?a mod ?m + ?b mod ?m) div ?m"
    by (rule decimal_base10_column_carry_value)
  have range: "(?a mod ?m + ?b mod ?m) div ?m \<le> 1"
    using column by (cases "decimal_base10_column_carry j ?a ?b") auto
  show ?thesis
    using range Suc by (simp add: antihydra_decimal_prefix_carry_def)
qed

lemma antihydra_decimal_prefix_floor_split_carry_bound:
  fixes left right source width :: nat
  shows
  "(((left+right) * (source mod 10^width)) div 10^width -
      (left * (source mod 10^width)) div 10^width -
      (right * (source mod 10^width)) div 10^width) \<le> 1"
  using antihydra_decimal_prefix_floor_split[of left right source width]
    antihydra_decimal_prefix_carry_bound[of left right source width]
  by (simp only: antihydra_decimal_prefix_floor_def
      antihydra_decimal_prefix_carry_def; arith)

lemma antihydra_decimal_prefix_floor_split_is_zero_or_one:
  fixes left right source width :: nat
  shows
  "(((left+right) * (source mod 10^width)) div 10^width -
      (left * (source mod 10^width)) div 10^width -
      (right * (source mod 10^width)) div 10^width) = 0 \<or>
    (((left+right) * (source mod 10^width)) div 10^width -
      (left * (source mod 10^width)) div 10^width -
      (right * (source mod 10^width)) div 10^width) = 1"
  using antihydra_decimal_prefix_floor_split_carry_bound[of left right source width]
  by arith

corollary antihydra_225_210_15_prefix_borrow_exact:
  "int (antihydra_decimal_prefix_floor 225 source width) -
      int (antihydra_decimal_prefix_floor 210 source width) -
      int (antihydra_decimal_prefix_floor 15 source width) =
    int (antihydra_decimal_prefix_carry 210 15 source width)"
proof -
  note split = antihydra_decimal_prefix_floor_split[of 210 15 source width]
  have cast:
    "int (antihydra_decimal_prefix_floor 225 source width) =
      int (antihydra_decimal_prefix_floor 210 source width) +
      int (antihydra_decimal_prefix_floor 15 source width) +
      int (antihydra_decimal_prefix_carry 210 15 source width)"
    using arg_cong[OF split, of int] by simp
  show ?thesis using cast by simp
qed

corollary antihydra_225_210_15_prefix_borrow_signed_range:
  "0 \<le> int (antihydra_decimal_prefix_floor 225 source width) -
      int (antihydra_decimal_prefix_floor 210 source width) -
      int (antihydra_decimal_prefix_floor 15 source width) \<and>
    int (antihydra_decimal_prefix_floor 225 source width) -
      int (antihydra_decimal_prefix_floor 210 source width) -
      int (antihydra_decimal_prefix_floor 15 source width) \<le> 1"
proof -
  note exact = antihydra_225_210_15_prefix_borrow_exact[of source width]
  note bounded = antihydra_decimal_prefix_carry_bound[of 210 15 source width]
  have lower:
    "0 \<le> int (antihydra_decimal_prefix_carry 210 15 source width)"
    by simp
  have upper:
    "int (antihydra_decimal_prefix_carry 210 15 source width) \<le> 1"
    using bounded by (simp only: of_nat_le_iff)
  show ?thesis using exact lower upper by arith
qed

corollary antihydra_225_210_15_prefix_borrow_signed_zero_or_one:
  "int (antihydra_decimal_prefix_floor 225 source width) -
      int (antihydra_decimal_prefix_floor 210 source width) -
      int (antihydra_decimal_prefix_floor 15 source width) = 0 \<or>
    int (antihydra_decimal_prefix_floor 225 source width) -
      int (antihydra_decimal_prefix_floor 210 source width) -
      int (antihydra_decimal_prefix_floor 15 source width) = 1"
proof -
  note exact = antihydra_225_210_15_prefix_borrow_exact[of source width]
  note bounded = antihydra_decimal_prefix_carry_bound[of 210 15 source width]
  have cases:
    "antihydra_decimal_prefix_carry 210 15 source width = 0 \<or>
      antihydra_decimal_prefix_carry 210 15 source width = 1"
    using bounded by arith
  show ?thesis using exact cases by auto
qed

corollary antihydra_15_14_1_prefix_borrow_exact:
  "int (antihydra_decimal_prefix_floor 15 source width) -
      int (antihydra_decimal_prefix_floor 14 source width) -
      int (antihydra_decimal_prefix_floor 1 source width) =
    int (antihydra_decimal_prefix_carry 14 1 source width)"
proof -
  note split = antihydra_decimal_prefix_floor_split[of 14 1 source width]
  have cast:
    "int (antihydra_decimal_prefix_floor 15 source width) =
      int (antihydra_decimal_prefix_floor 14 source width) +
      int (antihydra_decimal_prefix_floor 1 source width) +
      int (antihydra_decimal_prefix_carry 14 1 source width)"
    using arg_cong[OF split, of int] by simp
  show ?thesis using cast by simp
qed

corollary antihydra_15_14_1_prefix_borrow_signed_range:
  "0 \<le> int (antihydra_decimal_prefix_floor 15 source width) -
      int (antihydra_decimal_prefix_floor 14 source width) -
      int (antihydra_decimal_prefix_floor 1 source width) \<and>
    int (antihydra_decimal_prefix_floor 15 source width) -
      int (antihydra_decimal_prefix_floor 14 source width) -
      int (antihydra_decimal_prefix_floor 1 source width) \<le> 1"
proof -
  note exact = antihydra_15_14_1_prefix_borrow_exact[of source width]
  note bounded = antihydra_decimal_prefix_carry_bound[of 14 1 source width]
  have lower:
    "0 \<le> int (antihydra_decimal_prefix_carry 14 1 source width)"
    by simp
  have upper:
    "int (antihydra_decimal_prefix_carry 14 1 source width) \<le> 1"
    using bounded by (simp only: of_nat_le_iff)
  show ?thesis using exact lower upper by arith
qed

corollary antihydra_15_14_1_prefix_borrow_signed_zero_or_one:
  "int (antihydra_decimal_prefix_floor 15 source width) -
      int (antihydra_decimal_prefix_floor 14 source width) -
      int (antihydra_decimal_prefix_floor 1 source width) = 0 \<or>
    int (antihydra_decimal_prefix_floor 15 source width) -
      int (antihydra_decimal_prefix_floor 14 source width) -
      int (antihydra_decimal_prefix_floor 1 source width) = 1"
proof -
  note exact = antihydra_15_14_1_prefix_borrow_exact[of source width]
  note bounded = antihydra_decimal_prefix_carry_bound[of 14 1 source width]
  have cases:
    "antihydra_decimal_prefix_carry 14 1 source width = 0 \<or>
      antihydra_decimal_prefix_carry 14 1 source width = 1"
    using bounded by arith
  show ?thesis using exact cases by auto
qed

text \<open>The next physical field is obtained by multiplying the current
decimal field by 15 and subtracting the one parity-selected correction at
the moving cut.  This identity follows from the admitted orbit recurrence,
so it does not posit an independent endpoint.  Its digit at the old cut is
zero because the corrected field starts one decimal place later.\<close>

theorem antihydra_physical_moving_cut_next:
  "15 * (10::int)^n * int (antihydra_family_orbit h n) -
      5 * int (antihydra_family_orbit h n mod 2) * (10::int)^n =
    (10::int)^Suc n * int (antihydra_family_orbit h (Suc n))"
proof -
  let ?current = "antihydra_family_orbit h n"
  let ?next = "antihydra_family_orbit h (Suc n)"
  have orbit_step: "?next = antihydra_family_step ?current"
    by (rule antihydra_family_orbit_Suc_right)
  have recurrence:
    "2 * int ?next = 3 * int ?current - int (?current mod 2)"
    using orbit_step antihydra_family_step_skew_equation[of ?current]
    by simp
  have scaled:
    "(10::int)^n * (5 * (2 * int ?next)) =
      (10::int)^n * (5 * (3 * int ?current - int (?current mod 2)))"
    using recurrence by simp
  show ?thesis
    using scaled
    by (simp add: power_Suc algebra_simps)
qed

lemma antihydra_decimal_digit_at_power:
  fixes d :: nat
  shows
  "decimal_base10_digit n (10^n * d) = d mod 10"
  unfolding decimal_base10_digit_def
  by (simp add: mult.commute)

lemma antihydra_decimal_digit_below_power:
  fixes d :: nat
  shows
  "decimal_base10_digit n (10^Suc n * d) = 0"
proof -
  have quotient_at_n:
    "(10^Suc n * d) div 10^n = 10 * d"
    by (simp add: power_Suc mult.assoc mult.commute)
  have quotient_at_suc:
    "(10^Suc n * d) div 10^Suc n = d"
    by (simp add: mult.commute)
  note expansion =
    decimal_base10_digit_quotient_expansion[of "10^Suc n * d" n]
  show ?thesis using expansion quotient_at_n quotient_at_suc by arith
qed

lemma antihydra_digit15_parity_correction:
  fixes d :: nat
  shows
  "(15 * (d mod 10)) mod 10 = 5 * (d mod 2)"
proof -
  have low_parity: "(d mod 10) mod 2 = d mod 2"
    by (rule mod_mod_cancel; simp)
  have product15:
    "(15 * (d mod 10)) mod 10 =
      ((15 mod 10) * ((d mod 10) mod 10)) mod 10"
    by (rule mod_mult_eq[symmetric])
  have residue15: "(15::nat) mod 10 = 5" by simp
  have digit_residue: "(d mod 10) mod 10 = d mod 10"
    by (rule mod_mod_cancel; simp)
  have digit_product:
    "(15 * (d mod 10)) mod 10 = (5 * (d mod 10)) mod 10"
    using product15 residue15 digit_residue
    by (simp only: product15 residue15 digit_residue)
  have parity_product:
    "(5 * (d mod 10)) mod (5 * 2) = 5 * ((d mod 10) mod 2)"
    by (rule mod_mult_mult1)
  have decimal_base: "(5::nat) * 2 = 10" by simp
  have parity_base:
    "(5 * (d mod 10)) mod 10 = 5 * ((d mod 10) mod 2)"
    using parity_product by (simp only: decimal_base)
  have repaired_digit:
    "(5 * (d mod 10)) mod 10 = 5 * (d mod 2)"
    using parity_base low_parity by (simp only: parity_base low_parity)
  show ?thesis using digit_product repaired_digit
    by (simp only: digit_product repaired_digit)
qed

corollary antihydra_physical_moving_cut_point_read:
  "decimal_base10_digit n
      (10^Suc n * antihydra_family_orbit h (Suc n)) = 0"
  by (rule antihydra_decimal_digit_below_power)

corollary antihydra_physical_moving_cut_local_correction:
  "(15 * decimal_base10_digit n
        (10^n * antihydra_family_orbit h n)) mod 10 =
    5 * (antihydra_family_orbit h n mod 2)"
  using antihydra_decimal_digit_at_power[of n
      "antihydra_family_orbit h n"]
    antihydra_digit15_parity_correction[of
      "antihydra_family_orbit h n"]
  by simp

text \<open>The mod-101 source clock is the modular image of the exact physical
x15 identity.  The inverse phase is explicit: 91 is the inverse of 10
modulo 101, so cancellation does not rely on an assumed endpoint or a
floating-point clock calculation.\<close>

lemma antihydra_mod101_ten_power_inverse:
  "(91::int)^n * (10::int)^n mod 101 = 1"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have power:
    "(91::int)^Suc n * (10::int)^Suc n =
      ((91::int)^n * (10::int)^n) * (91 * 10)"
    by (simp add: power_Suc algebra_simps)
  have inverse_factor: "((91::int) * 10) mod 101 = 1" by simp
  have product:
    "(((91::int)^n * (10::int)^n) * (91 * 10)) mod 101 =
      ((((91::int)^n * (10::int)^n) mod 101) *
        ((91 * 10) mod 101)) mod 101"
    by (rule mod_mult_eq[symmetric])
  have normalized:
    "(((91::int)^n * (10::int)^n) mod 101) *
        ((91 * 10) mod 101) mod 101 = 1"
    using Suc.IH inverse_factor by simp
  have raw:
    "(((91::int)^n * (10::int)^n) * (91 * 10)) mod 101 = 1"
    using product normalized by (simp only: product normalized)
  show ?case using power raw by (simp only: power raw)
qed

lemma antihydra_mod101_cancel_ten_power:
  fixes x y :: int
  assumes equal:
    "((10::int)^n * x) mod 101 = ((10::int)^n * y) mod 101"
  shows "x mod 101 = y mod 101"
proof -
  have multiplied:
    "(91::int)^n * ((10::int)^n * x) mod 101 =
      (91^n * ((10::int)^n * y)) mod 101"
    using mod_mult_cong[OF refl equal] .
  have inverse: "(91::int)^n * (10::int)^n mod 101 = 1"
    by (rule antihydra_mod101_ten_power_inverse)
  have left:
    "((91::int)^n * (10::int)^n * x) mod 101 = x mod 101"
  proof -
    have product:
      "((91::int)^n * (10::int)^n * x) mod 101 =
        (((91::int)^n * (10::int)^n) mod 101 * (x mod 101)) mod 101"
      by (rule mod_mult_eq[symmetric])
    show ?thesis using product inverse by simp
  qed
  have right:
    "((91::int)^n * (10::int)^n * y) mod 101 = y mod 101"
  proof -
    have product:
      "((91::int)^n * (10::int)^n * y) mod 101 =
        (((91::int)^n * (10::int)^n) mod 101 * (y mod 101)) mod 101"
      by (rule mod_mult_eq[symmetric])
    show ?thesis using product inverse by simp
  qed
  have regrouped:
    "((91::int)^n * (10::int)^n * x) mod 101 =
      ((91::int)^n * (10::int)^n * y) mod 101"
    using multiplied by (simp only: mult.assoc)
  show ?thesis using regrouped left right by (simp only: left right)
qed

theorem antihydra_mod101_source_clock:
  "((52::int)^n * int h -
      (51::int)^n * antihydra_physical_floor_correction h n) mod 101 =
    int (antihydra_family_orbit h n) mod 101"
proof -
  have gain_base: "(10::int) * 52 mod 101 = 15 mod 101" by simp
  have correction_base: "(10::int) * 51 mod 101 = 5 mod 101" by simp
  have gain_power:
    "((10::int) * 52)^n mod 101 = (15::int)^n mod 101"
  proof -
    have left: "((10::int) * 52)^n mod 101 =
        (((10::int) * 52) mod 101)^n mod 101"
      by (rule power_mod[symmetric])
    have right: "(15::int)^n mod 101 = (15 mod 101)^n mod 101"
      by (rule power_mod[symmetric])
    show ?thesis
    proof -
      have "((10::int) * 52)^n mod 101 =
          (((10::int) * 52) mod 101)^n mod 101"
        by (rule left)
      also have "... = (15 mod 101)^n mod 101"
        by (simp only: gain_base)
      also have "... = (15::int)^n mod 101"
        by (rule sym[OF right])
      finally show ?thesis .
    qed
  qed
  have correction_power:
    "((10::int) * 51)^n mod 101 = (5::int)^n mod 101"
  proof -
    have left: "((10::int) * 51)^n mod 101 =
        (((10::int) * 51) mod 101)^n mod 101"
      by (rule power_mod[symmetric])
    have right: "(5::int)^n mod 101 = (5 mod 101)^n mod 101"
      by (rule power_mod[symmetric])
    show ?thesis
    proof -
      have "((10::int) * 51)^n mod 101 =
          (((10::int) * 51) mod 101)^n mod 101"
        by (rule left)
      also have "... = (5 mod 101)^n mod 101"
        by (simp only: correction_base)
      also have "... = (5::int)^n mod 101"
        by (rule sym[OF right])
      finally show ?thesis .
    qed
  qed
  have gain_product:
    "(10::int)^n * (52::int)^n = ((10::int) * 52)^n"
    by (rule power_mult_distrib[symmetric])
  have correction_product:
    "(10::int)^n * (51::int)^n = ((10::int) * 51)^n"
    by (rule power_mult_distrib[symmetric])
  have gain_coefficient:
    "((10::int)^n * (52::int)^n) mod 101 =
      (15::int)^n mod 101"
    using gain_product gain_power by (simp only: gain_product gain_power)
  have correction_coefficient:
    "((10::int)^n * (51::int)^n) mod 101 =
      (5::int)^n mod 101"
    using correction_product correction_power
    by (simp only: correction_product correction_power)
  have gain_term:
    "((10::int)^n * (52::int)^n * int h) mod 101 =
      ((15::int)^n * int h) mod 101"
    by (rule mod_mult_cong[OF gain_coefficient refl])
  have correction_term:
    "((10::int)^n * (51::int)^n *
        antihydra_physical_floor_correction h n) mod 101 =
      ((5::int)^n * antihydra_physical_floor_correction h n) mod 101"
    by (rule mod_mult_cong[OF correction_coefficient refl])
  have negative_correction:
    "(-((10::int)^n * (51::int)^n *
        antihydra_physical_floor_correction h n)) mod 101 =
      (-((5::int)^n * antihydra_physical_floor_correction h n)) mod 101"
  proof -
    have product:
      "(-1::int) * ((10::int)^n * (51::int)^n *
          antihydra_physical_floor_correction h n) mod 101 =
        (-1::int) * ((5::int)^n *
          antihydra_physical_floor_correction h n) mod 101"
      by (rule mod_mult_cong[OF refl correction_term])
    have left_negative:
      "-((10::int)^n * (51::int)^n *
          antihydra_physical_floor_correction h n) =
        (-1::int) * ((10::int)^n * (51::int)^n *
          antihydra_physical_floor_correction h n)"
      by simp
    have right_negative:
      "-((5::int)^n * antihydra_physical_floor_correction h n) =
        (-1::int) * ((5::int)^n *
          antihydra_physical_floor_correction h n)"
      by simp
    show ?thesis using product left_negative right_negative
      by (simp only: left_negative right_negative product)
  qed
  have scaled:
    "((10::int)^n *
        ((52::int)^n * int h -
          (51::int)^n * antihydra_physical_floor_correction h n)) mod 101 =
      ((15::int)^n * int h -
        (5::int)^n * antihydra_physical_floor_correction h n) mod 101"
  proof -
    have factor:
      "(10::int)^n *
          ((52::int)^n * int h -
            (51::int)^n * antihydra_physical_floor_correction h n) =
        ((10::int)^n * (52::int)^n * int h) +
          (-((10::int)^n * (51::int)^n *
            antihydra_physical_floor_correction h n))"
      by (simp add: algebra_simps)
    have transported:
      "((10::int)^n *
          ((52::int)^n * int h -
            (51::int)^n * antihydra_physical_floor_correction h n)) mod 101 =
        (((10::int)^n * (52::int)^n * int h) +
          (-((10::int)^n * (51::int)^n *
            antihydra_physical_floor_correction h n))) mod 101"
      using arg_cong[OF factor, of "\<lambda>x. x mod (101::int)"] .
    have joined:
      "(((10::int)^n * (52::int)^n * int h) +
          (-((10::int)^n * (51::int)^n *
            antihydra_physical_floor_correction h n))) mod 101 =
        (((15::int)^n * int h) +
          (-((5::int)^n * antihydra_physical_floor_correction h n))) mod 101"
      by (rule mod_add_cong[OF gain_term negative_correction])
    have result:
      "(((15::int)^n * int h) +
          (-((5::int)^n * antihydra_physical_floor_correction h n))) mod 101 =
        ((15::int)^n * int h -
          (5::int)^n * antihydra_physical_floor_correction h n) mod 101"
      unfolding diff_conv_add_uminus by simp
    show ?thesis using transported joined result
      by (simp only: transported joined result)
  qed
  have physical:
    "(15::int)^n * int h -
        (5::int)^n * antihydra_physical_floor_correction h n =
      (10::int)^n * int (antihydra_family_orbit h n)"
    using antihydra_physical_decimal_x15_identity[of n h] by (rule sym)
  have endpoint_scaled:
    "((10::int)^n *
        ((52::int)^n * int h -
          (51::int)^n * antihydra_physical_floor_correction h n)) mod 101 =
      ((10::int)^n * int (antihydra_family_orbit h n)) mod 101"
    using scaled physical by (simp only: physical)
  show ?thesis
    by (rule antihydra_mod101_cancel_ten_power[OF endpoint_scaled])
qed

corollary antihydra_mod101_reduced_source_clock:
  "(((52::int)^n mod 101) * int h -
      ((51::int)^n mod 101) *
        antihydra_physical_floor_correction h n) mod 101 =
    int (antihydra_family_orbit h n) mod 101"
proof -
  have gain_coefficient:
    "((52::int)^n mod 101) mod 101 = (52::int)^n mod 101"
    by simp
  have correction_coefficient:
    "((51::int)^n mod 101) mod 101 = (51::int)^n mod 101"
    by simp
  have gain:
    "(((52::int)^n mod 101) * int h) mod 101 =
      ((52::int)^n * int h) mod 101"
    by (rule mod_mult_cong[OF gain_coefficient refl])
  have correction:
    "(((51::int)^n mod 101) *
        antihydra_physical_floor_correction h n) mod 101 =
      ((51::int)^n * antihydra_physical_floor_correction h n) mod 101"
    by (rule mod_mult_cong[OF correction_coefficient refl])
  have negative_correction:
    "(-(((51::int)^n mod 101) *
        antihydra_physical_floor_correction h n)) mod 101 =
      (-((51::int)^n *
        antihydra_physical_floor_correction h n)) mod 101"
  proof -
    have product:
      "(-1::int) * (((51::int)^n mod 101) *
          antihydra_physical_floor_correction h n) mod 101 =
        (-1::int) * ((51::int)^n *
          antihydra_physical_floor_correction h n) mod 101"
      by (rule mod_mult_cong[OF refl correction])
    have left_negative:
      "-(((51::int)^n mod 101) *
          antihydra_physical_floor_correction h n) =
        (-1::int) * (((51::int)^n mod 101) *
          antihydra_physical_floor_correction h n)"
      by simp
    have right_negative:
      "-((51::int)^n *
          antihydra_physical_floor_correction h n) =
        (-1::int) * ((51::int)^n *
          antihydra_physical_floor_correction h n)"
      by simp
    show ?thesis using product left_negative right_negative
      by (simp only: left_negative right_negative product)
  qed
  show ?thesis
    using mod_add_cong[OF gain negative_correction]
      antihydra_mod101_source_clock[of n h]
    by (simp add: algebra_simps)
qed

text \<open>The two-parent identity is a quotient identity for one common
radix-15 source.  The recurrence relation on adjacent quotients is an
assumption; the theorem does not infer a periodic source or future carry
choices from a finite endpoint.\<close>

lemma x15_two_parent_correction_divisible:
  fixes previous current previous_carry :: nat
  assumes adjacent: "current = 15*previous + previous_carry"
  shows "4 dvd 3*previous_carry + current mod 4 + previous mod 4"
  using adjacent by presburger

theorem x15_two_parent_floor_recurrence:
  fixes previous current previous_carry current_carry :: nat
  assumes adjacent: "current = 15*previous + previous_carry"
  shows "15*current + current_carry =
    (57*current) div 4 + (45*previous) div 4 + current_carry +
      (3*previous_carry + current mod 4 + previous mod 4) div 4"
proof -
  have divisible:
    "4 dvd 3*previous_carry + current mod 4 + previous mod 4"
    by (rule x15_two_parent_correction_divisible[OF adjacent])
  have current_residue:
    "(57*current) mod 4 = current mod 4"
  proof -
    have "(57*current) mod 4 = ((57 mod 4)*(current mod 4)) mod 4"
      by (rule mod_mult_eq[symmetric])
    then show ?thesis by simp
  qed
  have previous_residue:
    "(45*previous) mod 4 = previous mod 4"
  proof -
    have "(45*previous) mod 4 = ((45 mod 4)*(previous mod 4)) mod 4"
      by (rule mod_mult_eq[symmetric])
    then show ?thesis by simp
  qed
  have current_quotient:
    "57*current = 4*((57*current) div 4) + current mod 4"
  proof -
    have quotient_identity:
      "((57*current) div 4)*4 + (57*current) mod 4 = 57*current"
      by (rule div_mult_mod_eq)
    have rewritten:
      "((57*current) div 4)*4 + current mod 4 = 57*current"
      using quotient_identity
      by (simp only: current_residue)
    show ?thesis using rewritten by (simp add: mult.commute)
  qed
  have previous_quotient:
    "45*previous = 4*((45*previous) div 4) + previous mod 4"
  proof -
    have quotient_identity:
      "((45*previous) div 4)*4 + (45*previous) mod 4 = 45*previous"
      by (rule div_mult_mod_eq)
    have rewritten:
      "((45*previous) div 4)*4 + previous mod 4 = 45*previous"
      using quotient_identity
      by (simp only: previous_residue)
    show ?thesis using rewritten by (simp add: mult.commute)
  qed
  have correction_residue:
    "(3*previous_carry + current mod 4 + previous mod 4) mod 4 = 0"
    using divisible by (simp add: dvd_eq_mod_eq_0)
  have correction_quotient:
    "3*previous_carry + current mod 4 + previous mod 4 =
      4*((3*previous_carry + current mod 4 + previous mod 4) div 4)"
  proof -
    let ?correction = "3*previous_carry + current mod 4 + previous mod 4"
    have quotient_identity:
      "(?correction div 4)*4 + ?correction mod 4 = ?correction"
      by (rule div_mult_mod_eq)
    have rewritten: "(?correction div 4)*4 = ?correction"
      using quotient_identity
      by (simp only: correction_residue)
    show ?thesis using rewritten by (simp add: mult.commute)
  qed
  show ?thesis
    using adjacent current_quotient previous_quotient correction_quotient
    by arith
qed

theorem x15_two_parent_polynomial_recurrence:
  fixes previous current previous_carry current_carry :: nat
  assumes adjacent: "current = 15*previous + previous_carry"
  shows "15*current + current_carry =
    10*current + 75*previous + 5*previous_carry + current_carry"
  using adjacent by arith

theorem antihydra_multiplier_carry_vector_refines_decimal_digits:
  "15 * decimal_lsd_value digits + 0 =
    decimal_lsd_value
      (fst (decimal_multiplier_columns 15 0 digits)) +
      10^(length digits) *
        snd (decimal_multiplier_columns 15 0 digits)"
  by (rule decimal_multiplier_columns_exact)

ML \<open>
  val checked = @{thms antihydra_physical_carry_tower_exact
    antihydra_physical_decimal_x15_identity antihydra_coupled_raw_cut_exact
    antihydra_decimal_prefix_floor_split
    antihydra_decimal_prefix_carry_bound
    antihydra_decimal_prefix_floor_split_carry_bound
    antihydra_decimal_prefix_floor_split_is_zero_or_one
    antihydra_225_210_15_prefix_borrow_exact
    antihydra_225_210_15_prefix_borrow_signed_range
    antihydra_225_210_15_prefix_borrow_signed_zero_or_one
    antihydra_15_14_1_prefix_borrow_exact
    antihydra_15_14_1_prefix_borrow_signed_range
    antihydra_15_14_1_prefix_borrow_signed_zero_or_one
    antihydra_physical_moving_cut_next
    antihydra_decimal_digit_at_power antihydra_decimal_digit_below_power
    antihydra_digit15_parity_correction
    antihydra_physical_moving_cut_point_read
    antihydra_physical_moving_cut_local_correction
    antihydra_mod101_ten_power_inverse
    antihydra_mod101_cancel_ten_power antihydra_mod101_source_clock
    antihydra_mod101_reduced_source_clock
    antihydra_centered_x15_innovation_exact
    antihydra_skew_offset_is_negative_physical_correction
    antihydra_centered_innovation_from_skew_action
    antihydra_eight_tick_endpoint_from_low_row
    antihydra_eight_tick_word_from_low_row
    antihydra_eight_tick_skew_action_from_low_row
    antihydra_eight_tick_ledger_from_low_row
    antihydra_eight_tick_chunks_are_chronological
    antihydra_eight_tick_chunks_join_remainder
    x15_two_parent_correction_divisible x15_two_parent_floor_recurrence
    x15_two_parent_polynomial_recurrence
    antihydra_multiplier_carry_vector_refines_decimal_digits};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Antihydra diagonal carry refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Antihydra diagonal carry refinement proof" else ();
\<close>

end
