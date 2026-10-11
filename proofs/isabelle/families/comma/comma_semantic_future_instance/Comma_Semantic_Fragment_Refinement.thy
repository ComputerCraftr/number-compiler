theory Comma_Semantic_Fragment_Refinement
  imports Comma_Semantic_Weighted_Selection
begin

text \<open>The indexed Python producer stores affine values as a reduced
integer triple `(A,B,D)` denoting `(A*S+B)/D` at an integer scale `S`, and
stores cycle and literal fragments as eight scalar fields.  These records
mirror those public payloads.  The checked Entry theorem connects one emitted
cycle fragment to the canonical weighted chart move.  The generic prefix
lemmas describe numeric scans of such records; a full theorem for Python's
complete bounded macro loop still needs the chart-list and terminal-outcome
relation.\<close>

record comma_python_affine_weight =
  comma_python_affine_scale :: int
  comma_python_affine_offset :: int
  comma_python_affine_denominator :: nat

record comma_python_sector_fragment =
  comma_python_fragment_leading :: nat
  comma_python_fragment_entering_digit :: nat
  comma_python_fragment_complete_cycles :: comma_python_affine_weight
  comma_python_fragment_period :: nat
  comma_python_fragment_displacement :: nat
  comma_python_fragment_maximum_guard :: nat
  comma_python_fragment_literal_steps :: nat
  comma_python_fragment_literal_increment :: nat

definition comma_python_affine_divides ::
  "comma_python_affine_weight \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_python_affine_divides w S \<longleftrightarrow>
    int (comma_python_affine_denominator w) dvd
      (comma_python_affine_scale w * int S +
        comma_python_affine_offset w)"

definition comma_python_affine_evaluate ::
  "comma_python_affine_weight \<Rightarrow> nat \<Rightarrow> int" where
  "comma_python_affine_evaluate w S =
    (comma_python_affine_scale w * int S +
      comma_python_affine_offset w) div
        int (comma_python_affine_denominator w)"

definition comma_python_affine_normalize ::
  "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> comma_python_affine_weight" where
  "comma_python_affine_normalize A B D =
    (let g = gcd (gcd (nat (abs A)) (nat (abs B))) D
     in \<lparr>comma_python_affine_scale = A div int g,
         comma_python_affine_offset = B div int g,
         comma_python_affine_denominator = D div g\<rparr>)"

lemma comma_python_affine_normalize_evaluate_exact:
  fixes A B :: int and D S :: nat
  assumes denominator: "0 < D"
    and exact: "int D dvd (A * int S + B)"
  shows "comma_python_affine_evaluate
      (comma_python_affine_normalize A B D) S =
    (A * int S + B) div int D"
    "int (comma_python_affine_denominator
      (comma_python_affine_normalize A B D)) dvd
      (comma_python_affine_scale (comma_python_affine_normalize A B D) *
        int S + comma_python_affine_offset
          (comma_python_affine_normalize A B D))"
proof -
  let ?g = "gcd (gcd (nat (abs A)) (nat (abs B))) D"
  let ?a = "A div int ?g"
  let ?b = "B div int ?g"
  let ?d = "D div ?g"
  let ?numerator = "A * int S + B"
  let ?reduced_numerator = "?a * int S + ?b"
  have gpos: "0 < ?g"
    using denominator by simp
  have gA: "?g dvd nat (abs A)"
    by simp
  have gB: "?g dvd nat (abs B)"
    by simp
  have gD: "?g dvd D"
    by simp
  have gA_abs: "int ?g dvd abs A"
  proof -
    have "int ?g dvd int (nat (abs A))"
      using gA by exact_mod_cast
    also have "int (nat (abs A)) = abs A"
      by simp
    finally show ?thesis .
  qed
  have gB_abs: "int ?g dvd abs B"
  proof -
    have "int ?g dvd int (nat (abs B))"
      using gB by exact_mod_cast
    also have "int (nat (abs B)) = abs B"
      by simp
    finally show ?thesis .
  qed
  have gA_int: "int ?g dvd A"
    using gA_abs by (cases A) auto
  have gB_int: "int ?g dvd B"
    using gB_abs by (cases B) auto
  have A_mod: "A mod int ?g = 0"
    using gA_int gpos by (simp add: dvd_eq_mod_eq_0)
  have B_mod: "B mod int ?g = 0"
    using gB_int gpos by (simp add: dvd_eq_mod_eq_0)
  have A_decomp: "A = int ?g * ?a"
    using A_mod by (simp add: div_mult_mod_eq mult.commute)
  have B_decomp: "B = int ?g * ?b"
    using B_mod by (simp add: div_mult_mod_eq mult.commute)
  have D_mod: "D mod ?g = 0"
    using gD by (simp add: dvd_eq_mod_eq_0)
  have D_decomp: "D = ?g * ?d"
    using D_mod by (simp add: div_mult_mod_eq mult.commute)
  have dpos: "0 < ?d"
    using denominator D_decomp gpos by (cases ?d) auto
  have N_decomp: "?numerator = int ?g * ?reduced_numerator"
    using A_decomp B_decomp by (simp add: algebra_simps)
  have N_mod: "?numerator mod int D = 0"
    using exact denominator by (simp add: dvd_eq_mod_eq_0)
  have N_factor:
    "?numerator = (?numerator div int D) * int D"
    using N_mod by (simp add: div_mult_mod_eq)
  have D_factor: "int D = int ?g * int ?d"
    using D_decomp by simp
  have cancel:
    "int ?g * ?reduced_numerator =
      int ?g * ((?numerator div int D) * int ?d)"
    using N_decomp N_factor D_factor by (simp add: algebra_simps)
  have N_reduced:
    "?reduced_numerator = (?numerator div int D) * int ?d"
    using cancel gpos by (metis mult_left_cancel)
  show "comma_python_affine_evaluate
      (comma_python_affine_normalize A B D) S =
    (A * int S + B) div int D"
    unfolding comma_python_affine_evaluate_def
      comma_python_affine_normalize_def Let_def
    using N_reduced dpos
    by (simp add: algebra_simps)
  show "int (comma_python_affine_denominator
      (comma_python_affine_normalize A B D)) dvd
      (comma_python_affine_scale (comma_python_affine_normalize A B D) *
        int S + comma_python_affine_offset
          (comma_python_affine_normalize A B D))"
    unfolding comma_python_affine_normalize_def Let_def
    unfolding dvd_def
    using N_reduced
    by (rule exI[where x="?numerator div int D"])
      (simp add: algebra_simps)
qed

definition comma_python_affine_zero :: comma_python_affine_weight where
  "comma_python_affine_zero = comma_python_affine_normalize 0 0 1"

definition comma_python_affine_add ::
  "comma_python_affine_weight \<Rightarrow> comma_python_affine_weight
    \<Rightarrow> comma_python_affine_weight" where
  "comma_python_affine_add a b = comma_python_affine_normalize
    (comma_python_affine_scale a * int (comma_python_affine_denominator b) +
      comma_python_affine_scale b * int (comma_python_affine_denominator a))
    (comma_python_affine_offset a * int (comma_python_affine_denominator b) +
      comma_python_affine_offset b * int (comma_python_affine_denominator a))
    (comma_python_affine_denominator a * comma_python_affine_denominator b)"

definition comma_python_affine_times ::
  "nat \<Rightarrow> comma_python_affine_weight \<Rightarrow>
    comma_python_affine_weight" where
  "comma_python_affine_times n w = comma_python_affine_normalize
    (int n * comma_python_affine_scale w)
    (int n * comma_python_affine_offset w)
    (comma_python_affine_denominator w)"

definition comma_python_chart_affine_weight ::
  "nat \<Rightarrow> comma_chart_weight \<Rightarrow> comma_python_affine_weight" where
  "comma_python_chart_affine_weight delta w =
    (case w of Comma_Chart_Weight scale _ offset denominator \<Rightarrow>
      comma_python_affine_normalize
        (int (scale * 10 ^ delta)) offset denominator)"

definition comma_python_affine_raw_chart_weight ::
  "nat \<Rightarrow> comma_chart_weight \<Rightarrow> comma_python_affine_weight" where
  "comma_python_affine_raw_chart_weight delta w =
    (case w of Comma_Chart_Weight scale _ offset denominator \<Rightarrow>
      \<lparr>comma_python_affine_scale = int (scale * 10 ^ delta),
       comma_python_affine_offset = offset,
       comma_python_affine_denominator = denominator\<rparr>)"

definition comma_python_affine_equivalent ::
  "comma_python_affine_weight \<Rightarrow> comma_python_affine_weight \<Rightarrow> bool" where
  "comma_python_affine_equivalent a b \<longleftrightarrow>
    0 < comma_python_affine_denominator a \<and>
    0 < comma_python_affine_denominator b \<and>
    comma_python_affine_scale a * int (comma_python_affine_denominator b) =
      comma_python_affine_scale b * int (comma_python_affine_denominator a) \<and>
    comma_python_affine_offset a * int (comma_python_affine_denominator b) =
      comma_python_affine_offset b * int (comma_python_affine_denominator a)"

lemma comma_python_affine_zero_fields [simp]:
  "comma_python_affine_scale comma_python_affine_zero = 0"
  "comma_python_affine_offset comma_python_affine_zero = 0"
  "comma_python_affine_denominator comma_python_affine_zero = 1"
  by (simp_all add: comma_python_affine_zero_def
      comma_python_affine_normalize_def Let_def)

lemma comma_python_affine_normalize_positive_denominator:
  assumes "0 < D"
  shows "0 < comma_python_affine_denominator
      (comma_python_affine_normalize A B D)"
  using assms by (simp add: comma_python_affine_normalize_def Let_def)

lemma comma_python_affine_evaluate_integral:
  assumes exact:
    "int (comma_python_affine_denominator w) dvd
      (comma_python_affine_scale w * int S +
        comma_python_affine_offset w)"
  shows "comma_python_affine_evaluate w S *
      int (comma_python_affine_denominator w) =
    comma_python_affine_scale w * int S +
      comma_python_affine_offset w"
  using exact by (simp add: comma_python_affine_evaluate_def
      dvd_eq_mod_eq_0 div_mult_mod_eq)

lemma comma_python_affine_add_exact_at_scale:
  fixes a b :: comma_python_affine_weight and S :: nat
  assumes a_positive: "0 < comma_python_affine_denominator a"
    and b_positive: "0 < comma_python_affine_denominator b"
    and a_exact: "comma_python_affine_divides a S"
    and b_exact: "comma_python_affine_divides b S"
  shows "int (comma_python_affine_denominator (comma_python_affine_add a b)) dvd
      (comma_python_affine_scale (comma_python_affine_add a b) * int S +
        comma_python_affine_offset (comma_python_affine_add a b))"
    and "comma_python_affine_evaluate (comma_python_affine_add a b) S =
      comma_python_affine_evaluate a S + comma_python_affine_evaluate b S"
proof -
  let ?da = "comma_python_affine_denominator a"
  let ?db = "comma_python_affine_denominator b"
  let ?na = "comma_python_affine_scale a * int S + comma_python_affine_offset a"
  let ?nb = "comma_python_affine_scale b * int S + comma_python_affine_offset b"
  let ?A = "comma_python_affine_scale a * int ?db + comma_python_affine_scale b * int ?da"
  let ?B = "comma_python_affine_offset a * int ?db + comma_python_affine_offset b * int ?da"
  let ?D = "?da * ?db"
  obtain x where a_factor: "?na = int ?da * x"
    using a_exact unfolding comma_python_affine_divides_def dvd_def by blast
  obtain y where b_factor: "?nb = int ?db * y"
    using b_exact unfolding comma_python_affine_divides_def dvd_def by blast
  have raw_factor: "?A * int S + ?B = int ?D * (x + y)"
    using a_factor b_factor by (simp add: algebra_simps)
  have raw_exact: "int ?D dvd (?A * int S + ?B)"
    using raw_factor by (simp add: dvd_def)
  have D_positive: "0 < ?D" using a_positive b_positive by simp
  have D_nonzero: "int ?D \<noteq> 0" using D_positive by simp
  have raw_evaluate: "(?A * int S + ?B) div int ?D = x + y"
  proof -
    have remainder: "(?A * int S + ?B) mod int ?D = 0"
      using raw_exact D_positive by (simp add: dvd_eq_mod_eq_0)
    have quotient:
      "((?A * int S + ?B) div int ?D) * int ?D = ?A * int S + ?B"
      using remainder by (simp add: div_mult_mod_eq)
    show ?thesis using quotient raw_factor D_nonzero
      by (metis mult_left_cancel mult.commute)
  qed
  have normalized_evaluate:
    "comma_python_affine_evaluate
        (comma_python_affine_normalize ?A ?B ?D) S =
      (?A * int S + ?B) div int ?D"
    by (rule comma_python_affine_normalize_evaluate_exact(1)
      [OF D_positive raw_exact])
  have normalized_exact:
    "int (comma_python_affine_denominator
        (comma_python_affine_normalize ?A ?B ?D)) dvd
      (comma_python_affine_scale (comma_python_affine_normalize ?A ?B ?D) *
        int S + comma_python_affine_offset
          (comma_python_affine_normalize ?A ?B ?D))"
    by (rule comma_python_affine_normalize_evaluate_exact(2)
      [OF D_positive raw_exact])
  show "int (comma_python_affine_denominator (comma_python_affine_add a b)) dvd
      (comma_python_affine_scale (comma_python_affine_add a b) * int S +
        comma_python_affine_offset (comma_python_affine_add a b))"
    using normalized_exact by (simp only: comma_python_affine_add_def)
  have eval_a: "comma_python_affine_evaluate a S * int ?da = ?na"
    and eval_b: "comma_python_affine_evaluate b S * int ?db = ?nb"
    using comma_python_affine_evaluate_integral[OF a_exact]
      comma_python_affine_evaluate_integral[OF b_exact] .
  have da_nonzero: "int ?da \<noteq> 0" and db_nonzero: "int ?db \<noteq> 0"
    using a_positive b_positive by simp_all
  have eval_a_value: "comma_python_affine_evaluate a S = x"
    using eval_a a_factor da_nonzero by (metis mult_left_cancel mult.commute)
  have eval_b_value: "comma_python_affine_evaluate b S = y"
    using eval_b b_factor db_nonzero by (metis mult_left_cancel mult.commute)
  show "comma_python_affine_evaluate (comma_python_affine_add a b) S =
      comma_python_affine_evaluate a S + comma_python_affine_evaluate b S"
    using normalized_evaluate raw_evaluate eval_a_value eval_b_value
    by (simp add: comma_python_affine_add_def)
qed

definition comma_python_affine_at_decimal_exponent ::
  "comma_python_affine_weight \<Rightarrow> nat \<Rightarrow> int" where
  "comma_python_affine_at_decimal_exponent w p =
    comma_python_affine_evaluate w (10 ^ p)"

lemma comma_python_raw_chart_affine_value:
  "comma_python_affine_at_decimal_exponent
      (comma_python_affine_raw_chart_weight delta w) p =
    (case w of Comma_Chart_Weight scale _ offset denominator \<Rightarrow>
      (int (scale * 10 ^ (p + delta)) + offset) div int denominator)"
  by (cases w) (simp add: comma_python_affine_at_decimal_exponent_def
    comma_python_affine_evaluate_def comma_python_affine_raw_chart_weight_def
    power_add mult.assoc)

definition comma_python_entry_sector_fragment ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    comma_python_sector_fragment" where
  "comma_python_entry_sector_fragment f delta offset h =
    (let P = comma_finite_period f (offset mod 10);
         L = comma_cycle_length f
     in \<lparr>comma_python_fragment_leading = f,
         comma_python_fragment_entering_digit = offset mod 10,
         comma_python_fragment_complete_cycles =
           comma_python_affine_normalize
             (int (10 ^ delta)) (- int (offset + h)) P,
         comma_python_fragment_period = L,
         comma_python_fragment_displacement = P,
         comma_python_fragment_maximum_guard =
           comma_phase_max_guard f (offset mod 10) L,
         comma_python_fragment_literal_steps = 0,
         comma_python_fragment_literal_increment = 0\<rparr>)"

definition comma_python_literal_fragment ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    comma_python_sector_fragment" where
  "comma_python_literal_fragment f digit steps increment =
    \<lparr>comma_python_fragment_leading = f,
     comma_python_fragment_entering_digit = digit mod 10,
     comma_python_fragment_complete_cycles = comma_python_affine_zero,
     comma_python_fragment_period = 0,
     comma_python_fragment_displacement = 0,
     comma_python_fragment_maximum_guard = 0,
     comma_python_fragment_literal_steps = steps,
     comma_python_fragment_literal_increment = increment\<rparr>"

lemma comma_python_literal_fragment_fields [simp]:
  "comma_python_fragment_leading (comma_python_literal_fragment f d n inc) = f"
  "comma_python_fragment_entering_digit (comma_python_literal_fragment f d n inc) = d mod 10"
  "comma_python_fragment_period (comma_python_literal_fragment f d n inc) = 0"
  "comma_python_fragment_displacement (comma_python_literal_fragment f d n inc) = 0"
  "comma_python_fragment_maximum_guard (comma_python_literal_fragment f d n inc) = 0"
  "comma_python_fragment_literal_steps (comma_python_literal_fragment f d n inc) = n"
  "comma_python_fragment_literal_increment (comma_python_literal_fragment f d n inc) = inc"
  by (simp_all add: comma_python_literal_fragment_def)

definition comma_python_fragment_weight_at_scale ::
  "comma_python_sector_fragment \<Rightarrow> nat \<Rightarrow> int" where
  "comma_python_fragment_weight_at_scale g S =
    int (comma_python_fragment_period g) *
      comma_python_affine_evaluate
        (comma_python_fragment_complete_cycles g) S +
    int (comma_python_fragment_literal_steps g)"

definition comma_python_fragment_displacement_at_scale ::
  "comma_python_sector_fragment \<Rightarrow> nat \<Rightarrow> int" where
  "comma_python_fragment_displacement_at_scale g S =
    int (comma_python_fragment_displacement g) *
      comma_python_affine_evaluate
        (comma_python_fragment_complete_cycles g) S +
    int (comma_python_fragment_literal_increment g)"

lemma comma_python_entry_fragment_fields:
  "comma_python_fragment_leading
      (comma_python_entry_sector_fragment f delta offset h) = f"
  "comma_python_fragment_entering_digit
      (comma_python_entry_sector_fragment f delta offset h) = offset mod 10"
  "comma_python_fragment_period
      (comma_python_entry_sector_fragment f delta offset h) =
        comma_cycle_length f"
  "comma_python_fragment_displacement
      (comma_python_entry_sector_fragment f delta offset h) =
        comma_finite_period f (offset mod 10)"
  "comma_python_fragment_maximum_guard
      (comma_python_entry_sector_fragment f delta offset h) =
        comma_phase_max_guard f (offset mod 10) (comma_cycle_length f)"
  "comma_python_fragment_literal_steps
      (comma_python_entry_sector_fragment f delta offset h) = 0"
  "comma_python_fragment_literal_increment
      (comma_python_entry_sector_fragment f delta offset h) = 0"
  by (simp_all add: comma_python_entry_sector_fragment_def Let_def)

text \<open>This is the fieldwise Entry bridge to the producer record.  The
reduced cycle triple evaluates to the number of complete digit cycles; its
period-weight is exactly the first component emitted by the canonical
weighted chart move.  The guard and displacement fields are the checked
cycle data, and this branch emits no literal Near steps.\<close>

theorem comma_python_entry_fragment_refines_chart_move:
  fixes f p delta offset :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and offset: "offset \<le> 98"
  defines "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "L \<equiv> comma_cycle_length f"
    and "c \<equiv> (10 ^ (p + delta) - offset - h) div P"
    and "fragment \<equiv> comma_python_entry_sector_fragment f delta offset h"
  shows "comma_weighted_step (p mod 924) (Comma_Entry f delta offset) =
      Comma_WNext (Comma_Near f delta h)
        (Comma_Chart_Weight L delta (- int (L * (offset + h))) P)"
    "0 < comma_python_affine_denominator
        (comma_python_fragment_complete_cycles fragment)"
    "comma_python_affine_divides
        (comma_python_fragment_complete_cycles fragment) (10 ^ p)"
    "comma_python_affine_evaluate
        (comma_python_fragment_complete_cycles fragment) (10 ^ p) = int c"
    "comma_python_fragment_weight_at_scale fragment (10 ^ p) =
        int (comma_chart_weight_value p
          (Comma_Chart_Weight L delta (- int (L * (offset + h))) P))"
    "comma_python_fragment_displacement_at_scale fragment (10 ^ p) =
        int (c * P)"
    "comma_python_affine_equivalent
       (comma_python_fragment_complete_cycles fragment)
       (comma_python_affine_normalize
          (int (10 ^ delta)) (- int (offset + h)) P)"
proof -
  note entry = comma_entry_chart_exact_literal_path[OF f exponent offset,
      of delta]
  have entry_fields:
    "comma_weighted_step (p mod 924) (Comma_Entry f delta offset) =
      Comma_WNext (Comma_Near f delta h)
        (Comma_Chart_Weight L delta (- int (L * (offset + h))) P)"
    using entry by (simp add: h_def P_def L_def)
  show "comma_weighted_step (p mod 924) (Comma_Entry f delta offset) =
      Comma_WNext (Comma_Near f delta h)
        (Comma_Chart_Weight L delta (- int (L * (offset + h))) P)"
    by (rule entry_fields)
  have f_positive: "0 < f" using f by simp
  have period_positive:
    "0 < comma_period_displacement f (offset mod 10)
      (comma_cycle_length f)"
    by (rule comma_period_displacement_admitted[OF f_positive
        comma_cycle_length_admitted(1)[OF f]])
  have period_exact:
    "comma_finite_period f (offset mod 10) =
      comma_period_displacement f (offset mod 10)
        (comma_cycle_length f)"
    by (rule comma_finite_period_refines[OF f]; simp)
  have nonzero: "0 < P"
    using period_positive period_exact by (simp add: P_def)
  have cycle_length: "0 < L"
    using comma_cycle_length_admitted(1)[OF f] by (simp add: L_def)
  have bound_product:
    "L * (offset + h) \<le> L * 10 ^ (p + delta)"
  proof -
    have int_bound:
      "int (L * (offset + h)) \<le> int (L * 10 ^ (p + delta))"
      using entry(9) by (simp add: h_def L_def)
    show ?thesis using int_bound by exact_mod_cast
  qed
  have bound: "offset + h \<le> 10 ^ (p + delta)"
    using bound_product cycle_length
    by (meson mult_le_cancel_left_pos)
  have period_divides: "P dvd 10 ^ (p + delta) - offset - h"
    using entry(8) by (simp add: P_def h_def)
  have displacement:
    "10 ^ (p + delta) - offset - h = c * P"
  proof -
    have factor:
      "10 ^ (p + delta) - offset - h =
        ((10 ^ (p + delta) - offset - h) div P) * P"
      using period_divides nonzero by (simp add: div_mult_mod_eq)
    show ?thesis using factor by (simp add: c_def)
  qed
  have exact_numerator:
    "int P dvd (int (10 ^ delta) * int (10 ^ p) - int (offset + h))"
  proof -
    have cast_divides:
      "int P dvd int (10 ^ (p + delta) - offset - h)"
      using period_divides by exact_mod_cast
    have numerator:
      "int (10 ^ (p + delta) - offset - h) =
        int (10 ^ delta) * int (10 ^ p) - int (offset + h)"
      using bound by (simp add: power_add algebra_simps)
    show ?thesis using cast_divides numerator by simp
  qed
  have count:
    "comma_python_affine_evaluate
        (comma_python_affine_normalize
          (int (10 ^ delta)) (- int (offset + h)) P) (10 ^ p) = int c"
  proof -
    have normalized:
      "comma_python_affine_evaluate
          (comma_python_affine_normalize
            (int (10 ^ delta)) (- int (offset + h)) P) (10 ^ p) =
        (int (10 ^ delta) * int (10 ^ p) - int (offset + h)) div int P"
      by (rule comma_python_affine_normalize_evaluate_exact(1)[OF nonzero
          exact_numerator])
    have numerator_value:
      "int (10 ^ delta) * int (10 ^ p) - int (offset + h) =
        int c * int P"
      using displacement bound by (simp add: power_add algebra_simps)
    show ?thesis using normalized numerator_value nonzero by simp
  qed
  show "0 < comma_python_affine_denominator
      (comma_python_fragment_complete_cycles fragment)"
    using comma_python_affine_normalize_positive_denominator[OF nonzero]
    by (simp add: fragment_def comma_python_entry_sector_fragment_def Let_def)
  show "comma_python_affine_divides
      (comma_python_fragment_complete_cycles fragment) (10 ^ p)"
  proof -
    have normalized_divides:
      "int (comma_python_affine_denominator
          (comma_python_affine_normalize
            (int (10 ^ delta)) (- int (offset + h)) P)) dvd
        (comma_python_affine_scale
          (comma_python_affine_normalize
            (int (10 ^ delta)) (- int (offset + h)) P) * int (10 ^ p) +
         comma_python_affine_offset
          (comma_python_affine_normalize
            (int (10 ^ delta)) (- int (offset + h)) P))"
      by (rule comma_python_affine_normalize_evaluate_exact(2)[OF nonzero
          exact_numerator])
    show ?thesis using normalized_divides
      by (simp add: comma_python_affine_divides_def fragment_def
          comma_python_entry_sector_fragment_def Let_def)
  qed
  show "comma_python_affine_evaluate
        (comma_python_fragment_complete_cycles fragment) (10 ^ p) = int c"
    using count by (simp add: fragment_def
      comma_python_entry_sector_fragment_def Let_def)
  have chart_weight:
    "comma_chart_weight_value p
      (Comma_Chart_Weight L delta (- int (L * (offset + h))) P) = L*c"
    using comma_chart_weight_entry_exact[OF nonzero bound displacement]
    by simp
  show "comma_python_fragment_weight_at_scale fragment (10 ^ p) =
      int (comma_chart_weight_value p
        (Comma_Chart_Weight L delta (- int (L * (offset + h))) P))"
    using chart_weight count
    by (simp add: comma_python_fragment_weight_at_scale_def
        fragment_def comma_python_entry_sector_fragment_def Let_def
        P_def L_def)
  show "comma_python_fragment_displacement_at_scale fragment (10 ^ p) =
      int (c * P)"
    using count by (simp add: comma_python_fragment_displacement_at_scale_def
        fragment_def comma_python_entry_sector_fragment_def Let_def
        P_def L_def)
  show "comma_python_affine_equivalent
      (comma_python_fragment_complete_cycles fragment)
      (comma_python_affine_normalize
        (int (10 ^ delta)) (- int (offset + h)) P)"
    using period_positive
    by (simp add: fragment_def comma_python_entry_sector_fragment_def
        comma_python_affine_equivalent_def Let_def)
qed

definition comma_python_fragment_is_literal ::
  "comma_python_sector_fragment \<Rightarrow> bool" where
  "comma_python_fragment_is_literal g \<longleftrightarrow>
    comma_python_fragment_period g = 0"

lemma comma_python_fixed_iter_add:
  "comma_fixed_iter f (n + m) k =
    comma_fixed_iter f m (comma_fixed_iter f n k)"
proof (induction m)
  case "0"
  then show ?case by simp
next
  case (Suc m)
  then show ?case by (simp add: add.assoc)
qed

lemma comma_python_period_displacement_append:
  "comma_period_displacement f (d mod 10) (n + m) =
    comma_period_displacement f (d mod 10) n +
      comma_period_displacement f ((d + n * f) mod 10) m"
proof -
  have phase:
    "(d + comma_period_displacement f (d mod 10) n) mod 10 =
      (d + n * f) mod 10"
    using comma_fixed_iter_phase[of f n d]
      comma_fixed_iter_displacement[of f n d]
    by (simp add: add.commute add.left_commute)
  have iter:
    "comma_fixed_iter f (n + m) d =
      comma_fixed_iter f m (comma_fixed_iter f n d)"
    by (rule comma_python_fixed_iter_add)
  show ?thesis
    using iter phase
      comma_fixed_iter_displacement[of f "n + m" d]
      comma_fixed_iter_displacement[of f n d]
      comma_fixed_iter_displacement[of f m
        "comma_fixed_iter f n d"]
    by (simp add: algebra_simps add_left_cancel)
qed

definition comma_python_near_fragment_shape ::
  "comma_python_sector_fragment \<Rightarrow> bool" where
  "comma_python_near_fragment_shape g \<longleftrightarrow>
    1 \<le> comma_python_fragment_leading g \<and>
    comma_python_fragment_leading g \<le> 9 \<and>
    comma_python_fragment_entering_digit g < 10 \<and>
    comma_python_fragment_period g = 0 \<and>
    comma_python_fragment_displacement g = 0 \<and>
    comma_python_fragment_maximum_guard g = 0 \<and>
    comma_python_affine_scale
      (comma_python_fragment_complete_cycles g) = 0 \<and>
    comma_python_affine_offset
      (comma_python_fragment_complete_cycles g) = 0 \<and>
    comma_python_affine_denominator
      (comma_python_fragment_complete_cycles g) = 1"

lemma comma_python_literal_fragment_near_shape:
  assumes f: "1 \<le> f" "f \<le> 9"
  shows
  "comma_python_near_fragment_shape
    (comma_python_literal_fragment f d n inc)"
  using f by (simp add: comma_python_near_fragment_shape_def
      comma_python_literal_fragment_def comma_python_affine_zero_def
      comma_python_affine_normalize_def Let_def)

definition comma_python_near_fragments_compatible ::
  "comma_python_sector_fragment \<Rightarrow> comma_python_sector_fragment
    \<Rightarrow> bool" where
  "comma_python_near_fragments_compatible a b \<longleftrightarrow>
    comma_python_near_fragment_shape a \<and>
    comma_python_near_fragment_shape b \<and>
    comma_python_fragment_leading a = comma_python_fragment_leading b \<and>
    comma_python_fragment_entering_digit b =
      (comma_python_fragment_entering_digit a +
        comma_python_fragment_literal_steps a *
          comma_python_fragment_leading a) mod 10"

definition comma_python_merge_near_fragments ::
  "comma_python_sector_fragment \<Rightarrow> comma_python_sector_fragment
    \<Rightarrow> comma_python_sector_fragment" where
  "comma_python_merge_near_fragments a b =
    (if comma_python_near_fragments_compatible a b then
      \<lparr>comma_python_fragment_leading = comma_python_fragment_leading a,
       comma_python_fragment_entering_digit =
         comma_python_fragment_entering_digit a,
       comma_python_fragment_complete_cycles = comma_python_affine_zero,
       comma_python_fragment_period = 0,
       comma_python_fragment_displacement = 0,
       comma_python_fragment_maximum_guard = 0,
       comma_python_fragment_literal_steps =
         comma_python_fragment_literal_steps a +
           comma_python_fragment_literal_steps b,
       comma_python_fragment_literal_increment =
         comma_python_fragment_literal_increment a +
           comma_python_fragment_literal_increment b\<rparr>
     else a)"

lemma comma_python_merge_near_fields:
  assumes compatible:
    "comma_python_near_fragments_compatible a b"
  shows "comma_python_fragment_leading
      (comma_python_merge_near_fragments a b) =
        comma_python_fragment_leading a"
    "comma_python_fragment_entering_digit
      (comma_python_merge_near_fragments a b) =
        comma_python_fragment_entering_digit a"
    "comma_python_fragment_literal_steps
      (comma_python_merge_near_fragments a b) =
        comma_python_fragment_literal_steps a +
          comma_python_fragment_literal_steps b"
    "comma_python_fragment_literal_increment
      (comma_python_merge_near_fragments a b) =
        comma_python_fragment_literal_increment a +
          comma_python_fragment_literal_increment b"
    "comma_python_fragment_period
      (comma_python_merge_near_fragments a b) = 0"
    "comma_python_fragment_displacement
      (comma_python_merge_near_fragments a b) = 0"
    "comma_python_fragment_maximum_guard
      (comma_python_merge_near_fragments a b) = 0"
    "comma_python_affine_equivalent
      (comma_python_fragment_complete_cycles
        (comma_python_merge_near_fragments a b)) comma_python_affine_zero"
  using compatible
  by (simp_all add: comma_python_merge_near_fragments_def
      comma_python_near_fragments_compatible_def
      comma_python_near_fragment_shape_def)

lemma comma_python_merge_near_preserves_weight:
  assumes compatible: "comma_python_near_fragments_compatible a b"
  shows "comma_python_fragment_weight_at_scale
      (comma_python_merge_near_fragments a b) S =
    comma_python_fragment_weight_at_scale a S +
      comma_python_fragment_weight_at_scale b S"
  using compatible
  by (simp add: comma_python_fragment_weight_at_scale_def
      comma_python_merge_near_fragments_def
      comma_python_near_fragments_compatible_def
      comma_python_near_fragment_shape_def)

lemma comma_python_merge_near_preserves_displacement:
  assumes compatible: "comma_python_near_fragments_compatible a b"
  shows "comma_python_fragment_displacement_at_scale
      (comma_python_merge_near_fragments a b) S =
    comma_python_fragment_displacement_at_scale a S +
      comma_python_fragment_displacement_at_scale b S"
  using compatible
  by (simp add: comma_python_fragment_displacement_at_scale_def
      comma_python_merge_near_fragments_def
      comma_python_near_fragments_compatible_def
      comma_python_near_fragment_shape_def)

lemma comma_python_merge_near_phase_increment:
  assumes compatible: "comma_python_near_fragments_compatible a b"
    and increment_a:
      "comma_python_fragment_literal_increment a =
        comma_period_displacement (comma_python_fragment_leading a)
          (comma_python_fragment_entering_digit a)
          (comma_python_fragment_literal_steps a)"
    and increment_b:
      "comma_python_fragment_literal_increment b =
        comma_period_displacement (comma_python_fragment_leading b)
          (comma_python_fragment_entering_digit b)
          (comma_python_fragment_literal_steps b)"
  shows "comma_python_fragment_literal_increment
      (comma_python_merge_near_fragments a b) =
    comma_period_displacement (comma_python_fragment_leading a)
      (comma_python_fragment_entering_digit a)
      (comma_python_fragment_literal_steps a +
        comma_python_fragment_literal_steps b)"
proof -
  have leading:
    "comma_python_fragment_leading a = comma_python_fragment_leading b"
    using compatible by (simp add: comma_python_near_fragments_compatible_def)
  have phase_b:
    "comma_python_fragment_entering_digit b =
      (comma_python_fragment_entering_digit a +
        comma_python_fragment_literal_steps a *
          comma_python_fragment_leading a) mod 10"
    using compatible by (simp add: comma_python_near_fragments_compatible_def)
  have append:
    "comma_period_displacement (comma_python_fragment_leading a)
        (comma_python_fragment_entering_digit a)
        (comma_python_fragment_literal_steps a +
          comma_python_fragment_literal_steps b) =
      comma_period_displacement (comma_python_fragment_leading a)
        (comma_python_fragment_entering_digit a)
        (comma_python_fragment_literal_steps a) +
      comma_period_displacement (comma_python_fragment_leading a)
        ((comma_python_fragment_entering_digit a +
          comma_python_fragment_literal_steps a *
            comma_python_fragment_leading a) mod 10)
        (comma_python_fragment_literal_steps b)"
    by (rule comma_python_period_displacement_append)
  show ?thesis
    using append phase_b leading increment_a increment_b compatible
    by (simp add: comma_python_merge_near_fragments_def
        comma_python_near_fragments_compatible_def)
qed

lemma comma_python_merge_near_shape:
  assumes compatible: "comma_python_near_fragments_compatible a b"
  shows "comma_python_near_fragment_shape
      (comma_python_merge_near_fragments a b)"
  using compatible
  by (simp add: comma_python_near_fragment_shape_def
      comma_python_merge_near_fragments_def
      comma_python_near_fragments_compatible_def)

fun comma_python_prefix_scan :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "comma_python_prefix_scan [] z = [z]"
| "comma_python_prefix_scan (x # xs) z =
    z # comma_python_prefix_scan xs (z+x)"

definition comma_python_prefix_weights_at_scale ::
  "comma_python_sector_fragment list \<Rightarrow> nat \<Rightarrow> int list" where
  "comma_python_prefix_weights_at_scale fragments S =
    comma_python_prefix_scan
      (map (\<lambda>g. comma_python_fragment_weight_at_scale g S) fragments) 0"

definition comma_python_prefix_displacements_at_scale ::
  "comma_python_sector_fragment list \<Rightarrow> nat \<Rightarrow> int list" where
  "comma_python_prefix_displacements_at_scale fragments S =
    comma_python_prefix_scan
      (map (\<lambda>g. comma_python_fragment_displacement_at_scale g S) fragments) 0"

lemma comma_python_prefix_scan_length:
  "length (comma_python_prefix_scan xs z) = Suc (length xs)"
  by (induction xs arbitrary: z) simp_all

lemma comma_python_prefix_scan_nth:
  assumes index: "i \<le> length xs"
  shows "comma_python_prefix_scan xs z ! i =
    z + sum_list (take i xs)"
  using index
proof (induction xs arbitrary: i z)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases i)
    case "0"
    then show ?thesis by simp
  next
    case (Suc j)
    have j: "j \<le> length xs" using Cons.prems Suc by simp
    show ?thesis using Cons.IH[OF j, of "z+x"] Suc
      by (simp add: add.assoc)
  qed
qed

lemma comma_python_prefix_weights_nth:
  assumes index: "i \<le> length fragments"
  shows "comma_python_prefix_weights_at_scale fragments S ! i =
    sum_list (map (\<lambda>g. comma_python_fragment_weight_at_scale g S)
      (take i fragments))"
  using comma_python_prefix_scan_nth[OF index, of
    "map (\<lambda>g. comma_python_fragment_weight_at_scale g S) fragments" 0]
  by (simp add: comma_python_prefix_weights_at_scale_def)

lemma comma_python_prefix_displacements_nth:
  assumes index: "i \<le> length fragments"
  shows "comma_python_prefix_displacements_at_scale fragments S ! i =
    sum_list (map (\<lambda>g. comma_python_fragment_displacement_at_scale g S)
      (take i fragments))"
  using comma_python_prefix_scan_nth[OF index, of
    "map (\<lambda>g. comma_python_fragment_displacement_at_scale g S) fragments" 0]
  by (simp add: comma_python_prefix_displacements_at_scale_def)

definition comma_python_fragment_select ::
  "comma_python_sector_fragment \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "comma_python_fragment_select g S remaining =
    (if comma_python_fragment_period g = 0 then
       if remaining = comma_python_fragment_literal_steps g then
         comma_python_fragment_displacement_at_scale g S
       else
         int (comma_period_displacement
           (comma_python_fragment_leading g)
           (comma_python_fragment_entering_digit g) remaining)
     else
       int (remaining div comma_python_fragment_period g) *
         int (comma_python_fragment_displacement g) +
       int (comma_period_displacement
         (comma_python_fragment_leading g)
         (comma_python_fragment_entering_digit g)
         (remaining mod comma_python_fragment_period g)))"

lemma comma_python_near_fragment_select:
  assumes shape: "comma_python_near_fragment_shape g"
    and increment:
      "comma_python_fragment_literal_increment g =
        comma_period_displacement (comma_python_fragment_leading g)
          (comma_python_fragment_entering_digit g)
          (comma_python_fragment_literal_steps g)"
  shows "comma_python_fragment_select g S remaining =
    int (comma_period_displacement (comma_python_fragment_leading g)
      (comma_python_fragment_entering_digit g) remaining)"
proof (cases "remaining = comma_python_fragment_literal_steps g")
  case True
  then show ?thesis using shape increment
    by (simp add: comma_python_fragment_select_def
        comma_python_fragment_displacement_at_scale_def
        comma_python_near_fragment_shape_def
        comma_python_affine_evaluate_def)
next
  case False
  then show ?thesis using shape
    by (simp add: comma_python_fragment_select_def
        comma_python_near_fragment_shape_def)
qed

lemma comma_python_merge_near_selection:
  assumes compatible: "comma_python_near_fragments_compatible a b"
    and increment_a:
      "comma_python_fragment_literal_increment a =
        comma_period_displacement (comma_python_fragment_leading a)
          (comma_python_fragment_entering_digit a)
          (comma_python_fragment_literal_steps a)"
    and increment_b:
      "comma_python_fragment_literal_increment b =
        comma_period_displacement (comma_python_fragment_leading b)
          (comma_python_fragment_entering_digit b)
          (comma_python_fragment_literal_steps b)"
    and remaining: "j \<le> comma_python_fragment_literal_steps b"
  shows "comma_python_fragment_select
      (comma_python_merge_near_fragments a b) S
      (comma_python_fragment_literal_steps a + j) =
    comma_python_fragment_select a S
      (comma_python_fragment_literal_steps a) +
    comma_python_fragment_select b S j"
proof -
  have shape_a:
    "comma_python_near_fragment_shape a"
    and shape_b: "comma_python_near_fragment_shape b"
    using compatible by (simp_all add: comma_python_near_fragments_compatible_def)
  have leading:
    "comma_python_fragment_leading a = comma_python_fragment_leading b"
    using compatible by (simp add: comma_python_near_fragments_compatible_def)
  have digit_b:
    "comma_python_fragment_entering_digit b =
      (comma_python_fragment_entering_digit a +
        comma_python_fragment_literal_steps a *
          comma_python_fragment_leading a) mod 10"
    using compatible by (simp add: comma_python_near_fragments_compatible_def)
  have merged_increment:
    "comma_python_fragment_literal_increment
       (comma_python_merge_near_fragments a b) =
      comma_period_displacement
        (comma_python_fragment_leading
          (comma_python_merge_near_fragments a b))
        (comma_python_fragment_entering_digit
          (comma_python_merge_near_fragments a b))
        (comma_python_fragment_literal_steps
          (comma_python_merge_near_fragments a b))"
    using comma_python_merge_near_phase_increment
      [OF compatible increment_a increment_b]
    by (simp add: comma_python_merge_near_fragments_def)
  have merged_select:
    "comma_python_fragment_select
       (comma_python_merge_near_fragments a b) S
       (comma_python_fragment_literal_steps a + j) =
      int (comma_period_displacement (comma_python_fragment_leading a)
        (comma_python_fragment_entering_digit a)
        (comma_python_fragment_literal_steps a + j))"
    using comma_python_near_fragment_select
      [OF comma_python_merge_near_shape[OF compatible] merged_increment,
        of S "comma_python_fragment_literal_steps a + j"]
    by (simp add: comma_python_merge_near_fragments_def)
  have first_select:
    "comma_python_fragment_select a S
        (comma_python_fragment_literal_steps a) =
      int (comma_period_displacement (comma_python_fragment_leading a)
        (comma_python_fragment_entering_digit a)
        (comma_python_fragment_literal_steps a))"
    by (rule comma_python_near_fragment_select[OF shape_a increment_a])
  have second_select:
    "comma_python_fragment_select b S j =
      int (comma_period_displacement (comma_python_fragment_leading b)
        (comma_python_fragment_entering_digit b) j)"
    by (rule comma_python_near_fragment_select[OF shape_b increment_b])
  have append:
    "comma_period_displacement (comma_python_fragment_leading a)
        (comma_python_fragment_entering_digit a)
        (comma_python_fragment_literal_steps a + j) =
      comma_period_displacement (comma_python_fragment_leading a)
        (comma_python_fragment_entering_digit a)
        (comma_python_fragment_literal_steps a) +
      comma_period_displacement (comma_python_fragment_leading b)
        (comma_python_fragment_entering_digit b) j"
    using comma_python_period_displacement_append[of
        "comma_python_fragment_leading a"
        "comma_python_fragment_entering_digit a"
        "comma_python_fragment_literal_steps a" j]
      digit_b leading by simp
  show ?thesis
    using merged_select first_select second_select append
    by (simp add: of_nat_add)
qed

text \<open>The executable indexed producer's local point formula is now tied
to the checked cycle closed form for an Entry sector.  The quotient is the
number of complete cycles, the remainder selects at most one ten-digit
phase, and the selected value agrees with the chart's partial Entry path.\<close>

theorem comma_python_entry_fragment_selection:
  fixes f p delta offset j :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and offset: "offset \<le> 98"
    and bound: "j \<le> ((10 ^ (p + delta) - offset -
      comma_finite_headroom f (p mod 924) delta offset) div
      comma_finite_period f (offset mod 10)) * comma_cycle_length f"
  defines "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "L \<equiv> comma_cycle_length f"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "fragment \<equiv> comma_python_entry_sector_fragment f delta offset h"
    and "k \<equiv> comma_chart_value p (Comma_Entry f delta offset)"
  shows "comma_chart_fragment_closed p (Comma_Entry f delta offset)
      (Comma_Near f delta h) j =
    k + comma_python_fragment_select fragment (10 ^ p) j"
proof -
  note selected = comma_admitted_entry_partial_selection(6)
    [OF f exponent offset bound, of delta]
  have formula:
    "comma_chart_fragment_closed p (Comma_Entry f delta offset)
       (Comma_Near f delta h) j =
     k + (j div L) * P +
       comma_period_displacement f (offset mod 10) (j mod L)"
    using selected(6) by (simp add: comma_chart_fragment_closed_def
      Let_def h_def L_def P_def k_def)
  show ?thesis
    using formula
    by (simp add: comma_python_fragment_select_def
        comma_python_fragment_weight_at_scale_def
        comma_python_fragment_displacement_at_scale_def
        fragment_def comma_python_entry_sector_fragment_def
        Let_def L_def P_def)
qed

lemmas comma_python_fragment_refinement_oracle_audit_bundle =
  comma_python_entry_fragment_refines_chart_move
  comma_python_merge_near_selection
  comma_python_entry_fragment_selection comma_python_affine_add_exact_at_scale

ML \<open>
val _ = if null (Thm_Deps.all_oracles @{thms
  comma_python_fragment_refinement_oracle_audit_bundle
}) then () else error "Comma_Semantic_Fragment_Refinement local oracle audit failed"
\<close>

end
