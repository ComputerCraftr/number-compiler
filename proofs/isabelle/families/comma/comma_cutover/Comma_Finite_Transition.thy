theory Comma_Finite_Transition
  imports Comma_Arithmetic.Comma_Literal_Path Comma_Arithmetic.Comma_Finite_Period
begin

text \<open>This is the small arithmetic state for a boundary macro.  An entry
stores the offset from the bottom of its decimal sector.  A near-boundary
state stores headroom from the top.  The complete phase-cycle count is
eliminated by the period guard; it is not an additional quotient state.
The source residue and scale shift determine the modular headroom.\<close>

datatype comma_finite_position =
    Comma_Entry nat nat nat
  | Comma_Near nat nat nat

datatype comma_finite_move =
    Comma_Next comma_finite_position
  | Comma_Fork nat nat
  | Comma_Landmine nat
  | Comma_Invalid

datatype comma_finite_outcome =
    Comma_Fork_At nat nat
  | Comma_Landmine_At nat

datatype comma_chart_weight =
  Comma_Chart_Weight nat nat int nat

definition comma_chart_weight_value ::
  "nat \<Rightarrow> comma_chart_weight \<Rightarrow> nat" where
  "comma_chart_weight_value p weight =
    (case weight of Comma_Chart_Weight scale delta offset denominator
      \<Rightarrow> nat ((int (scale * 10 ^ (p + delta)) + offset) div
        int denominator))"

lemma comma_chart_weight_unit [simp]:
  "comma_chart_weight_value p (Comma_Chart_Weight 0 0 1 1) = 1"
  by (simp add: comma_chart_weight_value_def)

lemma comma_chart_weight_entry_exact:
  fixes p delta offset h P L c :: nat
  assumes positive: "0 < P"
    and bound: "offset + h \<le> 10 ^ (p + delta)"
    and displacement:
      "10 ^ (p + delta) - offset - h = c * P"
  shows "comma_chart_weight_value p
      (Comma_Chart_Weight L delta (- int (L * (offset + h))) P)
    = L * c"
proof -
  let ?K = "(10::nat) ^ (p + delta)"
  have K: "?K = offset + h + c * P"
    using bound displacement by arith
  have numerator:
    "int (L * ?K) - int (L * (offset + h)) = int (L * c * P)"
    using K by (simp add: algebra_simps)
  have cast: "nat (int L * int c) = L * c"
    by (simp only: of_nat_mult[symmetric] nat_int)
  show ?thesis
    using numerator positive cast
    by (simp add: comma_chart_weight_value_def div_mult_self4)
qed

datatype comma_weighted_move =
    Comma_WNext comma_finite_position comma_chart_weight
  | Comma_WFork comma_finite_position nat nat
  | Comma_WLandmine comma_finite_position nat
  | Comma_WInvalid

fun comma_erase_weight ::
  "comma_weighted_move \<Rightarrow> comma_finite_move" where
  "comma_erase_weight (Comma_WNext next weight) = Comma_Next next"
| "comma_erase_weight (Comma_WFork terminal a delta) =
    Comma_Fork a delta"
| "comma_erase_weight (Comma_WLandmine terminal delta) =
    Comma_Landmine delta"
| "comma_erase_weight Comma_WInvalid = Comma_Invalid"

definition comma_weighted_step_with_headroom ::
  "(nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
    nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_weighted_move" where
  "comma_weighted_step_with_headroom headroom_of residue position =
    (case position of
      Comma_Entry f delta offset \<Rightarrow>
        if f < 1 \<or> 9 < f \<or> 98 < offset \<or>
           comma_finite_period f (offset mod 10) = 0
        then Comma_WInvalid
        else
          (let h = headroom_of f residue delta offset;
               P = comma_finite_period f (offset mod 10);
               L = comma_cycle_length f
           in Comma_WNext (Comma_Near f delta h)
             (Comma_Chart_Weight L delta
               (- int (L * (offset + h))) P))
    | Comma_Near f delta headroom \<Rightarrow>
        if f < 1 \<or> 9 < f \<or> headroom = 0 \<or> 540 < headroom
        then Comma_WInvalid
        else
          (let d = (10 - headroom mod 10) mod 10 in
            if f < 9 then
              (let low = 10 * d + f in
                if headroom > low + 1 then
                  Comma_WNext (Comma_Near f delta (headroom - low))
                    (Comma_Chart_Weight 0 0 1 1)
                else if headroom = low + 1 then
                  Comma_WFork position (f + 1) delta
                else Comma_WNext
                  (Comma_Entry (f + 1) delta (low + 1 - headroom))
                    (Comma_Chart_Weight 0 0 1 1))
            else
              (let same = 10 * d + 9; cross = 10 * d + 1 in
                if headroom > same then
                  Comma_WNext (Comma_Near 9 delta (headroom - same))
                    (Comma_Chart_Weight 0 0 1 1)
                else if headroom \<le> cross then
                  Comma_WNext (Comma_Entry 1 (Suc delta)
                    (cross - headroom)) (Comma_Chart_Weight 0 0 1 1)
                else Comma_WLandmine position delta)))"

definition comma_weighted_step ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_weighted_move" where
  "comma_weighted_step residue position =
    comma_weighted_step_with_headroom comma_finite_headroom residue position"

definition comma_finite_step ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_finite_move" where
  "comma_finite_step residue position =
    comma_erase_weight (comma_weighted_step residue position)"

declare comma_weighted_step_with_headroom_def [simp]
declare comma_weighted_step_def [simp]

lemma comma_finite_step_is_erasure:
  "comma_finite_step residue position =
    comma_erase_weight (comma_weighted_step residue position)"
  by (rule comma_finite_step_def)

fun comma_shift_position ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_finite_position" where
  "comma_shift_position k (Comma_Entry f delta offset) =
    Comma_Entry f (delta + k) offset"
| "comma_shift_position k (Comma_Near f delta headroom) =
    Comma_Near f (delta + k) headroom"

fun comma_shift_move ::
  "nat \<Rightarrow> comma_finite_move \<Rightarrow> comma_finite_move" where
  "comma_shift_move k (Comma_Next position) =
    Comma_Next (comma_shift_position k position)"
| "comma_shift_move k (Comma_Fork a delta) =
    Comma_Fork a (delta + k)"
| "comma_shift_move k (Comma_Landmine delta) =
    Comma_Landmine (delta + k)"
| "comma_shift_move k Comma_Invalid = Comma_Invalid"

lemma comma_near_step_delta_transport:
  "comma_finite_step source (Comma_Near f (delta + k) headroom) =
    comma_shift_move k
      (comma_finite_step other (Comma_Near f delta headroom))"
  by (simp add: comma_finite_step_def Let_def add_Suc_right
    split: if_splits)

lemma comma_entry_headroom_phase:
  assumes phase: "(source + delta) mod 924 =
    (other + transported_delta) mod 924"
  shows "comma_finite_headroom f source delta offset =
    comma_finite_headroom f other transported_delta offset"
  using phase by (simp add: comma_finite_headroom_def Let_def)

lemma comma_entry_step_phase_transport:
  assumes phase: "(source + delta) mod 924 =
    (other + transported_delta) mod 924"
  shows "(comma_finite_step source (Comma_Entry f delta offset) =
      Comma_Next (Comma_Near f delta headroom)) =
    (comma_finite_step other
      (Comma_Entry f transported_delta offset) =
      Comma_Next (Comma_Near f transported_delta headroom))"
  using comma_entry_headroom_phase[OF phase]
  by (simp add: comma_finite_step_def Let_def)

lemma comma_finite_step_phase_shift:
  "comma_finite_step residue (comma_shift_position k position) =
    comma_shift_move k
      (comma_finite_step ((residue + k) mod 924) position)"
proof (cases position)
  case (Comma_Entry f delta offset)
  have phase: "(residue + (delta + k)) mod 924 =
      (((residue + k) mod 924) + delta) mod 924"
  proof -
    have "(((residue + k) mod 924) + delta) mod 924 =
        (residue + k + delta) mod 924"
      by (rule mod_add_left_eq)
    then show ?thesis by (simp add: algebra_simps)
  qed
  have headroom: "comma_finite_headroom f residue (delta + k) offset =
      comma_finite_headroom f ((residue + k) mod 924) delta offset"
    using comma_entry_headroom_phase[OF phase] .
  show ?thesis
    using headroom
    by (simp add: Comma_Entry comma_finite_step_def
      comma_weighted_step_def Let_def algebra_simps)
next
  case (Comma_Near f delta headroom)
  show ?thesis
    using comma_near_step_delta_transport
      [where source=residue and other="(residue + k) mod 924"
        and f=f and delta=delta and k=k and headroom=headroom]
    by (simp add: Comma_Near)
qed

text \<open>The normalized control keeps the local phase, not the absolute
exponent gain.  It reuses the canonical finite step; normalization is an
observation of its chart and terminal phase.\<close>

fun comma_normalize_position ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_finite_position" where
  "comma_normalize_position residue (Comma_Entry f delta offset) =
    Comma_Entry f ((residue + delta) mod 924) offset"
| "comma_normalize_position residue (Comma_Near f delta headroom) =
    Comma_Near f ((residue + delta) mod 924) headroom"

fun comma_normalize_move ::
  "nat \<Rightarrow> comma_finite_move \<Rightarrow> comma_finite_move" where
  "comma_normalize_move residue (Comma_Next position) =
    Comma_Next (comma_normalize_position residue position)"
| "comma_normalize_move residue (Comma_Fork a delta) =
    Comma_Fork a ((residue + delta) mod 924)"
| "comma_normalize_move residue (Comma_Landmine delta) =
    Comma_Landmine ((residue + delta) mod 924)"
| "comma_normalize_move residue Comma_Invalid = Comma_Invalid"

definition comma_normalized_step ::
  "comma_finite_position \<Rightarrow> comma_finite_move" where
  "comma_normalized_step position =
    comma_normalize_move 0 (comma_finite_step 0 position)"

lemma comma_normalize_position_shift [simp]:
  "comma_normalize_position 0 (comma_shift_position k position) =
    comma_normalize_position k position"
  by (cases position) (simp_all add: add_ac)

lemma comma_normalize_move_shift [simp]:
  "comma_normalize_move 0 (comma_shift_move k move) =
    comma_normalize_move k move"
  by (cases move) (simp_all add: add_ac)

lemma comma_normalize_step_phase:
  "comma_normalize_move 0 (comma_finite_step 0 position) =
    comma_normalize_move 0
      (comma_finite_step 0 (comma_normalize_position 0 position))"
proof (cases position)
  case (Comma_Entry f delta offset)
  have headroom: "comma_finite_headroom f 0 delta offset =
      comma_finite_headroom f 0 (delta mod 924) offset"
    using comma_entry_headroom_phase
      [of 0 delta 0 "delta mod 924" f offset] by simp
  show ?thesis
    using headroom
    by (simp add: Comma_Entry comma_finite_step_def
      comma_weighted_step_def Let_def)
next
  case (Comma_Near f delta headroom)
  have successor_phase:
      "Suc delta mod 924 = Suc (delta mod 924) mod 924"
  proof -
    have reduction: "((delta mod 924) + 1) mod 924 =
        (delta + 1) mod 924"
      by (rule mod_add_left_eq)
    have "Suc delta mod 924 = (delta + 1) mod 924"
      by (simp only: Suc_eq_plus1)
    also have "... = ((delta mod 924) + 1) mod 924"
      by (rule sym[OF reduction])
    also have "... = Suc (delta mod 924) mod 924"
      by (simp only: Suc_eq_plus1)
    finally show ?thesis .
  qed
  show ?thesis
    using successor_phase
    by (simp add: Comma_Near comma_finite_step_def
      comma_weighted_step_def Let_def)
qed

theorem comma_normalized_step_commutes:
  assumes canonical: "residue < 924"
  shows "comma_normalize_move residue (comma_finite_step residue position) =
    comma_normalized_step (comma_normalize_position residue position)"
proof -
  have shifted: "comma_normalize_move residue
      (comma_finite_step residue position) =
      comma_normalize_move 0
        (comma_finite_step 0 (comma_shift_position residue position))"
    using comma_finite_step_phase_shift[of 0 residue position]
      canonical
    by simp
  show ?thesis
    using shifted comma_normalize_step_phase
      [of "comma_shift_position residue position"]
    by (simp add: comma_normalized_step_def)
qed

lemma comma_normalized_terminal_phase:
  "comma_normalize_move residue (Comma_Fork a delta) =
      Comma_Fork a ((residue + delta) mod 924)"
  "comma_normalize_move residue (Comma_Landmine delta) =
      Comma_Landmine ((residue + delta) mod 924)"
  by simp_all

lemma comma_normalization_forgets_exponent_gain:
  "comma_normalize_position 0 (Comma_Entry f 0 offset) =
      comma_normalize_position 0 (Comma_Entry f 924 offset)"
  "(0::nat) \<noteq> 924"
  by simp_all

fun comma_finite_run ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_finite_outcome option" where
  "comma_finite_run 0 residue position = None"
| "comma_finite_run (Suc fuel) residue position =
    (case comma_finite_step residue position of
      Comma_Next next \<Rightarrow> comma_finite_run fuel residue next
    | Comma_Fork a delta \<Rightarrow> Some (Comma_Fork_At a delta)
    | Comma_Landmine delta \<Rightarrow> Some (Comma_Landmine_At delta)
    | Comma_Invalid \<Rightarrow> None)"

lemma comma_finite_run_nat:
  "comma_finite_run n residue position =
    (if n = 0 then None else
      case comma_finite_step residue position of
        Comma_Next next \<Rightarrow>
          comma_finite_run (n - 1) residue next
      | Comma_Fork a delta \<Rightarrow> Some (Comma_Fork_At a delta)
      | Comma_Landmine delta \<Rightarrow> Some (Comma_Landmine_At delta)
      | Comma_Invalid \<Rightarrow> None)"
  by (cases n; cases "comma_finite_step residue position")
    (simp_all add: diff_Suc_1)

lemma comma_finite_run_more:
  assumes "comma_finite_run fuel residue position = Some outcome"
  shows "comma_finite_run (fuel + extra) residue position = Some outcome"
  using assms
proof (induction fuel arbitrary: position)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  then show ?case
    by (cases "comma_finite_step residue position") auto
qed

fun comma_finite_trace_ok ::
  "nat \<Rightarrow> comma_finite_position list \<Rightarrow>
    comma_finite_outcome \<Rightarrow> bool" where
  "comma_finite_trace_ok residue [] outcome = False"
| "comma_finite_trace_ok residue [position] outcome =
    (case comma_finite_step residue position of
      Comma_Fork a delta \<Rightarrow> outcome = Comma_Fork_At a delta
    | Comma_Landmine delta \<Rightarrow> outcome = Comma_Landmine_At delta
    | _ \<Rightarrow> False)"
| "comma_finite_trace_ok residue (position # next # rest) outcome =
    (comma_finite_step residue position = Comma_Next next \<and>
      comma_finite_trace_ok residue (next # rest) outcome)"

lemma comma_finite_trace_ok_sound:
  assumes "comma_finite_trace_ok residue positions outcome"
  shows "positions \<noteq> [] \<and>
    comma_finite_run (length positions) residue (hd positions) = Some outcome"
  using assms
proof (induction positions)
  case Nil
  then show ?case by simp
next
  case (Cons position tail)
  note ih = Cons.IH
  note prems = Cons.prems
  show ?case
  proof (cases tail)
    case Nil
    then show ?thesis
      using prems
      by (cases "comma_finite_step residue position") auto
  next
    case (Cons tail_head tail_rest)
    have step: "comma_finite_step residue position = Comma_Next tail_head"
      using prems Cons by simp
    have valid: "comma_finite_trace_ok residue
      (tail_head # tail_rest) outcome"
      using prems Cons by simp
    have suffix: "comma_finite_run
      (length (tail_head # tail_rest)) residue tail_head =
      Some outcome"
      using ih valid Cons by simp
    show ?thesis using step suffix Cons by simp
  qed
qed

definition comma_finite_initial ::
  "comma_boundary_state \<Rightarrow> comma_finite_position" where
  "comma_finite_initial q =
    (case q of (kind,a,r) \<Rightarrow>
      if kind = Comma_N then Comma_Near (a - 1) 0 1
      else Comma_Entry a 0 0)"

definition comma_chart_value ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> nat" where
  "comma_chart_value p position =
    (case position of
      Comma_Entry f delta offset \<Rightarrow>
        f * 10 ^ (p + delta) + offset
    | Comma_Near f delta headroom \<Rightarrow>
        (f + 1) * 10 ^ (p + delta) - headroom)"

lemma comma_chart_initial_N:
  assumes "2 \<le> a"
  shows "comma_chart_value p (comma_finite_initial (Comma_N,a,r)) =
    a * 10 ^ p - 1"
  using assms by (simp add: comma_chart_value_def comma_finite_initial_def)

lemma comma_chart_initial_Z:
  "comma_chart_value p (comma_finite_initial (Comma_Z,a,r)) =
    a * 10 ^ p"
  by (simp add: comma_chart_value_def comma_finite_initial_def)

lemma comma_chart_initial_refines_boundary:
  assumes "comma_boundary_valid q"
  shows "comma_chart_value p (comma_finite_initial q) =
    comma_boundary_value q p"
proof -
  obtain kind a r where q: "q = (kind,a,r)"
    by (cases q) auto
  have a: "2 \<le> a"
    using assms by (simp add: q comma_boundary_valid_def)
  show ?thesis
    using a by (cases kind)
      (simp_all add: q comma_chart_initial_N comma_chart_initial_Z
        comma_boundary_value_def)
qed

definition comma_finite_macro ::
  "nat \<Rightarrow> comma_boundary_state \<Rightarrow>
    comma_finite_outcome option" where
  "comma_finite_macro fuel q =
    (case q of (kind,a,r) \<Rightarrow>
      if \<not> comma_boundary_valid q then None
      else comma_finite_run fuel r (comma_finite_initial q))"

definition comma_finite_children ::
  "nat \<Rightarrow> comma_boundary_state \<Rightarrow>
    comma_boundary_state list option" where
  "comma_finite_children fuel q =
    (case q of (kind,a,r) \<Rightarrow>
      case comma_finite_macro fuel q of
        None \<Rightarrow> None
      | Some (Comma_Landmine_At delta) \<Rightarrow> Some []
      | Some (Comma_Fork_At a' delta) \<Rightarrow>
          Some [(Comma_N,a',(r + delta) mod 924),
                (Comma_Z,a',(r + delta) mod 924)])"

text \<open>The same chart supplies the actual literal weight.  An Entry
transition removes a whole admitted phase cycle; a Near transition that
continues executes exactly one literal child edge.  A terminal Fork or
Landmine executes no edge, and its terminal chart retains the exact value
(including a landmine's headroom, which the finite outcome erases).\<close>

definition comma_finite_next_weight ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> nat" where
  "comma_finite_next_weight p position =
    (case comma_weighted_step (p mod 924) position of
      Comma_WNext next weight \<Rightarrow> comma_chart_weight_value p weight
    | _ \<Rightarrow> 0)"

lemma comma_finite_near_next_weight:
  assumes "comma_finite_step (p mod 924)
    (Comma_Near f delta headroom) = Comma_Next next"
  shows "comma_finite_next_weight p (Comma_Near f delta headroom) = 1"
  using assms by (auto simp: comma_finite_next_weight_def
    comma_finite_step_def comma_chart_weight_value_def Let_def
    split: if_splits)

lemma comma_finite_entry_guard_refines:
  assumes "1 \<le> f" "f \<le> 9" "d < 10"
  shows "comma_phase_max_guard f d (comma_cycle_length f) =
    comma_finite_period f d + comma_finite_guard_extra f"
proof -
  have length: "0 < comma_cycle_length f"
    using comma_cycle_length_admitted[OF assms(1,2)] by simp
  have guard: "comma_phase_max_guard f d (comma_cycle_length f) =
    comma_period_displacement f d (comma_cycle_length f) +
      (if f < 9 then 1 else 0)"
    using comma_phase_max_guard_closed[OF length assms(2)] .
  show ?thesis
    using guard comma_finite_period_refines[OF assms]
    by (simp add: comma_finite_guard_extra_def)
qed

lemma comma_safe_count_reduced_headroom:
  fixes H P e :: nat
  assumes positive: "0 < P" and lower: "1 + e \<le> H"
  shows "comma_safe_cycle_count H (P + e) P (H + 1) =
    (H - (1 + e)) div P"
proof -
  let ?x = "H - (1 + e)"
  let ?c = "?x div P"
  let ?r = "?x mod P"
  have rem: "?r < P" using positive by simp
  have decomp: "H = 1 + e + ?c * P + ?r"
    using lower by (simp add: div_mult_mod_eq)
  have cP: "?c \<le> ?c * P"
    using positive by (simp add: mult_le_mono1)
  have product_below: "?c * P \<le> H"
  proof -
    have decomposition_x: "?c * P + ?r = ?x"
      using div_mult_mod_eq[of ?x P] by (simp add: algebra_simps)
    have "?c * P \<le> ?x" using decomposition_x by arith
    also have "?x \<le> H" by simp
    finally show ?thesis .
  qed
  have cap: "?c \<le> H + 1"
  proof -
    have "?c \<le> H" using cP product_below by (rule order_trans)
    then show ?thesis by simp
  qed
  show ?thesis
  proof (cases "?c = 0")
    case True
    have raw_zero: "H = 1 + e + 0 * P + ?r"
      using decomp True by (simp only: True)
    have zero_decomp: "H = 1 + e + ?r"
      using raw_zero by simp
    have "H \<le> P + e" using zero_decomp rem by simp
    then show ?thesis
      using True by (simp add: comma_safe_cycle_count_def)
  next
    case False
    have cpos: "0 < ?c" using False by simp
    obtain k where c: "?c = Suc k"
      using cpos by (cases ?c) auto
    have positive_decomp: "H = 1 + e + P + k * P + ?r"
    proof -
      have raw: "H = 1 + e + Suc k * P + ?r"
        using decomp c by (simp only: c)
      show ?thesis using raw by (simp add: algebra_simps)
    qed
    define R where "R = ?r"
    have R_bound: "R < P" using rem by (simp add: R_def)
    have simple_decomp: "H = 1 + e + P + k * P + R"
      using positive_decomp by (simp only: R_def)
    have guard: "P + e < H" using simple_decomp by simp
    have difference: "H - 1 - (P + e) = k * P + R"
      using simple_decomp by arith
    have quotient: "(H - 1 - (P + e)) div P + 1 = ?c"
      using difference R_bound c positive
      by (simp add: div_mult_self4 add.commute)
    show ?thesis
      using cap guard quotient
      by (simp add: comma_safe_cycle_count_def)
  qed
qed

lemma comma_reduced_headroom_weight:
  fixes H P e :: nat
  assumes positive: "0 < P" and lower: "1 + e \<le> H"
  defines "h \<equiv> 1 + e + (H - (1 + e)) mod P"
  shows "(H - h) div P =
    comma_safe_cycle_count H (P + e) P (H + 1)"
proof -
  let ?x = "H - (1 + e)"
  define C where "C = ?x div P"
  have decomposition: "H = h + (?x div P) * P"
    using lower by (simp add: h_def div_mult_mod_eq algebra_simps)
  have decomposition_C: "H = h + C * P"
    using decomposition by (simp only: C_def)
  have difference: "H - h = C * P"
    using decomposition_C by arith
  have quotient: "(H - h) div P = ?x div P"
    using difference positive by (simp add: C_def)
  show ?thesis
    using quotient comma_safe_count_reduced_headroom[OF positive lower]
    by simp
qed

lemma comma_int_mod_reduced_headroom:
  fixes K offset shift P :: nat
  assumes lower: "offset + shift \<le> K" and positive: "0 < P"
  shows "nat ((int (K mod P) - int offset - int shift) mod int P) =
    (K - offset - shift) mod P"
proof -
  have "(int (K mod P) - int offset - int shift) mod int P =
      (int K - int offset - int shift) mod int P"
  proof -
    have grouped: "(int K mod int P -
        (int offset + int shift)) mod int P =
        (int K - (int offset + int shift)) mod int P"
      by (rule mod_diff_left_eq)
    show ?thesis using grouped
      by (simp add: of_nat_mod algebra_simps)
  qed
  also have "... = int ((K - offset - shift) mod P)"
  proof -
    have cast: "int (K - (offset + shift)) =
      int K - int offset - int shift"
      using lower by (simp add: of_nat_diff)
    show ?thesis
      using cast by (simp add: of_nat_mod)
  qed
  finally show ?thesis by simp
qed

lemma comma_finite_headroom_reduced:
  fixes f p delta offset :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and offset: "offset \<le> 98"
  shows "comma_finite_headroom f (p mod 924) delta offset =
    (let P = comma_finite_period f (offset mod 10);
         e = comma_finite_guard_extra f;
         H = 10 ^ (p + delta) - offset
     in 1 + e + (H - (1 + e)) mod P)"
proof -
  let ?P = "comma_finite_period f (offset mod 10)"
  let ?e = "comma_finite_guard_extra f"
  let ?K = "(10::nat) ^ (p + delta)"
  have length: "0 < comma_cycle_length f"
    using comma_cycle_length_admitted[OF sector] by simp
  have f_positive: "0 < f" using sector(1) by simp
  have positive: "0 < ?P"
    using comma_period_displacement_admitted[OF f_positive length,
      of "offset mod 10"]
      comma_finite_period_refines[OF sector, of "offset mod 10"]
    by simp
  have e_bound: "?e \<le> 1"
    by (simp add: comma_finite_guard_extra_def)
  have order: "5 \<le> p + delta" using exponent by simp
  have power: "100000 \<le> ?K"
  proof -
    have "(10::nat) ^ 5 \<le> 10 ^ (p + delta)"
      by (rule power_increasing[OF order]) simp
    then show ?thesis by simp
  qed
  have lower: "offset + (1 + ?e) \<le> ?K"
    using offset e_bound power by arith
  have refines: "comma_finite_headroom f (p mod 924) delta offset =
      1 + ?e + nat ((int (?K mod ?P) - int offset -
        int (1 + ?e)) mod int ?P)"
    using comma_finite_headroom_refines[OF sector exponent,
      of delta offset] by simp
  have reduced: "nat ((int (?K mod ?P) - int offset -
      int (1 + ?e)) mod int ?P) =
      (?K - offset - (1 + ?e)) mod ?P"
    using comma_int_mod_reduced_headroom[OF lower positive] .
  have exact: "comma_finite_headroom f (p mod 924) delta offset =
      1 + ?e + (?K - offset - (1 + ?e)) mod ?P"
    using refines reduced by (simp only: reduced)
  show ?thesis using exact by (simp only: Let_def)
qed

fun comma_finite_weighted_run ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_finite_position \<Rightarrow>
    (comma_finite_outcome \<times> nat \<times> comma_finite_position) option" where
  "comma_finite_weighted_run 0 p position = None"
| "comma_finite_weighted_run (Suc fuel) p position =
    (case comma_weighted_step (p mod 924) position of
      Comma_WNext next local_weight \<Rightarrow>
        (case comma_finite_weighted_run fuel p next of
          None \<Rightarrow> None
        | Some (outcome,weight,terminal) \<Rightarrow>
            Some (outcome,
              comma_chart_weight_value p local_weight + weight,terminal))
    | Comma_WFork terminal a delta \<Rightarrow>
        Some (Comma_Fork_At a delta,0,terminal)
    | Comma_WLandmine terminal delta \<Rightarrow>
        Some (Comma_Landmine_At delta,0,terminal)
    | Comma_WInvalid \<Rightarrow> None)"

lemma comma_finite_weighted_erasure:
  "map_option fst (comma_finite_weighted_run fuel p position) =
    comma_finite_run fuel (p mod 924) position"
proof (induction fuel arbitrary: position)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "comma_weighted_step (p mod 924) position")
    case (Comma_WNext successor step_weight)
    then show ?thesis
      using Suc.IH[of successor]
      by (cases "comma_finite_weighted_run fuel p successor")
        (auto simp: comma_finite_step_def)
  qed (auto simp: comma_finite_step_def)
qed

lemma comma_weighted_terminal_is_source:
  assumes "comma_weighted_step residue position =
      Comma_WFork terminal a delta \<or>
    comma_weighted_step residue position =
      Comma_WLandmine terminal delta"
  shows "terminal = position"
  using assms
  by (cases position)
    (auto simp: comma_weighted_step_def Let_def split: if_splits)

lemma comma_finite_weighted_terminal:
  assumes run: "comma_finite_weighted_run fuel p position =
    Some (outcome,weight,terminal)"
  shows "(\<exists>a delta. outcome = Comma_Fork_At a delta \<and>
      comma_finite_step (p mod 924) terminal = Comma_Fork a delta) \<or>
    (\<exists>delta. outcome = Comma_Landmine_At delta \<and>
      comma_finite_step (p mod 924) terminal = Comma_Landmine delta)"
  using run
proof (induction fuel arbitrary: position weight)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "comma_weighted_step (p mod 924) position")
    case (Comma_WNext successor step_weight)
    have equation: "comma_finite_weighted_run (Suc fuel) p position =
      (case comma_finite_weighted_run fuel p successor of
        None \<Rightarrow> None
      | Some (tail_out,tail_count,tail_terminal) \<Rightarrow>
          Some (tail_out,
            comma_chart_weight_value p step_weight + tail_count,
            tail_terminal))"
      using Comma_WNext
      by (simp del: comma_weighted_step_def)
    obtain result where result:
      "comma_finite_weighted_run fuel p successor = Some result"
      using Suc.prems equation
      by (cases "comma_finite_weighted_run fuel p successor")
        (simp_all del: comma_weighted_step_def)
    obtain tail_out tail_count tail_terminal where triple:
      "result = (tail_out,tail_count,tail_terminal)"
      by (cases result) auto
    have tail: "comma_finite_weighted_run fuel p successor =
      Some (tail_out,tail_count,tail_terminal)"
      using result triple by simp
    have coordinates: "outcome = tail_out"
      "terminal = tail_terminal"
      using Suc.prems equation tail by simp_all
    have tail_fixed:
      "comma_finite_weighted_run fuel p successor =
        Some (outcome,tail_count,terminal)"
      using tail coordinates by simp
    have property:
      "(\<exists>a delta. outcome = Comma_Fork_At a delta \<and>
          comma_finite_step (p mod 924) terminal =
            Comma_Fork a delta) \<or>
        (\<exists>delta. outcome = Comma_Landmine_At delta \<and>
          comma_finite_step (p mod 924) terminal =
            Comma_Landmine delta)"
      using Suc.IH[OF tail_fixed] .
    show ?thesis using property .
  next
    case (Comma_WFork terminal a delta)
    have "terminal = position"
      using comma_weighted_terminal_is_source[of "p mod 924"
        position terminal a delta] Comma_WFork by simp
    then show ?thesis using Suc.prems Comma_WFork
      by (simp add: comma_finite_step_def
        del: comma_weighted_step_def)
  next
    case (Comma_WLandmine terminal delta)
    have "terminal = position"
      using comma_weighted_terminal_is_source[of "p mod 924"
        position terminal 0 delta] Comma_WLandmine by simp
    then show ?thesis using Suc.prems Comma_WLandmine
      by (simp add: comma_finite_step_def
        del: comma_weighted_step_def)
  next
    case Comma_WInvalid
    then show ?thesis using Suc.prems
      by (simp del: comma_weighted_step_def)
  qed
qed

definition comma_finite_weighted_macro ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_boundary_state \<Rightarrow>
    (comma_finite_outcome \<times> nat \<times> comma_finite_position) option" where
  "comma_finite_weighted_macro fuel p q =
    (if p < 5 \<or> \<not> comma_boundary_valid q \<or>
        p mod 924 \<noteq> snd (snd q)
     then None
     else comma_finite_weighted_run fuel p (comma_finite_initial q))"

lemma comma_finite_weighted_macro_erasure:
  assumes "5 \<le> p" "p mod 924 = snd (snd q)"
  shows "map_option fst (comma_finite_weighted_macro fuel p q) =
    comma_finite_macro fuel q"
  using assms comma_finite_weighted_erasure[of fuel p "comma_finite_initial q"]
  by (cases q) (simp add: comma_finite_weighted_macro_def
    comma_finite_macro_def)

text \<open>The refinement from these small transitions to the literal comma
relation, as well as their totality on all 14,784 boundary states, must be
proved before this option-valued constructor authorizes a losing graph.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_finite_period_catalog comma_finite_period_refines
      comma_finite_period_in_catalog comma_power_period_924_repeated
      comma_residue_exponent_decomposition comma_residue_power_refines
      comma_finite_headroom_refines comma_finite_run_more
      comma_finite_run_nat comma_finite_step_is_erasure
      comma_chart_weight_unit comma_chart_weight_entry_exact
      comma_near_step_delta_transport comma_entry_headroom_phase
      comma_entry_step_phase_transport comma_finite_step_phase_shift
      comma_normalize_position_shift comma_normalize_move_shift
      comma_normalize_step_phase comma_normalized_step_commutes
      comma_normalized_terminal_phase
      comma_normalization_forgets_exponent_gain
      comma_finite_trace_ok_sound comma_chart_initial_N
      comma_chart_initial_Z comma_chart_initial_refines_boundary
      comma_finite_near_next_weight comma_finite_entry_guard_refines
      comma_safe_count_reduced_headroom comma_reduced_headroom_weight
      comma_int_mod_reduced_headroom comma_finite_headroom_reduced
      comma_finite_weighted_erasure comma_weighted_terminal_is_source
      comma_finite_weighted_terminal
      comma_finite_weighted_macro_erasure})
    then () else error "Comma finite-transition proof depends on an oracle";
\<close>

end
