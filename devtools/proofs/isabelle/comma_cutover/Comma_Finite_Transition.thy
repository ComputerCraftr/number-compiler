theory Comma_Finite_Transition
  imports Comma_Macro_Constructor "Comma_Arithmetic.Comma_Finite_Period"
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

definition comma_finite_step ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_finite_move" where
  "comma_finite_step residue position =
    (case position of
      Comma_Entry f delta offset \<Rightarrow>
        if f < 1 \<or> 9 < f \<or> 98 < offset \<or>
           comma_finite_period f (offset mod 10) = 0
        then Comma_Invalid
        else Comma_Next (Comma_Near f delta
          (comma_finite_headroom f residue delta offset))
    | Comma_Near f delta headroom \<Rightarrow>
        if f < 1 \<or> 9 < f \<or> headroom = 0 then Comma_Invalid
        else
          (let d = (10 - headroom mod 10) mod 10 in
            if f < 9 then
              (let low = 10 * d + f in
                if headroom > low + 1 then
                  Comma_Next (Comma_Near f delta (headroom - low))
                else if headroom = low + 1 then
                  Comma_Fork (f + 1) delta
                else Comma_Next
                  (Comma_Entry (f + 1) delta (low + 1 - headroom)))
            else
              (let same = 10 * d + 9; cross = 10 * d + 1 in
                if headroom > same then
                  Comma_Next (Comma_Near 9 delta (headroom - same))
                else if headroom \<le> cross then
                  Comma_Next (Comma_Entry 1 (Suc delta)
                    (cross - headroom))
                else Comma_Landmine delta)))"

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
  by (simp add: comma_finite_step_def)

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

lemma comma_finite_first_step:
  "comma_finite_step 10 (Comma_Entry 2 0 91) =
    Comma_Next (Comma_Near 2 0 29)"
  by (simp add: comma_finite_step_def comma_finite_headroom_def
    comma_finite_period_def comma_finite_guard_extra_def
    comma_residue_exponent_def)

text \<open>This 92-position witness is untrusted data.  Its local transitions
are checked below against the executable finite cylinder; the list alone
does not establish branch safety or a global rank certificate.\<close>

definition comma_first_winning_trace :: "comma_finite_position list" where
  "comma_first_winning_trace = [
      (Comma_Entry 2 0 91), (Comma_Near 2 0 29), (Comma_Near 2 0 17), (Comma_Entry 3 0 16),
      (Comma_Near 3 0 144), (Comma_Near 3 0 81), (Comma_Entry 4 0 13), (Comma_Near 4 0 267),
      (Comma_Near 4 0 233), (Comma_Near 4 0 159), (Comma_Near 4 0 145), (Comma_Near 4 0 91),
      (Comma_Entry 5 0 4), (Comma_Near 5 0 56), (Comma_Near 5 0 11), (Comma_Entry 6 0 85),
      (Comma_Near 6 0 115), (Comma_Near 6 0 59), (Comma_Near 6 0 43), (Comma_Entry 7 0 34),
      (Comma_Near 7 0 86), (Comma_Near 7 0 39), (Comma_Near 7 0 22), (Comma_Entry 8 0 66),
      (Comma_Near 8 0 94), (Comma_Near 8 0 26), (Comma_Entry 9 0 23), (Comma_Near 9 0 257),
      (Comma_Near 9 0 218), (Comma_Near 9 0 189), (Comma_Near 9 0 170), (Comma_Near 9 0 161),
      (Comma_Near 9 0 62), (Comma_Entry 1 1 19), (Comma_Near 1 1 141), (Comma_Near 1 1 50),
      (Comma_Near 1 1 49), (Comma_Near 1 1 38), (Comma_Near 1 1 17), (Comma_Entry 2 1 15),
      (Comma_Near 2 1 145), (Comma_Near 2 1 93), (Comma_Near 2 1 21), (Comma_Entry 3 1 72),
      (Comma_Near 3 1 88), (Comma_Near 3 1 65), (Comma_Near 3 1 12), (Comma_Entry 4 1 72),
      (Comma_Near 4 1 48), (Comma_Near 4 1 24), (Comma_Entry 5 1 41), (Comma_Near 5 1 39),
      (Comma_Near 5 1 24), (Comma_Entry 6 1 42), (Comma_Near 6 1 118), (Comma_Near 6 1 92),
      (Comma_Near 6 1 6), (Comma_Entry 7 1 41), (Comma_Near 7 1 119), (Comma_Near 7 1 102),
      (Comma_Near 7 1 15), (Comma_Entry 8 1 43), (Comma_Near 8 1 17), (Comma_Entry 9 1 22),
      (Comma_Near 9 1 78), (Comma_Near 9 1 49), (Comma_Near 9 1 30), (Comma_Near 9 1 21),
      (Comma_Entry 1 2 70), (Comma_Near 1 2 150), (Comma_Near 1 2 149), (Comma_Near 1 2 138),
      (Comma_Near 1 2 117), (Comma_Near 1 2 86), (Comma_Near 1 2 45), (Comma_Entry 2 2 7),
      (Comma_Near 2 2 33), (Comma_Entry 3 2 40), (Comma_Near 3 2 120), (Comma_Near 3 2 117),
      (Comma_Near 3 2 84), (Comma_Near 3 2 21), (Comma_Entry 4 2 73), (Comma_Near 4 2 117),
      (Comma_Near 4 2 83), (Comma_Near 4 2 9), (Comma_Entry 5 2 6), (Comma_Near 5 2 74),
      (Comma_Near 5 2 9), (Comma_Entry 6 2 7), (Comma_Near 6 2 113), (Comma_Near 6 2 37)
    ]"

lemma comma_first_winning_trace_length:
  "length comma_first_winning_trace = 92"
  unfolding comma_first_winning_trace_def by simp

lemma comma_first_winning_trace_head:
  "hd comma_first_winning_trace = Comma_Entry 2 0 91"
  unfolding comma_first_winning_trace_def by simp

lemma comma_first_trace_chunk_0:
  "comma_finite_step 10 (Comma_Entry 2 0 91) = Comma_Next (Comma_Near 2 0 29) \<and>
    comma_finite_step 10 (Comma_Near 2 0 29) = Comma_Next (Comma_Near 2 0 17) \<and>
    comma_finite_step 10 (Comma_Near 2 0 17) = Comma_Next (Comma_Entry 3 0 16) \<and>
    comma_finite_step 10 (Comma_Entry 3 0 16) = Comma_Next (Comma_Near 3 0 144) \<and>
    comma_finite_step 10 (Comma_Near 3 0 144) = Comma_Next (Comma_Near 3 0 81) \<and>
    comma_finite_step 10 (Comma_Near 3 0 81) = Comma_Next (Comma_Entry 4 0 13) \<and>
    comma_finite_step 10 (Comma_Entry 4 0 13) = Comma_Next (Comma_Near 4 0 267) \<and>
    comma_finite_step 10 (Comma_Near 4 0 267) = Comma_Next (Comma_Near 4 0 233)"
  by (simp add: comma_finite_step_def comma_finite_headroom_def
    comma_finite_period_def comma_finite_guard_extra_def
    comma_residue_exponent_def Let_def gcd_nat.simps)

lemma comma_first_trace_chunk_1:
  "comma_finite_step 10 (Comma_Near 4 0 233) = Comma_Next (Comma_Near 4 0 159) \<and>
    comma_finite_step 10 (Comma_Near 4 0 159) = Comma_Next (Comma_Near 4 0 145) \<and>
    comma_finite_step 10 (Comma_Near 4 0 145) = Comma_Next (Comma_Near 4 0 91) \<and>
    comma_finite_step 10 (Comma_Near 4 0 91) = Comma_Next (Comma_Entry 5 0 4) \<and>
    comma_finite_step 10 (Comma_Entry 5 0 4) = Comma_Next (Comma_Near 5 0 56) \<and>
    comma_finite_step 10 (Comma_Near 5 0 56) = Comma_Next (Comma_Near 5 0 11) \<and>
    comma_finite_step 10 (Comma_Near 5 0 11) = Comma_Next (Comma_Entry 6 0 85) \<and>
    comma_finite_step 10 (Comma_Entry 6 0 85) = Comma_Next (Comma_Near 6 0 115)"
  by (simp add: comma_finite_step_def comma_finite_headroom_def
    comma_finite_period_def comma_finite_guard_extra_def
    comma_residue_exponent_def Let_def gcd_nat.simps)

lemma comma_first_trace_chunk_2:
  "comma_finite_step 10 (Comma_Near 6 0 115) = Comma_Next (Comma_Near 6 0 59) \<and>
    comma_finite_step 10 (Comma_Near 6 0 59) = Comma_Next (Comma_Near 6 0 43) \<and>
    comma_finite_step 10 (Comma_Near 6 0 43) = Comma_Next (Comma_Entry 7 0 34) \<and>
    comma_finite_step 10 (Comma_Entry 7 0 34) = Comma_Next (Comma_Near 7 0 86) \<and>
    comma_finite_step 10 (Comma_Near 7 0 86) = Comma_Next (Comma_Near 7 0 39) \<and>
    comma_finite_step 10 (Comma_Near 7 0 39) = Comma_Next (Comma_Near 7 0 22) \<and>
    comma_finite_step 10 (Comma_Near 7 0 22) = Comma_Next (Comma_Entry 8 0 66) \<and>
    comma_finite_step 10 (Comma_Entry 8 0 66) = Comma_Next (Comma_Near 8 0 94)"
  by (simp add: comma_finite_step_def comma_finite_headroom_def
    comma_finite_period_def comma_finite_guard_extra_def
    comma_residue_exponent_def Let_def gcd_nat.simps)

lemma comma_first_trace_chunk_3:
  "comma_finite_step 10 (Comma_Near 8 0 94) = Comma_Next (Comma_Near 8 0 26) \<and>
    comma_finite_step 10 (Comma_Near 8 0 26) = Comma_Next (Comma_Entry 9 0 23) \<and>
    comma_finite_step 10 (Comma_Entry 9 0 23) = Comma_Next (Comma_Near 9 0 257) \<and>
    comma_finite_step 10 (Comma_Near 9 0 257) = Comma_Next (Comma_Near 9 0 218) \<and>
    comma_finite_step 10 (Comma_Near 9 0 218) = Comma_Next (Comma_Near 9 0 189) \<and>
    comma_finite_step 10 (Comma_Near 9 0 189) = Comma_Next (Comma_Near 9 0 170) \<and>
    comma_finite_step 10 (Comma_Near 9 0 170) = Comma_Next (Comma_Near 9 0 161) \<and>
    comma_finite_step 10 (Comma_Near 9 0 161) = Comma_Next (Comma_Near 9 0 62)"
  by (simp add: comma_finite_step_def comma_finite_headroom_def
    comma_finite_period_def comma_finite_guard_extra_def
    comma_residue_exponent_def Let_def gcd_nat.simps)

lemma comma_first_trace_chunk_4:
  "comma_finite_step 10 (Comma_Near 9 0 62) = Comma_Next (Comma_Entry 1 1 19) \<and>
    comma_finite_step 10 (Comma_Entry 1 1 19) = Comma_Next (Comma_Near 1 1 141) \<and>
    comma_finite_step 10 (Comma_Near 1 1 141) = Comma_Next (Comma_Near 1 1 50) \<and>
    comma_finite_step 10 (Comma_Near 1 1 50) = Comma_Next (Comma_Near 1 1 49) \<and>
    comma_finite_step 10 (Comma_Near 1 1 49) = Comma_Next (Comma_Near 1 1 38) \<and>
    comma_finite_step 10 (Comma_Near 1 1 38) = Comma_Next (Comma_Near 1 1 17) \<and>
    comma_finite_step 10 (Comma_Near 1 1 17) = Comma_Next (Comma_Entry 2 1 15) \<and>
    comma_finite_step 10 (Comma_Entry 2 1 15) = Comma_Next (Comma_Near 2 1 145)"
  by (simp add: comma_finite_step_def comma_finite_headroom_def
    comma_finite_period_def comma_finite_guard_extra_def
    comma_residue_exponent_def Let_def gcd_nat.simps)

lemma comma_first_trace_chunk_5:
  "comma_finite_step 10 (Comma_Near 2 1 145) = Comma_Next (Comma_Near 2 1 93) \<and>
    comma_finite_step 10 (Comma_Near 2 1 93) = Comma_Next (Comma_Near 2 1 21) \<and>
    comma_finite_step 10 (Comma_Near 2 1 21) = Comma_Next (Comma_Entry 3 1 72) \<and>
    comma_finite_step 10 (Comma_Entry 3 1 72) = Comma_Next (Comma_Near 3 1 88) \<and>
    comma_finite_step 10 (Comma_Near 3 1 88) = Comma_Next (Comma_Near 3 1 65) \<and>
    comma_finite_step 10 (Comma_Near 3 1 65) = Comma_Next (Comma_Near 3 1 12) \<and>
    comma_finite_step 10 (Comma_Near 3 1 12) = Comma_Next (Comma_Entry 4 1 72) \<and>
    comma_finite_step 10 (Comma_Entry 4 1 72) = Comma_Next (Comma_Near 4 1 48)"
  by (simp add: comma_finite_step_def comma_finite_headroom_def
    comma_finite_period_def comma_finite_guard_extra_def
    comma_residue_exponent_def Let_def gcd_nat.simps)

lemma comma_first_trace_chunk_6:
  "comma_finite_step 10 (Comma_Near 4 1 48) = Comma_Next (Comma_Near 4 1 24) \<and>
    comma_finite_step 10 (Comma_Near 4 1 24) = Comma_Next (Comma_Entry 5 1 41) \<and>
    comma_finite_step 10 (Comma_Entry 5 1 41) = Comma_Next (Comma_Near 5 1 39) \<and>
    comma_finite_step 10 (Comma_Near 5 1 39) = Comma_Next (Comma_Near 5 1 24) \<and>
    comma_finite_step 10 (Comma_Near 5 1 24) = Comma_Next (Comma_Entry 6 1 42) \<and>
    comma_finite_step 10 (Comma_Entry 6 1 42) = Comma_Next (Comma_Near 6 1 118) \<and>
    comma_finite_step 10 (Comma_Near 6 1 118) = Comma_Next (Comma_Near 6 1 92) \<and>
    comma_finite_step 10 (Comma_Near 6 1 92) = Comma_Next (Comma_Near 6 1 6)"
  by (simp add: comma_finite_step_def comma_finite_headroom_def
    comma_finite_period_def comma_finite_guard_extra_def
    comma_residue_exponent_def Let_def gcd_nat.simps)

lemma comma_first_trace_chunk_7:
  "comma_finite_step 10 (Comma_Near 6 1 6) = Comma_Next (Comma_Entry 7 1 41) \<and>
    comma_finite_step 10 (Comma_Entry 7 1 41) = Comma_Next (Comma_Near 7 1 119) \<and>
    comma_finite_step 10 (Comma_Near 7 1 119) = Comma_Next (Comma_Near 7 1 102) \<and>
    comma_finite_step 10 (Comma_Near 7 1 102) = Comma_Next (Comma_Near 7 1 15) \<and>
    comma_finite_step 10 (Comma_Near 7 1 15) = Comma_Next (Comma_Entry 8 1 43) \<and>
    comma_finite_step 10 (Comma_Entry 8 1 43) = Comma_Next (Comma_Near 8 1 17) \<and>
    comma_finite_step 10 (Comma_Near 8 1 17) = Comma_Next (Comma_Entry 9 1 22) \<and>
    comma_finite_step 10 (Comma_Entry 9 1 22) = Comma_Next (Comma_Near 9 1 78)"
  by (simp add: comma_finite_step_def comma_finite_headroom_def
    comma_finite_period_def comma_finite_guard_extra_def
    comma_residue_exponent_def Let_def gcd_nat.simps)

lemma comma_first_trace_chunk_8:
  "comma_finite_step 10 (Comma_Near 9 1 78) = Comma_Next (Comma_Near 9 1 49) \<and>
    comma_finite_step 10 (Comma_Near 9 1 49) = Comma_Next (Comma_Near 9 1 30) \<and>
    comma_finite_step 10 (Comma_Near 9 1 30) = Comma_Next (Comma_Near 9 1 21) \<and>
    comma_finite_step 10 (Comma_Near 9 1 21) = Comma_Next (Comma_Entry 1 2 70) \<and>
    comma_finite_step 10 (Comma_Entry 1 2 70) = Comma_Next (Comma_Near 1 2 150) \<and>
    comma_finite_step 10 (Comma_Near 1 2 150) = Comma_Next (Comma_Near 1 2 149) \<and>
    comma_finite_step 10 (Comma_Near 1 2 149) = Comma_Next (Comma_Near 1 2 138) \<and>
    comma_finite_step 10 (Comma_Near 1 2 138) = Comma_Next (Comma_Near 1 2 117)"
  by (simp add: comma_finite_step_def comma_finite_headroom_def
    comma_finite_period_def comma_finite_guard_extra_def
    comma_residue_exponent_def Let_def gcd_nat.simps)

lemma comma_first_trace_chunk_9:
  "comma_finite_step 10 (Comma_Near 1 2 117) = Comma_Next (Comma_Near 1 2 86) \<and>
    comma_finite_step 10 (Comma_Near 1 2 86) = Comma_Next (Comma_Near 1 2 45) \<and>
    comma_finite_step 10 (Comma_Near 1 2 45) = Comma_Next (Comma_Entry 2 2 7) \<and>
    comma_finite_step 10 (Comma_Entry 2 2 7) = Comma_Next (Comma_Near 2 2 33) \<and>
    comma_finite_step 10 (Comma_Near 2 2 33) = Comma_Next (Comma_Entry 3 2 40) \<and>
    comma_finite_step 10 (Comma_Entry 3 2 40) = Comma_Next (Comma_Near 3 2 120) \<and>
    comma_finite_step 10 (Comma_Near 3 2 120) = Comma_Next (Comma_Near 3 2 117) \<and>
    comma_finite_step 10 (Comma_Near 3 2 117) = Comma_Next (Comma_Near 3 2 84)"
  by (simp add: comma_finite_step_def comma_finite_headroom_def
    comma_finite_period_def comma_finite_guard_extra_def
    comma_residue_exponent_def Let_def gcd_nat.simps)

lemma comma_first_trace_chunk_10:
  "comma_finite_step 10 (Comma_Near 3 2 84) = Comma_Next (Comma_Near 3 2 21) \<and>
    comma_finite_step 10 (Comma_Near 3 2 21) = Comma_Next (Comma_Entry 4 2 73) \<and>
    comma_finite_step 10 (Comma_Entry 4 2 73) = Comma_Next (Comma_Near 4 2 117) \<and>
    comma_finite_step 10 (Comma_Near 4 2 117) = Comma_Next (Comma_Near 4 2 83) \<and>
    comma_finite_step 10 (Comma_Near 4 2 83) = Comma_Next (Comma_Near 4 2 9) \<and>
    comma_finite_step 10 (Comma_Near 4 2 9) = Comma_Next (Comma_Entry 5 2 6) \<and>
    comma_finite_step 10 (Comma_Entry 5 2 6) = Comma_Next (Comma_Near 5 2 74) \<and>
    comma_finite_step 10 (Comma_Near 5 2 74) = Comma_Next (Comma_Near 5 2 9)"
  by (simp add: comma_finite_step_def comma_finite_headroom_def
    comma_finite_period_def comma_finite_guard_extra_def
    comma_residue_exponent_def Let_def gcd_nat.simps)

lemma comma_first_trace_chunk_11:
  "comma_finite_step 10 (Comma_Near 5 2 9) = Comma_Next (Comma_Entry 6 2 7) \<and>
    comma_finite_step 10 (Comma_Entry 6 2 7) = Comma_Next (Comma_Near 6 2 113) \<and>
    comma_finite_step 10 (Comma_Near 6 2 113) = Comma_Next (Comma_Near 6 2 37) \<and>
    comma_finite_step 10 (Comma_Near 6 2 37) = Comma_Fork 7 2"
  by (simp add: comma_finite_step_def comma_finite_headroom_def
    comma_finite_period_def comma_finite_guard_extra_def
    comma_residue_exponent_def Let_def gcd_nat.simps)

lemma comma_first_winning_trace_checked:
  "comma_finite_trace_ok 10 comma_first_winning_trace
    (Comma_Fork_At 7 2)"
  using comma_first_trace_chunk_0 comma_first_trace_chunk_1
    comma_first_trace_chunk_2 comma_first_trace_chunk_3
    comma_first_trace_chunk_4 comma_first_trace_chunk_5
    comma_first_trace_chunk_6 comma_first_trace_chunk_7
    comma_first_trace_chunk_8 comma_first_trace_chunk_9
    comma_first_trace_chunk_10 comma_first_trace_chunk_11
  by (auto simp: comma_first_winning_trace_def)

definition comma_finite_macro ::
  "nat \<Rightarrow> comma_boundary_state \<Rightarrow>
    comma_finite_outcome option" where
  "comma_finite_macro fuel q =
    (case q of (kind,a,r) \<Rightarrow>
      if \<not> comma_boundary_valid q then None
      else comma_finite_run fuel r
        (Comma_Entry a 0 (if kind = Comma_N then a + 89 else 0)))"

lemma comma_finite_first_winning_macro_92:
  "comma_finite_macro 92 (Comma_N, 2, 10) =
    Some (Comma_Fork_At 7 2)"
proof -
  have run: "comma_finite_run 92 10 (Comma_Entry 2 0 91) =
    Some (Comma_Fork_At 7 2)"
    using comma_finite_trace_ok_sound[OF comma_first_winning_trace_checked]
      comma_first_winning_trace_length comma_first_winning_trace_head
    by simp
  show ?thesis
    using run by (simp add: comma_finite_macro_def comma_boundary_valid_def)
qed

lemma comma_finite_first_winning_macro:
  "comma_finite_macro 4096 (Comma_N, 2, 10) =
    Some (Comma_Fork_At 7 2)"
proof -
  have base: "comma_finite_run 92 10 (Comma_Entry 2 0 91) =
    Some (Comma_Fork_At 7 2)"
    using comma_finite_first_winning_macro_92
    by (simp add: comma_finite_macro_def comma_boundary_valid_def)
  have more: "comma_finite_run (92 + 4004) 10
    (Comma_Entry 2 0 91) = Some (Comma_Fork_At 7 2)"
    using comma_finite_run_more[OF base] .
  show ?thesis
    using more
    by (simp add: comma_finite_macro_def comma_boundary_valid_def)
qed

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

text \<open>The refinement from these small transitions to the literal comma
relation, as well as their totality on all 14,784 boundary states, must be
proved before this option-valued constructor authorizes a losing graph.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_finite_period_catalog comma_finite_period_refines
      comma_finite_period_in_catalog comma_power_period_924_repeated
      comma_residue_exponent_decomposition comma_residue_power_refines
      comma_finite_headroom_refines comma_finite_run_more
      comma_finite_run_nat
      comma_near_step_delta_transport comma_entry_headroom_phase
      comma_entry_step_phase_transport
      comma_finite_trace_ok_sound comma_first_winning_trace_checked
      comma_finite_first_step
      comma_finite_first_winning_macro_92
      comma_finite_first_winning_macro})
    then () else error "Comma finite-transition proof depends on an oracle";
\<close>

end
