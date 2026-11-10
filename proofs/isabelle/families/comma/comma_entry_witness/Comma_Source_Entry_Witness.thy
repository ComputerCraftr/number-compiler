theory Comma_Source_Entry_Witness
  imports Comma_Literal_Bridge.Comma_Macro_Selection
    Comma_Entry_Arithmetic.Comma_Entry_Arithmetic
begin

text \<open>The following charts are untrusted source-20 candidate data.
Each edge, the terminal fork, and every weight are checked through the
canonical finite/weighted chart definitions; no Python row is a premise.\<close>

definition comma_source_tail_positions_0 :: "comma_finite_position list" where
  "comma_source_tail_positions_0 = [
    Comma_Entry 1 0 3, Comma_Near 1 0 177, Comma_Near 1 0 146, Comma_Near 1 0 105,
    Comma_Near 1 0 54, Comma_Entry 2 0 8, Comma_Near 2 0 32, Comma_Entry 3 0 51,
    Comma_Near 3 0 109, Comma_Near 3 0 96, Comma_Near 3 0 53, Comma_Entry 4 0 21,
    Comma_Near 4 0 79, Comma_Near 4 0 65, Comma_Near 4 0 11, Comma_Entry 5 0 84,
    Comma_Near 5 0 96, Comma_Near 5 0 51, Comma_Entry 6 0 45, Comma_Near 6 0 275,
    Comma_Near 6 0 219, Comma_Near 6 0 203, Comma_Near 6 0 127, Comma_Near 6 0 91,
    Comma_Entry 7 0 6, Comma_Near 7 0 154, Comma_Near 7 0 87, Comma_Near 7 0 50,
    Comma_Near 7 0 43, Comma_Entry 8 0 35, Comma_Near 8 0 205, Comma_Near 8 0 147,
    Comma_Near 8 0 109, Comma_Near 8 0 91, Comma_Entry 9 0 8, Comma_Near 9 0 92,
    Comma_Near 9 0 3
  ]"

definition comma_source_tail_positions_1 :: "comma_finite_position list" where
  "comma_source_tail_positions_1 = [
    Comma_Entry 1 1 68, Comma_Near 1 1 352, Comma_Near 1 1 271, Comma_Near 1 1 180,
    Comma_Near 1 1 179, Comma_Near 1 1 168, Comma_Near 1 1 147, Comma_Near 1 1 116,
    Comma_Near 1 1 75, Comma_Near 1 1 24, Comma_Entry 2 1 38, Comma_Near 2 1 152,
    Comma_Near 2 1 70, Comma_Near 2 1 68, Comma_Near 2 1 46, Comma_Near 2 1 4,
    Comma_Entry 3 1 59, Comma_Near 3 1 101, Comma_Near 3 1 8, Comma_Entry 4 1 16,
    Comma_Near 4 1 84, Comma_Near 4 1 20, Comma_Near 4 1 16, Comma_Entry 5 1 29,
    Comma_Near 5 1 91, Comma_Entry 6 1 5, Comma_Near 6 1 115, Comma_Near 6 1 59,
    Comma_Near 6 1 43, Comma_Entry 7 1 34, Comma_Near 7 1 6, Comma_Entry 8 1 42,
    Comma_Near 8 1 118, Comma_Near 8 1 90, Comma_Near 8 1 82, Comma_Entry 9 1 7,
    Comma_Near 9 1 453, Comma_Near 9 1 374, Comma_Near 9 1 305, Comma_Near 9 1 246,
    Comma_Near 9 1 197, Comma_Near 9 1 158, Comma_Near 9 1 129, Comma_Near 9 1 110,
    Comma_Near 9 1 101, Comma_Near 9 1 2
  ]"

definition comma_source_tail_positions_2 :: "comma_finite_position list" where
  "comma_source_tail_positions_2 = [
    Comma_Entry 1 2 79, Comma_Near 1 2 441, Comma_Near 1 2 350, Comma_Near 1 2 349,
    Comma_Near 1 2 338, Comma_Near 1 2 317, Comma_Near 1 2 286, Comma_Near 1 2 245,
    Comma_Near 1 2 194, Comma_Near 1 2 133, Comma_Near 1 2 62, Comma_Entry 2 2 20,
    Comma_Near 2 2 200, Comma_Near 2 2 198, Comma_Near 2 2 176, Comma_Near 2 2 134,
    Comma_Near 2 2 72, Comma_Entry 3 2 11, Comma_Near 3 2 149, Comma_Near 3 2 136,
    Comma_Near 3 2 93, Comma_Near 3 2 20, Comma_Near 3 2 17, Comma_Entry 4 2 17,
    Comma_Near 4 2 263, Comma_Near 4 2 189, Comma_Near 4 2 175, Comma_Near 4 2 121,
    Comma_Near 4 2 27, Comma_Entry 5 2 8, Comma_Near 5 2 32, Comma_Entry 6 2 54,
    Comma_Near 6 2 6, Comma_Entry 7 2 41, Comma_Near 7 2 359, Comma_Near 7 2 342,
    Comma_Near 7 2 255, Comma_Near 7 2 198, Comma_Near 7 2 171, Comma_Near 7 2 74,
    Comma_Near 7 2 7, Comma_Entry 8 2 31, Comma_Near 8 2 189, Comma_Near 8 2 171,
    Comma_Near 8 2 73, Comma_Entry 9 2 6, Comma_Near 9 2 274, Comma_Near 9 2 205,
    Comma_Near 9 2 146, Comma_Near 9 2 97, Comma_Near 9 2 58, Comma_Near 9 2 29,
    Comma_Near 9 2 10, Comma_Near 9 2 1
  ]"

definition comma_source_tail_positions_3 :: "comma_finite_position list" where
  "comma_source_tail_positions_3 = [
    Comma_Entry 1 3 90, Comma_Near 1 3 50, Comma_Near 1 3 49, Comma_Near 1 3 38,
    Comma_Near 1 3 17, Comma_Entry 2 3 15, Comma_Near 2 3 85, Comma_Near 2 3 33,
    Comma_Entry 3 3 40, Comma_Near 3 3 120, Comma_Near 3 3 117, Comma_Near 3 3 84,
    Comma_Near 3 3 21, Comma_Entry 4 3 73, Comma_Near 4 3 27, Comma_Entry 5 3 8,
    Comma_Near 5 3 32, Comma_Entry 6 3 54, Comma_Near 6 3 86, Comma_Near 6 3 40,
    Comma_Near 6 3 34, Comma_Entry 7 3 33, Comma_Near 7 3 327, Comma_Near 7 3 290,
    Comma_Near 7 3 283, Comma_Near 7 3 206, Comma_Near 7 3 159, Comma_Near 7 3 142,
    Comma_Near 7 3 55, Comma_Entry 8 3 3, Comma_Near 8 3 167, Comma_Near 8 3 129,
    Comma_Near 8 3 111, Comma_Near 8 3 13, Comma_Entry 9 3 66, Comma_Near 9 3 34
  ]"

definition comma_source_tail_positions_4 :: "comma_finite_position list" where
  "comma_source_tail_positions_4 = [
    Comma_Entry 1 4 27, Comma_Near 1 4 453, Comma_Near 1 4 382, Comma_Near 1 4 301,
    Comma_Near 1 4 210, Comma_Near 1 4 209, Comma_Near 1 4 198, Comma_Near 1 4 177,
    Comma_Near 1 4 146, Comma_Near 1 4 105, Comma_Near 1 4 54, Comma_Entry 2 4 8,
    Comma_Near 2 4 152, Comma_Near 2 4 70, Comma_Near 2 4 68, Comma_Near 2 4 46,
    Comma_Near 2 4 4, Comma_Entry 3 4 59, Comma_Near 3 4 101, Comma_Near 3 4 8,
    Comma_Entry 4 4 16, Comma_Near 4 4 104, Comma_Near 4 4 40, Comma_Near 4 4 36,
    Comma_Entry 5 4 9, Comma_Near 5 4 11, Comma_Entry 6 4 85, Comma_Near 6 4 75,
    Comma_Near 6 4 19, Comma_Near 6 4 3, Comma_Entry 7 4 74, Comma_Near 7 4 406,
    Comma_Near 7 4 359, Comma_Near 7 4 342, Comma_Near 7 4 255, Comma_Near 7 4 198,
    Comma_Near 7 4 171, Comma_Near 7 4 74, Comma_Near 7 4 7, Comma_Entry 8 4 31,
    Comma_Near 8 4 219, Comma_Near 8 4 201, Comma_Near 8 4 103, Comma_Near 8 4 25,
    Comma_Entry 9 4 34, Comma_Near 9 4 426, Comma_Near 9 4 377, Comma_Near 9 4 338,
    Comma_Near 9 4 309, Comma_Near 9 4 290, Comma_Near 9 4 281, Comma_Near 9 4 182,
    Comma_Near 9 4 93, Comma_Near 9 4 14
  ]"

definition comma_source_tail_positions_5 :: "comma_finite_position list" where
  "comma_source_tail_positions_5 = [
    Comma_Entry 1 5 47, Comma_Near 1 5 153, Comma_Near 1 5 82
  ]"

definition comma_source_tail_positions :: "comma_finite_position list" where
  "comma_source_tail_positions =
    comma_source_tail_positions_0 @ comma_source_tail_positions_1 @
    comma_source_tail_positions_2 @ comma_source_tail_positions_3 @
    comma_source_tail_positions_4 @ comma_source_tail_positions_5"

lemma comma_source_trace_splice:
  assumes nonempty: "ys \<noteq> []"
    and prefix: "\<And>tail outcome. comma_finite_trace_ok residue
      (xs @ hd ys # tail) outcome =
      comma_finite_trace_ok residue (hd ys # tail) outcome"
  shows "comma_finite_trace_ok residue (xs @ ys @ tail) outcome =
    comma_finite_trace_ok residue (ys @ tail) outcome"
proof -
  obtain y rest where ys: "ys = y # rest"
    using nonempty by (cases ys) auto
  show ?thesis using prefix[of "rest @ tail" outcome]
    by (simp add: ys)
qed

lemma comma_source_trace_prefix_from_edges:
  assumes nonempty: "xs \<noteq> []"
    and edges: "list_all (\<lambda>(left,right).
      comma_finite_step residue left = Comma_Next right)
      (zip xs (tl xs))"
    and seam: "comma_finite_step residue (last xs) = Comma_Next y"
  shows "comma_finite_trace_ok residue (xs @ y # tail) outcome =
    comma_finite_trace_ok residue (y # tail) outcome"
  using nonempty edges seam
proof (induction xs arbitrary: y tail outcome)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis using Cons.prems by simp
  next
    case (Cons z zs)
    have edge: "comma_finite_step residue x = Comma_Next z"
      using Cons.prems(2) Cons by simp
    have suffix_edges: "list_all (\<lambda>(left,right).
        comma_finite_step residue left = Comma_Next right)
        (zip (z # zs) (tl (z # zs)))"
      using Cons.prems(2) Cons by simp
    have suffix_seam:
      "comma_finite_step residue (last (z # zs)) = Comma_Next y"
      using Cons.prems(3) Cons by simp
    have xs_nonempty: "xs \<noteq> []" using Cons by simp
    have xs_edges: "list_all (\<lambda>(left,right).
        comma_finite_step residue left = Comma_Next right)
        (zip xs (tl xs))"
      using suffix_edges Cons by simp
    have xs_seam: "comma_finite_step residue (last xs) = Comma_Next y"
      using suffix_seam Cons by simp
    have ih: "comma_finite_trace_ok residue (xs @ y # tail) outcome =
        comma_finite_trace_ok residue (y # tail) outcome"
      using Cons.IH[OF xs_nonempty xs_edges xs_seam, of tail outcome] .
    have suffix: "comma_finite_trace_ok residue
        ((z # zs) @ y # tail) outcome =
      comma_finite_trace_ok residue (y # tail) outcome"
      using ih Cons by simp
    show ?thesis using suffix edge Cons by simp
  qed
qed

lemma comma_source_trace_terminal_from_edges:
  assumes nonempty: "xs \<noteq> []"
    and edges: "list_all (\<lambda>(left,right).
      comma_finite_step residue left = Comma_Next right)
      (zip xs (tl xs))"
    and terminal: "comma_finite_step residue (last xs) = Comma_Fork a delta"
  shows "comma_finite_trace_ok residue xs (Comma_Fork_At a delta)"
  using nonempty edges terminal
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis using Cons.prems by simp
  next
    case (Cons y ys)
    have edge: "comma_finite_step residue x = Comma_Next y"
      using Cons.prems(2) Cons by simp
    have suffix_edges: "list_all (\<lambda>(left,right).
        comma_finite_step residue left = Comma_Next right)
        (zip (y # ys) (tl (y # ys)))"
      using Cons.prems(2) Cons by simp
    have suffix_terminal:
      "comma_finite_step residue (last (y # ys)) = Comma_Fork a delta"
      using Cons.prems(3) Cons by simp
    have xs_nonempty: "xs \<noteq> []" using Cons by simp
    have xs_edges: "list_all (\<lambda>(left,right).
        comma_finite_step residue left = Comma_Next right)
        (zip xs (tl xs))"
      using suffix_edges Cons by simp
    have xs_terminal:
      "comma_finite_step residue (last xs) = Comma_Fork a delta"
      using suffix_terminal Cons by simp
    have suffix: "comma_finite_trace_ok residue (y # ys)
        (Comma_Fork_At a delta)"
      using Cons.IH[OF xs_nonempty xs_edges xs_terminal] Cons by simp
    show ?thesis using edge suffix Cons by simp
  qed
qed

text \<open>Reuse the checked arithmetic catalog for local chart edges. Control
checking does not construct unused weighted payloads, and shared period/power
facts avoid rebuilding the same closed arithmetic for every occurrence.\<close>

lemmas comma_source_control_simps =
  comma_entry_control_formula comma_near_control_formula
  comma_finite_headroom_def comma_finite_guard_extra_def
  comma_power_residue_def comma_short_period_def Let_def
  comma_compiled_cycle_length_facts comma_compiled_period_facts
  comma_compiled_short_period_facts comma_compiled_power_facts

ML \<open>
  fun comma_source_arithmetic_context ctxt =
    Comma_Entry_Arithmetic.natural_context ctxt |> Simplifier.add_simps
      @{thms comma_source_control_simps comma_finite_move.inject
        comma_finite_move.distinct comma_finite_position.inject
        comma_finite_position.distinct list_all_Nil_iff list_all_Cons_iff
        zip.simps list.sel list.case list.distinct list.inject last.simps
        of_nat_numeral of_nat_0 of_nat_1 zmod_zminus1_eq_if zmod_zminus2_eq_if};
\<close>

method_setup comma_source_control = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD'
    (simp_tac (comma_source_arithmetic_context ctxt)))
\<close>

lemma comma_source_tail_trace_0:
  "comma_finite_trace_ok 5
    (comma_source_tail_positions_0 @
      hd comma_source_tail_positions_1 # tail) outcome =
   comma_finite_trace_ok 5
    (hd comma_source_tail_positions_1 # tail) outcome"
proof -
  have edges: "list_all (\<lambda>(left,right).
      comma_finite_step 5 left = Comma_Next right)
      (zip comma_source_tail_positions_0
        (tl comma_source_tail_positions_0))"
    unfolding comma_source_tail_positions_0_def
    by comma_source_control
  have seam: "comma_finite_step 5 (last comma_source_tail_positions_0) =
      Comma_Next (hd comma_source_tail_positions_1)"
    unfolding comma_source_tail_positions_0_def
      comma_source_tail_positions_1_def
    by comma_source_control
  have nonempty: "comma_source_tail_positions_0 \<noteq> []"
    by (simp add: comma_source_tail_positions_0_def)
  show ?thesis
    using comma_source_trace_prefix_from_edges[OF nonempty edges seam] .
qed

lemma comma_source_tail_trace_1:
  "comma_finite_trace_ok 5
    (comma_source_tail_positions_1 @
      hd comma_source_tail_positions_2 # tail) outcome =
   comma_finite_trace_ok 5
    (hd comma_source_tail_positions_2 # tail) outcome"
proof -
  have edges: "list_all (\<lambda>(left,right).
      comma_finite_step 5 left = Comma_Next right)
      (zip comma_source_tail_positions_1
        (tl comma_source_tail_positions_1))"
    unfolding comma_source_tail_positions_1_def
    by comma_source_control
  have seam: "comma_finite_step 5 (last comma_source_tail_positions_1) =
      Comma_Next (hd comma_source_tail_positions_2)"
    unfolding comma_source_tail_positions_1_def
      comma_source_tail_positions_2_def
    by comma_source_control
  have nonempty: "comma_source_tail_positions_1 \<noteq> []"
    by (simp add: comma_source_tail_positions_1_def)
  show ?thesis
    using comma_source_trace_prefix_from_edges[OF nonempty edges seam] .
qed

lemma comma_source_tail_trace_2:
  "comma_finite_trace_ok 5
    (comma_source_tail_positions_2 @
      hd comma_source_tail_positions_3 # tail) outcome =
   comma_finite_trace_ok 5
    (hd comma_source_tail_positions_3 # tail) outcome"
proof -
  have edges: "list_all (\<lambda>(left,right).
      comma_finite_step 5 left = Comma_Next right)
      (zip comma_source_tail_positions_2
        (tl comma_source_tail_positions_2))"
    unfolding comma_source_tail_positions_2_def
    by comma_source_control
  have seam: "comma_finite_step 5 (last comma_source_tail_positions_2) =
      Comma_Next (hd comma_source_tail_positions_3)"
    unfolding comma_source_tail_positions_2_def
      comma_source_tail_positions_3_def
    by comma_source_control
  have nonempty: "comma_source_tail_positions_2 \<noteq> []"
    by (simp add: comma_source_tail_positions_2_def)
  show ?thesis
    using comma_source_trace_prefix_from_edges[OF nonempty edges seam] .
qed

lemma comma_source_tail_trace_3:
  "comma_finite_trace_ok 5
    (comma_source_tail_positions_3 @
      hd comma_source_tail_positions_4 # tail) outcome =
   comma_finite_trace_ok 5
    (hd comma_source_tail_positions_4 # tail) outcome"
proof -
  have edges: "list_all (\<lambda>(left,right).
      comma_finite_step 5 left = Comma_Next right)
      (zip comma_source_tail_positions_3
        (tl comma_source_tail_positions_3))"
    unfolding comma_source_tail_positions_3_def
    by comma_source_control
  have seam: "comma_finite_step 5 (last comma_source_tail_positions_3) =
      Comma_Next (hd comma_source_tail_positions_4)"
    unfolding comma_source_tail_positions_3_def
      comma_source_tail_positions_4_def
    by comma_source_control
  have nonempty: "comma_source_tail_positions_3 \<noteq> []"
    by (simp add: comma_source_tail_positions_3_def)
  show ?thesis
    using comma_source_trace_prefix_from_edges[OF nonempty edges seam] .
qed

lemma comma_source_tail_trace_4:
  "comma_finite_trace_ok 5
    (comma_source_tail_positions_4 @
      hd comma_source_tail_positions_5 # tail) outcome =
   comma_finite_trace_ok 5
    (hd comma_source_tail_positions_5 # tail) outcome"
proof -
  have edges: "list_all (\<lambda>(left,right).
      comma_finite_step 5 left = Comma_Next right)
      (zip comma_source_tail_positions_4
        (tl comma_source_tail_positions_4))"
    unfolding comma_source_tail_positions_4_def
    by comma_source_control
  have seam: "comma_finite_step 5 (last comma_source_tail_positions_4) =
      Comma_Next (hd comma_source_tail_positions_5)"
    unfolding comma_source_tail_positions_4_def
      comma_source_tail_positions_5_def
    by comma_source_control
  have nonempty: "comma_source_tail_positions_4 \<noteq> []"
    by (simp add: comma_source_tail_positions_4_def)
  show ?thesis
    using comma_source_trace_prefix_from_edges[OF nonempty edges seam] .
qed

lemma comma_source_tail_trace_5:
  "comma_finite_trace_ok 5 comma_source_tail_positions_5
    (Comma_Fork_At 2 5)"
proof -
  have edges: "list_all (\<lambda>(left,right).
      comma_finite_step 5 left = Comma_Next right)
      (zip comma_source_tail_positions_5
        (tl comma_source_tail_positions_5))"
    unfolding comma_source_tail_positions_5_def
    by comma_source_control
  have terminal: "comma_finite_step 5 (last comma_source_tail_positions_5) =
      Comma_Fork 2 5"
    unfolding comma_source_tail_positions_5_def
    by comma_source_control
  have nonempty: "comma_source_tail_positions_5 \<noteq> []"
    by (simp add: comma_source_tail_positions_5_def)
  show ?thesis
    using comma_source_trace_terminal_from_edges
      [OF nonempty edges terminal] .
qed

lemma comma_source_tail_trace:
  "comma_finite_trace_ok 5 comma_source_tail_positions
    (Comma_Fork_At 2 5)"
proof -
  have seam_0: "comma_finite_trace_ok 5
      (comma_source_tail_positions_0 @ comma_source_tail_positions_1 @ tail)
      outcome =
      comma_finite_trace_ok 5 (comma_source_tail_positions_1 @ tail) outcome"
    for tail outcome
    by (rule comma_source_trace_splice[OF _ comma_source_tail_trace_0])
      (simp add: comma_source_tail_positions_1_def)
  have seam_1: "comma_finite_trace_ok 5
      (comma_source_tail_positions_1 @ comma_source_tail_positions_2 @ tail)
      outcome =
      comma_finite_trace_ok 5 (comma_source_tail_positions_2 @ tail) outcome"
    for tail outcome
    by (rule comma_source_trace_splice[OF _ comma_source_tail_trace_1])
      (simp add: comma_source_tail_positions_2_def)
  have seam_2: "comma_finite_trace_ok 5
      (comma_source_tail_positions_2 @ comma_source_tail_positions_3 @ tail)
      outcome =
      comma_finite_trace_ok 5 (comma_source_tail_positions_3 @ tail) outcome"
    for tail outcome
    by (rule comma_source_trace_splice[OF _ comma_source_tail_trace_2])
      (simp add: comma_source_tail_positions_3_def)
  have seam_3: "comma_finite_trace_ok 5
      (comma_source_tail_positions_3 @ comma_source_tail_positions_4 @ tail)
      outcome =
      comma_finite_trace_ok 5 (comma_source_tail_positions_4 @ tail) outcome"
    for tail outcome
    by (rule comma_source_trace_splice[OF _ comma_source_tail_trace_3])
      (simp add: comma_source_tail_positions_4_def)
  have seam_4: "comma_finite_trace_ok 5
      (comma_source_tail_positions_4 @ comma_source_tail_positions_5 @ tail)
      outcome =
      comma_finite_trace_ok 5 (comma_source_tail_positions_5 @ tail) outcome"
    for tail outcome
    by (rule comma_source_trace_splice[OF _ comma_source_tail_trace_4])
      (simp add: comma_source_tail_positions_5_def)
  have terminal_suffix: "comma_finite_trace_ok 5
      (comma_source_tail_positions_4 @ comma_source_tail_positions_5)
      (Comma_Fork_At 2 5)"
    using seam_4[of "[]" "Comma_Fork_At 2 5"] comma_source_tail_trace_5
    by simp
  show ?thesis
    using terminal_suffix
    by (simp only: comma_source_tail_positions_def seam_0 seam_1
      seam_2 seam_3)
qed

lemma comma_source_tail_shape:
  "length comma_source_tail_positions = 230"
  "hd comma_source_tail_positions = Comma_Entry 1 0 3"
  "last comma_source_tail_positions = Comma_Near 1 5 82"
  by (simp_all add: comma_source_tail_positions_def
    comma_source_tail_positions_0_def comma_source_tail_positions_1_def
    comma_source_tail_positions_2_def comma_source_tail_positions_3_def
    comma_source_tail_positions_4_def comma_source_tail_positions_5_def)

lemma comma_source_near_weight:
  "comma_finite_next_weight p (Comma_Near f delta h) =
    (case comma_finite_step (p mod 924) (Comma_Near f delta h) of
       Comma_Next next \<Rightarrow> 1 | _ \<Rightarrow> 0)"
  by (simp add: comma_finite_next_weight_def comma_finite_step_def
      comma_chart_weight_value_def Let_def split: if_splits)

lemma comma_source_entry_weight:
  "comma_finite_next_weight p (Comma_Entry f delta offset) =
    (if f < 1 \<or> 9 < f \<or> 98 < offset \<or>
        comma_finite_period f (offset mod 10) = 0
     then 0
     else comma_chart_weight_value p
       (Comma_Chart_Weight (comma_cycle_length f) delta
         (- int (comma_cycle_length f *
           (offset + comma_finite_headroom f (p mod 924) delta offset)))
         (comma_finite_period f (offset mod 10))))"
  by (simp add: comma_finite_next_weight_def Let_def)

method_setup comma_source_weight = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (simp_tac
    (comma_source_arithmetic_context ctxt |> Simplifier.add_simps
      @{thms comma_source_near_weight comma_source_entry_weight
        comma_chart_weight_value_def comma_chart_weight.case
        comma_finite_move.case list.map sum_list.Cons sum_list.Nil
        power_numeral_even power_numeral_odd power_0 power_one_right})))
\<close>

lemma comma_source_tail_weight_0:
  "sum_list (map (comma_finite_next_weight 5) comma_source_tail_positions_0) = 17204"
  unfolding comma_source_tail_positions_0_def
    by comma_source_weight

lemma comma_source_tail_weight_1:
  "sum_list (map (comma_finite_next_weight 5) comma_source_tail_positions_1) = 179836"
  unfolding comma_source_tail_positions_1_def
    by comma_source_weight

lemma comma_source_tail_weight_2:
  "sum_list (map (comma_finite_next_weight 5) comma_source_tail_positions_2) = 1782971"
  unfolding comma_source_tail_positions_2_def
    by comma_source_weight

lemma comma_source_tail_weight_3:
  "sum_list (map (comma_finite_next_weight 5) comma_source_tail_positions_3) = 17371823"
  unfolding comma_source_tail_positions_3_def
    by comma_source_weight

lemma comma_source_tail_weight_4:
  "sum_list (map (comma_finite_next_weight 5) comma_source_tail_positions_4) = 176242784"
  unfolding comma_source_tail_positions_4_def
    by comma_source_weight

lemma comma_source_tail_weight_5:
  "sum_list (map (comma_finite_next_weight 5) comma_source_tail_positions_5) = 217391301"
  unfolding comma_source_tail_positions_5_def
    by comma_source_weight

lemma comma_source_tail_weight:
  "sum_list (map (comma_finite_next_weight 5)
    (butlast comma_source_tail_positions)) = 412985919"
proof -
  have nonempty: "comma_source_tail_positions_5 \<noteq> []"
    by (simp add: comma_source_tail_positions_5_def)
  have last_position: "last comma_source_tail_positions_5 = Comma_Near 1 5 82"
    by (simp add: comma_source_tail_positions_5_def)
  have final_zero:
    "comma_finite_next_weight 5 (Comma_Near 1 5 82) = 0"
    by (simp add: comma_source_near_weight comma_near_control_formula Let_def)
  have final_split: "sum_list (map (comma_finite_next_weight 5)
      comma_source_tail_positions_5) =
    sum_list (map (comma_finite_next_weight 5)
      (butlast comma_source_tail_positions_5)) +
      comma_finite_next_weight 5 (last comma_source_tail_positions_5)"
    using arg_cong[OF append_butlast_last_id[OF nonempty],
      where f="\<lambda>xs. sum_list (map (comma_finite_next_weight 5) xs)"]
    by simp
  have final: "sum_list (map (comma_finite_next_weight 5)
      (butlast comma_source_tail_positions_5)) = 217391301"
    using comma_source_tail_weight_5 final_split final_zero last_position by simp
  show ?thesis using comma_source_tail_weight_0 comma_source_tail_weight_1
    comma_source_tail_weight_2 comma_source_tail_weight_3
    comma_source_tail_weight_4 final nonempty
    by (simp add: comma_source_tail_positions_def butlast_append)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_source_trace_splice
      comma_source_trace_prefix_from_edges comma_source_tail_trace_0
      comma_source_trace_terminal_from_edges
      comma_source_tail_trace_1 comma_source_tail_trace_2
      comma_source_tail_trace_3 comma_source_tail_trace_4
      comma_source_tail_trace_5 comma_source_tail_trace
      comma_source_tail_shape
      comma_source_tail_weight_0 comma_source_tail_weight_1
      comma_source_tail_weight_2 comma_source_tail_weight_3
      comma_source_tail_weight_4 comma_source_tail_weight_5
      comma_source_tail_weight})
    then () else error "Comma source witness depends on an oracle";
\<close>

end
