theory Double_Reverse_Periodic_Ring_Action
  imports Double_Reverse_Temporal_Refinement "HOL.Bit_Operations"
begin

unbundle bit_operations_syntax

theorem double_reverse_T_run_source_root_square:
  "double_reverse_T_run (first + second) source =
    double_reverse_T_run second (double_reverse_T_run first source)"
proof -
  have exponent: "first + second = second + first"
    by (simp add: add.commute)
  show ?thesis
    unfolding double_reverse_T_run_def
    by (simp only: exponent funpow_add comp_apply)
qed

corollary double_reverse_T_run_actual_midpoint_square:
  "double_reverse_T_run (2 * steps) source =
    double_reverse_T_run steps (double_reverse_T_run steps source)"
proof -
  have "2 * steps = steps + steps" by simp
  then show ?thesis by (simp only: double_reverse_T_run_source_root_square)
qed

text \<open>The NC15 periodic-core executor applies the exact T-squared local
digit law to a finite cyclic word after an external source certificate proves
that the demanded causal cones stay inside a periodic interior.  This theory
formalizes that finite action and its temporal powering.  A cycle premise is
an explicit certificate input: the finite ring itself does not prove that an
arbitrary integer source has a periodic interior or an indefinitely recurring
finite-source boundary.\<close>

definition double_reverse_ring_digit :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_ring_digit word i = word ! (i mod length word)"

definition double_reverse_ring_step :: "nat list \<Rightarrow> nat list" where
  "double_reverse_ring_step word =
    map (\<lambda>i. double_reverse_t2_digit
      (double_reverse_ring_digit word (i + length word - 1))
      (double_reverse_ring_digit word i)
      (double_reverse_ring_digit word (i + 1))) [0..<length word]"

text \<open>The finite periodic shortcut evolves a word with the same inward
orientation as the shrinking packed row: output position i reads cells i,
i+1, and i+2.  This is a cyclic state transition only; its use on a source
row is justified below by equality on the whole extracted row and the exact
causal-halo bound for each demanded output.\<close>

definition double_reverse_ring_inward_step :: "nat list \<Rightarrow> nat list" where
  "double_reverse_ring_inward_step word =
    map (\<lambda>i. double_reverse_t2_digit
      (double_reverse_ring_digit word i)
      (double_reverse_ring_digit word (i+1))
      (double_reverse_ring_digit word (i+2))) [0..<length word]"

lemma double_reverse_ring_inward_step_length:
  "length (double_reverse_ring_inward_step word) = length word"
  by (simp add: double_reverse_ring_inward_step_def)

lemma double_reverse_ring_inward_step_digit:
  assumes nonempty: "0 < length word"
      and index: "i < length word"
  shows "double_reverse_ring_inward_step word ! i =
    double_reverse_t2_digit
      (double_reverse_ring_digit word i)
      (double_reverse_ring_digit word (i+1))
      (double_reverse_ring_digit word (i+2))"
  using nonempty index
  by (simp add: double_reverse_ring_inward_step_def)

lemma double_reverse_ring_digit_shift_mod:
  assumes nonempty: "0 < length word"
  shows "double_reverse_ring_digit word
      (i mod length word + offset) =
    double_reverse_ring_digit word (i+offset)"
  unfolding double_reverse_ring_digit_def
  by (simp only: mod_add_left_eq)

lemma double_reverse_ring_inward_step_ring_digit:
  assumes nonempty: "0 < length word"
  shows "double_reverse_ring_digit (double_reverse_ring_inward_step word) i =
    double_reverse_t2_digit
      (double_reverse_ring_digit word i)
      (double_reverse_ring_digit word (i+1))
      (double_reverse_ring_digit word (i+2))"
proof -
  let ?k = "i mod length word"
  have k_bound: "?k < length word"
    using nonempty by simp
  have cell:
    "double_reverse_ring_inward_step word ! ?k =
      double_reverse_t2_digit
        (double_reverse_ring_digit word ?k)
        (double_reverse_ring_digit word (?k+1))
        (double_reverse_ring_digit word (?k+2))"
    by (rule double_reverse_ring_inward_step_digit[OF nonempty k_bound])
  have first:
    "double_reverse_ring_digit word ?k = double_reverse_ring_digit word i"
    by (simp add: double_reverse_ring_digit_def)
  have second:
    "double_reverse_ring_digit word (?k+1) =
      double_reverse_ring_digit word (i+1)"
    by (rule double_reverse_ring_digit_shift_mod[OF nonempty])
  have third:
    "double_reverse_ring_digit word (?k+2) =
      double_reverse_ring_digit word (i+2)"
    by (rule double_reverse_ring_digit_shift_mod[OF nonempty])
  show ?thesis
    using cell first second third
    by (simp add: double_reverse_ring_digit_def
      double_reverse_ring_inward_step_length)
qed

lemma double_reverse_ring_step_length:
  "length (double_reverse_ring_step word) = length word"
  by (simp add: double_reverse_ring_step_def)

lemma double_reverse_ring_step_cell:
  assumes "i < length word"
  shows "double_reverse_ring_step word ! i =
    double_reverse_t2_digit
      (double_reverse_ring_digit word (i + length word - 1))
      (double_reverse_ring_digit word i)
      (double_reverse_ring_digit word (i + 1))"
  using assms
  by (simp add: double_reverse_ring_step_def double_reverse_ring_digit_def)

lemma double_reverse_ring_step_digits:
  assumes "i < length word"
  shows "double_reverse_ring_step word ! i < 10"
  using double_reverse_ring_step_cell[OF assms]
  by (simp add: double_reverse_t2_digit_def)

lemma double_reverse_open_right_carry_is_five_residue:
  assumes digits: "center < 10" "right < 10"
  shows "(if (2*right + threshold5_digit center) mod 10 \<ge> 5
      then (1::nat) else 0) =
    (if right mod 5 = 3 \<or> right mod 5 = 4 then 1 else 0) +
    (if 5 \<le> center \<and> right mod 5 = 2 then 1 else 0)"
  using digits
  by (cases "center < 5";
      simp add: threshold5_digit_def; presburger)

text \<open>This cell law is the open-stencil bridge: the three decimal digits
are supplied by an externally admitted causal halo, and the proof converts the
two-pass carry expression to the radix-five selector used by the Moore bank.
It has no cyclic-neighbor, repeated-input, or infinite-source premise.\<close>

theorem double_reverse_t2_open_stencil_exact:
  assumes digits: "left < 10" "center < 10" "right < 10"
  shows "double_reverse_t2_digit left center right =
    (4*center + 2*(if 5 \<le> left then 1 else 0) +
      (if right mod 5 = 3 \<or> right mod 5 = 4 then 1 else 0) +
      (if 5 \<le> center \<and> right mod 5 = 2 then 1 else 0)) mod 10"
proof -
  have carry:
    "(if (2*right + threshold5_digit center) mod 10 \<ge> 5
        then (1::nat) else 0) =
      (if right mod 5 = 3 \<or> right mod 5 = 4 then 1 else 0) +
      (if 5 \<le> center \<and> right mod 5 = 2 then 1 else 0)"
    by (rule double_reverse_open_right_carry_is_five_residue[OF digits(2,3)])
  show ?thesis
    using carry
    by (simp add: double_reverse_t2_digit_def threshold5_digit_def)
qed

text \<open>The production open bank consumes a finite, source-issued pair of
exterior digits at every time step.  This fold keeps those inlets explicit;
invalid ports refuse rather than being wrapped around a finite ring or
defaulted to zero.\<close>

definition double_reverse_open_inputs_valid :: "(nat \<times> nat) list \<Rightarrow> bool" where
  "double_reverse_open_inputs_valid inputs \<longleftrightarrow>
    list_all (\<lambda>ports. fst ports < 10 \<and> snd ports < 10) inputs"

fun double_reverse_open_stencil_trace :: "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat" where
  "double_reverse_open_stencil_trace center [] = center"
| "double_reverse_open_stencil_trace center ((left,right)#inputs) =
    double_reverse_open_stencil_trace
      (double_reverse_t2_digit left center right) inputs"

fun double_reverse_open_stencil_guarded ::
    "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat option" where
  "double_reverse_open_stencil_guarded center [] =
    (if center < 10 then Some center else None)"
| "double_reverse_open_stencil_guarded center ((left,right)#inputs) =
    (if center < 10 \<and> left < 10 \<and> right < 10
     then double_reverse_open_stencil_guarded
       (double_reverse_t2_digit left center right) inputs
     else None)"

lemma double_reverse_t2_output_bounded:
  "double_reverse_t2_digit left center right < 10"
  by (simp add: double_reverse_t2_digit_def)

theorem double_reverse_open_stencil_trace_append:
  "double_reverse_open_stencil_trace center (prefix @ suffix) =
    double_reverse_open_stencil_trace
      (double_reverse_open_stencil_trace center prefix) suffix"
proof (induction prefix arbitrary: center)
  case Nil
  then show ?case by simp
next
  case (Cons ports prefix)
  obtain left right where ports: "ports = (left,right)" by (cases ports) auto
  show ?case
    using Cons.IH[of "double_reverse_t2_digit left center right"]
    by (simp add: ports)
qed

theorem double_reverse_open_stencil_guarded_exact:
  "double_reverse_open_stencil_guarded center inputs =
    (if center < 10 \<and> double_reverse_open_inputs_valid inputs
     then Some (double_reverse_open_stencil_trace center inputs) else None)"
proof (induction inputs arbitrary: center)
  case Nil
  then show ?case by (simp add: double_reverse_open_inputs_valid_def)
next
  case (Cons ports inputs)
  obtain left right where ports: "ports = (left,right)" by (cases ports) auto
  have bounded: "double_reverse_t2_digit left center right < 10"
    by (rule double_reverse_t2_output_bounded)
  show ?case
    using Cons.IH[of "double_reverse_t2_digit left center right"] bounded
    by (cases "center < 10"; cases "left < 10"; cases "right < 10";
        simp add: ports double_reverse_open_inputs_valid_def)
qed

section \<open>Finite packed-window consumer refinement\<close>

text \<open>The packed production evaluator applies its decimal stencil to
disjoint digit lanes.  The following cell function is its exact lane result:
the radix-five center residue, the left threshold bit, and the two right
borrow cases determine one decimal output.  Its equality to the two-pass
stencil is used below before any finite source window is advanced.  This
formalizes the selected-lane semantics; the raw machine-word bit operations
remain an implementation of this function and are separately checked by the
runtime differential tests.\<close>

definition double_reverse_packed_t2_cell :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_packed_t2_cell left center right =
    (4*(center mod 5) + 2*(if 5 \<le> left then 1 else 0) +
      (if right mod 5 = 3 \<or> right mod 5 = 4 then 1 else 0) +
      (if 5 \<le> center \<and> right mod 5 = 2 then 1 else 0)) mod 10"

lemma double_reverse_four_center_residue:
  fixes center :: nat
  assumes center: "center < 10"
  shows "(4*(center mod 5)) mod 10 = (4*center) mod 10"
proof -
  have cases:
    "center = 0 \<or> center = 1 \<or> center = 2 \<or> center = 3 \<or>
     center = 4 \<or> center = 5 \<or> center = 6 \<or> center = 7 \<or>
     center = 8 \<or> center = 9"
    using center by arith
  then show ?thesis by auto
qed

theorem double_reverse_packed_t2_cell_refines_stencil:
  assumes digits: "left < 10" "center < 10" "right < 10"
  shows "double_reverse_packed_t2_cell left center right =
    double_reverse_t2_digit left center right"
proof -
  let ?tail =
    "2*(if 5 \<le> left then 1 else 0) +
      (if right mod 5 = 3 \<or> right mod 5 = 4 then 1 else 0) +
      (if 5 \<le> center \<and> right mod 5 = 2 then 1 else 0)"
  have center_congruence:
    "(4*(center mod 5)) mod 10 = (4*center) mod 10"
    by (rule double_reverse_four_center_residue[OF digits(2)])
  have packed_congruence:
    "(4*(center mod 5) + ?tail) mod 10 =
      (4*center + ?tail) mod 10"
  proof -
    have "(4*(center mod 5) + ?tail) mod 10 =
        ((4*(center mod 5)) mod 10 + ?tail) mod 10"
      by (rule sym[OF mod_add_left_eq])
    also have "... = ((4*center) mod 10 + ?tail) mod 10"
      using center_congruence by simp
    also have "... = (4*center + ?tail) mod 10"
      by (rule mod_add_left_eq)
    finally show ?thesis .
  qed
  have stencil:
    "double_reverse_t2_digit left center right = (4*center + ?tail) mod 10"
    using double_reverse_t2_open_stencil_exact[OF digits]
    by (simp add: add.assoc)
  show ?thesis
    using packed_congruence stencil
    by (simp add: double_reverse_packed_t2_cell_def add.assoc)
qed

definition double_reverse_packed_row_step :: "nat list \<Rightarrow> nat list" where
  "double_reverse_packed_row_step row =
    map (\<lambda>i. double_reverse_packed_t2_cell
      (row ! i) (row ! (i+1)) (row ! (i+2))) [0..<length row - 2]"

lemma double_reverse_packed_row_step_length:
  "length (double_reverse_packed_row_step row) = length row - 2"
  by (simp add: double_reverse_packed_row_step_def)

lemma double_reverse_packed_row_step_cell:
  assumes index: "i < length row - 2"
  shows "double_reverse_packed_row_step row ! i =
    double_reverse_packed_t2_cell (row ! i) (row ! (i+1)) (row ! (i+2))"
  using index by (simp add: double_reverse_packed_row_step_def)

lemma double_reverse_packed_row_step_digit:
  assumes index: "i < length row - 2"
  shows "double_reverse_packed_row_step row ! i < 10"
  using double_reverse_packed_row_step_cell[OF index]
  by (simp add: double_reverse_packed_t2_cell_def)

definition double_reverse_decimal_row :: "nat list \<Rightarrow> bool" where
  "double_reverse_decimal_row row \<longleftrightarrow>
    (\<forall>i<length row. row ! i < 10)"

lemma double_reverse_packed_row_step_decimal:
  "double_reverse_decimal_row (double_reverse_packed_row_step row)"
  unfolding double_reverse_decimal_row_def
  by (auto simp: double_reverse_packed_row_step_length
      intro: double_reverse_packed_row_step_digit)

definition double_reverse_row_matches_ring :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "double_reverse_row_matches_ring row motif \<longleftrightarrow>
    0 < length motif \<and>
    (\<forall>j<length row. row ! j = double_reverse_ring_digit motif j)"

lemma double_reverse_packed_row_step_matches_inward_ring:
  assumes match: "double_reverse_row_matches_ring row motif"
      and decimal: "double_reverse_decimal_row row"
      and index: "i < length row - 2"
  shows "double_reverse_packed_row_step row ! i =
    double_reverse_ring_digit (double_reverse_ring_inward_step motif) i"
proof -
  have motif_nonempty: "0 < length motif"
    using match by (simp add: double_reverse_row_matches_ring_def)
  have row_left: "row ! i = double_reverse_ring_digit motif i"
    using match index
    by (auto simp: double_reverse_row_matches_ring_def; arith)
  have row_center: "row ! (i+1) = double_reverse_ring_digit motif (i+1)"
    using match index by (auto simp: double_reverse_row_matches_ring_def; arith)
  have row_right: "row ! (i+2) = double_reverse_ring_digit motif (i+2)"
    using match index by (auto simp: double_reverse_row_matches_ring_def; arith)
  have left_decimal: "row ! i < 10"
    using decimal index
    unfolding double_reverse_decimal_row_def by (auto; arith)
  have center_decimal: "row ! (i+1) < 10"
    using decimal index
    unfolding double_reverse_decimal_row_def by (auto; arith)
  have right_decimal: "row ! (i+2) < 10"
    using decimal index
    unfolding double_reverse_decimal_row_def by (auto; arith)
  have row_cell:
    "double_reverse_packed_row_step row ! i =
      double_reverse_t2_digit (row ! i) (row ! (i+1)) (row ! (i+2))"
    using double_reverse_packed_row_step_cell[OF index]
      double_reverse_packed_t2_cell_refines_stencil
        [OF left_decimal center_decimal right_decimal]
    by simp
  have motif_cell:
    "double_reverse_ring_digit (double_reverse_ring_inward_step motif) i =
      double_reverse_t2_digit
        (double_reverse_ring_digit motif i)
        (double_reverse_ring_digit motif (i+1))
        (double_reverse_ring_digit motif (i+2))"
    by (rule double_reverse_ring_inward_step_ring_digit[OF motif_nonempty])
  show ?thesis
    using row_cell row_left row_center row_right motif_cell by simp
qed

lemma double_reverse_packed_row_step_matches_ring:
  assumes match: "double_reverse_row_matches_ring row motif"
      and decimal: "double_reverse_decimal_row row"
  shows "double_reverse_row_matches_ring
      (double_reverse_packed_row_step row)
      (double_reverse_ring_inward_step motif)"
proof -
  have motif_nonempty: "0 < length motif"
    using match by (simp add: double_reverse_row_matches_ring_def)
  have child_nonempty:
    "0 < length (double_reverse_ring_inward_step motif)"
    using motif_nonempty
    by (simp add: double_reverse_ring_inward_step_length)
  have all_positions:
    "double_reverse_packed_row_step row ! j =
      double_reverse_ring_digit (double_reverse_ring_inward_step motif) j"
    if "j < length (double_reverse_packed_row_step row)" for j
  proof -
    have j_bound: "j < length row - 2"
      using that by (simp add: double_reverse_packed_row_step_length)
    show ?thesis
      by (rule double_reverse_packed_row_step_matches_inward_ring
        [OF match decimal j_bound])
  qed
  show ?thesis
    unfolding double_reverse_row_matches_ring_def
    using child_nonempty all_positions by blast
qed

fun double_reverse_packed_row_run :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "double_reverse_packed_row_run 0 row = row"
| "double_reverse_packed_row_run (Suc steps) row =
    double_reverse_packed_row_run steps (double_reverse_packed_row_step row)"

fun double_reverse_packed_row_ports ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "double_reverse_packed_row_ports 0 row i = []"
| "double_reverse_packed_row_ports (Suc steps) row i =
    (row ! (i+steps), row ! (i+steps+2)) #
      double_reverse_packed_row_ports steps
        (double_reverse_packed_row_step row) i"

fun double_reverse_ring_inward_run :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "double_reverse_ring_inward_run 0 word = word"
| "double_reverse_ring_inward_run (Suc steps) word =
    double_reverse_ring_inward_run steps
      (double_reverse_ring_inward_step word)"

lemma double_reverse_ring_inward_run_suc:
  "double_reverse_ring_inward_run (Suc steps) word =
    double_reverse_ring_inward_run steps
      (double_reverse_ring_inward_step word)"
  by simp

fun double_reverse_ring_inward_ports ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "double_reverse_ring_inward_ports 0 word i = []"
| "double_reverse_ring_inward_ports (Suc steps) word i =
    (double_reverse_ring_digit word (i+steps),
      double_reverse_ring_digit word (i+steps+2)) #
        double_reverse_ring_inward_ports steps
          (double_reverse_ring_inward_step word) i"

lemma double_reverse_packed_row_run_matches_inward_ring:
  assumes match: "double_reverse_row_matches_ring row motif"
      and decimal: "double_reverse_decimal_row row"
      and halo: "i + 2*steps < length row"
  shows "double_reverse_packed_row_run steps row ! i =
    double_reverse_ring_digit (double_reverse_ring_inward_run steps motif) i"
  using match decimal halo
proof (induction steps arbitrary: row motif i)
  case 0
  then show ?case
    by (auto simp: double_reverse_row_matches_ring_def)
next
  case (Suc steps)
  have child_match:
    "double_reverse_row_matches_ring
      (double_reverse_packed_row_step row)
      (double_reverse_ring_inward_step motif)"
    by (rule double_reverse_packed_row_step_matches_ring
      [OF Suc.prems(1,2)])
  have child_decimal:
    "double_reverse_decimal_row (double_reverse_packed_row_step row)"
    by (rule double_reverse_packed_row_step_decimal)
  have child_halo:
    "i + 2*steps < length (double_reverse_packed_row_step row)"
    using Suc.prems(3)
    by (simp add: double_reverse_packed_row_step_length; arith)
  have child:
    "double_reverse_packed_row_run steps
        (double_reverse_packed_row_step row) ! i =
      double_reverse_ring_digit
        (double_reverse_ring_inward_run steps
          (double_reverse_ring_inward_step motif)) i"
    by (rule Suc.IH[OF child_match child_decimal child_halo])
  show ?case
    using child
    by (simp add: double_reverse_packed_row_run.simps
      double_reverse_ring_inward_run_suc)
qed

lemma double_reverse_packed_row_ports_matches_inward_ring:
  assumes match: "double_reverse_row_matches_ring row motif"
      and decimal: "double_reverse_decimal_row row"
      and halo: "i + 2*steps < length row"
  shows "double_reverse_packed_row_ports steps row i =
    double_reverse_ring_inward_ports steps motif i"
  using match decimal halo
proof (induction steps arbitrary: row motif i)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  have child_match:
    "double_reverse_row_matches_ring
      (double_reverse_packed_row_step row)
      (double_reverse_ring_inward_step motif)"
    by (rule double_reverse_packed_row_step_matches_ring
      [OF Suc.prems(1,2)])
  have child_decimal:
    "double_reverse_decimal_row (double_reverse_packed_row_step row)"
    by (rule double_reverse_packed_row_step_decimal)
  have child_halo:
    "i + 2*steps < length (double_reverse_packed_row_step row)"
    using Suc.prems(3)
    by (simp add: double_reverse_packed_row_step_length; arith)
  have child:
    "double_reverse_packed_row_ports steps
        (double_reverse_packed_row_step row) i =
      double_reverse_ring_inward_ports steps
        (double_reverse_ring_inward_step motif) i"
    by (rule Suc.IH[OF child_match child_decimal child_halo])
  have left_bound: "i+steps < length row"
    using Suc.prems(3) by arith
  have right_bound: "i+steps+2 < length row"
    using Suc.prems(3) by arith
  have left_match:
    "row ! (i+steps) = double_reverse_ring_digit motif (i+steps)"
    using Suc.prems(1) left_bound
    by (auto simp: double_reverse_row_matches_ring_def)
  have right_match:
    "row ! (i+steps+2) = double_reverse_ring_digit motif (i+steps+2)"
    using Suc.prems(1) right_bound
    by (auto simp: double_reverse_row_matches_ring_def)
  show ?case
    using child left_match right_match by simp
qed

theorem double_reverse_packed_row_point_periodic_ring:
  assumes match: "double_reverse_row_matches_ring row motif"
      and decimal: "double_reverse_decimal_row row"
      and halo: "i + 2*steps < length row"
  shows "(double_reverse_packed_row_run steps row ! i,
      double_reverse_packed_row_ports steps row i) =
    (double_reverse_ring_digit (double_reverse_ring_inward_run steps motif) i,
      double_reverse_ring_inward_ports steps motif i)"
  using double_reverse_packed_row_run_matches_inward_ring
      [OF match decimal halo]
    double_reverse_packed_row_ports_matches_inward_ring
      [OF match decimal halo]
  by simp

lemma double_reverse_packed_row_run_length:
  assumes enough: "2*steps \<le> length row"
  shows "length (double_reverse_packed_row_run steps row) =
    length row - 2*steps"
  using enough
proof (induction steps arbitrary: row)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  have child_enough:
    "2*steps \<le> length (double_reverse_packed_row_step row)"
    using Suc.prems
    by (simp add: double_reverse_packed_row_step_length; arith)
  have child_length:
    "length (double_reverse_packed_row_run steps
      (double_reverse_packed_row_step row)) =
       length (double_reverse_packed_row_step row) - 2*steps"
    by (rule Suc.IH[OF child_enough])
  show ?case
    using Suc.prems child_length
    by (simp add: double_reverse_packed_row_step_length; arith)
qed

theorem double_reverse_packed_row_point_is_open_trace:
  assumes halo: "i + 2*steps < length row"
      and decimal: "double_reverse_decimal_row row"
  shows "double_reverse_packed_row_run steps row ! i =
    double_reverse_open_stencil_trace (row ! (i+steps))
      (double_reverse_packed_row_ports steps row i)"
  using halo decimal
proof (induction steps arbitrary: row i)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  have child_halo:
    "i + 2*steps < length (double_reverse_packed_row_step row)"
    using Suc.prems
    by (simp add: double_reverse_packed_row_step_length; arith)
  have cell_index: "i+steps < length row - 2"
    using Suc.prems by arith
  have child:
    "double_reverse_packed_row_run steps
        (double_reverse_packed_row_step row) ! i =
      double_reverse_open_stencil_trace
        (double_reverse_packed_row_step row ! (i+steps))
        (double_reverse_packed_row_ports steps
          (double_reverse_packed_row_step row) i)"
    by (rule Suc.IH[OF child_halo
      double_reverse_packed_row_step_decimal])
  have cell:
    "double_reverse_packed_row_step row ! (i+steps) =
      double_reverse_packed_t2_cell
        (row ! (i+steps)) (row ! (i+steps+1)) (row ! (i+steps+2))"
    by (rule double_reverse_packed_row_step_cell[OF cell_index])
  have indices:
    "i+steps < length row \<and>
      i+steps+1 < length row \<and>
      i+steps+2 < length row"
    using Suc.prems(1) by arith
  have first_digit: "row ! (i+steps) < 10"
    using Suc.prems(2) indices
    unfolding double_reverse_decimal_row_def by blast
  have center_digit: "row ! (i+steps+1) < 10"
    using Suc.prems(2) indices
    unfolding double_reverse_decimal_row_def by blast
  have last_digit: "row ! (i+steps+2) < 10"
    using Suc.prems(2) indices
    unfolding double_reverse_decimal_row_def
    by blast
  have cell_exact:
    "double_reverse_packed_t2_cell
        (row ! (i+steps)) (row ! (i+steps+1)) (row ! (i+steps+2)) =
      double_reverse_t2_digit
        (row ! (i+steps)) (row ! (i+steps+1)) (row ! (i+steps+2))"
    by (rule double_reverse_packed_t2_cell_refines_stencil
      [OF first_digit center_digit last_digit])
  show ?case
    using child cell cell_exact
    by (simp add: double_reverse_open_stencil_trace.simps)
qed

lemma double_reverse_packed_window_extent:
  assumes positive: "0 < count"
      and window_length:
        "length row = 2*(steps + count div 2) + 1"
  shows "length (double_reverse_packed_row_run steps row) =
    (if even count then count+1 else count)"
proof -
  have enough: "2*steps \<le> length row"
    using window_length by arith
  have run_length:
    "length (double_reverse_packed_row_run steps row) = length row - 2*steps"
    by (rule double_reverse_packed_row_run_length[OF enough])
  have halves:
    "2*(count div 2) + 1 = (if even count then count+1 else count)"
  proof -
    have divmod: "count = 2*(count div 2) + count mod 2"
      by (metis div_mult_mod_eq mult.commute)
    have remainder: "count mod 2 = 0 \<or> count mod 2 = 1"
      using mod_less_divisor[of count 2] by arith
    show ?thesis using divmod remainder
      by (auto simp: even_iff_mod_2_eq_zero; arith)
  qed
  show ?thesis
    using run_length window_length halves
    by arith
qed

definition double_reverse_packed_window_crop :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "double_reverse_packed_window_crop row count =
    take count (drop (if even count then 1 else 0) row)"

theorem double_reverse_packed_window_crop_exact:
  assumes extent:
    "length row = (if even count then count+1 else count)"
  shows "length (double_reverse_packed_window_crop row count) = count"
  using extent
  by (cases "even count")
    (simp_all add: double_reverse_packed_window_crop_def)

lemma double_reverse_packed_window_crop_nth:
  assumes extent:
      "length row = (if even count then count+1 else count)"
      and index: "i < count"
  shows "double_reverse_packed_window_crop row count ! i =
    row ! (i + (if even count then 1 else 0))"
  using extent index
  by (cases "even count"; simp_all
      add: double_reverse_packed_window_crop_def add.commute)

theorem double_reverse_packed_window_emits_requested_extent:
  assumes positive: "0 < count"
      and source_window:
        "length row = 2*(steps + count div 2) + 1"
  shows "length (double_reverse_packed_window_crop
      (double_reverse_packed_row_run steps row) count) = count"
  by (rule double_reverse_packed_window_crop_exact[
      OF double_reverse_packed_window_extent[OF positive source_window]])

theorem double_reverse_packed_window_point_refines_open_trace:
  assumes positive: "0 < count"
      and source_window:
        "length row = 2*(steps + count div 2) + 1"
      and index: "i < count"
      and decimal: "double_reverse_decimal_row row"
  shows "double_reverse_packed_window_crop
      (double_reverse_packed_row_run steps row) count ! i =
    double_reverse_open_stencil_trace
      (row ! (i + (if even count then 1 else 0) + steps))
      (double_reverse_packed_row_ports steps row
        (i + (if even count then 1 else 0)))"
proof -
  have extent:
    "length (double_reverse_packed_row_run steps row) =
      (if even count then count+1 else count)"
    by (rule double_reverse_packed_window_extent[OF positive source_window])
  have start_bound:
    "i + (if even count then 1 else 0) + 2*steps < length row"
    using source_window index
    by (cases "even count"; simp_all; arith)
  have point:
    "double_reverse_packed_row_run steps row !
        (i + (if even count then 1 else 0)) =
      double_reverse_open_stencil_trace
        (row ! (i + (if even count then 1 else 0) + steps))
        (double_reverse_packed_row_ports steps row
          (i + (if even count then 1 else 0)))"
    by (rule double_reverse_packed_row_point_is_open_trace
      [OF start_bound decimal])
  have crop_point:
    "double_reverse_packed_window_crop
        (double_reverse_packed_row_run steps row) count ! i =
      double_reverse_packed_row_run steps row !
        (i + (if even count then 1 else 0))"
    by (rule double_reverse_packed_window_crop_nth[OF extent index])
  show ?thesis using crop_point point by simp
qed

theorem double_reverse_packed_window_periodic_ring_exact:
  assumes positive: "0 < count"
      and source_window:
        "length row = 2*(steps + count div 2) + 1"
      and index: "i < count"
      and decimal: "double_reverse_decimal_row row"
      and match: "double_reverse_row_matches_ring row motif"
  shows "(double_reverse_packed_window_crop
        (double_reverse_packed_row_run steps row) count ! i,
      double_reverse_packed_row_ports steps row
        (i + (if even count then 1 else 0))) =
    (double_reverse_ring_digit (double_reverse_ring_inward_run steps motif)
        (i + (if even count then 1 else 0)),
      double_reverse_ring_inward_ports steps motif
        (i + (if even count then 1 else 0)))"
proof -
  let ?position = "i + (if even count then 1 else 0)"
  have extent:
    "length (double_reverse_packed_row_run steps row) =
      (if even count then count+1 else count)"
    by (rule double_reverse_packed_window_extent[OF positive source_window])
  have crop_point:
    "double_reverse_packed_window_crop
        (double_reverse_packed_row_run steps row) count ! i =
      double_reverse_packed_row_run steps row ! ?position"
    by (rule double_reverse_packed_window_crop_nth[OF extent index])
  have halo: "?position + 2*steps < length row"
    using source_window index
    by (cases "even count"; simp_all; arith)
  have periodic_point:
    "(double_reverse_packed_row_run steps row ! ?position,
      double_reverse_packed_row_ports steps row ?position) =
      (double_reverse_ring_digit
          (double_reverse_ring_inward_run steps motif) ?position,
        double_reverse_ring_inward_ports steps motif ?position)"
    by (rule double_reverse_packed_row_point_periodic_ring
      [OF match decimal halo])
  show ?thesis using crop_point periodic_point by simp
qed

definition double_reverse_ring_run :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "double_reverse_ring_run steps word =
    (double_reverse_ring_step ^^ steps) word"

lemma double_reverse_ring_run_add:
  "double_reverse_ring_run (first + second) word =
    double_reverse_ring_run second (double_reverse_ring_run first word)"
proof -
  have exponent: "first + second = second + first"
    by (simp add: add.commute)
  show ?thesis
    unfolding double_reverse_ring_run_def
    by (simp only: exponent funpow_add comp_apply)
qed

lemma double_reverse_ring_inward_run_add:
  "double_reverse_ring_inward_run (first + second) word =
    double_reverse_ring_inward_run second
      (double_reverse_ring_inward_run first word)"
proof (induction first arbitrary: word)
  case 0
  then show ?case by simp
next
  case (Suc first)
  have exponent: "Suc first + second = Suc (first + second)"
    by simp
  have induction:
    "double_reverse_ring_inward_run (first + second)
        (double_reverse_ring_inward_step word) =
      double_reverse_ring_inward_run second
        (double_reverse_ring_inward_run first
          (double_reverse_ring_inward_step word))"
    by (rule Suc.IH)
  show ?case
    using induction by (simp add: exponent)
qed

definition double_reverse_ring_inward_cycle :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "double_reverse_ring_inward_cycle period word \<longleftrightarrow>
    0 < period \<and> double_reverse_ring_inward_run period word = word"

theorem double_reverse_ring_inward_cycle_repeats:
  assumes cycle: "double_reverse_ring_inward_cycle period word"
  shows "double_reverse_ring_inward_run (period * count) word = word"
proof (induction count)
  case 0
  then show ?case
    by simp
next
  case (Suc count)
  have cycle_step: "double_reverse_ring_inward_run period word = word"
    using cycle by (simp add: double_reverse_ring_inward_cycle_def)
  have arithmetic: "period * Suc count = period * count + period"
    by (simp add: algebra_simps)
  show ?case
    using Suc.IH cycle_step
    by (simp only: arithmetic double_reverse_ring_inward_run_add
      Suc.IH cycle_step)
qed

theorem double_reverse_ring_inward_cycle_future_periodic:
  assumes cycle: "double_reverse_ring_inward_cycle period word"
  shows "double_reverse_ring_inward_run (time + period) word =
    double_reverse_ring_inward_run time word"
proof -
  have state_cycle: "double_reverse_ring_inward_run period word = word"
    using cycle by (simp add: double_reverse_ring_inward_cycle_def)
  have reindex: "time + period = period + time"
    by (simp add: add.commute)
  have cyclic:
    "double_reverse_ring_inward_run (period + time) word =
      double_reverse_ring_inward_run time
        (double_reverse_ring_inward_run period word)"
    by (rule double_reverse_ring_inward_run_add)
  have final_state:
    "double_reverse_ring_inward_run time
        (double_reverse_ring_inward_run period word) =
      double_reverse_ring_inward_run time word"
    using state_cycle by simp
  show ?thesis
    by (subst reindex; simp only: cyclic final_state)
qed

theorem double_reverse_packed_row_cycle_reduces_point:
  assumes match: "double_reverse_row_matches_ring row motif"
      and decimal: "double_reverse_decimal_row row"
      and cycle: "double_reverse_ring_inward_cycle period motif"
      and halo: "i + 2*(steps+period) < length row"
  shows "double_reverse_packed_row_run (steps+period) row ! i =
    double_reverse_packed_row_run steps row ! i"
proof -
  have long_halo: "i + 2*(steps+period) < length row"
    by (rule halo)
  have short_halo: "i + 2*steps < length row"
    using halo by arith
  have long_point:
    "double_reverse_packed_row_run (steps+period) row ! i =
      double_reverse_ring_digit
        (double_reverse_ring_inward_run (steps+period) motif) i"
    by (rule double_reverse_packed_row_run_matches_inward_ring
      [OF match decimal long_halo])
  have short_point:
    "double_reverse_packed_row_run steps row ! i =
      double_reverse_ring_digit (double_reverse_ring_inward_run steps motif) i"
    by (rule double_reverse_packed_row_run_matches_inward_ring
      [OF match decimal short_halo])
  have ring_point:
    "double_reverse_ring_digit
        (double_reverse_ring_inward_run (steps+period) motif) i =
      double_reverse_ring_digit (double_reverse_ring_inward_run steps motif) i"
    using double_reverse_ring_inward_cycle_future_periodic[OF cycle, of steps]
    by simp
  show ?thesis using long_point short_point ring_point by simp
qed

definition double_reverse_ring_cycle :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "double_reverse_ring_cycle period word \<longleftrightarrow>
    0 < period \<and> double_reverse_ring_run period word = word"

theorem double_reverse_ring_cycle_repeats:
  assumes cycle: "double_reverse_ring_cycle period word"
  shows "double_reverse_ring_run (period * count) word = word"
proof (induction count)
  case 0
  then show ?case by (simp add: double_reverse_ring_run_def)
next
  case (Suc count)
  have cycle_step: "double_reverse_ring_run period word = word"
    using cycle by (simp add: double_reverse_ring_cycle_def)
  have arithmetic: "period * Suc count = period * count + period"
    by (simp add: algebra_simps)
  show ?case
    using Suc.IH cycle_step
    by (simp only: arithmetic double_reverse_ring_run_add Suc.IH cycle_step)
qed

theorem double_reverse_ring_cycle_future_periodic:
  assumes cycle: "double_reverse_ring_cycle period word"
  shows "double_reverse_ring_run (time + period) word =
    double_reverse_ring_run time word"
proof -
  have state_cycle: "double_reverse_ring_run period word = word"
    using cycle by (simp add: double_reverse_ring_cycle_def)
  have reindex: "time + period = period + time" by (simp add: add.commute)
  have cyclic:
    "double_reverse_ring_run (period + time) word =
      double_reverse_ring_run time
        (double_reverse_ring_run period word)"
    by (rule double_reverse_ring_run_add)
  have final_state:
    "double_reverse_ring_run time
        (double_reverse_ring_run period word) =
      double_reverse_ring_run time word"
    using state_cycle by simp
  show ?thesis
    by (subst reindex; simp only: cyclic final_state)
qed

corollary double_reverse_ring_observation_periodic:
  assumes cycle: "double_reverse_ring_cycle period word"
      and coordinate: "i < length word"
  shows "double_reverse_ring_run (time + period) word ! i =
    double_reverse_ring_run time word ! i"
  using double_reverse_ring_cycle_future_periodic[OF cycle, of time]
  by simp

text \<open>Thus a certified ring cycle is a complete future quotient for the
ring's emitted digit word, and any projection of that word inherits the same
powered action.  Connecting a finite source interval to this ring remains a
separate causal-halo refinement obligation; the ring-period theorem alone is
not authority to publish digits outside that certified interval.\<close>

ML \<open>
  val checked = @{thms double_reverse_ring_step_length
    double_reverse_T_run_source_root_square
    double_reverse_T_run_actual_midpoint_square
    double_reverse_ring_step_cell double_reverse_ring_step_digits
    double_reverse_ring_inward_step_length
    double_reverse_ring_inward_step_digit
    double_reverse_ring_digit_shift_mod
    double_reverse_ring_inward_step_ring_digit
    double_reverse_open_right_carry_is_five_residue
    double_reverse_t2_open_stencil_exact double_reverse_t2_output_bounded
    double_reverse_open_stencil_trace_append
    double_reverse_open_stencil_guarded_exact
    double_reverse_packed_t2_cell_refines_stencil
    double_reverse_packed_row_step_length
    double_reverse_packed_row_step_cell
    double_reverse_packed_row_step_digit
    double_reverse_packed_row_step_decimal
    double_reverse_packed_row_step_matches_inward_ring
    double_reverse_packed_row_step_matches_ring
    double_reverse_ring_inward_run_suc
    double_reverse_packed_row_run_length
    double_reverse_packed_row_point_is_open_trace
    double_reverse_packed_row_run_matches_inward_ring
    double_reverse_packed_row_ports_matches_inward_ring
    double_reverse_packed_row_point_periodic_ring
    double_reverse_packed_window_extent
    double_reverse_packed_window_crop_exact
    double_reverse_packed_window_crop_nth
    double_reverse_packed_window_emits_requested_extent
    double_reverse_packed_window_point_refines_open_trace
    double_reverse_packed_window_periodic_ring_exact
    double_reverse_ring_run_add double_reverse_ring_cycle_repeats
    double_reverse_ring_cycle_future_periodic
    double_reverse_ring_observation_periodic
    double_reverse_ring_inward_run_add
    double_reverse_ring_inward_cycle_repeats
    double_reverse_ring_inward_cycle_future_periodic
    double_reverse_packed_row_cycle_reduces_point};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse periodic ring action depends on an oracle";
\<close>

end
