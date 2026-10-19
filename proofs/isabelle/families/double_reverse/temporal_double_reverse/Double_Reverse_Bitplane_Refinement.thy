theory Double_Reverse_Bitplane_Refinement
  imports Double_Reverse_Periodic_Ring_Action
begin

unbundle bit_operations_syntax

section \<open>Integer bitplane implementation refinement\<close>

text \<open>The preceding finite-window theorem describes the scalar lane
operation.  These definitions model the production representation itself:
ten little-endian integer bitplanes, arithmetic shifts, bitwise masks,
infinite two's-complement negation followed by a finite output cap, and OR
publication into the output planes.  Thus the next theorem connects the
machine-mask algorithm to the scalar window theorem rather than merely
re-stating its cell formula.\<close>

fun double_reverse_decimal_plane :: "nat \<Rightarrow> nat list \<Rightarrow> int" where
  "double_reverse_decimal_plane digit [] = 0"
| "double_reverse_decimal_plane digit (cell#cells) =
    (if cell=digit then 1 else 0) OR
      push_bit 1 (double_reverse_decimal_plane digit cells)"

lemma double_reverse_decimal_row_cell_bound:
  assumes decimal: "double_reverse_decimal_row row"
      and index: "i < length row"
  shows "row ! i < 10"
  using decimal index unfolding double_reverse_decimal_row_def by blast

definition double_reverse_decimal_planes :: "nat list \<Rightarrow> int list" where
  "double_reverse_decimal_planes row =
    map (\<lambda>digit. double_reverse_decimal_plane digit row) [0..<10]"

lemma double_reverse_decimal_plane_bit:
  "bit (double_reverse_decimal_plane digit row) i \<longleftrightarrow>
    i < length row \<and> row ! i = digit"
proof (induction row arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons cell cells)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis
      by (simp only: double_reverse_decimal_plane.simps bit_or_iff
          bit_push_bit_iff; simp)
  next
    case (Suc j)
    have tail:
      "bit (double_reverse_decimal_plane digit cells) j \<longleftrightarrow>
        j < length cells \<and> cells ! j = digit"
      by (rule Cons.IH)
    show ?thesis
      using Suc tail
      by (simp only: double_reverse_decimal_plane.simps bit_or_iff
          bit_push_bit_iff; simp)
  qed
qed

lemma double_reverse_decimal_planes_nth:
  assumes digit: "digit < 10"
  shows "bit (double_reverse_decimal_planes row ! digit) i \<longleftrightarrow>
    i < length row \<and> row ! i = digit"
  using digit
  by (simp add: double_reverse_decimal_planes_def
      double_reverse_decimal_plane_bit)

definition double_reverse_planes_high :: "int list \<Rightarrow> int" where
  "double_reverse_planes_high planes =
    planes ! 5 OR planes ! 6 OR planes ! 7 OR planes ! 8 OR planes ! 9"

definition double_reverse_planes_rho :: "int list \<Rightarrow> int" where
  "double_reverse_planes_rho planes =
    planes ! 3 OR planes ! 4 OR planes ! 8 OR planes ! 9"

definition double_reverse_planes_residue_two :: "int list \<Rightarrow> int" where
  "double_reverse_planes_residue_two planes = planes ! 2 OR planes ! 7"

definition double_reverse_planes_gate :: "int list \<Rightarrow> int" where
  "double_reverse_planes_gate planes =
    drop_bit 2 (double_reverse_planes_rho planes) OR
      (drop_bit 1 (double_reverse_planes_high planes) AND
       drop_bit 2 (double_reverse_planes_residue_two planes))"

definition double_reverse_planes_centers ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "double_reverse_planes_centers planes residue =
    drop_bit 1 (planes ! residue OR planes ! (residue + 5))"

definition double_reverse_planes_contribution ::
    "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "double_reverse_planes_contribution planes digit residue left_carry right_carry =
    (if digit = (4*residue + 2*left_carry + right_carry) mod 10 then
       double_reverse_planes_centers planes residue AND
         (if left_carry=1 then double_reverse_planes_high planes
          else NOT (double_reverse_planes_high planes)) AND
         (if right_carry=1 then double_reverse_planes_gate planes
          else NOT (double_reverse_planes_gate planes))
     else 0)"

fun double_reverse_planes_or :: "int list \<Rightarrow> int" where
  "double_reverse_planes_or [] = 0"
| "double_reverse_planes_or (plane#planes) =
    plane OR double_reverse_planes_or planes"

definition double_reverse_planes_contributions ::
    "int list \<Rightarrow> nat \<Rightarrow> int list" where
  "double_reverse_planes_contributions planes digit =
    concat (map (\<lambda>residue.
      concat (map (\<lambda>left_carry.
        map (\<lambda>right_carry.
          double_reverse_planes_contribution
            planes digit residue left_carry right_carry) [0..<2])
          [0..<2])) [0..<5])"

definition double_reverse_bitplane_step ::
    "int list \<Rightarrow> nat \<Rightarrow> int list" where
  "double_reverse_bitplane_step planes row_length =
    map (\<lambda>digit. take_bit (row_length - 2)
      (double_reverse_planes_or
        (double_reverse_planes_contributions planes digit))) [0..<10]"

lemma double_reverse_planes_high_bit:
  assumes row: "double_reverse_decimal_row row" and
    index: "i < length row"
  shows "bit (double_reverse_planes_high
      (double_reverse_decimal_planes row)) i \<longleftrightarrow>
    5 \<le> row ! i"
proof -
  have digit_bound: "row ! i < 10"
    by (rule double_reverse_decimal_row_cell_bound[OF row index])
  show ?thesis
    using index digit_bound
    by (simp add: double_reverse_planes_high_def bit_simps
        double_reverse_decimal_planes_nth; presburger)
qed

lemma double_reverse_planes_rho_bit:
  assumes row: "double_reverse_decimal_row row" and
    index: "i < length row"
  shows "bit (double_reverse_planes_rho
      (double_reverse_decimal_planes row)) i \<longleftrightarrow>
    (row ! i) mod 5 = 3 \<or> (row ! i) mod 5 = 4"
proof -
  have digit_bound: "row ! i < 10"
    by (rule double_reverse_decimal_row_cell_bound[OF row index])
  show ?thesis
    using index digit_bound
    by (simp add: double_reverse_planes_rho_def bit_simps
        double_reverse_decimal_planes_nth; presburger)
qed

lemma double_reverse_planes_residue_two_bit:
  assumes row: "double_reverse_decimal_row row" and
    index: "i < length row"
  shows "bit (double_reverse_planes_residue_two
      (double_reverse_decimal_planes row)) i \<longleftrightarrow>
    (row ! i) mod 5 = 2"
proof -
  have digit_bound: "row ! i < 10"
    by (rule double_reverse_decimal_row_cell_bound[OF row index])
  show ?thesis
    using index digit_bound
    by (simp add: double_reverse_planes_residue_two_def bit_simps
        double_reverse_decimal_planes_nth; presburger)
qed

lemma double_reverse_decimal_digit_mod5_fiber:
  fixes digit residue :: nat
  assumes digit: "digit < 10" and residue: "residue < 5"
  shows "digit mod 5 = residue \<longleftrightarrow>
      digit = residue \<or> digit = residue + 5"
  using digit residue by presburger

lemma double_reverse_planes_center_bit:
  assumes decimal: "double_reverse_decimal_row row"
      and extent: "i + 1 < length row"
      and residue: "residue < 5"
  shows "bit (double_reverse_planes_centers
      (double_reverse_decimal_planes row) residue) i \<longleftrightarrow>
    (row ! (i+1)) mod 5 = residue"
proof -
  have middle_index: "i+1 < length row"
    using extent by arith
  have middle_bound: "row ! (i+1) < 10"
    by (rule double_reverse_decimal_row_cell_bound[OF decimal middle_index])
  have residue_digit: "residue + 5 < 10"
    using residue by arith
  have low_digit: "residue < 10"
    using residue by arith
  have low_plane:
    "bit (double_reverse_decimal_planes row ! residue) (i+1) \<longleftrightarrow>
      i+1 < length row \<and> row ! (i+1) = residue"
    by (rule double_reverse_decimal_planes_nth[OF low_digit])
  have high_plane:
    "bit (double_reverse_decimal_planes row ! (residue+5)) (i+1) \<longleftrightarrow>
      i+1 < length row \<and> row ! (i+1) = residue+5"
    by (rule double_reverse_decimal_planes_nth[OF residue_digit])
  have expanded:
    "bit (double_reverse_planes_centers
        (double_reverse_decimal_planes row) residue) i =
      (bit (double_reverse_decimal_planes row ! residue) (i+1) \<or>
       bit (double_reverse_decimal_planes row ! (residue+5)) (i+1))"
    unfolding double_reverse_planes_centers_def
    by (simp only: bit_drop_bit_eq comp_apply bit_or_iff add.commute)
  show ?thesis
    using expanded middle_index middle_bound low_plane high_plane residue
    by (simp add: double_reverse_decimal_digit_mod5_fiber)
qed

lemma double_reverse_planes_gate_bit:
  assumes decimal: "double_reverse_decimal_row row"
      and extent: "i + 2 < length row"
  shows "bit (double_reverse_planes_gate
      (double_reverse_decimal_planes row)) i \<longleftrightarrow>
      ((row ! (i+2)) mod 5 = 3 \<or>
       (row ! (i+2)) mod 5 = 4 \<or>
       (5 \<le> row ! (i+1) \<and> (row ! (i+2)) mod 5 = 2))"
proof -
  have middle_index: "i+1 < length row" using extent by arith
  have middle_bound: "row ! (i+1) < 10"
    by (rule double_reverse_decimal_row_cell_bound[OF decimal middle_index])
  have right_bound: "row ! (i+2) < 10"
    by (rule double_reverse_decimal_row_cell_bound[OF decimal extent])
  have rho_at:
    "bit (double_reverse_planes_rho
        (double_reverse_decimal_planes row)) (i+2) \<longleftrightarrow>
      (row ! (i+2)) mod 5 = 3 \<or> (row ! (i+2)) mod 5 = 4"
    by (rule double_reverse_planes_rho_bit[OF decimal extent])
  have high_at:
    "bit (double_reverse_planes_high
        (double_reverse_decimal_planes row)) (i+1) \<longleftrightarrow>
      5 \<le> row ! (i+1)"
    by (rule double_reverse_planes_high_bit[OF decimal middle_index])
  have residue_at:
    "bit (double_reverse_planes_residue_two
        (double_reverse_decimal_planes row)) (i+2) \<longleftrightarrow>
      (row ! (i+2)) mod 5 = 2"
    by (rule double_reverse_planes_residue_two_bit[OF decimal extent])
  have expanded:
    "bit (double_reverse_planes_gate
        (double_reverse_decimal_planes row)) i =
      (bit (double_reverse_planes_rho
          (double_reverse_decimal_planes row)) (i+2) \<or>
       (bit (double_reverse_planes_high
          (double_reverse_decimal_planes row)) (i+1) \<and>
        bit (double_reverse_planes_residue_two
          (double_reverse_decimal_planes row)) (i+2)))"
    unfolding double_reverse_planes_gate_def
    by (simp only: bit_drop_bit_eq comp_apply bit_or_iff bit_and_iff add.commute)
  show ?thesis using expanded rho_at high_at residue_at by simp
qed

lemma double_reverse_planes_contribution_bit:
  assumes decimal: "double_reverse_decimal_row row"
      and extent: "i + 2 < length row"
      and digit: "digit < 10"
      and residue: "residue < 5"
      and left_carry: "left_carry < 2"
      and right_carry: "right_carry < 2"
  shows "bit (double_reverse_planes_contribution
      (double_reverse_decimal_planes row) digit residue
      left_carry right_carry) i \<longleftrightarrow>
    (digit = (4*residue + 2*left_carry + right_carry) mod 10 \<and>
     (row ! (i+1)) mod 5 = residue \<and>
     left_carry = (if 5 \<le> row ! i then 1 else 0) \<and>
     right_carry = (if (row ! (i+2)) mod 5 = 3 \<or>
                         (row ! (i+2)) mod 5 = 4 \<or>
                         (5 \<le> row ! (i+1) \<and>
                           (row ! (i+2)) mod 5 = 2) then 1 else 0))"
proof -
  have left_index: "i < length row" using extent by arith
  have left_bound: "row ! i < 10"
    by (rule double_reverse_decimal_row_cell_bound[OF decimal left_index])
  have middle_index: "i+1 < length row" using extent by arith
  have middle_bound: "row ! (i+1) < 10"
    by (rule double_reverse_decimal_row_cell_bound[OF decimal middle_index])
  have right_bound: "row ! (i+2) < 10"
    by (rule double_reverse_decimal_row_cell_bound[OF decimal extent])
  show ?thesis
    using decimal extent digit residue left_carry right_carry
      left_bound middle_bound right_bound
    by (simp add: double_reverse_planes_contribution_def bit_simps
        double_reverse_planes_center_bit double_reverse_planes_high_bit
        double_reverse_planes_gate_bit double_reverse_decimal_digit_mod5_fiber;
        presburger)
qed

lemma double_reverse_planes_or_bit:
  "bit (double_reverse_planes_or planes) i \<longleftrightarrow>
    (\<exists>plane\<in>set planes. bit plane i)"
  by (induction planes) (auto simp: bit_simps)

lemma double_reverse_planes_contributions_set:
  "set (double_reverse_planes_contributions planes digit) =
    {double_reverse_planes_contribution planes digit residue left_carry
       right_carry | residue left_carry right_carry.
       residue < 5 \<and> left_carry < 2 \<and> right_carry < 2}"
  unfolding double_reverse_planes_contributions_def
  by (fastforce simp: set_concat set_map set_upt image_iff)

lemma double_reverse_planes_contribution_choice_bit:
  "bit (double_reverse_planes_or
      (double_reverse_planes_contributions planes digit)) i \<longleftrightarrow>
    (\<exists>residue left_carry right_carry.
      residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
      bit (double_reverse_planes_contribution planes digit residue
        left_carry right_carry) i)"
  using double_reverse_planes_or_bit[of
      "double_reverse_planes_contributions planes digit" i]
  by (simp only: double_reverse_planes_contributions_set; blast)

lemma double_reverse_packed_t2_cell_selected_carries:
  fixes left center right :: nat
  shows "double_reverse_packed_t2_cell left center right =
    (4*(center mod 5) + 2*(if 5 \<le> left then (1::nat) else 0) +
      (if right mod 5 = 3 \<or> right mod 5 = 4 \<or>
          (5 \<le> center \<and> right mod 5 = 2) then (1::nat) else 0)) mod 10"
proof -
  have residue_bound: "right mod 5 < 5" by simp
  have right_carry_split:
    "(if right mod 5 = 3 \<or> right mod 5 = 4 then (1::nat) else 0) +
        (if 5 \<le> center \<and> right mod 5 = 2 then (1::nat) else 0) =
      (if right mod 5 = 3 \<or> right mod 5 = 4 \<or>
          (5 \<le> center \<and> right mod 5 = 2) then (1::nat) else 0)"
    using residue_bound
    by (cases "right mod 5 = 3"; cases "right mod 5 = 4";
        cases "right mod 5 = 2"; simp_all)
  show ?thesis
    unfolding double_reverse_packed_t2_cell_def
    using right_carry_split by simp
qed

lemma double_reverse_packed_t2_cell_choice_exact:
  assumes left: "left < 10" and center: "center < 10"
      and right: "right < 10" and digit: "digit < 10"
  shows "(\<exists>residue left_carry right_carry.
      residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
      digit = (4*residue + 2*left_carry + right_carry) mod 10 \<and>
      residue = center mod 5 \<and>
      left_carry = (if 5 \<le> left then 1 else 0) \<and>
      right_carry = (if right mod 5 = 3 \<or> right mod 5 = 4 \<or>
          (5 \<le> center \<and> right mod 5 = 2) then 1 else 0))
      \<longleftrightarrow>
    digit = double_reverse_packed_t2_cell left center right"
proof
  assume selected:
    "\<exists>residue left_carry right_carry.
      residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
      digit = (4*residue + 2*left_carry + right_carry) mod 10 \<and>
      residue = center mod 5 \<and>
      left_carry = (if 5 \<le> left then 1 else 0) \<and>
      right_carry = (if right mod 5 = 3 \<or> right mod 5 = 4 \<or>
          (5 \<le> center \<and> right mod 5 = 2) then 1 else 0)"
  then obtain residue left_carry right_carry where parts:
    "residue < 5" "left_carry < 2" "right_carry < 2"
    "digit = (4*residue + 2*left_carry + right_carry) mod 10"
    "residue = center mod 5"
    "left_carry = (if 5 \<le> left then 1 else 0)"
    "right_carry = (if right mod 5 = 3 \<or> right mod 5 = 4 \<or>
        (5 \<le> center \<and> right mod 5 = 2) then 1 else 0)"
    by blast
  have digit_is_selected:
    "digit = (4*(center mod 5) + 2*(if 5 \<le> left then 1 else 0) +
      (if right mod 5 = 3 \<or> right mod 5 = 4 \<or>
          (5 \<le> center \<and> right mod 5 = 2) then 1 else 0)) mod 10"
    using parts by simp
  show "digit = double_reverse_packed_t2_cell left center right"
    using digit_is_selected double_reverse_packed_t2_cell_selected_carries
    by simp
next
  assume digit:
    "digit = double_reverse_packed_t2_cell left center right"
  have residue_bound: "center mod 5 < 5" by simp
  have left_bound: "(if 5 \<le> left then (1::nat) else 0) < (2::nat)" by simp
  have right_bound:
    "(if right mod 5 = 3 \<or> right mod 5 = 4 \<or>
      (5 \<le> center \<and> right mod 5 = 2) then (1::nat) else 0) < (2::nat)"
    by simp
  have digit_selected:
    "digit = (4*(center mod 5) + 2*(if 5 \<le> left then 1 else 0) +
      (if right mod 5 = 3 \<or> right mod 5 = 4 \<or>
          (5 \<le> center \<and> right mod 5 = 2) then 1 else 0)) mod 10"
    using digit double_reverse_packed_t2_cell_selected_carries by simp
  show "\<exists>residue left_carry right_carry.
      residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
      digit = (4*residue + 2*left_carry + right_carry) mod 10 \<and>
      residue = center mod 5 \<and>
      left_carry = (if 5 \<le> left then 1 else 0) \<and>
      right_carry = (if right mod 5 = 3 \<or> right mod 5 = 4 \<or>
          (5 \<le> center \<and> right mod 5 = 2) then 1 else 0)"
    using residue_bound left_bound right_bound digit_selected by blast
qed

theorem double_reverse_bitplane_step_digit_exact:
  assumes length: "3 \<le> length row"
      and decimal: "double_reverse_decimal_row row"
      and index: "i < length row - 2"
      and digit: "digit < 10"
  shows "bit (double_reverse_bitplane_step
      (double_reverse_decimal_planes row) (length row) ! digit) i \<longleftrightarrow>
    double_reverse_packed_row_step row ! i = digit"
proof -
  have left_index: "i < length row" using length index by arith
  have middle_index: "i+1 < length row" using length index by arith
  have right_index: "i+2 < length row" using length index by arith
  have left_bound: "row ! i < 10"
    by (rule double_reverse_decimal_row_cell_bound[OF decimal left_index])
  have middle_bound: "row ! (i+1) < 10"
    by (rule double_reverse_decimal_row_cell_bound[OF decimal middle_index])
  have right_bound: "row ! (i+2) < 10"
    by (rule double_reverse_decimal_row_cell_bound[OF decimal right_index])
  have contributions:
    "(\<exists>residue left_carry right_carry.
      residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
      bit (double_reverse_planes_contribution
        (double_reverse_decimal_planes row) digit residue
        left_carry right_carry) i) \<longleftrightarrow>
     (\<exists>residue left_carry right_carry.
      residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
      digit = (4*residue + 2*left_carry + right_carry) mod 10 \<and>
      residue = (row ! (i+1)) mod 5 \<and>
      left_carry = (if 5 \<le> row ! i then 1 else 0) \<and>
      right_carry = (if (row ! (i+2)) mod 5 = 3 \<or>
          (row ! (i+2)) mod 5 = 4 \<or>
          (5 \<le> row ! (i+1) \<and> (row ! (i+2)) mod 5 = 2)
        then 1 else 0))"
  proof -
    have extent: "i+2 < length row" using length index by arith
    have pointwise:
      "bit (double_reverse_planes_contribution
          (double_reverse_decimal_planes row) digit residue
          left_carry right_carry) i \<longleftrightarrow>
        (digit = (4*residue + 2*left_carry + right_carry) mod 10 \<and>
         residue = (row ! (i+1)) mod 5 \<and>
         left_carry = (if 5 \<le> row ! i then 1 else 0) \<and>
         right_carry = (if (row ! (i+2)) mod 5 = 3 \<or>
           (row ! (i+2)) mod 5 = 4 \<or>
           (5 \<le> row ! (i+1) \<and> (row ! (i+2)) mod 5 = 2)
           then 1 else 0))"
      if residue_bound: "residue < 5"
        and left_bound: "left_carry < 2"
        and right_bound: "right_carry < 2"
      for residue left_carry right_carry
    proof -
      have exact:
        "bit (double_reverse_planes_contribution
            (double_reverse_decimal_planes row) digit residue
            left_carry right_carry) i \<longleftrightarrow>
          (digit = (4*residue + 2*left_carry + right_carry) mod 10 \<and>
           (row ! (i+1)) mod 5 = residue \<and>
           left_carry = (if 5 \<le> row ! i then 1 else 0) \<and>
           right_carry = (if (row ! (i+2)) mod 5 = 3 \<or>
             (row ! (i+2)) mod 5 = 4 \<or>
             (5 \<le> row ! (i+1) \<and> (row ! (i+2)) mod 5 = 2)
             then 1 else 0))"
        by (rule double_reverse_planes_contribution_bit
          [OF decimal extent digit residue_bound left_bound right_bound])
      have residue_symmetry:
        "(row ! (i+1)) mod 5 = residue \<Longrightarrow>
          residue = (row ! (i+1)) mod 5"
        by (rule sym)
      show ?thesis using exact residue_symmetry by blast
    qed
    show ?thesis
    proof
      assume selected:
        "\<exists>residue left_carry right_carry.
          residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
          bit (double_reverse_planes_contribution
            (double_reverse_decimal_planes row) digit residue
            left_carry right_carry) i"
      then obtain residue left_carry right_carry where
        residue_bound: "residue < 5" and
        left_carry_bound: "left_carry < 2" and
        right_carry_bound: "right_carry < 2" and
        contribution_bit: "bit (double_reverse_planes_contribution
          (double_reverse_decimal_planes row) digit residue
          left_carry right_carry) i"
        by blast
      have facts:
        "digit = (4*residue + 2*left_carry + right_carry) mod 10"
        "residue = (row ! (i+1)) mod 5"
        "left_carry = (if 5 \<le> row ! i then 1 else 0)"
        "right_carry = (if (row ! (i+2)) mod 5 = 3 \<or>
           (row ! (i+2)) mod 5 = 4 \<or>
           (5 \<le> row ! (i+1) \<and> (row ! (i+2)) mod 5 = 2)
           then 1 else 0)"
        using pointwise[OF residue_bound left_carry_bound right_carry_bound]
          contribution_bit by blast+
      show "\<exists>residue left_carry right_carry.
          residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
          digit = (4*residue + 2*left_carry + right_carry) mod 10 \<and>
          residue = (row ! (i+1)) mod 5 \<and>
          left_carry = (if 5 \<le> row ! i then 1 else 0) \<and>
          right_carry = (if (row ! (i+2)) mod 5 = 3 \<or>
            (row ! (i+2)) mod 5 = 4 \<or>
            (5 \<le> row ! (i+1) \<and> (row ! (i+2)) mod 5 = 2)
            then 1 else 0)"
        using residue_bound left_carry_bound right_carry_bound facts by blast
    next
      assume selected:
        "\<exists>residue left_carry right_carry.
          residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
          digit = (4*residue + 2*left_carry + right_carry) mod 10 \<and>
          residue = (row ! (i+1)) mod 5 \<and>
          left_carry = (if 5 \<le> row ! i then 1 else 0) \<and>
          right_carry = (if (row ! (i+2)) mod 5 = 3 \<or>
            (row ! (i+2)) mod 5 = 4 \<or>
            (5 \<le> row ! (i+1) \<and> (row ! (i+2)) mod 5 = 2)
            then 1 else 0)"
      then obtain residue left_carry right_carry where
        residue_bound: "residue < 5" and
        left_carry_bound: "left_carry < 2" and
        right_carry_bound: "right_carry < 2" and
        digit_condition: "digit = (4*residue + 2*left_carry + right_carry) mod 10" and
        residue_condition: "residue = (row ! (i+1)) mod 5" and
        left_condition: "left_carry = (if 5 \<le> row ! i then 1 else 0)" and
        right_condition: "right_carry = (if (row ! (i+2)) mod 5 = 3 \<or>
           (row ! (i+2)) mod 5 = 4 \<or>
           (5 \<le> row ! (i+1) \<and> (row ! (i+2)) mod 5 = 2)
           then 1 else 0)"
        by blast
      have bit:
        "bit (double_reverse_planes_contribution
          (double_reverse_decimal_planes row) digit residue
          left_carry right_carry) i"
        using pointwise[OF residue_bound left_carry_bound right_carry_bound]
          digit_condition residue_condition left_condition right_condition
        by blast
      show "\<exists>residue left_carry right_carry.
          residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
          bit (double_reverse_planes_contribution
            (double_reverse_decimal_planes row) digit residue
            left_carry right_carry) i"
        using residue_bound left_carry_bound right_carry_bound bit by blast
    qed
  qed
  have selected:
    "(\<exists>residue left_carry right_carry.
      residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
      digit = (4*residue + 2*left_carry + right_carry) mod 10 \<and>
      residue = (row ! (i+1)) mod 5 \<and>
      left_carry = (if 5 \<le> row ! i then 1 else 0) \<and>
      right_carry = (if (row ! (i+2)) mod 5 = 3 \<or>
          (row ! (i+2)) mod 5 = 4 \<or>
          (5 \<le> row ! (i+1) \<and> (row ! (i+2)) mod 5 = 2)
        then 1 else 0)) \<longleftrightarrow>
      digit = double_reverse_packed_t2_cell
        (row ! i) (row ! (i+1)) (row ! (i+2))"
    using left_bound middle_bound right_bound digit
    by (rule double_reverse_packed_t2_cell_choice_exact[of
        "row ! i" "row ! (i+1)" "row ! (i+2)" digit])
  have selected_reversed:
    "(\<exists>residue left_carry right_carry.
      residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
      digit = (4*residue + 2*left_carry + right_carry) mod 10 \<and>
      residue = (row ! (i+1)) mod 5 \<and>
      left_carry = (if 5 \<le> row ! i then 1 else 0) \<and>
      right_carry = (if (row ! (i+2)) mod 5 = 3 \<or>
          (row ! (i+2)) mod 5 = 4 \<or>
          (5 \<le> row ! (i+1) \<and> (row ! (i+2)) mod 5 = 2)
        then 1 else 0)) \<longleftrightarrow>
      double_reverse_packed_t2_cell
        (row ! i) (row ! (i+1)) (row ! (i+2)) = digit"
  proof
    assume chosen:
      "\<exists>residue left_carry right_carry.
        residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
        digit = (4*residue + 2*left_carry + right_carry) mod 10 \<and>
        residue = (row ! (i+1)) mod 5 \<and>
        left_carry = (if 5 \<le> row ! i then 1 else 0) \<and>
        right_carry = (if (row ! (i+2)) mod 5 = 3 \<or>
            (row ! (i+2)) mod 5 = 4 \<or>
            (5 \<le> row ! (i+1) \<and> (row ! (i+2)) mod 5 = 2)
          then 1 else 0)"
    have forward:
      "digit = double_reverse_packed_t2_cell
        (row ! i) (row ! (i+1)) (row ! (i+2))"
      using chosen selected by blast
    show "double_reverse_packed_t2_cell
        (row ! i) (row ! (i+1)) (row ! (i+2)) = digit"
      using forward by (rule sym)
  next
    assume reverse:
      "double_reverse_packed_t2_cell
        (row ! i) (row ! (i+1)) (row ! (i+2)) = digit"
    have forward:
      "digit = double_reverse_packed_t2_cell
        (row ! i) (row ! (i+1)) (row ! (i+2))"
      using reverse by (rule sym)
    show "\<exists>residue left_carry right_carry.
        residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
        digit = (4*residue + 2*left_carry + right_carry) mod 10 \<and>
        residue = (row ! (i+1)) mod 5 \<and>
        left_carry = (if 5 \<le> row ! i then 1 else 0) \<and>
        right_carry = (if (row ! (i+2)) mod 5 = 3 \<or>
            (row ! (i+2)) mod 5 = 4 \<or>
            (5 \<le> row ! (i+1) \<and> (row ! (i+2)) mod 5 = 2)
          then 1 else 0)"
      using forward selected by blast
  qed
  have output_bit:
    "bit (double_reverse_bitplane_step
        (double_reverse_decimal_planes row) (length row) ! digit) i \<longleftrightarrow>
      (\<exists>residue left_carry right_carry.
        residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
        bit (double_reverse_planes_contribution
          (double_reverse_decimal_planes row) digit residue
          left_carry right_carry) i)"
    using index digit
    by (simp add: double_reverse_bitplane_step_def bit_take_bit_iff
        double_reverse_planes_contribution_choice_bit)
  have cell:
    "double_reverse_packed_row_step row ! i =
      double_reverse_packed_t2_cell (row ! i) (row ! (i+1)) (row ! (i+2))"
    by (rule double_reverse_packed_row_step_cell[OF index])
  have output_iff_local_conditions:
    "bit (double_reverse_bitplane_step
        (double_reverse_decimal_planes row) (length row) ! digit) i \<longleftrightarrow>
      (\<exists>residue left_carry right_carry.
        residue < 5 \<and> left_carry < 2 \<and> right_carry < 2 \<and>
        digit = (4*residue + 2*left_carry + right_carry) mod 10 \<and>
        residue = (row ! (i+1)) mod 5 \<and>
        left_carry = (if 5 \<le> row ! i then 1 else 0) \<and>
        right_carry = (if (row ! (i+2)) mod 5 = 3 \<or>
            (row ! (i+2)) mod 5 = 4 \<or>
            (5 \<le> row ! (i+1) \<and> (row ! (i+2)) mod 5 = 2)
          then 1 else 0))"
    using output_bit contributions by blast
  have output_iff_selected:
    "bit (double_reverse_bitplane_step
        (double_reverse_decimal_planes row) (length row) ! digit) i \<longleftrightarrow>
      double_reverse_packed_t2_cell
        (row ! i) (row ! (i+1)) (row ! (i+2)) = digit"
    using output_iff_local_conditions selected_reversed by blast
  show ?thesis
    using output_iff_selected
    by (simp only: cell)
qed

theorem double_reverse_bitplane_step_refines_row:
  assumes length: "3 \<le> length row"
      and decimal: "double_reverse_decimal_row row"
  shows "double_reverse_bitplane_step
      (double_reverse_decimal_planes row) (length row) =
    double_reverse_decimal_planes (double_reverse_packed_row_step row)"
proof -
  have output_length:
    "length (double_reverse_packed_row_step row) = length row - 2"
    by (rule double_reverse_packed_row_step_length)
  have planes_equal:
    "double_reverse_bitplane_step
        (double_reverse_decimal_planes row) (length row) ! digit =
      double_reverse_decimal_plane digit
        (double_reverse_packed_row_step row)"
    if digit_bound: "digit < 10" for digit
  proof (rule bit_eqI)
    fix i
    show "bit (double_reverse_bitplane_step
        (double_reverse_decimal_planes row) (length row) ! digit) i =
      bit (double_reverse_decimal_plane digit
        (double_reverse_packed_row_step row)) i"
    proof (cases "i < length row - 2")
      case True
      have result_digit:
        "double_reverse_packed_row_step row ! i < 10"
        by (rule double_reverse_packed_row_step_digit[OF True])
      show ?thesis
        using double_reverse_bitplane_step_digit_exact
          [OF length decimal True digit_bound] result_digit True
        by (simp add: double_reverse_decimal_plane_bit output_length)
    next
      case False
      have output_index: "\<not> i < length (double_reverse_packed_row_step row)"
        using False output_length by simp
      show ?thesis
        using False output_index digit_bound
        by (simp add: double_reverse_bitplane_step_def
            double_reverse_decimal_planes_def
            double_reverse_decimal_plane_bit output_length
            bit_take_bit_iff)
    qed
  qed
  have planes_equal_expanded:
    "take_bit (length row - 2)
        (double_reverse_planes_or
          (double_reverse_planes_contributions
            (double_reverse_decimal_planes row) digit)) =
      double_reverse_decimal_plane digit
        (double_reverse_packed_row_step row)"
    if digit_bound: "digit < 10" for digit
    using planes_equal[OF digit_bound] digit_bound
    by (simp add: double_reverse_bitplane_step_def nth_map nth_upt)
  have map_result:
    "map (\<lambda>digit. take_bit (length row - 2)
        (double_reverse_planes_or
          (double_reverse_planes_contributions
            (double_reverse_decimal_planes row) digit))) [0..<10] =
      map (\<lambda>digit. double_reverse_decimal_plane digit
        (double_reverse_packed_row_step row)) [0..<10]"
  proof (rule map_cong)
    show "[0..<10] = [0..<10]" by simp
  next
    fix digit
    assume digit_in: "digit \<in> set [0..<10]"
    have digit_bound: "digit < 10" using digit_in by simp
    show "take_bit (length row - 2)
        (double_reverse_planes_or
          (double_reverse_planes_contributions
            (double_reverse_decimal_planes row) digit)) =
      double_reverse_decimal_plane digit (double_reverse_packed_row_step row)"
      by (rule planes_equal_expanded[OF digit_bound])
  qed
  have step_map:
    "double_reverse_bitplane_step
        (double_reverse_decimal_planes row) (length row) =
      map (\<lambda>digit. take_bit (length row - 2)
        (double_reverse_planes_or
          (double_reverse_planes_contributions
            (double_reverse_decimal_planes row) digit))) [0..<10]"
    by (simp only: double_reverse_bitplane_step_def)
  have target_map:
    "double_reverse_decimal_planes (double_reverse_packed_row_step row) =
      map (\<lambda>digit. double_reverse_decimal_plane digit
        (double_reverse_packed_row_step row)) [0..<10]"
    by (simp only: double_reverse_decimal_planes_def)
  show ?thesis
  proof (rule trans[OF step_map])
    show "map (\<lambda>digit. take_bit (length row - 2)
        (double_reverse_planes_or
          (double_reverse_planes_contributions
            (double_reverse_decimal_planes row) digit))) [0..<10] =
      double_reverse_decimal_planes (double_reverse_packed_row_step row)"
      by (rule trans[OF map_result target_map[symmetric]])
  qed
qed

fun double_reverse_bitplane_row_run :: "nat \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int list" where
  "double_reverse_bitplane_row_run 0 planes row_length = planes"
| "double_reverse_bitplane_row_run (Suc steps) planes row_length =
    double_reverse_bitplane_row_run steps
      (double_reverse_bitplane_step planes row_length) (row_length - 2)"

theorem double_reverse_bitplane_row_run_refines_packed_run:
  assumes enough: "2*steps < length row"
      and decimal: "double_reverse_decimal_row row"
  shows "double_reverse_bitplane_row_run steps
      (double_reverse_decimal_planes row) (length row) =
    double_reverse_decimal_planes (double_reverse_packed_row_run steps row)"
  using enough decimal
proof (induction steps arbitrary: row)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  have source_length: "3 \<le> length row"
    using Suc.prems(1) by arith
  have stepped_decimal:
    "double_reverse_decimal_row (double_reverse_packed_row_step row)"
    by (rule double_reverse_packed_row_step_decimal)
  have enough_after:
    "2*steps < length (double_reverse_packed_row_step row)"
    using Suc.prems(1)
    by (simp add: double_reverse_packed_row_step_length; arith)
  have one_step:
    "double_reverse_bitplane_step
        (double_reverse_decimal_planes row) (length row) =
      double_reverse_decimal_planes (double_reverse_packed_row_step row)"
    by (rule double_reverse_bitplane_step_refines_row
      [OF source_length Suc.prems(2)])
  have tail:
    "double_reverse_bitplane_row_run steps
        (double_reverse_decimal_planes (double_reverse_packed_row_step row))
        (length (double_reverse_packed_row_step row)) =
      double_reverse_decimal_planes
        (double_reverse_packed_row_run steps
          (double_reverse_packed_row_step row))"
    by (rule Suc.IH[OF enough_after stepped_decimal])
  show ?case
    using one_step tail
    by (simp only: double_reverse_bitplane_row_run.simps
        double_reverse_packed_row_run.simps
        double_reverse_packed_row_step_length)
qed

theorem double_reverse_bitplane_window_point_refines_open_trace:
  assumes positive: "0 < count"
      and source_window:
        "length row = 2*(steps + count div 2) + 1"
      and index: "i < count"
      and decimal: "double_reverse_decimal_row row"
      and digit: "digit < 10"
  shows "bit (double_reverse_bitplane_row_run steps
      (double_reverse_decimal_planes row) (length row) ! digit)
      (i + (if even count then 1 else 0)) \<longleftrightarrow>
    double_reverse_open_stencil_trace
      (row ! (i + (if even count then 1 else 0) + steps))
      (double_reverse_packed_row_ports steps row
        (i + (if even count then 1 else 0))) = digit"
proof -
  have enough: "2*steps < length row"
    using positive source_window by arith
  have run:
    "double_reverse_bitplane_row_run steps
        (double_reverse_decimal_planes row) (length row) =
      double_reverse_decimal_planes (double_reverse_packed_row_run steps row)"
    by (rule double_reverse_bitplane_row_run_refines_packed_run
      [OF enough decimal])
  have extent:
    "length (double_reverse_packed_row_run steps row) =
      (if even count then count+1 else count)"
    by (rule double_reverse_packed_window_extent[OF positive source_window])
  have point_index:
    "i + (if even count then 1 else 0) <
      length (double_reverse_packed_row_run steps row)"
    using extent index by (cases "even count"; simp_all; arith)
  have cropped:
    "double_reverse_packed_window_crop
        (double_reverse_packed_row_run steps row) count ! i =
      double_reverse_packed_row_run steps row !
        (i + (if even count then 1 else 0))"
    by (rule double_reverse_packed_window_crop_nth[OF extent index])
  have selected_digit:
    "bit (double_reverse_decimal_planes
        (double_reverse_packed_row_run steps row) ! digit)
        (i + (if even count then 1 else 0)) \<longleftrightarrow>
      double_reverse_packed_row_run steps row !
        (i + (if even count then 1 else 0)) = digit"
    using digit point_index
    by (simp add: double_reverse_decimal_planes_nth)
  have scalar:
    "double_reverse_packed_window_crop
        (double_reverse_packed_row_run steps row) count ! i =
      double_reverse_open_stencil_trace
        (row ! (i + (if even count then 1 else 0) + steps))
        (double_reverse_packed_row_ports steps row
          (i + (if even count then 1 else 0)))"
    by (rule double_reverse_packed_window_point_refines_open_trace
      [OF positive source_window index decimal])
  show ?thesis using run cropped selected_digit scalar by simp
qed

theorem double_reverse_bitplane_row_periodic_ring_exact:
  assumes match: "double_reverse_row_matches_ring row motif"
      and decimal: "double_reverse_decimal_row row"
      and halo: "i + 2*steps < length row"
      and digit: "digit < 10"
  shows "bit (double_reverse_bitplane_row_run steps
      (double_reverse_decimal_planes row) (length row) ! digit) i \<longleftrightarrow>
    double_reverse_ring_digit
      (double_reverse_ring_inward_run steps motif) i = digit"
proof -
  have enough: "2*steps < length row"
    using halo by arith
  have bitplanes:
    "double_reverse_bitplane_row_run steps
        (double_reverse_decimal_planes row) (length row) =
      double_reverse_decimal_planes
        (double_reverse_packed_row_run steps row)"
    by (rule double_reverse_bitplane_row_run_refines_packed_run
      [OF enough decimal])
  have row_point:
    "double_reverse_packed_row_run steps row ! i =
      double_reverse_ring_digit (double_reverse_ring_inward_run steps motif) i"
    by (rule double_reverse_packed_row_run_matches_inward_ring
      [OF match decimal halo])
  have run_length:
    "length (double_reverse_packed_row_run steps row) =
      length row - 2*steps"
  proof (rule double_reverse_packed_row_run_length)
    show "2*steps \<le> length row" using enough by arith
  qed
  have output_index: "i < length (double_reverse_packed_row_run steps row)"
    using halo run_length by arith
  show ?thesis
    using bitplanes row_point output_index digit
    by (simp add: double_reverse_decimal_planes_nth)
qed

theorem double_reverse_bitplane_window_periodic_ring_exact:
  assumes positive: "0 < count"
      and source_window:
        "length row = 2*(steps + count div 2) + 1"
      and index: "i < count"
      and decimal: "double_reverse_decimal_row row"
      and match: "double_reverse_row_matches_ring row motif"
      and digit: "digit < 10"
  shows "bit (double_reverse_bitplane_row_run steps
      (double_reverse_decimal_planes row) (length row) ! digit)
      (i + (if even count then 1 else 0)) \<longleftrightarrow>
    double_reverse_ring_digit (double_reverse_ring_inward_run steps motif)
      (i + (if even count then 1 else 0)) = digit"
proof -
  let ?position = "i + (if even count then 1 else 0)"
  have halo: "?position + 2*steps < length row"
    using source_window index
    by (cases "even count"; simp_all; arith)
  show ?thesis
    by (rule double_reverse_bitplane_row_periodic_ring_exact
      [OF match decimal halo digit])
qed

ML \<open>
  val checked = @{thms double_reverse_decimal_row_cell_bound
    double_reverse_decimal_plane_bit double_reverse_decimal_planes_nth
    double_reverse_planes_high_bit double_reverse_planes_rho_bit
    double_reverse_planes_residue_two_bit double_reverse_decimal_digit_mod5_fiber
    double_reverse_planes_center_bit double_reverse_planes_gate_bit
    double_reverse_planes_contribution_bit double_reverse_planes_or_bit
    double_reverse_planes_contributions_set
    double_reverse_planes_contribution_choice_bit
    double_reverse_packed_t2_cell_selected_carries
    double_reverse_packed_t2_cell_choice_exact
    double_reverse_bitplane_step_digit_exact
    double_reverse_bitplane_step_refines_row
    double_reverse_bitplane_row_run_refines_packed_run
    double_reverse_bitplane_window_point_refines_open_trace
    double_reverse_bitplane_row_periodic_ring_exact
    double_reverse_bitplane_window_periodic_ring_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse bitplane refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Double-reverse bitplane refinement contains skip_proof"
    else ();
\<close>

end
