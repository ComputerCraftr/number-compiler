theory Double_Reverse_Group_Ring_Carry_Cut
  imports Double_Reverse_Temporal_Refinement
    Shared_Carry_Dynamics.Decimal_Normalization_Morphism
    Shared_Carry_Dynamics.Shared_Carry_Tape
begin

text \<open>The physical recurrence is \(T=2R\).  This theory deliberately
keeps that action separate from reverse/add's \(I+R\) action.  A finite
mod-32 group-ring result below is only a projection of an authenticated
finite digit cut: it retains the carry escaping the cut and does not certify
future repetition or replace the output word.\<close>

section \<open>One physical doubling-normalization cut\<close>

definition double_reverse_decimal_word :: "nat list \<Rightarrow> bool" where
  "double_reverse_decimal_word source \<longleftrightarrow>
    (\<forall>digit\<in>set source. digit < 10)"

definition double_reverse_cut_carry :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_cut_carry source j =
    (if j < length source then threshold5_digit (source ! j) else 0)"

definition double_reverse_cut_incoming :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_cut_incoming source j =
    (if j = 0 then 0 else double_reverse_cut_carry source (j-1))"

definition double_reverse_cut_output :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_cut_output source j =
    (if j < length source then
      (2 * (source ! j) + double_reverse_cut_incoming source j) mod 10
     else 0)"

definition double_reverse_cut_polynomial ::
    "(nat \<Rightarrow> 'a::comm_ring_1) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
  "double_reverse_cut_polynomial coefficient width z =
    (\<Sum>j<width. coefficient j * z^j)"

definition double_reverse_cut_raw_coefficient ::
    "nat list \<Rightarrow> nat \<Rightarrow> int" where
  "double_reverse_cut_raw_coefficient source j =
    (if j < length source then 2 * int (source ! j) else 0)"

definition double_reverse_cut_normalized_coefficient ::
    "nat list \<Rightarrow> nat \<Rightarrow> int" where
  "double_reverse_cut_normalized_coefficient source j =
    int (double_reverse_cut_output source j)"

definition double_reverse_cut_carry_coefficient ::
    "nat list \<Rightarrow> nat \<Rightarrow> int" where
  "double_reverse_cut_carry_coefficient source j =
    int (double_reverse_cut_carry source j)"

lemma double_reverse_cut_carry_bound:
  "double_reverse_cut_carry source j \<le> 1"
  by (simp add: double_reverse_cut_carry_def threshold5_digit_def)

lemma double_reverse_cut_column_balance:
  assumes admitted: "double_reverse_decimal_word source"
      and index: "j < length source"
  shows "int (2 * (source ! j)) -
      double_reverse_cut_normalized_coefficient source j =
    10 * double_reverse_cut_carry_coefficient source j -
      (if j=0 then 0 else
        double_reverse_cut_carry_coefficient source (j-1))"
proof -
  have digit: "source ! j < 10"
    using admitted index unfolding double_reverse_decimal_word_def
    by (meson nth_mem)
  have incoming: "double_reverse_cut_incoming source j \<le> 1"
    unfolding double_reverse_cut_incoming_def
    using double_reverse_cut_carry_bound[of source "j-1"] by auto
  have balance:
    "2 * (source ! j) + double_reverse_cut_incoming source j =
      (2 * (source ! j) + double_reverse_cut_incoming source j) mod 10 +
        10 * threshold5_digit (source ! j)"
    using decimal_double_digit_carry[OF digit incoming]
    by (simp add: threshold5_digit_def)
  have balance_int_lifted:
    "int (2 * (source ! j) + double_reverse_cut_incoming source j) =
      int ((2 * (source ! j) + double_reverse_cut_incoming source j) mod 10 +
        10 * threshold5_digit (source ! j))"
    using balance by (rule arg_cong[where f=int])
  have balance_int:
    "2 * int (source ! j) + int (double_reverse_cut_incoming source j) =
      int ((2 * (source ! j) + double_reverse_cut_incoming source j) mod 10) +
        10 * int (threshold5_digit (source ! j))"
    using balance_int_lifted
    by (simp only: of_nat_add of_nat_mult)
  have incoming_int:
    "int (double_reverse_cut_incoming source j) =
      (if j=0 then 0 else double_reverse_cut_carry_coefficient source (j-1))"
    by (simp add: double_reverse_cut_incoming_def
        double_reverse_cut_carry_coefficient_def)
  have outgoing_int:
    "int (threshold5_digit (source ! j)) =
      double_reverse_cut_carry_coefficient source j"
    using index by (simp add: double_reverse_cut_carry_coefficient_def
        double_reverse_cut_carry_def)
  have output_int:
    "int ((2 * (source ! j) + double_reverse_cut_incoming source j) mod 10) =
      double_reverse_cut_normalized_coefficient source j"
    using index by (simp add: double_reverse_cut_normalized_coefficient_def
        double_reverse_cut_output_def)
  have result:
    "2 * int (source ! j) - double_reverse_cut_normalized_coefficient source j =
      10 * double_reverse_cut_carry_coefficient source j -
        (if j=0 then 0 else double_reverse_cut_carry_coefficient source (j-1))"
    using balance_int incoming_int outgoing_int output_int by linarith
  show ?thesis using result by simp
qed

lemma double_reverse_cut_columns_normalize:
  assumes admitted: "double_reverse_decimal_word source"
      and index: "j < length source"
  shows "double_reverse_cut_raw_coefficient source j -
      double_reverse_cut_normalized_coefficient source j =
    10 * double_reverse_cut_carry_coefficient source j -
      (if j=0 then 0 else
        double_reverse_cut_carry_coefficient source (j-1))"
  using double_reverse_cut_column_balance[OF admitted index] index
  by (simp add: double_reverse_cut_raw_coefficient_def)

definition double_reverse_cut_carry_polynomial ::
    "nat list \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a" where
  "double_reverse_cut_carry_polynomial source z =
    double_reverse_cut_polynomial
      (\<lambda>j. of_int (double_reverse_cut_carry_coefficient source j))
      (length source) z"

definition double_reverse_cut_raw_polynomial ::
    "nat list \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a" where
  "double_reverse_cut_raw_polynomial source z =
    double_reverse_cut_polynomial
      (\<lambda>j. of_int (double_reverse_cut_raw_coefficient source j))
      (length source) z"

definition double_reverse_cut_normalized_polynomial ::
    "nat list \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a" where
  "double_reverse_cut_normalized_polynomial source z =
    double_reverse_cut_polynomial
      (\<lambda>j. of_int (double_reverse_cut_normalized_coefficient source j))
      (length source) z"

theorem double_reverse_cut_mod32_carry_projection:
  fixes z w :: "'a::comm_ring_1"
  assumes admitted: "double_reverse_decimal_word source"
      and characteristic: "(32::'a)=0"
      and inverse_root: "z*w=1"
  shows "double_reverse_cut_carry_polynomial source z =
    decimal_base_z_inverse_kernel w *
      (double_reverse_cut_raw_polynomial source z -
       double_reverse_cut_normalized_polynomial source z -
       (if length source=0 then 0 else
          of_int (double_reverse_cut_carry_coefficient source
            (length source-1)) * z^(length source)))"
proof -
  have columns: "\<And>j. j < length source \<Longrightarrow>
      (of_int (double_reverse_cut_raw_coefficient source j) :: 'a) -
        of_int (double_reverse_cut_normalized_coefficient source j) =
      10 * of_int (double_reverse_cut_carry_coefficient source j) -
        (if j=0 then 0 else
          of_int (double_reverse_cut_carry_coefficient source (j-1)))"
  proof -
    fix j
    assume j: "j < length source"
    have balance:
      "double_reverse_cut_raw_coefficient source j -
          double_reverse_cut_normalized_coefficient source j =
       10 * double_reverse_cut_carry_coefficient source j -
          (if j=0 then 0 else
            double_reverse_cut_carry_coefficient source (j-1))"
      by (rule double_reverse_cut_columns_normalize[OF admitted j])
    have lifted:
      "(of_int (double_reverse_cut_raw_coefficient source j -
          double_reverse_cut_normalized_coefficient source j) :: 'a) =
        of_int (10 * double_reverse_cut_carry_coefficient source j -
          (if j=0 then 0 else double_reverse_cut_carry_coefficient source (j-1)))"
      by (rule arg_cong[OF balance])
    show "(of_int (double_reverse_cut_raw_coefficient source j) :: 'a) -
          of_int (double_reverse_cut_normalized_coefficient source j) =
       10 * of_int (double_reverse_cut_carry_coefficient source j) -
          (if j=0 then 0 else
            of_int (double_reverse_cut_carry_coefficient source (j-1)))"
      using lifted by (simp add: of_int_diff of_int_mult)
  qed
  have reconstruction:
    "(\<Sum>j<length source.
        of_int (double_reverse_cut_carry_coefficient source j) * z^j) =
      decimal_base_z_inverse_kernel w *
        ((\<Sum>j<length source.
            of_int (double_reverse_cut_raw_coefficient source j) * z^j) -
         (\<Sum>j<length source.
            of_int (double_reverse_cut_normalized_coefficient source j) * z^j) -
         (if length source=0 then 0 else
            of_int (double_reverse_cut_carry_coefficient source
              (length source-1)) * z^(length source)))"
    by (rule decimal_normalization_mod32_reconstruct_cut
        [OF characteristic inverse_root columns])
  show ?thesis
    using reconstruction
    by (simp add: double_reverse_cut_carry_polynomial_def
        double_reverse_cut_raw_polynomial_def
        double_reverse_cut_normalized_polynomial_def
        double_reverse_cut_polynomial_def)
qed

theorem double_reverse_cut_integer_carry_projection:
  assumes admitted: "double_reverse_decimal_word source"
  shows "(\<Sum>j<length source.
      int (double_reverse_cut_output source j) * (10::int)^j) +
      (if length source=0 then 0 else
        int (double_reverse_cut_carry source (length source-1)) *
          10^(length source)) =
    2 * (\<Sum>j<length source. int (source ! j) * 10^j)"
proof -
  have columns: "\<And>j. j < length source \<Longrightarrow>
      int (2 * (source ! j)) - int (double_reverse_cut_output source j) =
        10 * int (double_reverse_cut_carry source j) -
          (if j=0 then 0 else int (double_reverse_cut_carry source (j-1)))"
    using double_reverse_cut_column_balance[OF admitted]
    by (simp add: double_reverse_cut_normalized_coefficient_def
        double_reverse_cut_carry_coefficient_def)
  note cut = decimal_normalization_finite_cut
    [where raw="\<lambda>j. int (2 * (source ! j))"
      and normalized="\<lambda>j. int (double_reverse_cut_output source j)"
      and carry="\<lambda>j. int (double_reverse_cut_carry source j)"
      and width="length source" and z="(10::int)"]
  have equation:
    "(\<Sum>j<length source.
        (int (2 * (source ! j)) - int (double_reverse_cut_output source j)) *
          (10::int)^j) =
      (10-(10::int)) *
          (\<Sum>j<length source.
            int (double_reverse_cut_carry source j) * (10::int)^j) +
        (if length source=0 then 0 else
          int (double_reverse_cut_carry source (length source-1)) *
            10^(length source))"
    by (rule cut[OF columns])
  have raw_sum:
    "(\<Sum>j<length source. int (2 * (source ! j)) * (10::int)^j) =
      2 * (\<Sum>j<length source. int (source ! j) * 10^j)"
    by (simp add: sum_distrib_left algebra_simps)
  show ?thesis
    using equation raw_sum
    by (simp add: sum_subtractf algebra_simps)
qed

text \<open>The two equations above describe one physical \(2R_w\) step when
the input list is supplied in the low-to-high scan order of the reversed
source. For the runtime's most-significant-first source list, this scan order
is the source list itself, not its reversal.
The carry coefficient is source-selected at each position.  Modulo 32 only
the projected carry polynomial is recovered; it is not a certificate for a
full tape or for the next source word.\<close>

ML \<open>
  val checked = @{thms double_reverse_cut_column_balance
    double_reverse_cut_columns_normalize
    double_reverse_cut_mod32_carry_projection
    double_reverse_cut_integer_carry_projection};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse carry-cut refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped double-reverse carry-cut proof" else ();
\<close>

end
