theory Comma_C1_Normalization_Morphism
  imports Comma_C1_Source_Coefficients
    Shared_Carry_Dynamics.Decimal_Normalization_Morphism
begin

text \<open>The phase-only coefficient defect is derived from the admitted finite
C1 action for arbitrary high prefix H and symbolic duration n. It is independent
of literal path admission. Its finite spatial projection retains the outgoing
cut carry. The source-admitted theorem below is the separate physical-path
refinement. No temporal word or width-sized digit list is constructed.\<close>

theorem comma_c1_phase_mod32_carry_operator:
  fixes z w :: "'a::comm_ring_1"
  assumes phase: "comma_c1_phase_admitted C"
    and characteristic: "(32::'a)=0" and inverse_root: "z*w=1"
  shows "(\<Sum>j<width. of_nat (comma_c1_source_carry_coefficient j C H n)*z^j) =
    decimal_base_z_inverse_kernel w *
      ((\<Sum>j<width. of_nat (comma_c1_source_raw_coefficient j C H n)*z^j) -
       (\<Sum>j<width. of_nat (comma_c1_source_normalized_coefficient j C H n)*z^j) -
       (if width=0 then 0 else
         of_nat (comma_c1_source_carry_coefficient (width-1) C H n)*z^width))"
proof -
  have columns:
    "(of_nat (comma_c1_source_raw_coefficient j C H n)::'a) -
       of_nat (comma_c1_source_normalized_coefficient j C H n) =
      10 * of_nat (comma_c1_source_carry_coefficient j C H n) -
       (if j=0 then 0 else of_nat (comma_c1_source_carry_coefficient (j-1) C H n))"
    for j
  proof -
    have coefficient:
      "int (comma_c1_source_raw_coefficient j C H n) -
         int (comma_c1_source_normalized_coefficient j C H n) =
        10 * int (comma_c1_source_carry_coefficient j C H n) -
         int (comma_c1_source_prior_carry_coefficient j C H n)"
      by (rule comma_c1_phase_source_base_z_coefficient_defect[OF phase])
    note transported = arg_cong[OF coefficient, of "\<lambda>x::int. of_int x::'a"]
    show ?thesis using transported
      by (simp add: comma_c1_source_prior_carry_coefficient_def)
  qed
  show ?thesis
    by (rule decimal_normalization_mod32_reconstruct_cut
        [OF characteristic inverse_root]) (rule columns)
qed

theorem comma_c1_source_mod32_carry_morphism:
  fixes z w :: "'a::comm_ring_1"
  assumes admitted: "comma_c1_source_admitted C H p n"
    and characteristic: "(32::'a)=0" and inverse_root: "z*w=1"
  shows "(\<Sum>j<width. of_nat (comma_c1_source_carry_coefficient j C H n)*z^j) =
    decimal_base_z_inverse_kernel w *
      ((\<Sum>j<width. of_nat (comma_c1_source_raw_coefficient j C H n)*z^j) -
       (\<Sum>j<width. of_nat (comma_c1_source_normalized_coefficient j C H n)*z^j) -
       (if width=0 then 0 else
         of_nat (comma_c1_source_carry_coefficient (width-1) C H n)*z^width))"
proof -
  have phase: "comma_c1_phase_admitted C"
    using admitted by (simp add: comma_c1_source_admitted_def)
  show ?thesis
    by (rule comma_c1_phase_mod32_carry_operator
        [OF phase characteristic inverse_root])
qed

ML \<open>
  val checked = @{thms comma_c1_phase_mod32_carry_operator
    comma_c1_source_mod32_carry_morphism};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "C1 normalization morphism depends on an oracle";
\<close>

end
