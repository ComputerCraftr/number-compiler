theory Comma_C1_Boundary_Carry
  imports Comma_C1_Carry_Cylinder
begin

text \<open>The homogeneous N/Z tail occupies only the columns below the
leading boundary. After stripping two digits, its precision is p-2. Thus the
simplified carry-wire formula applies for j<p, not j\<le>p. The top wire must
retain the actual high-prefix residue through comma_carry_wire.\<close>

lemma comma_c1_zero_tail_wire:
  assumes wire: "2 \<le> j" and zero: "H mod 10^(j-1) = 0"
  shows "comma_carry_wire j C H n =
    (comma_c1 (c1_target (comma_c1_return C n)) \<and>
      (c1_count (comma_c1_return C n)+1) mod 10^(j-1) = 0)"
proof -
  let ?N = "c1_count (comma_c1_return C n)"
  let ?M = "10^(j-1)"
  have shifted: "(H+(?N+1)) mod ?M = (0+(?N+1)) mod ?M"
    by (rule mod_add_cong) (use zero in simp, rule refl)
  have j0: "j \<noteq> 0" and j1: "j \<noteq> 1" using wire by arith+
  show ?thesis using shifted j0 j1
    by (simp add: comma_carry_wire_def add.assoc)
qed

lemma comma_c1_nine_tail_wire:
  assumes wire: "2 \<le> j" and nines: "(H+1) mod 10^(j-1) = 0"
  shows "comma_carry_wire j C H n =
    (comma_c1 (c1_target (comma_c1_return C n)) \<and>
      c1_count (comma_c1_return C n) mod 10^(j-1) = 0)"
proof -
  let ?N = "c1_count (comma_c1_return C n)"
  let ?M = "10^(j-1)"
  have shifted: "(H+1+?N) mod ?M = (0+?N) mod ?M"
    by (rule mod_add_cong) (use nines in simp, rule refl)
  have j0: "j \<noteq> 0" and j1: "j \<noteq> 1" using wire by arith+
  show ?thesis using shifted j0 j1
    by (simp add: comma_carry_wire_def add.assoc add.commute add.left_commute)
qed

lemma comma_c1_boundary_high_zero:
  fixes a p j :: nat
  assumes "2 \<le> j" "j < p"
  shows "(a * 10^(p-2)) mod 10^(j-1) = 0"
proof -
  have exponents: "j-1 \<le> p-2" using assms by arith
  have power: "(10::nat)^(j-1) dvd 10^(p-2)"
    by (rule le_imp_power_dvd[OF exponents])
  have multiple: "10^(j-1) dvd a * 10^(p-2)"
    by (rule dvd_mult[OF power])
  show ?thesis by (rule dvd_imp_mod_0[OF multiple])
qed

lemma comma_c1_boundary_Z_wire:
  assumes "2 \<le> j" "j < p"
  shows "comma_carry_wire j C (a * 10^(p-2)) n =
    (comma_c1 (c1_target (comma_c1_return C n)) \<and>
      (c1_count (comma_c1_return C n)+1) mod 10^(j-1) = 0)"
  by (rule comma_c1_zero_tail_wire[OF assms(1)
      comma_c1_boundary_high_zero[OF assms]])

lemma comma_c1_boundary_N_wire:
  assumes positive: "0<a" and wire: "2 \<le> j" "j < p"
  shows "comma_carry_wire j C (a * 10^(p-2)-1) n =
    (comma_c1 (c1_target (comma_c1_return C n)) \<and>
      c1_count (comma_c1_return C n) mod 10^(j-1) = 0)"
proof -
  have high: "0 < a * 10^(p-2)" using positive by simp
  have restored: "a * 10^(p-2)-1+1 = a * 10^(p-2)"
    using high by arith
  have nines: "(a * 10^(p-2)-1+1) mod 10^(j-1) = 0"
    by (simp only: restored comma_c1_boundary_high_zero[OF wire])
  show ?thesis by (rule comma_c1_nine_tail_wire[OF wire(1) nines])
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms
    comma_c1_zero_tail_wire comma_c1_nine_tail_wire
    comma_c1_boundary_Z_wire comma_c1_boundary_N_wire})
    then () else error "C1 boundary carry proof depends on an oracle";
\<close>
end
