theory Comma_C1_Boundary_Carry
  imports Comma_C1_Carry_Cylinder
begin

text \<open>The homogeneous N/Z tail occupies only the columns below the
leading boundary. After stripping two digits, its precision is p-2. Thus the
simplified carry-wire formula applies for j<p, not j\<le>p. The top wire must
retain the actual high-prefix residue through comma_carry_wire.\<close>

fun comma_c1_carry_wire_total ::
  "nat \<Rightarrow> comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_carry_wire_total j C H 0 = 0"
| "comma_c1_carry_wire_total j C H (Suc n) =
    comma_c1_carry_wire_total j C H n +
      (if comma_carry_wire j C H n then 1 else 0)"

lemma comma_c1_carry_quotient_suc:
  fixes H K M :: nat
  assumes modulus: "2 \<le> M"
  shows "(H mod M + (K + 1)) div M =
      (H mod M + K) div M +
        (if (H + K + 1) mod M = 0 then 1 else 0)"
proof -
  let ?x = "H mod M + K"
  let ?q = "?x div M"
  let ?r = "?x mod M"
  have decomposition: "?q * M + ?r = ?x"
    by (rule div_mult_mod_eq)
  have positive_modulus: "M > 0" using modulus by arith
  have remainder: "?r < M" by (simp add: positive_modulus)
  have remainder_suc: "?r + 1 \<le> M" using remainder by arith
  have x_suc: "?x + 1 = ?q * M + (?r + 1)"
    using decomposition by arith
  have phase: "(H + K + 1) mod M = (?x + 1) mod M"
    by (simp only: add.assoc; rule mod_add_left_eq[symmetric])
  have phase_suc: "(?x + 1) mod M = (?r + 1) mod M"
  proof -
    have qmod: "(?q * M) mod M = 0"
      by (simp add: mult.commute)
    have "(?x + 1) mod M = (?q * M + (?r + 1)) mod M"
      using x_suc by simp
    also have "... = ((?q * M) mod M + (?r + 1) mod M) mod M"
      by (rule mod_add_eq[symmetric])
    also have "... = (?r + 1) mod M" using qmod by simp
    finally show ?thesis .
  qed
  have phase_zero: "((H + K + 1) mod M = 0) \<longleftrightarrow> ?r + 1 = M"
  proof -
    have remainder_zero: "(?r + 1) mod M = 0 \<longleftrightarrow> ?r + 1 = M"
    proof
      assume zero: "(?r + 1) mod M = 0"
      have not_less: "\<not> ?r + 1 < M"
      proof
        assume less: "?r + 1 < M"
        have "(?r + 1) mod M = ?r + 1"
          using less modulus by simp
        with zero have "?r + 1 = 0" by simp
        then show False by simp
      qed
      show "?r + 1 = M"
        using not_less remainder_suc by arith
    next
      assume equal: "?r + 1 = M"
      then show "(?r + 1) mod M = 0" by simp
    qed
    have "(H + K + 1) mod M = (?r + 1) mod M"
      using phase phase_suc by simp
    then show ?thesis using remainder_zero by simp
  qed
  have quotient_suc: "(?x + 1) div M = ?q + (?r + 1) div M"
    using div_add1_eq[of ?x 1 M] modulus by simp
  have remainder_suc_div:
    "(?r + 1) div M = (if ?r + 1 = M then 1 else 0)"
  proof (cases "?r + 1 = M")
    case True
    then show ?thesis by simp
  next
    case False
    have less: "?r + 1 < M"
      using remainder_suc False by arith
    then show ?thesis by simp
  qed
  show ?thesis
    using quotient_suc remainder_suc_div phase_zero
    by (simp add: add.assoc)
qed

lemma comma_c1_carry_wire_total_exact:
  fixes j :: nat
  assumes wire: "2 \<le> j"
  shows "comma_c1_carry_wire_total j C H n =
    (H mod 10^(j-1) + comma_c1_count C n) div 10^(j-1)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?M = "(10::nat)^(j-1)"
  have modulus: "2 \<le> ?M"
  proof -
    have exponent: "1 \<le> j-1" using wire by arith
    have "2 \<le> (10::nat)^1" by simp
    also have "... \<le> 10^(j-1)"
      by (rule power_increasing) (use exponent in auto)
    finally show ?thesis .
  qed
  have carry:
    "comma_carry_wire j C H n =
      (comma_c1 (comma_c1_iter n C) \<and>
        (H + comma_c1_count C n + 1) mod ?M = 0)"
    using wire by (simp add: comma_carry_wire_def comma_c1_return_def)
  have count:
    "comma_c1_count C (Suc n) = comma_c1_count C n +
      (if comma_c1 (comma_c1_iter n C) then 1 else 0)"
    by simp
  have quotient_step:
    "(H mod ?M + (comma_c1_count C n + 1)) div ?M =
      (H mod ?M + comma_c1_count C n) div ?M +
        (if (H + comma_c1_count C n + 1) mod ?M = 0 then 1 else 0)"
    using comma_c1_carry_quotient_suc
      [where H=H and K="comma_c1_count C n" and M="?M", OF modulus]
    by simp
  show ?case
  proof (cases "comma_c1 (comma_c1_iter n C)")
    case True
    then show ?thesis
      using Suc.IH carry count quotient_step
      by (simp add: comma_c1_carry_wire_total.simps)
  next
    case False
    then show ?thesis
      using Suc.IH carry count
      by (simp add: comma_c1_carry_wire_total.simps)
  qed
qed

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
    comma_c1_carry_wire_total_exact comma_c1_zero_tail_wire comma_c1_nine_tail_wire
    comma_c1_boundary_Z_wire comma_c1_boundary_N_wire})
    then () else error "C1 boundary carry proof depends on an oracle";
\<close>
end
