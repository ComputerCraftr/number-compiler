theory Comma_Phase_Scope
  imports Comma_Sparse_Core.Comma_Sparse_Temporal_Composition
    Shared_S_Arithmetic.CRT_Predicate
begin

unbundle bit_operations_syntax

text \<open>
A phase scope is a single residue class inside the 924-position clock.  The
period and residue describe an occurrence guard, not a source-action identity.
The corresponding 924-bit mask is only a finite output encoding.  A meet is accepted from a supplied CRT witness
only after the kernel checks its lcm and residue equations.
\<close>

definition comma_phase_scope_admitted :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_phase_scope_admitted period residue \<longleftrightarrow>
    0 < period \<and> period \<le> 924 \<and> period dvd 924 \<and> residue < period"

lemma comma_phase_scope_class_bit:
  "bit (comma_phase_class period 0 residue) r =
    (r < 924 \<and> r mod period = residue)"
  by (simp add: comma_phase_class_def comma_phase_mask_bit)

lemma comma_phase_scope_output_admitted:
  assumes left: "comma_phase_scope_admitted p a"
    and right: "comma_phase_scope_admitted q b"
    and modulus: "l = lcm p q"
    and residue: "c < l"
  shows "comma_phase_scope_admitted l c"
proof -
  have p_divides: "p dvd 924" and q_divides: "q dvd 924"
    using left right by (auto simp: comma_phase_scope_admitted_def)
  have lcm_divides: "lcm p q dvd 924"
    by (rule lcm_least[OF p_divides q_divides])
  have p_positive: "0 < p" and q_positive: "0 < q"
    using left right by (auto simp: comma_phase_scope_admitted_def)
  have lcm_positive: "0 < l"
    using modulus p_positive q_positive by (simp add: lcm_pos_nat)
  have lcm_bound: "l \<le> 924"
    using modulus lcm_divides by (auto intro: dvd_imp_le)
  show ?thesis
    using lcm_positive lcm_bound lcm_divides modulus residue
    by (simp add: comma_phase_scope_admitted_def)
qed

lemma comma_phase_scope_nonzero:
  assumes admitted: "comma_phase_scope_admitted period residue"
  shows "comma_phase_class period 0 residue \<noteq> 0"
proof
  assume zero: "comma_phase_class period 0 residue = 0"
  have in_range: "residue < 924"
    using admitted by (auto simp: comma_phase_scope_admitted_def)
  have set_bit: "bit (comma_phase_class period 0 residue) residue"
    using in_range admitted
    by (simp add: comma_phase_scope_class_bit comma_phase_scope_admitted_def)
  from set_bit zero show False by simp
qed

lemma comma_phase_scope_bounded:
  shows "take_bit 924 (comma_phase_class period 0 residue) =
    comma_phase_class period 0 residue"
  by (rule bit_eqI)
    (auto simp: bit_take_bit_iff comma_phase_scope_class_bit)

lemma comma_phase_scope_meet:
  assumes left: "comma_phase_scope_admitted p a"
    and right: "comma_phase_scope_admitted q b"
    and modulus: "l = lcm p q"
    and witness_bound: "c < l"
    and witness_left: "c mod p = a"
    and witness_right: "c mod q = b"
  shows "comma_phase_class p 0 a AND comma_phase_class q 0 b =
    comma_phase_class l 0 c"
proof -
  have p_lcm: "p dvd l" and q_lcm: "q dvd l"
    using modulus by simp_all
  have p_positive: "0 < p" and q_positive: "0 < q"
    using left right by (auto simp: comma_phase_scope_admitted_def)
  have same_class:
    "(r mod p = a \<and> r mod q = b) \<longleftrightarrow> r mod l = c"
    for r :: nat
    by (rule residue_predicate_lcm[OF p_positive q_positive modulus
        witness_bound witness_left witness_right])
  show ?thesis
  proof (rule bit_eqI)
    fix r
    show "bit (comma_phase_class p 0 a AND comma_phase_class q 0 b) r =
      bit (comma_phase_class l 0 c) r"
      using same_class[of r]
      by (simp only: bit_and_iff comma_phase_scope_class_bit; blast)
  qed
qed

lemma comma_phase_scope_disjoint:
  assumes left: "comma_phase_scope_admitted p a"
    and right: "comma_phase_scope_admitted q b"
    and incompatible:
      "a mod gcd p q \<noteq> b mod gcd p q"
  shows "comma_phase_class p 0 a AND comma_phase_class q 0 b = 0"
proof -
  have p_positive: "0 < p" and q_positive: "0 < q"
    using left right by (auto simp: comma_phase_scope_admitted_def)
  have residue_classes:
    "{r. r mod p = a} \<inter> {r. r mod q = b} = {}"
    by (rule residue_predicates_gcd_disjoint[OF p_positive q_positive incompatible])
  have disjoint:
    "\<not> (r mod p = a \<and> r mod q = b)" for r :: nat
    using residue_classes by auto
  show ?thesis
  proof (rule bit_eqI)
    fix r
    show "bit (comma_phase_class p 0 a AND comma_phase_class q 0 b) r = bit (0::nat) r"
      using disjoint[of r]
      by (auto simp: bit_and_iff comma_phase_scope_class_bit)
  qed
qed

ML \<open>
  val checked = @{thms comma_phase_scope_class_bit comma_phase_scope_output_admitted
    comma_phase_scope_nonzero
    comma_phase_scope_bounded comma_phase_scope_meet comma_phase_scope_disjoint}
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Phase scope arithmetic depends on an oracle"
\<close>

end
