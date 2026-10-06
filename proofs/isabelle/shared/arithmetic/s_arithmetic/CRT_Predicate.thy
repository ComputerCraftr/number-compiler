theory CRT_Predicate
  imports "HOL-Number_Theory.Cong"
begin

text \<open>
Clock scopes are predicates on residues, so their composition belongs in the
shared arithmetic layer rather than in a bit-mask representation.  These
lemmas state the exact generalized-CRT law for compatible residue predicates.
\<close>

lemma residue_predicate_lcm:
  fixes x p q l a b c :: nat
  assumes p_positive: "0 < p"
    and q_positive: "0 < q"
    and lcm_value: "l = lcm p q"
    and canonical: "c < l"
    and left_witness: "c mod p = a"
    and right_witness: "c mod q = b"
  shows "(x mod p = a \<and> x mod q = b) \<longleftrightarrow> x mod l = c"
proof
  assume residues: "x mod p = a \<and> x mod q = b"
  have p_residue: "x mod p = a" and q_residue: "x mod q = b"
    using residues by auto
  have p_cong: "[x = c] (mod p)"
  proof -
    have "x mod p = c mod p"
      using p_residue left_witness by simp
    then show ?thesis by (simp add: cong_def)
  qed
  have q_cong: "[x = c] (mod q)"
  proof -
    have "x mod q = c mod q"
      using q_residue right_witness by simp
    then show ?thesis by (simp add: cong_def)
  qed
  have combined_lcm: "[x = c] (mod lcm p q)"
    by (rule cong_cong_lcm_nat[OF p_cong q_cong])
  have combined: "[x = c] (mod l)"
    using combined_lcm lcm_value by simp
  show "x mod l = c"
    using combined canonical by (simp add: cong_def)
next
  assume residue: "x mod l = c"
  have p_lcm: "p dvd l" and q_lcm: "q dvd l"
    using lcm_value by simp_all
  have p_reduce: "(x mod l) mod p = x mod p"
    by (rule mod_mod_cancel[OF p_lcm])
  have q_reduce: "(x mod l) mod q = x mod q"
    by (rule mod_mod_cancel[OF q_lcm])
  have p_result: "x mod p = a"
  proof -
    have "x mod p = (x mod l) mod p"
      by (rule p_reduce[symmetric])
    also have "... = c mod p"
      using residue by simp
    also have "... = a"
      by (rule left_witness)
    finally show ?thesis .
  qed
  have q_result: "x mod q = b"
  proof -
    have "x mod q = (x mod l) mod q"
      by (rule q_reduce[symmetric])
    also have "... = c mod q"
      using residue by simp
    also have "... = b"
      by (rule right_witness)
    finally show ?thesis .
  qed
  show "x mod p = a \<and> x mod q = b"
    using p_result q_result by blast
qed

lemma residue_predicates_lcm_intersection:
  fixes p q l a b c :: nat
  assumes p_positive: "0 < p"
    and q_positive: "0 < q"
    and lcm_value: "l = lcm p q"
    and canonical: "c < l"
    and left_witness: "c mod p = a"
    and right_witness: "c mod q = b"
  shows "{x. x mod p = a} \<inter> {x. x mod q = b} = {x. x mod l = c}"
  using residue_predicate_lcm[OF p_positive q_positive lcm_value canonical
      left_witness right_witness]
  by auto

lemma residue_predicates_gcd_disjoint:
  fixes p q a b :: nat
  assumes p_positive: "0 < p"
    and q_positive: "0 < q"
    and incompatible: "a mod gcd p q \<noteq> b mod gcd p q"
  shows "{x. x mod p = a} \<inter> {x. x mod q = b} = {}"
proof (rule set_eqI)
  fix x
  show "x \<in> {x. x mod p = a} \<inter> {x. x mod q = b} \<longleftrightarrow> x \<in> {}"
  proof
    assume member: "x \<in> {x. x mod p = a} \<inter> {x. x mod q = b}"
    have residues: "x mod p = a" "x mod q = b"
      using member by auto
    have gcd_p: "gcd p q dvd p" and gcd_q: "gcd p q dvd q"
      by simp_all
    have a_value: "a mod gcd p q = x mod gcd p q"
    proof -
      have "a = x mod p"
        using residues(1) by simp
      then show ?thesis
        by (metis mod_mod_cancel[OF gcd_p])
    qed
    have b_value: "b mod gcd p q = x mod gcd p q"
    proof -
      have "b = x mod q"
        using residues(2) by simp
      then show ?thesis
        by (metis mod_mod_cancel[OF gcd_q])
    qed
    show "x \<in> {}"
      using incompatible a_value b_value by simp
  next
    assume "x \<in> {}"
    then show "x \<in> {x. x mod p = a} \<inter> {x. x mod q = b}"
      by simp
  qed
qed

ML \<open>
  val checked = @{thms residue_predicate_lcm
    residue_predicates_lcm_intersection residue_predicates_gcd_disjoint}
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Generic CRT predicate arithmetic depends on an oracle"
\<close>

end
