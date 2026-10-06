theory Comma_C1_Occurrence
  imports Comma_C1_Borrow_Cocycle.Comma_C1_Borrow_Cocycle
    Comma_Arithmetic.Comma_Literal_Path
begin

text \<open>
Concrete occurrence interfaces for the checked C1 return. A C1 state is
attached to a physical integer by its exact high prefix and decoded low
suffix. Fixed-sector paths are asserted only under the source guard. The
crossing lemma records the exact chart rebase at a 9-to-1 decade seam; it
does not construct a native round or a global future selector.
\<close>

definition comma_c1_physical_occurrence ::
  "comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_c1_physical_occurrence C H p k \<longleftrightarrow>
    comma_c1_phase_admitted C \<and>
    k = 100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C) \<and>
    comma_sector (c1_sector C) p k \<and>
    C = comma_c1_phase_of (c1_sector C) (k mod 100)"


definition comma_c1_resector :: "nat \<Rightarrow> comma_c1_phase \<Rightarrow> comma_c1_phase" where
  "comma_c1_resector g C =
    comma_c1_phase_of g (comma_c1_decode (c1_mod4 C) (c1_mod25 C))"


lemma comma_c1_resector_decode:
  "comma_c1_decode
      (c1_mod4 (comma_c1_resector g C))
      (c1_mod25 (comma_c1_resector g C)) =
    comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
proof -
  let ?x = "comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
  have crt: "comma_c1_decode (?x mod 4) (?x mod 25) = ?x mod 100"
    by (rule comma_c1_decode_residue)
  have bound: "?x < 100" by (simp add: comma_c1_decode_def)
  show ?thesis
    unfolding comma_c1_resector_def comma_c1_phase_of_def
    using crt bound by simp
qed


lemma comma_c1_resector_admitted:
  assumes "1 \<le> g" "g \<le> 9"
  shows "comma_c1_phase_admitted (comma_c1_resector g C)"
  using assms
  by (simp add: comma_c1_phase_admitted_def comma_c1_resector_def
      comma_c1_phase_of_def)


lemma comma_c1_occurrence_of_source:
  assumes source: "comma_c1_source_admitted C H p n"
  shows "comma_c1_physical_occurrence C H p
    (100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C))"
proof -
  have phase: "comma_c1_phase_admitted C"
    using source by (simp add: comma_c1_source_admitted_def)
  have sector:
    "comma_sector (c1_sector C) p
      (100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C))"
    using source by (simp add: comma_c1_source_admitted_def)
  have low: "(100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C)) mod 100 =
      comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
    by (simp add: comma_c1_decode_def)
  have phase_of: "C = comma_c1_phase_of (c1_sector C)
      (comma_c1_decode (c1_mod4 C) (c1_mod25 C))"
    using comma_c1_phase_of_decode[OF phase] by simp
  show ?thesis
    unfolding comma_c1_physical_occurrence_def
    using phase sector low phase_of by simp
qed


theorem comma_c1_fixed_sector_occurrence_path:
  assumes source: "comma_c1_source_admitted C H p n"
  shows "comma_literal_path n
      (100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C))
      (100 * (H + c1_count (comma_c1_return C n)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return C n)))
          (c1_mod25 (c1_target (comma_c1_return C n))))"
    and "comma_c1_physical_occurrence
      (c1_target (comma_c1_return C n))
      (H + c1_count (comma_c1_return C n)) p
      (100 * (H + c1_count (comma_c1_return C n)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return C n)))
          (c1_mod25 (c1_target (comma_c1_return C n))))"
proof -
  let ?T = "c1_target (comma_c1_return C n)"
  let ?H = "H + c1_count (comma_c1_return C n)"
  let ?k = "100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
  let ?k' = "100 * ?H + comma_c1_decode (c1_mod4 ?T) (c1_mod25 ?T)"
  have phase: "comma_c1_phase_admitted C"
    using source by (simp add: comma_c1_source_admitted_def)
  have edge: "comma_child (comma_fixed_iter (c1_sector C) j ?k)
      (comma_fixed_iter (c1_sector C) (Suc j) ?k)" if "j < n" for j
    using comma_c1_source_unique_child(1)[OF source that]
    by simp
  have edges: "\<forall>j<n. comma_child (comma_fixed_iter (c1_sector C) j ?k)
      (comma_fixed_iter (c1_sector C) (Suc j) ?k)"
    using edge by blast
  have iter_path: "comma_literal_path n ?k (comma_fixed_iter (c1_sector C) n ?k)"
    using comma_fixed_iter_literal_path[OF edges] by simp
  have physical: "comma_fixed_iter (c1_sector C) n ?k = ?k'"
    using comma_c1_iter_physical[OF phase, where H=H and n=n]
    by (simp add: comma_c1_return_def)
  show "comma_literal_path n ?k ?k'"
    using iter_path physical by simp

  have target_admitted: "comma_c1_phase_admitted ?T"
    using comma_c1_iter_closed[OF phase, of n]
    by (simp add: comma_c1_return_def)
  have target_sector_base:
    "comma_sector (c1_sector C) p ?k'"
    using comma_c1_source_endpoint[OF source]
    by (simp add: comma_c1_return_def)
  have target_sector_eq: "c1_sector ?T = c1_sector C"
    by (simp add: comma_c1_return_def comma_c1_iter_sector)
  have target_sector: "comma_sector (c1_sector ?T) p ?k'"
    using target_sector_base target_sector_eq by simp
  have target_low_bound:
    "comma_c1_decode (c1_mod4 ?T) (c1_mod25 ?T) < 100"
    by (simp add: comma_c1_decode_def)
  have target_suffix:
    "?k' mod 100 = comma_c1_decode (c1_mod4 ?T) (c1_mod25 ?T)"
  proof -
    have multiple: "(100 * ?H) mod 100 = 0"
      by (simp only: mod_mult_self1_is_0)
    have split:
      "(100 * ?H + comma_c1_decode (c1_mod4 ?T) (c1_mod25 ?T)) mod 100 =
        ((100 * ?H) mod 100 +
          comma_c1_decode (c1_mod4 ?T) (c1_mod25 ?T) mod 100) mod 100"
      by (rule mod_add_eq[symmetric])
    show ?thesis
      using split multiple target_low_bound by simp
  qed
  have target_phase:
    "?T = comma_c1_phase_of (c1_sector ?T) (?k' mod 100)"
    using comma_c1_phase_of_decode[OF target_admitted] target_suffix by simp
  show "comma_c1_physical_occurrence ?T ?H p ?k'"
    unfolding comma_c1_physical_occurrence_def
    using target_admitted target_sector target_suffix target_phase
    by simp
qed


theorem comma_c1_fixed_sector_powered_occurrence_path:
  assumes source: "comma_c1_source_admitted C H p n"
  shows "comma_literal_path n
      (100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C))
      (100 * (H + c1_count (comma_c1_powered_return C n)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_powered_return C n)))
          (c1_mod25 (c1_target (comma_c1_powered_return C n))))"
    and "comma_c1_physical_occurrence
      (c1_target (comma_c1_powered_return C n))
      (H + c1_count (comma_c1_powered_return C n)) p
      (100 * (H + c1_count (comma_c1_powered_return C n)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_powered_return C n)))
          (c1_mod25 (c1_target (comma_c1_powered_return C n))))"
proof -
  have phase: "comma_c1_phase_admitted C"
    using source by (simp add: comma_c1_source_admitted_def)
  have powered:
    "comma_c1_powered_return C n = comma_c1_return C n"
    by (rule comma_c1_powered_return_exact[OF phase])
  have fixed_path: "comma_literal_path n
      (100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C))
      (100 * (H + c1_count (comma_c1_return C n)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return C n)))
          (c1_mod25 (c1_target (comma_c1_return C n))))"
    by (rule comma_c1_fixed_sector_occurrence_path(1)[OF source])
  have fixed_occurrence: "comma_c1_physical_occurrence
      (c1_target (comma_c1_return C n))
      (H + c1_count (comma_c1_return C n)) p
      (100 * (H + c1_count (comma_c1_return C n)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return C n)))
          (c1_mod25 (c1_target (comma_c1_return C n))))"
    by (rule comma_c1_fixed_sector_occurrence_path(2)[OF source])
  show "comma_literal_path n
      (100 * H + comma_c1_decode (c1_mod4 C) (c1_mod25 C))
      (100 * (H + c1_count (comma_c1_powered_return C n)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_powered_return C n)))
          (c1_mod25 (c1_target (comma_c1_powered_return C n))))"
    using fixed_path by (simp only: powered)
  show "comma_c1_physical_occurrence
      (c1_target (comma_c1_powered_return C n))
      (H + c1_count (comma_c1_powered_return C n)) p
      (100 * (H + c1_count (comma_c1_powered_return C n)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_powered_return C n)))
          (c1_mod25 (c1_target (comma_c1_powered_return C n))))"
    using fixed_occurrence by (simp only: powered)
qed


definition comma_c1_async_borrow_innovation ::
  "comma_c1_phase \<Rightarrow> comma_c1_phase \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "comma_c1_async_borrow_innovation P Q m n =
    int (c1_count (comma_c1_return Q n)) -
    int (c1_count (comma_c1_return P m)) +
    int (comma_c1_suffix_borrow
      (comma_c1_decode (c1_mod4 P) (c1_mod25 P))
      (comma_c1_decode (c1_mod4 Q) (c1_mod25 Q))) -
    int (comma_c1_suffix_borrow
      (comma_c1_decode (c1_mod4 (c1_target (comma_c1_return P m)))
        (c1_mod25 (c1_target (comma_c1_return P m))))
      (comma_c1_decode (c1_mod4 (c1_target (comma_c1_return Q n)))
        (c1_mod25 (c1_target (comma_c1_return Q n)))))"


lemma comma_c1_borrow_physical_difference:
  fixes HA HB xA xB :: nat
  assumes xA: "xA < 100" and xB: "xB < 100"
  shows "int (100 * HB + xB) - int (100 * HA + xA) =
    100 * (int HB - int HA -
      int (comma_c1_suffix_borrow xA xB)) +
      int (comma_c1_suffix_delta xA xB)"
proof -
  have borrow:
    "xB + 100 * comma_c1_suffix_borrow xA xB =
      xA + comma_c1_suffix_delta xA xB"
    by (rule comma_c1_suffix_delta_borrow[OF xA xB])
  have borrow_int:
    "int xB + 100 * int (comma_c1_suffix_borrow xA xB) =
      int xA + int (comma_c1_suffix_delta xA xB)"
    using arg_cong[where f="\<lambda>z::nat. int z", OF borrow]
    by (simp only: of_nat_add of_nat_mult of_nat_numeral)
  have castB: "int (100 * HB + xB) = 100 * int HB + int xB"
    by (simp add: of_nat_add of_nat_mult)
  have castA: "int (100 * HA + xA) = 100 * int HA + int xA"
    by (simp add: of_nat_add of_nat_mult)
  have normalized:
    "100 * int HB + int xB - (100 * int HA + int xA) =
      100 * (int HB - int HA -
        int (comma_c1_suffix_borrow xA xB)) +
        int (comma_c1_suffix_delta xA xB)"
    using borrow_int by (simp add: algebra_simps; linarith)
  show ?thesis
    using castB castA normalized by simp
qed


theorem comma_c1_async_borrow_endpoint:
  assumes sourceP: "comma_c1_source_admitted P HP pP m"
    and sourceQ: "comma_c1_source_admitted Q HQ pQ n"
  shows "int (HQ + c1_count (comma_c1_return Q n)) -
      int (HP + c1_count (comma_c1_return P m)) -
      int (comma_c1_suffix_borrow
        (comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return P m)))
          (c1_mod25 (c1_target (comma_c1_return P m))))
        (comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return Q n)))
          (c1_mod25 (c1_target (comma_c1_return Q n))))) =
    (int HQ - int HP -
      int (comma_c1_suffix_borrow
        (comma_c1_decode (c1_mod4 P) (c1_mod25 P))
        (comma_c1_decode (c1_mod4 Q) (c1_mod25 Q))) +
      comma_c1_async_borrow_innovation P Q m n)"
    and "comma_c1_physical_occurrence
      (c1_target (comma_c1_return P m))
      (HP + c1_count (comma_c1_return P m)) pP
      (100 * (HP + c1_count (comma_c1_return P m)) + comma_c1_decode
        (c1_mod4 (c1_target (comma_c1_return P m)))
        (c1_mod25 (c1_target (comma_c1_return P m))))"
    and "comma_c1_physical_occurrence
      (c1_target (comma_c1_return Q n))
      (HQ + c1_count (comma_c1_return Q n)) pQ
      (100 * (HQ + c1_count (comma_c1_return Q n)) + comma_c1_decode
        (c1_mod4 (c1_target (comma_c1_return Q n)))
        (c1_mod25 (c1_target (comma_c1_return Q n))))"
    and "int (100 * HQ + comma_c1_decode (c1_mod4 Q) (c1_mod25 Q)) -
      int (100 * HP + comma_c1_decode (c1_mod4 P) (c1_mod25 P)) =
      100 * (int HQ - int HP -
        int (comma_c1_suffix_borrow
          (comma_c1_decode (c1_mod4 P) (c1_mod25 P))
          (comma_c1_decode (c1_mod4 Q) (c1_mod25 Q)))) +
        int (comma_c1_suffix_delta
          (comma_c1_decode (c1_mod4 P) (c1_mod25 P))
          (comma_c1_decode (c1_mod4 Q) (c1_mod25 Q)))"
    and "int (100 * (HQ + c1_count (comma_c1_return Q n)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return Q n)))
          (c1_mod25 (c1_target (comma_c1_return Q n)))) -
      int (100 * (HP + c1_count (comma_c1_return P m)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return P m)))
          (c1_mod25 (c1_target (comma_c1_return P m)))) =
      100 * (int (HQ + c1_count (comma_c1_return Q n)) -
        int (HP + c1_count (comma_c1_return P m)) -
        int (comma_c1_suffix_borrow
          (comma_c1_decode
            (c1_mod4 (c1_target (comma_c1_return P m)))
            (c1_mod25 (c1_target (comma_c1_return P m))))
          (comma_c1_decode
            (c1_mod4 (c1_target (comma_c1_return Q n)))
            (c1_mod25 (c1_target (comma_c1_return Q n)))))) +
      int (comma_c1_suffix_delta
        (comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return P m)))
          (c1_mod25 (c1_target (comma_c1_return P m))))
        (comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return Q n)))
          (c1_mod25 (c1_target (comma_c1_return Q n)))))"
proof -
  have physicalP: "comma_c1_physical_occurrence
      (c1_target (comma_c1_return P m))
      (HP + c1_count (comma_c1_return P m)) pP
      (100 * (HP + c1_count (comma_c1_return P m)) + comma_c1_decode
        (c1_mod4 (c1_target (comma_c1_return P m)))
        (c1_mod25 (c1_target (comma_c1_return P m))))"
    using comma_c1_fixed_sector_occurrence_path(2)[OF sourceP] .
  have physicalQ: "comma_c1_physical_occurrence
      (c1_target (comma_c1_return Q n))
      (HQ + c1_count (comma_c1_return Q n)) pQ
      (100 * (HQ + c1_count (comma_c1_return Q n)) + comma_c1_decode
        (c1_mod4 (c1_target (comma_c1_return Q n)))
        (c1_mod25 (c1_target (comma_c1_return Q n))))"
    using comma_c1_fixed_sector_occurrence_path(2)[OF sourceQ] .
  have innovation:
    "int (HQ + c1_count (comma_c1_return Q n)) -
       int (HP + c1_count (comma_c1_return P m)) -
       int (comma_c1_suffix_borrow
         (comma_c1_decode
           (c1_mod4 (c1_target (comma_c1_return P m)))
           (c1_mod25 (c1_target (comma_c1_return P m))))
         (comma_c1_decode
           (c1_mod4 (c1_target (comma_c1_return Q n)))
           (c1_mod25 (c1_target (comma_c1_return Q n))))) =
     (int HQ - int HP -
       int (comma_c1_suffix_borrow
         (comma_c1_decode (c1_mod4 P) (c1_mod25 P))
         (comma_c1_decode (c1_mod4 Q) (c1_mod25 Q))) +
       comma_c1_async_borrow_innovation P Q m n)"
    unfolding comma_c1_async_borrow_innovation_def
    by arith
  show "int (HQ + c1_count (comma_c1_return Q n)) -
      int (HP + c1_count (comma_c1_return P m)) -
      int (comma_c1_suffix_borrow
        (comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return P m)))
          (c1_mod25 (c1_target (comma_c1_return P m))))
        (comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return Q n)))
          (c1_mod25 (c1_target (comma_c1_return Q n))))) =
    (int HQ - int HP -
      int (comma_c1_suffix_borrow
        (comma_c1_decode (c1_mod4 P) (c1_mod25 P))
        (comma_c1_decode (c1_mod4 Q) (c1_mod25 Q))) +
      comma_c1_async_borrow_innovation P Q m n)"
    by (rule innovation)
  show "comma_c1_physical_occurrence
      (c1_target (comma_c1_return P m))
      (HP + c1_count (comma_c1_return P m)) pP
      (100 * (HP + c1_count (comma_c1_return P m)) + comma_c1_decode
        (c1_mod4 (c1_target (comma_c1_return P m)))
        (c1_mod25 (c1_target (comma_c1_return P m))))"
    by (rule physicalP)
  show "comma_c1_physical_occurrence
      (c1_target (comma_c1_return Q n))
      (HQ + c1_count (comma_c1_return Q n)) pQ
      (100 * (HQ + c1_count (comma_c1_return Q n)) + comma_c1_decode
        (c1_mod4 (c1_target (comma_c1_return Q n)))
        (c1_mod25 (c1_target (comma_c1_return Q n))))"
    by (rule physicalQ)
  show "int (100 * HQ + comma_c1_decode (c1_mod4 Q) (c1_mod25 Q)) -
      int (100 * HP + comma_c1_decode (c1_mod4 P) (c1_mod25 P)) =
      100 * (int HQ - int HP -
        int (comma_c1_suffix_borrow
          (comma_c1_decode (c1_mod4 P) (c1_mod25 P))
          (comma_c1_decode (c1_mod4 Q) (c1_mod25 Q)))) +
        int (comma_c1_suffix_delta
          (comma_c1_decode (c1_mod4 P) (c1_mod25 P))
          (comma_c1_decode (c1_mod4 Q) (c1_mod25 Q)))"
    by (rule comma_c1_borrow_physical_difference)
      (simp add: comma_c1_decode_def)+
  show "int (100 * (HQ + c1_count (comma_c1_return Q n)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return Q n)))
          (c1_mod25 (c1_target (comma_c1_return Q n)))) -
      int (100 * (HP + c1_count (comma_c1_return P m)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return P m)))
          (c1_mod25 (c1_target (comma_c1_return P m)))) =
      100 * (int (HQ + c1_count (comma_c1_return Q n)) -
        int (HP + c1_count (comma_c1_return P m)) -
        int (comma_c1_suffix_borrow
          (comma_c1_decode
            (c1_mod4 (c1_target (comma_c1_return P m)))
            (c1_mod25 (c1_target (comma_c1_return P m))))
          (comma_c1_decode
            (c1_mod4 (c1_target (comma_c1_return Q n)))
            (c1_mod25 (c1_target (comma_c1_return Q n)))))) +
      int (comma_c1_suffix_delta
        (comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return P m)))
          (c1_mod25 (c1_target (comma_c1_return P m))))
        (comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_return Q n)))
          (c1_mod25 (c1_target (comma_c1_return Q n)))))"
    by (rule comma_c1_borrow_physical_difference)
      (simp add: comma_c1_decode_def)+
qed

ML \<open>
  val checked = @{thms comma_c1_resector_decode comma_c1_resector_admitted
    comma_c1_occurrence_of_source comma_c1_fixed_sector_occurrence_path
    comma_c1_fixed_sector_powered_occurrence_path
    comma_c1_async_borrow_endpoint};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "C1 occurrence refinement depends on an oracle";
\<close>
end
