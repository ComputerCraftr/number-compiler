theory Comma_Finite_Period
  imports Comma_Period_Guard Comma_Power_Residue
begin

definition comma_finite_period :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_finite_period f d =
    (let g = gcd f 10;
         L = 10 div g;
         r = d mod g
     in 10 * (L * r + g * L * (L - 1) div 2) + L * f)"

lemma comma_finite_period_1:
  "list_all (\<lambda>d. comma_finite_period 1 d =
    comma_period_displacement 1 d (comma_cycle_length 1)) [0..<10]"
  unfolding comma_finite_period_def comma_cycle_length_def
    comma_period_displacement_def comma_phase_digit_def
  by code_simp

lemma comma_finite_period_2:
  "list_all (\<lambda>d. comma_finite_period 2 d =
    comma_period_displacement 2 d (comma_cycle_length 2)) [0..<10]"
  unfolding comma_finite_period_def comma_cycle_length_def
    comma_period_displacement_def comma_phase_digit_def
  by code_simp

lemma comma_finite_period_3:
  "list_all (\<lambda>d. comma_finite_period 3 d =
    comma_period_displacement 3 d (comma_cycle_length 3)) [0..<10]"
  unfolding comma_finite_period_def comma_cycle_length_def
    comma_period_displacement_def comma_phase_digit_def
  by code_simp

lemma comma_finite_period_4:
  "list_all (\<lambda>d. comma_finite_period 4 d =
    comma_period_displacement 4 d (comma_cycle_length 4)) [0..<10]"
  unfolding comma_finite_period_def comma_cycle_length_def
    comma_period_displacement_def comma_phase_digit_def
  by code_simp

lemma comma_finite_period_5:
  "list_all (\<lambda>d. comma_finite_period 5 d =
    comma_period_displacement 5 d (comma_cycle_length 5)) [0..<10]"
  unfolding comma_finite_period_def comma_cycle_length_def
    comma_period_displacement_def comma_phase_digit_def
  by code_simp

lemma comma_finite_period_6:
  "list_all (\<lambda>d. comma_finite_period 6 d =
    comma_period_displacement 6 d (comma_cycle_length 6)) [0..<10]"
  unfolding comma_finite_period_def comma_cycle_length_def
    comma_period_displacement_def comma_phase_digit_def
  by code_simp

lemma comma_finite_period_7:
  "list_all (\<lambda>d. comma_finite_period 7 d =
    comma_period_displacement 7 d (comma_cycle_length 7)) [0..<10]"
  unfolding comma_finite_period_def comma_cycle_length_def
    comma_period_displacement_def comma_phase_digit_def
  by code_simp

lemma comma_finite_period_8:
  "list_all (\<lambda>d. comma_finite_period 8 d =
    comma_period_displacement 8 d (comma_cycle_length 8)) [0..<10]"
  unfolding comma_finite_period_def comma_cycle_length_def
    comma_period_displacement_def comma_phase_digit_def
  by code_simp

lemma comma_finite_period_9:
  "list_all (\<lambda>d. comma_finite_period 9 d =
    comma_period_displacement 9 d (comma_cycle_length 9)) [0..<10]"
  unfolding comma_finite_period_def comma_cycle_length_def
    comma_period_displacement_def comma_phase_digit_def
  by code_simp

lemma comma_finite_period_catalog:
  "\<forall>f \<in> {1..<10}. \<forall>d \<in> {0..<10}.
    comma_finite_period f d =
      comma_period_displacement f d (comma_cycle_length f)"
proof -
  have cases: "\<And>f::nat. f \<in> {1..<10} \<Longrightarrow>
    f = 1 \<or> f = 2 \<or> f = 3 \<or> f = 4 \<or> f = 5 \<or>
    f = 6 \<or> f = 7 \<or> f = 8 \<or> f = 9"
    by auto
  show ?thesis
  proof (intro ballI)
    fix f :: nat assume f: "f \<in> {1..<10}"
    fix d :: nat assume d: "d \<in> {0..<10}"
    have alternatives: "f = 1 \<or> f = 2 \<or> f = 3 \<or>
      f = 4 \<or> f = 5 \<or> f = 6 \<or> f = 7 \<or>
      f = 8 \<or> f = 9"
      using cases[OF f] .
    show "comma_finite_period f d =
      comma_period_displacement f d (comma_cycle_length f)"
      using alternatives d comma_finite_period_1 comma_finite_period_2
        comma_finite_period_3 comma_finite_period_4
        comma_finite_period_5 comma_finite_period_6
        comma_finite_period_7 comma_finite_period_8
        comma_finite_period_9
      by (auto simp: list_all_iff)
  qed
qed

lemma comma_finite_period_refines:
  assumes "1 \<le> f" "f \<le> 9" "d < 10"
  shows "comma_finite_period f d =
    comma_period_displacement f d (comma_cycle_length f)"
  using comma_finite_period_catalog assms by auto

lemma comma_sector_displacements_eq_finite:
  assumes sector: "1 \<le> f" "f \<le> 9"
  shows "comma_sector_displacements f =
    set (map (comma_finite_period f) [0..<10])"
proof -
  have point: "comma_period_displacement f d (comma_cycle_length f) =
      comma_finite_period f d" if "d \<in> set [0..<10]" for d
    using comma_finite_period_refines[OF sector] that by simp
  have mapped: "map (\<lambda>d. comma_period_displacement f d
      (comma_cycle_length f)) [0..<10] =
      map (comma_finite_period f) [0..<10]"
    using point by (intro map_cong refl) auto
  show ?thesis by (simp add: comma_sector_displacements_def mapped)
qed

lemma comma_sector_displacements_1: "comma_sector_displacements 1 = {460}"
proof -
  have bridge: "comma_sector_displacements 1 =
      set (map (comma_finite_period 1) [0..<10])"
    using comma_sector_displacements_eq_finite[of 1] by simp
  show ?thesis unfolding bridge comma_finite_period_def by code_simp
qed

lemma comma_sector_displacements_2: "comma_sector_displacements 2 = {210,260}"
proof -
  have bridge: "comma_sector_displacements 2 =
      set (map (comma_finite_period 2) [0..<10])"
    using comma_sector_displacements_eq_finite[of 2] by simp
  show ?thesis unfolding bridge comma_finite_period_def by code_simp
qed

lemma comma_sector_displacements_3: "comma_sector_displacements 3 = {480}"
proof -
  have bridge: "comma_sector_displacements 3 =
      set (map (comma_finite_period 3) [0..<10])"
    using comma_sector_displacements_eq_finite[of 3] by simp
  show ?thesis unfolding bridge comma_finite_period_def by code_simp
qed

lemma comma_sector_displacements_4: "comma_sector_displacements 4 = {220,270}"
proof -
  have bridge: "comma_sector_displacements 4 =
      set (map (comma_finite_period 4) [0..<10])"
    using comma_sector_displacements_eq_finite[of 4] by simp
  show ?thesis unfolding bridge comma_finite_period_def by code_simp
qed

lemma comma_sector_displacements_5: "comma_sector_displacements 5 = {60,80,100,120,140}"
proof -
  have bridge: "comma_sector_displacements 5 =
      set (map (comma_finite_period 5) [0..<10])"
    using comma_sector_displacements_eq_finite[of 5] by simp
  show ?thesis unfolding bridge comma_finite_period_def by code_simp
qed

lemma comma_sector_displacements_6: "comma_sector_displacements 6 = {230,280}"
proof -
  have bridge: "comma_sector_displacements 6 =
      set (map (comma_finite_period 6) [0..<10])"
    using comma_sector_displacements_eq_finite[of 6] by simp
  show ?thesis unfolding bridge comma_finite_period_def by code_simp
qed

lemma comma_sector_displacements_7: "comma_sector_displacements 7 = {520}"
proof -
  have bridge: "comma_sector_displacements 7 =
      set (map (comma_finite_period 7) [0..<10])"
    using comma_sector_displacements_eq_finite[of 7] by simp
  show ?thesis unfolding bridge comma_finite_period_def by code_simp
qed

lemma comma_sector_displacements_8: "comma_sector_displacements 8 = {240,290}"
proof -
  have bridge: "comma_sector_displacements 8 =
      set (map (comma_finite_period 8) [0..<10])"
    using comma_sector_displacements_eq_finite[of 8] by simp
  show ?thesis unfolding bridge comma_finite_period_def by code_simp
qed

lemma comma_sector_displacements_9: "comma_sector_displacements 9 = {540}"
proof -
  have bridge: "comma_sector_displacements 9 =
      set (map (comma_finite_period 9) [0..<10])"
    using comma_sector_displacements_eq_finite[of 9] by simp
  show ?thesis unfolding bridge comma_finite_period_def by code_simp
qed

lemma comma_cycle_displacement_catalog:
  "set (concat (map (\<lambda>f. map
      (\<lambda>d. comma_period_displacement f d (comma_cycle_length f))
      [(0::nat)..<10]) [(1::nat)..<10])) =
    comma_cycle_displacements"
proof -
  have source: "[(1::nat)..<10] = [1,2,3,4,5,6,7,8,9]"
    by code_simp
  have lifted: "\<And>f. (\<lambda>d. comma_period_displacement f d
      (comma_cycle_length f)) ` {0..<10} = comma_sector_displacements f"
    by (simp add: comma_sector_displacements_def)
  have first: "comma_sector_displacements (Suc 0) = {460}"
    using comma_sector_displacements_1 by simp
  show ?thesis
    unfolding source comma_cycle_displacements_def
    by (auto simp: lifted first
      comma_sector_displacements_2 comma_sector_displacements_3
      comma_sector_displacements_4 comma_sector_displacements_5
      comma_sector_displacements_6 comma_sector_displacements_7
      comma_sector_displacements_8 comma_sector_displacements_9)
qed

lemma comma_finite_period_in_catalog:
  "\<forall>f \<in> {1..<10}. \<forall>d \<in> {0..<10}.
    comma_finite_period f d \<in> comma_cycle_displacements"
proof (intro ballI)
  fix f :: nat assume f: "f \<in> {1..<10}"
  fix d :: nat assume d: "d \<in> {0..<10}"
  have period: "comma_finite_period f d =
    comma_period_displacement f d (comma_cycle_length f)"
    using comma_finite_period_catalog f d by blast
  have sector_member: "f \<in> set [(1::nat)..<10]"
    using f by simp
  have digit_member: "d \<in> set [(0::nat)..<10]"
    using d by simp
  have inner_member:
    "comma_period_displacement f d (comma_cycle_length f) \<in>
      set (map (\<lambda>y. comma_period_displacement f y
        (comma_cycle_length f)) [(0::nat)..<10])"
    using digit_member by auto
  let ?catalog = "set (concat (map
    (\<lambda>x. map (\<lambda>y. comma_period_displacement x y
      (comma_cycle_length x)) [(0::nat)..<10])
    [(1::nat)..<10]))"
  have member: "comma_period_displacement f d (comma_cycle_length f)
    \<in> ?catalog"
    using sector_member inner_member by auto
  have catalog: "?catalog = comma_cycle_displacements"
    by (rule comma_cycle_displacement_catalog)
  have in_catalog: "comma_period_displacement f d
    (comma_cycle_length f) \<in> comma_cycle_displacements"
    using member by (simp only: catalog)
  show "comma_finite_period f d \<in> comma_cycle_displacements"
    using period in_catalog by simp
qed

lemmas comma_power_period_924_repeated = comma_short_period_924_repeated
lemmas comma_residue_exponent_decomposition = comma_short_representative_decomposition

lemma comma_residue_power_refines:
  assumes period: "P \<in> comma_cycle_displacements"
    and exponent: "5 \<le> p"
  shows "10 ^ p mod P =
    mod_exp (10::nat) (comma_residue_exponent (p mod 924)) P"
  using comma_short_representative_correct[OF period exponent]
  by (simp only: mod_exp_def)

definition comma_finite_guard_extra :: "nat \<Rightarrow> nat" where
  "comma_finite_guard_extra f = (if f < 9 then 1 else 0)"

definition comma_finite_headroom ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_finite_headroom f residue delta offset =
    (let P = comma_finite_period f (offset mod 10);
         e = comma_finite_guard_extra f;
         r = (residue + delta) mod 924;
         power = comma_power_residue P r
     in 1 + e + nat ((int power - int offset - int (1 + e)) mod int P))"

lemma comma_finite_headroom_refines:
  fixes f p delta offset :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
  defines "P \<equiv> comma_finite_period f (offset mod 10)"
    and "e \<equiv> comma_finite_guard_extra f"
  shows "comma_finite_headroom f (p mod 924) delta offset =
    1 + e + nat ((int (10 ^ (p + delta) mod P) - int offset -
      int (1 + e)) mod int P)"
proof -
  have period: "P \<in> comma_cycle_displacements"
    using comma_finite_period_in_catalog sector
    unfolding P_def by auto
  have lower: "5 \<le> p + delta"
    using exponent by simp
  have residue: "(p mod 924 + delta) mod 924 = (p + delta) mod 924"
    by (simp add: mod_simps)
  have power: "comma_power_residue P
      ((p mod 924 + delta) mod 924) = 10 ^ (p + delta) mod P"
    using comma_power_residue_correct[OF period lower] residue
    by simp
  show ?thesis
    unfolding comma_finite_headroom_def P_def e_def
    using power[unfolded P_def] by (simp add: Let_def)
qed


ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_finite_period_catalog comma_finite_period_refines
      comma_finite_period_in_catalog comma_sector_displacements_eq_finite
      comma_sector_displacements_1 comma_sector_displacements_2
      comma_sector_displacements_3 comma_sector_displacements_4
      comma_sector_displacements_5 comma_sector_displacements_6
      comma_sector_displacements_7 comma_sector_displacements_8
      comma_sector_displacements_9 comma_cycle_displacement_catalog
      comma_power_period_924_repeated
      comma_residue_exponent_decomposition comma_residue_power_refines
      comma_finite_headroom_refines})
    then () else error "Comma finite-period proof depends on an oracle";
\<close>

end
