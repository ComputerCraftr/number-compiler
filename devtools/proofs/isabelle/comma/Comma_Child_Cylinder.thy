theory Comma_Child_Cylinder
  imports Main
begin

text \<open>The literal decimal rule is kept separate from any assertion that a
particular child has an infinite continuation. A sector carries its decimal
scale explicitly, so a phase calculation cannot silently cross a boundary.\<close>

definition comma_sector :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_sector e p k \<longleftrightarrow>
    1 \<le> e \<and> e \<le> 9 \<and>
    e * 10 ^ p \<le> k \<and> k < (e + 1) * 10 ^ p"

definition comma_child :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_child k k' \<longleftrightarrow>
    (\<exists>e p. comma_sector e p k' \<and>
      k' = k + 10 * (k mod 10) + e)"

lemma comma_startup:
  "comma_child 20 22" "comma_child 22 46" "comma_child 46 107"
proof -
  show "comma_child 20 22"
    unfolding comma_child_def
    by (rule exI[where x=2], rule exI[where x=1],
        simp add: comma_sector_def)
  show "comma_child 22 46"
    unfolding comma_child_def
    by (rule exI[where x=4], rule exI[where x=1],
        simp add: comma_sector_def)
  show "comma_child 46 107"
    unfolding comma_child_def
    by (rule exI[where x=1], rule exI[where x=2],
        simp add: comma_sector_def)
qed

definition comma_phase_step :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_phase_step e m d = 10 * m + d + 10 * d + e"

lemma comma_phase_carry:
  assumes "d < 10"
  shows "comma_phase_step e m d =
      10 * (m + d + (d + e) div 10) + (d + e) mod 10"
  using assms by (simp add: comma_phase_step_def div_mult_mod_eq algebra_simps)

lemma comma_phase_residue:
  "comma_phase_step e m d mod 10 = (d + e) mod 10"
proof -
  have expanded: "comma_phase_step e m d = 10 * (m + d) + (d + e)"
    by (simp add: comma_phase_step_def algebra_simps)
  have reduced: "(10 * (m + d) + (d + e)) mod 10 = (d + e) mod 10"
    by (rule mod_mult_self4)
  show ?thesis using expanded reduced by metis
qed

lemma comma_phase_quotient:
  assumes "d < 10"
  shows "comma_phase_step e m d div 10 =
    m + d + (d + e) div 10"
  using assms by (simp add: comma_phase_carry)

fun comma_fixed_iter :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_fixed_iter e 0 k = k"
| "comma_fixed_iter e (Suc n) k =
    comma_fixed_iter e n k + 10 * (comma_fixed_iter e n k mod 10) + e"

lemma comma_fixed_iter_phase:
  "comma_fixed_iter e n k mod 10 = (k mod 10 + n * e) mod 10"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?v = "comma_fixed_iter e n k"
  have expanded: "comma_fixed_iter e (Suc n) k = (?v + e) + 10 * (?v mod 10)"
    by (simp add: algebra_simps)
  have reduced: "((?v + e) + 10 * (?v mod 10)) mod 10 = (?v + e) mod 10"
    by (rule mod_mult_self2)
  have step: "comma_fixed_iter e (Suc n) k mod 10 = (?v + e) mod 10"
    using expanded reduced by metis
  have lift: "(?v mod 10 + e) mod 10 =
      ((k mod 10 + n * e) mod 10 + e) mod 10"
    using Suc.IH by metis
  have "(?v + e) mod 10 = (?v mod 10 + e) mod 10"
    by (rule mod_add_left_eq[symmetric])
  also have "... = ((k mod 10 + n * e) mod 10 + e) mod 10"
    by (rule lift)
  also have "... = (k mod 10 + n * e + e) mod 10"
    by (rule mod_add_left_eq)
  also have "... = (k mod 10 + Suc n * e) mod 10"
    by (simp add: algebra_simps)
  finally show ?case using step by metis
qed

definition comma_period_displacement :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_period_displacement e d len =
    (\<Sum>j<len. 10 * ((d + j * e) mod 10) + e)"

lemma comma_fixed_iter_displacement:
  "comma_fixed_iter e n k =
    k + comma_period_displacement e (k mod 10) n"
proof (induction n)
  case 0
  then show ?case by (simp add: comma_period_displacement_def)
next
  case (Suc n)
  have residue: "comma_fixed_iter e n k mod 10 =
      (k mod 10 + n * e) mod 10"
    by (rule comma_fixed_iter_phase)
  have step: "comma_fixed_iter e (Suc n) k =
      comma_fixed_iter e n k + 10 * (comma_fixed_iter e n k mod 10) + e"
    by simp
  have sum: "comma_period_displacement e (k mod 10) (Suc n) =
      comma_period_displacement e (k mod 10) n +
      10 * ((k mod 10 + n * e) mod 10) + e"
    by (simp add: comma_period_displacement_def sum.lessThan_Suc)
  show ?case using Suc.IH residue step sum by presburger
qed

lemma comma_period_phase_close:
  assumes "10 dvd len * e"
  shows "comma_fixed_iter e len k mod 10 = k mod 10"
proof -
  have zero: "len * e mod 10 = 0" using assms by simp
  have "(k mod 10 + len * e) mod 10 =
      (k mod 10 + len * e mod 10) mod 10"
    by (rule mod_add_right_eq[symmetric])
  also have "... = k mod 10" using zero by simp
  finally show ?thesis using comma_fixed_iter_phase by metis
qed

lemma comma_guarded_interior_child:
  assumes source: "comma_sector f p k"
    and strict: "k + 99 < (f + 1) * 10 ^ p"
    and result: "k' = k + 10 * (k mod 10) + f"
  shows "comma_sector f p k'"
proof -
  have digit: "k mod 10 \<le> 9" by simp
  have fbound: "f \<le> 9" using source
    by (simp add: comma_sector_def)
  have bound: "k' \<le> k + 99" using result digit fbound by linarith
  show ?thesis
    using source strict bound result
    by (auto simp: comma_sector_def)
qed

lemma comma_guarded_fixed_iter_sector:
  assumes source: "comma_sector f p k"
    and guard: "comma_fixed_iter f n k + 99 < (f + 1) * 10 ^ p"
  shows "comma_sector f p (comma_fixed_iter f n k)"
  using guard
proof (induction n)
  case 0
  then show ?case using source by simp
next
  case (Suc n)
  have step: "comma_fixed_iter f (Suc n) k =
      comma_fixed_iter f n k + 10 * (comma_fixed_iter f n k mod 10) + f"
    by simp
  have earlier: "comma_fixed_iter f n k + 99 < (f + 1) * 10 ^ p"
    using Suc.prems step by linarith
  have admitted: "comma_sector f p (comma_fixed_iter f n k)"
    using Suc.IH[OF earlier] .
  show ?case
    using comma_guarded_interior_child[OF admitted earlier step] .
qed

lemma comma_guarded_fixed_iter_path:
  assumes source: "comma_sector f p k"
    and guard: "comma_fixed_iter f n k + 99 < (f + 1) * 10 ^ p"
  shows "rtranclp comma_child k (comma_fixed_iter f n k)"
  using guard
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have step: "comma_fixed_iter f (Suc n) k =
      comma_fixed_iter f n k + 10 * (comma_fixed_iter f n k mod 10) + f"
    by simp
  have earlier: "comma_fixed_iter f n k + 99 < (f + 1) * 10 ^ p"
    using Suc.prems step by linarith
  have path: "rtranclp comma_child k (comma_fixed_iter f n k)"
    using Suc.IH[OF earlier] .
  have admitted: "comma_sector f p (comma_fixed_iter f (Suc n) k)"
    using comma_guarded_fixed_iter_sector[OF source Suc.prems] .
  have edge: "comma_child (comma_fixed_iter f n k)
      (comma_fixed_iter f (Suc n) k)"
    unfolding comma_child_def
  proof (rule exI[where x=f], rule exI[where x=p], rule conjI)
    show "comma_sector f p (comma_fixed_iter f (Suc n) k)"
      by (rule admitted)
    show "comma_fixed_iter f (Suc n) k =
        comma_fixed_iter f n k +
        10 * (comma_fixed_iter f n k mod 10) + f"
      by (rule step)
  qed
  show ?case using path edge by (meson rtranclp.rtrancl_into_rtrancl)
qed

text \<open>The published OEIS prefix additionally requires a proof that all
smaller root trees terminate and that the root-20 tree has unbounded depth.
The local phase and guard lemmas alone do not supply that premise.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_startup comma_phase_carry comma_phase_residue comma_phase_quotient
      comma_fixed_iter_phase comma_fixed_iter_displacement
      comma_period_phase_close comma_guarded_interior_child
      comma_guarded_fixed_iter_sector comma_guarded_fixed_iter_path})
    then () else error "Comma-cylinder proof depends on an oracle";
\<close>
end
