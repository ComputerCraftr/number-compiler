theory Reverse_Seven_Bands
  imports Reverse_Residuals
begin

definition q7 :: "nat \<Rightarrow> nat" where
  "q7 s = (if s < 4 then 0 else if s = 4 then 1 else
     if s < 9 then 2 else if s = 9 then 3 else
     if s < 14 then 4 else if s = 14 then 5 else 6)"

definition no_growth_domain :: "nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> carry_domain" where
  "no_growth_domain s c d = domain
     (((s + (if c then 1 else 0)) mod 10) +
      ((s + (if d then 1 else 0)) mod 10))"

definition responses where
  "responses s = (no_growth_domain s False False, no_growth_domain s False True,
      no_growth_domain s True False, no_growth_domain s True True)"

definition representative where
  "representative s = [0,4,5,9,10,14,15] ! q7 s"

lemma representative_table:
  "list_all (\<lambda>s. responses s = responses (representative s)) [0..<19]"
  by code_simp

theorem seven_bands_suffice:
  assumes "s \<le> 18" "t \<le> 18" "q7 s = q7 t"
  shows "no_growth_domain s c d = no_growth_domain t c d"
proof -
  have rows: "responses x = responses (representative x)" if "x < 19" for x
    using representative_table that by (simp add: list_all_iff)
  have "responses s = responses t"
    using rows[of s] rows[of t] assms by (simp add: representative_def)
  then show ?thesis by (cases c; cases d; simp add: responses_def)
qed

lemma growth_edge_separates_seven_band:
  "q7 16 = q7 18 \<and> domain (16 mod 10 + 1) \<noteq> domain (18 mod 10 + 1)"
  by (simp add: q7_def domain_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms seven_bands_suffice growth_edge_separates_seven_band}) then ()
    else error "Seven-band proof depends on an oracle";
\<close>

end
