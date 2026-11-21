theory Reflected_Repeat_Sheets
  imports Main
begin

text \<open>The source digit is in multiplication-input order. Reflection into
physical column coordinates is a separate operation.\<close>

lemma five_repeat_sheets:
  fixes d b :: nat
  assumes "d < 10" "b < 5"
  shows "(5 * d + b) mod 10 = d \<longleftrightarrow>
    ((5 * (d mod 2) + b) div 2 = d div 2 \<and> b mod 2 = 0)"
proof -
  have d_cases: "d = 0 \<or> d = 1 \<or> d = 2 \<or> d = 3 \<or> d = 4 \<or>
      d = 5 \<or> d = 6 \<or> d = 7 \<or> d = 8 \<or> d = 9"
    using assms by arith
  have b_cases: "b = 0 \<or> b = 1 \<or> b = 2 \<or> b = 3 \<or> b = 4"
    using assms by arith
  show ?thesis using d_cases b_cases by auto
qed

lemma two_repeat_sheets:
  fixes d b :: nat
  assumes "d < 10" "b < 2"
  defines "h \<equiv> (2 * (d mod 5) + b) div 2"
  shows "(2 * d + b) mod 10 = d \<longleftrightarrow>
    (d div 5 = 0 \<and> b = 0 \<and> h = 0 \<or>
     d div 5 = 1 \<and> b = 1 \<and> h = 4)"
proof -
  have d_cases: "d = 0 \<or> d = 1 \<or> d = 2 \<or> d = 3 \<or> d = 4 \<or>
      d = 5 \<or> d = 6 \<or> d = 7 \<or> d = 8 \<or> d = 9"
    using assms by arith
  have b_cases: "b = 0 \<or> b = 1" using assms by arith
  show ?thesis using d_cases b_cases unfolding h_def by auto
qed

end
