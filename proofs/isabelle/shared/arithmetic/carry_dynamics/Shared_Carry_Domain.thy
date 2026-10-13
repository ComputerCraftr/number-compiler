theory Shared_Carry_Domain
  imports Main
begin

text \<open>A family-independent three-element carry domain, its scalar decimal
threshold classifier, and ordered identity/reset/set actions.\<close>

datatype carry_domain = Below | Equal | Above

definition domain :: "nat \<Rightarrow> carry_domain" where
  "domain s = (if s < 9 then Below else if s = 9 then Equal else Above)"

fun carry_apply :: "carry_domain \<Rightarrow> bool \<Rightarrow> bool" where
  "carry_apply Below c = False"
| "carry_apply Equal c = c"
| "carry_apply Above c = True"

definition carry_then ::
    "carry_domain \<Rightarrow> carry_domain \<Rightarrow> carry_domain" where
  "carry_then after before = (if after = Equal then before else after)"

lemma carry_then_apply:
  "carry_apply (carry_then after before) c =
    carry_apply after (carry_apply before c)"
  by (cases after; cases before; cases c; simp_all add: carry_then_def)

lemma carry_apply_decimal_threshold:
  "carry_apply (domain s) c = (10 \<le> s + (if c then 1 else 0))"
  by (cases c; auto simp: domain_def split: if_splits; arith)

lemma decimal_double_digit_floor_carry:
  assumes digit: "d < 10"
  shows "carry_apply (domain (d + d)) c =
      ((d + d + (if c then 1 else 0)) div 10 = 1)"
proof -
  have bound: "d + d + (if c then 1 else 0) < 20"
    using digit by (cases c; arith)
  have carry:
    "carry_apply (domain (d + d)) c =
      (10 \<le> d + d + (if c then 1 else 0))"
    by (rule carry_apply_decimal_threshold)
  let ?total = "d + d + (if c then 1 else 0)"
  have decomposition: "?total = 10 * (?total div 10) + ?total mod 10"
    by (simp add: mult.commute)
  have remainder: "?total mod 10 < 10" by simp
  have quotient: "?total div 10 = (if 10 \<le> ?total then 1 else 0)"
  proof (cases "10 \<le> ?total")
    case True
    have "?total div 10 = 1"
      using True bound decomposition remainder by arith
    then show ?thesis by simp
  next
    case False
    have "?total div 10 = 0"
      using False decomposition remainder by arith
    then show ?thesis by simp
  qed
  show ?thesis
    using carry quotient by simp
qed

ML \<open>
  val checked = @{thms carry_then_apply carry_apply_decimal_threshold
      decimal_double_digit_floor_carry};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Shared carry-domain proof depends on an oracle";
\<close>

end
