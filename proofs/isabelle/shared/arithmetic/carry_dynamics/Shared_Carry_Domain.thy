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

ML \<open>
  val checked = @{thms carry_then_apply};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Shared carry-domain proof depends on an oracle";
\<close>

end
