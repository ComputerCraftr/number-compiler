theory Comma_Fast_Totality_Check
  imports Comma_Fast_Control.Comma_Fast_Kernel
    Comma_Total_Macro.Comma_Total_Macro
begin

text \<open>This Boolean checker accepts only a terminal event reached within
its inspection budget. Its proof transports every continued state through the
semantic control relation, so success establishes inductive termination.\<close>

fun comma_fast_finishes_within :: "nat \<Rightarrow> comma_decade_state \<Rightarrow> bool" where
  "comma_fast_finishes_within 0 s = False"
| "comma_fast_finishes_within (Suc n) s =
    (case comma_fast_decade_control s of
       Comma_Decade_Fork a d \<Rightarrow> True
     | Comma_Decade_Landmine d \<Rightarrow> True
     | Comma_Decade_Continue t \<Rightarrow> comma_fast_finishes_within n t
     | Comma_Decade_Invalid \<Rightarrow> False)"

lemma comma_fast_finishes_within_sound:
  assumes valid: "comma_decade_admitted s"
    and checked: "comma_fast_finishes_within n s"
  shows "\<exists>k\<le>n. comma_decade_finishes s k"
  using valid checked
proof (induction n arbitrary: s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have control: "comma_fast_decade_control s=comma_decade_control s"
    by (rule comma_fast_decade_control_correct[OF Suc.prems(1)])
  show ?case
  proof (cases "comma_decade_control s")
    case (Comma_Decade_Fork a d)
    have "comma_decade_finishes s 1"
      by (rule comma_decade_finishes.fork[OF Comma_Decade_Fork])
    then show ?thesis by auto
  next
    case (Comma_Decade_Landmine d)
    have "comma_decade_finishes s 1"
      by (rule comma_decade_finishes.landmine[OF Comma_Decade_Landmine])
    then show ?thesis by auto
  next
    case (Comma_Decade_Continue t)
    have admitted: "comma_decade_admitted t"
      by (rule comma_decade_control_closed(2)[OF Suc.prems(1) Comma_Decade_Continue refl])
    have tail: "comma_fast_finishes_within n t"
      using Suc.prems(2) by (simp only: comma_fast_finishes_within.simps
        control Comma_Decade_Continue comma_decade_outcome.case)
    obtain k where k: "k\<le>n" "comma_decade_finishes t k"
      using Suc.IH[OF admitted tail] by blast
    have "comma_decade_finishes s (Suc k)"
      by (rule comma_decade_finishes.crossing[OF Comma_Decade_Continue k(2)])
    then show ?thesis using k(1) by auto
  next
    case Comma_Decade_Invalid
    then show ?thesis using Suc.prems(2)
      by (simp only: comma_fast_finishes_within.simps control comma_decade_outcome.case)
  qed
qed

definition comma_fast_totality_rectangle :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_fast_totality_rectangle phases fuel =
    list_all (\<lambda>r. list_all (\<lambda>x.
      comma_fast_finishes_within fuel (Comma_Decade r x)) [0..<91]) [0..<phases]"

definition comma_fast_totality_phase :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_fast_totality_phase r n =
    list_all (\<lambda>x. comma_fast_finishes_within n (Comma_Decade r x)) [0..<91]"

definition comma_fast_totality_range :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_fast_totality_range lo hi n =
    list_all (\<lambda>r. comma_fast_totality_phase r n) [lo..<hi]"

lemma comma_fast_totality_range_join:
  assumes left: "comma_fast_totality_range a b n"
    and right: "comma_fast_totality_range b c n"
  shows "comma_fast_totality_range a c n"
proof -
  have phase: "\<And>r. a\<le>r \<Longrightarrow> r<c \<Longrightarrow> comma_fast_totality_phase r n"
  proof -
    fix r assume r: "a\<le>r" "r<c"
    show "comma_fast_totality_phase r n"
    proof (cases "r<b")
      case True
      then show ?thesis using left r
        by (auto simp: comma_fast_totality_range_def list_all_iff)
    next
      case False
      then show ?thesis using right r
        by (auto simp: comma_fast_totality_range_def list_all_iff)
    qed
  qed
  show ?thesis using phase
    by (auto simp: comma_fast_totality_range_def list_all_iff)
qed

lemma comma_fast_totality_range_rectangle:
  "comma_fast_totality_range 0 phases n = comma_fast_totality_rectangle phases n"
  by (simp only: comma_fast_totality_range_def comma_fast_totality_phase_def
    comma_fast_totality_rectangle_def)

lemma comma_fast_totality_rectangle_sound:
  assumes checked: "comma_fast_totality_rectangle 924 n"
    and valid: "comma_decade_admitted s"
  shows "\<exists>k\<le>n. comma_decade_finishes s k"
proof -
  obtain r x where s: "s=Comma_Decade r x" by (cases s) auto
  have bounds: "r<924" "x<91" using valid by (auto simp: s)
  have success: "comma_fast_finishes_within n s"
    using checked bounds by (auto simp: comma_fast_totality_rectangle_def list_all_iff s)
  show ?thesis by (rule comma_fast_finishes_within_sound[OF valid success])
qed

lemma comma_fast_totality_rectangle_macro:
  assumes checked: "comma_fast_totality_rectangle 924 n"
    and valid: "comma_boundary_valid q"
  shows "comma_macro_defined q"
  by (rule comma_boundary_macro_exists[OF _ valid])
    (use comma_fast_totality_rectangle_sound[OF checked] in blast)

text \<open>Closed proof evaluation keeps natural numbers in binary notation.
Only these fast executable equations are installed alongside numeral arithmetic;
the semantic round and weighted specifications are absent from this simpset.
The counter equations avoid lowering arbitrary numerals to unary constructors.\<close>

lemma comma_fast_finishes_within_eval:
  "comma_fast_finishes_within n s =
    (if n=0 then False else
      case comma_fast_decade_control s of
        Comma_Decade_Fork a d \<Rightarrow> True
      | Comma_Decade_Landmine d \<Rightarrow> True
      | Comma_Decade_Continue t \<Rightarrow> comma_fast_finishes_within (n-1) t
      | Comma_Decade_Invalid \<Rightarrow> False)"
  by (cases n) (simp_all cong: comma_decade_outcome.case_cong)


ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_fast_finishes_within_sound comma_fast_totality_rectangle_sound
      comma_fast_totality_rectangle_macro comma_fast_totality_range_join
      comma_fast_totality_range_rectangle}) then ()
    else error "Fast totality bridge depends on an oracle";
\<close>
end
