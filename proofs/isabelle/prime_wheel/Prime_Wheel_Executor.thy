theory Prime_Wheel_Executor
  imports Prime_Wheel_Bridge
begin

datatype phi_frame = Enter nat nat | Finish nat nat
type_synonym phi_config = "phi_frame list \<times> phi_store"

inductive phi_step :: "nat list \<Rightarrow> phi_config \<Rightarrow> phi_config \<Rightarrow> bool" for ps where
  cached:
    "M (d,x) = Some v \<Longrightarrow>
      phi_step ps (Enter d x # S, M) (S, M)"
| base:
    "phi_step ps (Enter 0 x # S, M) (S, M((0,x) \<mapsto> x))"
| expand:
    "Suc d \<le> length ps \<Longrightarrow> M (Suc d,x) = None \<Longrightarrow>
      phi_step ps (Enter (Suc d) x # S, M)
        (Enter d x # Enter d (x div (ps ! d)) # Finish (Suc d) x # S, M)"
| finish:
    "M (d,x) = Some l \<Longrightarrow> M (d,x div (ps ! d)) = Some r \<Longrightarrow>
      phi_step ps (Finish (Suc d) x # S, M)
        (S, M(((Suc d,x)) \<mapsto> (l-r)))"

abbreviation phi_steps :: "nat list \<Rightarrow> phi_config \<Rightarrow> phi_config \<Rightarrow> bool" where
  "phi_steps ps \<equiv> (phi_step ps)\<^sup>*\<^sup>*"

definition store_extends :: "phi_store \<Rightarrow> phi_store \<Rightarrow> bool" where
  "store_extends M M' \<longleftrightarrow> (\<forall>k v. M k = Some v \<longrightarrow> M' k = Some v)"

lemma exact_update_extends:
  assumes "valid_phi_store ps M" "d \<le> length ps"
    "v = numerical_Phi ps d x"
  shows "store_extends M (M((d,x) \<mapsto> v))"
  using assms valid_phi_store_lookup
  by (auto simp: store_extends_def split: if_splits)

lemma phi_steps_one:
  "phi_step ps a b \<Longrightarrow> phi_steps ps a b"
  by (rule r_into_rtranclp)

lemma phi_steps_trans:
  "phi_steps ps a b \<Longrightarrow> phi_steps ps b c \<Longrightarrow> phi_steps ps a c"
  by (rule rtranclp_trans)

lemma depth_one_shortcut_exact:
  "numerical_Phi ps 1 x = x - x div (ps ! 0)"
  by simp

lemma phi_cached_run:
  assumes "M (d,x) = Some v"
  shows "phi_steps ps (Enter d x # S, M) (S, M)"
  by (rule phi_steps_one, rule phi_step.cached) (fact assms)

theorem phi_postorder_completes:
  assumes valid: "valid_phi_store ps M" and depth: "d \<le> length ps"
  shows "\<exists>M'. phi_steps ps (Enter d x # S, M) (S, M') \<and>
    valid_phi_store ps M' \<and> store_extends M M' \<and>
    M' (d,x) = Some (numerical_Phi ps d x)"
  using depth valid
proof (induction d arbitrary: x S M)
  case 0
  have valid0: "valid_phi_store ps M" by fact
  show ?case
  proof (cases "M (0,x)")
    case (Some v)
    have exact: "v = numerical_Phi ps 0 x"
      using valid_phi_store_lookup[OF valid0 Some] by simp
    have run: "phi_steps ps (Enter 0 x # S, M) (S, M)"
      by (rule phi_cached_run) (fact Some)
    show ?thesis
      using run valid0 Some exact
      by (auto simp: store_extends_def)
  next
    case None
    let ?M = "M((0,x) \<mapsto> x)"
    have step: "phi_steps ps (Enter 0 x # S, M) (S, ?M)"
      by (rule phi_steps_one) (rule phi_step.base)
    have valid': "valid_phi_store ps ?M"
      by (rule valid_phi_store_update[OF valid0]) simp_all
    have extends: "store_extends M ?M"
      by (rule exact_update_extends[OF valid0]) simp_all
    show ?thesis using step valid' extends by auto
  qed
next
  case (Suc d)
  show ?case
  proof (cases "M (Suc d,x)")
    case (Some v)
    have exact: "v = numerical_Phi ps (Suc d) x"
      using valid_phi_store_lookup[OF Suc.prems(2) Some] by simp
    have run: "phi_steps ps (Enter (Suc d) x # S, M) (S, M)"
      by (rule phi_cached_run) (fact Some)
    show ?thesis
      using run Suc.prems(2) Some exact
      by (auto simp: store_extends_def)
  next
    case None
    let ?y = "x div (ps ! d)"
    let ?tail = "Finish (Suc d) x # S"
    have ddepth: "d \<le> length ps" using Suc.prems(1) by simp
    have expand: "phi_steps ps (Enter (Suc d) x # S, M)
        (Enter d x # Enter d ?y # ?tail, M)"
      by (rule phi_steps_one, rule phi_step.expand) fact+
    obtain M1 where left:
      "phi_steps ps (Enter d x # Enter d ?y # ?tail, M)
        (Enter d ?y # ?tail, M1)"
      and valid1: "valid_phi_store ps M1"
      and extends1: "store_extends M M1"
      and left_value: "M1 (d,x) = Some (numerical_Phi ps d x)"
      using Suc.IH[OF ddepth Suc.prems(2), of x "Enter d ?y # ?tail"] by blast
    obtain M2 where right:
      "phi_steps ps (Enter d ?y # ?tail, M1) (?tail, M2)"
      and valid2: "valid_phi_store ps M2"
      and extends2: "store_extends M1 M2"
      and right_value: "M2 (d,?y) = Some (numerical_Phi ps d ?y)"
      using Suc.IH[OF ddepth valid1, of ?y ?tail] by blast
    have left_preserved: "M2 (d,x) = Some (numerical_Phi ps d x)"
      using extends2 left_value by (auto simp: store_extends_def)
    let ?M3 = "M2(((Suc d,x)) \<mapsto>
      (numerical_Phi ps d x - numerical_Phi ps d ?y))"
    have finish: "phi_steps ps (?tail, M2) (S, ?M3)"
      by (rule phi_steps_one, rule phi_step.finish) fact+
    have valid3: "valid_phi_store ps ?M3"
      by (rule valid_phi_store_update[OF valid2 Suc.prems(1)]) simp
    have extends3: "store_extends M2 ?M3"
      by (rule exact_update_extends[OF valid2 Suc.prems(1)]) simp
    have extends: "store_extends M ?M3"
      using extends1 extends2 extends3
      by (auto simp: store_extends_def)
    have run: "phi_steps ps (Enter (Suc d) x # S, M) (S, ?M3)"
      using expand left right finish by (meson phi_steps_trans)
    show ?thesis using run valid3 extends by auto
  qed
qed

corollary empty_postorder_returns_root:
  assumes "d \<le> length ps"
  shows "\<exists>M. phi_steps ps (Enter d x # [], \<lambda>_. None) ([], M) \<and>
    M (d,x) = Some (numerical_Phi ps d x)"
  using phi_postorder_completes[OF empty_phi_store_valid assms, of x "[]"] by blast

text \<open>
  These rules expose the concrete Enter/Finish order and prove that an
  uncached or locally cached request has a finite exact postorder run.  The
  depth-one production shortcut is the recurrence equation above.  The Python
  loop additionally short-circuits inputs at most one, avoids pushing children
  already present in the local memo, checks a shared root before traversal,
  and performs resource and lease checks.
  A deterministic simulation including those branches, exception cleanup, and
  budget accounting is not asserted by this theory.
\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms phi_postorder_completes empty_postorder_returns_root}) then ()
    else error "Prime postorder executor depends on an oracle";
\<close>

end
