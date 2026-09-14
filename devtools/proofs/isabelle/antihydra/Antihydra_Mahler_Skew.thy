theory Antihydra_Mahler_Skew
  imports Antihydra_Literal_TM "Shared_S_Arithmetic.S_Arithmetic_Skew"
begin

text \<open>The return-section scalar map and its centered Mahler coordinate
are defined independently of any claimed all-time barrier.\<close>

definition antihydra_h_step :: "nat \<Rightarrow> nat" where
  "antihydra_h_step h = (3*h - h mod 2) div 2"

definition mahler_D_step :: "nat \<Rightarrow> nat" where
  "mahler_D_step D = (3*D + 1) div 2"

lemma nat_mod_two_cases:
  fixes D :: nat
  obtains k where "D = 2*k" | k where "D = 2*k+1"
proof (cases "D mod 2")
  case 0
  have "2 dvd D" using 0 by (simp add: dvd_eq_mod_eq_0)
  then obtain k where "D = 2*k" by (auto simp: dvd_def mult.commute)
  then show thesis by (rule that(1))
next
  case (Suc r)
  have bound: "D mod 2 < 2" by simp
  with Suc have rem: "D mod 2 = 1" by arith
  have decomposition: "D mod 2 + D div 2 * 2 = D"
    by (rule mod_div_mult_eq)
  have "D = 2*(D div 2)+1" using rem decomposition by arith
  then show thesis by (rule that(2))
qed

lemma mahler_D_step_parity:
  "mahler_D_step D = (3*D + D mod 2) div 2"
  by (cases D rule: nat_mod_two_cases;
      simp add: mahler_D_step_def algebra_simps mod_Suc)

theorem centered_return_commutes:
  "antihydra_h_step (D+1) = mahler_D_step D + 1"
  by (cases D rule: nat_mod_two_cases;
      simp add: antihydra_h_step_def mahler_D_step_def algebra_simps mod_Suc)

definition mahler_X :: "nat \<Rightarrow> int" where
  "mahler_X D = 2*int D + 1"

definition mahler_sigma :: "nat \<Rightarrow> int" where
  "mahler_sigma D = 1 - 2*int (D mod 2)"

theorem mahler_balanced_action:
  "2 * mahler_X (mahler_D_step D) = 3 * mahler_X D - mahler_sigma D"
  by (cases D rule: nat_mod_two_cases;
      simp add: mahler_X_def mahler_sigma_def mahler_D_step_def
        algebra_simps mod_Suc)

theorem mahler_D_step_even_lift:
  "mahler_D_step (D + 2*k) = mahler_D_step D + 3*k"
  by (cases D rule: nat_mod_two_cases;
      simp add: mahler_D_step_def algebra_simps)

record antihydra_skew =
  sk_width :: nat
  sk_A :: int
  sk_D :: int
  sk_J :: int
  sk_delta :: int
  sk_minprefix :: int

definition skew_identity :: antihydra_skew where
  "skew_identity = \<lparr>sk_width=0, sk_A=1, sk_D=1, sk_J=0,
    sk_delta=0, sk_minprefix=0\<rparr>"

definition skew_valid :: "antihydra_skew \<Rightarrow> bool" where
  "skew_valid g \<longleftrightarrow>
    sk_minprefix g \<le> 0 \<and> sk_minprefix g \<le> sk_delta g"

definition skew_then :: "antihydra_skew \<Rightarrow> antihydra_skew \<Rightarrow> antihydra_skew" where
  "skew_then a b = \<lparr>
    sk_width = sk_width a + sk_width b,
    sk_A = sk_A b * sk_A a,
    sk_D = sk_D b * sk_D a,
    sk_J = sk_A b * sk_J a + sk_J b * sk_D a,
    sk_delta = sk_delta a + sk_delta b,
    sk_minprefix = min (sk_minprefix a) (sk_delta a + sk_minprefix b)\<rparr>"

lemma skew_then_identity [simp]:
  assumes "skew_valid a"
  shows "skew_then skew_identity a = a" "skew_then a skew_identity = a"
  using assms by (simp_all add: skew_valid_def skew_then_def
      skew_identity_def antihydra_skew.equality min_def)

lemma skew_then_valid:
  assumes "skew_valid a" "skew_valid b"
  shows "skew_valid (skew_then a b)"
  using assms by (auto simp: skew_valid_def skew_then_def min_def)

theorem skew_then_assoc:
  "skew_then (skew_then a b) c = skew_then a (skew_then b c)"
  by (simp add: skew_then_def antihydra_skew.equality min.assoc
      min_def algebra_simps)

definition skew_numerator :: "antihydra_skew \<Rightarrow> int \<Rightarrow> int" where
  "skew_numerator g x = sk_A g*x + sk_J g"

theorem skew_numerator_composition:
  "skew_numerator (skew_then a b) x =
    sk_A b * skew_numerator a x + sk_J b * sk_D a"
  by (simp add: skew_numerator_def skew_then_def algebra_simps)

text \<open>This projection forgets width and ledger geometry only for linear
arithmetic observations; it does not authorize guarded action substitution.\<close>

definition antihydra_linear_projection ::
    "antihydra_skew \<Rightarrow> int skew_transfer" where
  "antihydra_linear_projection g =
    \<lparr>upper = sk_A g, offset = sk_J g, lower = sk_D g\<rparr>"

lemma antihydra_linear_projection_identity:
  "antihydra_linear_projection skew_identity = shared_skew_identity"
  by (simp add: antihydra_linear_projection_def
      skew_identity_def shared_skew_identity_def)

lemma antihydra_linear_projection_then:
  "antihydra_linear_projection (skew_then a b) = shared_skew_then
    (antihydra_linear_projection a) (antihydra_linear_projection b)"
  by (cases a; cases b)
    (simp add: antihydra_linear_projection_def skew_then_def
      shared_skew_then_def algebra_simps)

lemma antihydra_linear_projection_numerator:
  "skew_numerator g x = upper (antihydra_linear_projection g) * x +
    offset (antihydra_linear_projection g)"
  by (simp add: skew_numerator_def antihydra_linear_projection_def)

theorem skew_minprefix_composition:
  "sk_minprefix (skew_then a b) =
    min (sk_minprefix a) (sk_delta a + sk_minprefix b)"
  by (simp add: skew_then_def)

text \<open>The atom is indexed by the physical return branch bit b=h mod 2.
Thus J=-b, while the ledger change is +2 on b=0 and -1 on b=1.  The Mahler
epsilon used in the source-barrier theory is D mod 2=1-b.\<close>

definition skew_atom :: "nat \<Rightarrow> antihydra_skew" where
  "skew_atom b = \<lparr>sk_width=1, sk_A=3, sk_D=2, sk_J= - int b,
    sk_delta=2-3*int b, sk_minprefix=min 0 (2-3*int b)\<rparr>"

fun skew_word :: "nat list \<Rightarrow> antihydra_skew" where
  "skew_word [] = skew_identity"
| "skew_word (e#es) = skew_then (skew_atom e) (skew_word es)"

fun ledger_word_delta :: "nat list \<Rightarrow> int" where
  "ledger_word_delta [] = 0"
| "ledger_word_delta (b#bs) = 2-3*int b + ledger_word_delta bs"

fun ledger_word_minprefix :: "nat list \<Rightarrow> int" where
  "ledger_word_minprefix [] = 0"
| "ledger_word_minprefix (b#bs) =
    min (min 0 (2-3*int b)) (2-3*int b + ledger_word_minprefix bs)"

lemma skew_atom_valid [simp]: "skew_valid (skew_atom e)"
  by (simp add: skew_valid_def skew_atom_def min_def)

lemma skew_word_valid [simp]: "skew_valid (skew_word es)"
proof (induct es)
  case Nil
  then show ?case by (simp add: skew_identity_def skew_valid_def)
next
  case (Cons e es)
  show ?case
    by (simp only: skew_word.simps; rule skew_then_valid[OF skew_atom_valid Cons])
qed

theorem skew_word_append:
  "skew_word (xs @ ys) = skew_then (skew_word xs) (skew_word ys)"
  by (induct xs) (simp_all add: skew_then_assoc)

theorem skew_word_induces_ledger_geometry:
  "sk_delta (skew_word es) = ledger_word_delta es"
  "sk_minprefix (skew_word es) = ledger_word_minprefix es"
  by (induct es) (simp_all add: skew_identity_def skew_atom_def skew_then_def)

definition one_return_h :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "one_return_h b x = 3*x+b"

definition one_return_ledger :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "one_return_ledger b a = a + (if b=0 then 2 else -1)"

definition one_return_physical_roof4 :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "one_return_physical_roof4 b x a =
    (if b=0 then 12*int x^2 + 8*a - 4 else 12*int x^2 - 28)"

theorem one_return_skew_equation:
  assumes "b < 2"
  shows "2 * int (one_return_h b x) = 3 * int (2*x+b) - int b"
  using assms by (simp add: one_return_h_def algebra_simps)

theorem one_return_kernel_coefficients:
  "one_return_physical_roof4 0 x a = 12*int x^2 + 8*a - 4"
  "one_return_physical_roof4 1 x a = 12*int x^2 - 28"
  "one_return_ledger 0 a = a+2"
  "one_return_ledger 1 a = a-1"
  by (simp_all add: one_return_physical_roof4_def one_return_ledger_def)

text \<open>The roof equations above match the production width-one kernel on
its safe nonhalting domain.  In particular, the odd branch requires incoming
ledger at least one; ledger zero follows the separate terminal F/0 roof and is
not described by the odd polynomial above.  These equations do not prove that
the compressed section grammar realizes the counts from every literal tape
A(a,b).  That parametric literal-to-macro simulation lemma remains required
before a nonhalting result may cross the TM boundary.\<close>

lemma source_seven_is_blank_return_center:
  "7 + 1 = (8::nat)"
  by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms antihydra_linear_projection_identity antihydra_linear_projection_then
      antihydra_linear_projection_numerator nat_mod_two_cases mahler_D_step_parity centered_return_commutes
      mahler_balanced_action mahler_D_step_even_lift
      skew_then_identity skew_then_valid skew_then_assoc
      skew_numerator_composition skew_minprefix_composition
      skew_atom_valid skew_word_valid skew_word_append
      skew_word_induces_ledger_geometry
      one_return_skew_equation one_return_kernel_coefficients
      source_seven_is_blank_return_center}) then ()
    else error "Antihydra Mahler/skew proof depends on an oracle";
\<close>

end
