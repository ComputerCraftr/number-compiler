theory Cylinder_Innovation_Transport
  imports Main
begin

text \<open>
  Chart transport for signed innovation atoms.  The operators below are
  coefficient-level algebra only; this theory does not claim source carry
  closure, cyclotomic refinement, or a bounded 196 grammar.
\<close>

type_synonym coefficient_function = "int => int"

definition innovation_neighbor ::
    "coefficient_function => coefficient_function" where
  "innovation_neighbor f i = f i + f (i - 1)"

definition innovation_reflect ::
    "int => coefficient_function => coefficient_function" where
  "innovation_reflect d f i = f (d - i)"

definition innovation_translate ::
    "int => coefficient_function => coefficient_function" where
  "innovation_translate a f i = f (i - a)"

definition innovation_double ::
    "coefficient_function => coefficient_function" where
  "innovation_double f i = 2 * f i"

definition innovation_add ::
    "coefficient_function => coefficient_function => coefficient_function" where
  "innovation_add f g i = f i + g i"

definition innovation_negate ::
    "coefficient_function => coefficient_function" where
  "innovation_negate f i = - f i"

definition innovation_residue ::
    "int => coefficient_function => coefficient_function" where
  "innovation_residue q f i = f i mod q"

lemma innovation_reflect_neighbor:
  "innovation_reflect d (innovation_neighbor f) =
    innovation_neighbor (innovation_reflect (d - 1) f)"
  by (rule ext) (simp add: innovation_reflect_def innovation_neighbor_def
      algebra_simps)

lemma innovation_reflect_neighbor_power:
  "innovation_reflect d ((innovation_neighbor ^^ r) f) =
    (innovation_neighbor ^^ r) (innovation_reflect (d - int r) f)"
proof (induction r arbitrary: d)
  case 0
  then show ?case by (simp add: innovation_reflect_def)
next
  case (Suc r)
  have local:
    "innovation_reflect d (innovation_neighbor ((innovation_neighbor ^^ r) f)) =
      innovation_neighbor
        (innovation_reflect (d - 1) ((innovation_neighbor ^^ r) f))"
    using innovation_reflect_neighbor[of d "(innovation_neighbor ^^ r) f"] .
  have tail:
    "innovation_reflect (d - 1) ((innovation_neighbor ^^ r) f) =
      (innovation_neighbor ^^ r)
        (innovation_reflect (d - 1 - int r) f)"
    using Suc.IH[of "d - 1"] .
  show ?case
    using local tail
    by (simp add: funpow_Suc_right algebra_simps)
qed

lemma innovation_translate_neighbor:
  "innovation_translate a (innovation_neighbor f) =
    innovation_neighbor (innovation_translate a f)"
  by (rule ext) (simp add: innovation_translate_def innovation_neighbor_def
      algebra_simps)

lemma innovation_double_neighbor:
  "innovation_double (innovation_neighbor f) =
    innovation_neighbor (innovation_double f)"
  by (rule ext) (simp add: innovation_double_def innovation_neighbor_def
      algebra_simps)

lemma innovation_reflect_translate:
  "innovation_reflect d (innovation_translate a f) =
    innovation_translate (-a) (innovation_reflect d f)"
  by (rule ext) (simp add: innovation_reflect_def innovation_translate_def
      algebra_simps)

lemma innovation_reflect_double:
  "innovation_reflect d (innovation_double f) =
    innovation_double (innovation_reflect d f)"
  by (rule ext) (simp add: innovation_reflect_def innovation_double_def
      algebra_simps)

lemma innovation_double_translate:
  "innovation_double (innovation_translate a f) =
    innovation_translate a (innovation_double f)"
  by (rule ext) (simp add: innovation_double_def innovation_translate_def
      algebra_simps)

lemma innovation_add_negate:
  "innovation_add f (innovation_negate f) = (\<lambda>i. 0)"
  by (rule ext) (simp add: innovation_add_def innovation_negate_def)

lemma innovation_residue_add:
  "innovation_residue q (innovation_add f g) =
    innovation_residue q
      (innovation_add (innovation_residue q f) (innovation_residue q g))"
  by (rule ext) (simp add: innovation_residue_def innovation_add_def
      mod_add_eq)

lemma innovation_residue_cancel:
  "innovation_residue q (innovation_add f (innovation_negate f)) =
    (\<lambda>i. 0)"
  by (rule ext) (simp add: innovation_add_negate innovation_residue_def)

text \<open>
  The main chart-push rule is the power identity above: a reflected radial
  multiplier transports its chart by exactly the represented operator order.
  No source occurrence or carry quotient is inferred from this identity.
\<close>

text \<open>
  Arithmetic syntax for simultaneous primitive-atom substitution. These seven
  constructors correspond to SymbolicInnovationArena's node kinds. Evaluation
  observes the original replacement environment, not a recursively rewritten
  replacement. This supplies the semantic specification for substitute_many;
  memo/worklist refinement, complete-channel source admission and temporal
  grammar bounds remain separate obligations.
\<close>

datatype 'a innovation_expr =
    IZero
  | IAtom 'a
  | IInterval nat
  | IRadial nat nat "'a innovation_expr"
  | IChart int int "'a innovation_expr"
  | IScale int "'a innovation_expr"
  | IAdd "'a innovation_expr" "'a innovation_expr"

fun innovation_eval ::
  "('a => coefficient_function) => 'a innovation_expr => coefficient_function"
where
  "innovation_eval env IZero = (\<lambda>i. 0)"
| "innovation_eval env (IAtom a) = env a"
| "innovation_eval env (IInterval n) =
    (\<lambda>i. if 0 \<le> i \<and> i < int n then 1 else 0)"
| "innovation_eval env (IRadial q r x) =
    (innovation_double ^^ q) ((innovation_neighbor ^^ r) (innovation_eval env x))"
| "innovation_eval env (IChart s offset x) =
    (\<lambda>i. innovation_eval env x (s * i + offset))"
| "innovation_eval env (IScale c x) = (\<lambda>i. c * innovation_eval env x i)"
| "innovation_eval env (IAdd x y) =
    innovation_add (innovation_eval env x) (innovation_eval env y)"

fun innovation_substitute ::
  "('a => 'b innovation_expr) => 'a innovation_expr => 'b innovation_expr"
where
  "innovation_substitute sigma IZero = IZero"
| "innovation_substitute sigma (IAtom a) = sigma a"
| "innovation_substitute sigma (IInterval n) = IInterval n"
| "innovation_substitute sigma (IRadial q r x) =
    IRadial q r (innovation_substitute sigma x)"
| "innovation_substitute sigma (IChart s offset x) =
    IChart s offset (innovation_substitute sigma x)"
| "innovation_substitute sigma (IScale c x) =
    IScale c (innovation_substitute sigma x)"
| "innovation_substitute sigma (IAdd x y) =
    IAdd (innovation_substitute sigma x) (innovation_substitute sigma y)"

lemma innovation_substitute_semantics:
  "innovation_eval env (innovation_substitute sigma x) =
    innovation_eval (\<lambda>a. innovation_eval env (sigma a)) x"
  by (induction x) auto

lemma innovation_substitute_identity:
  "innovation_substitute IAtom x = x"
  by (induction x) auto

lemma innovation_substitute_composition:
  "innovation_substitute tau (innovation_substitute sigma x) =
    innovation_substitute (\<lambda>a. innovation_substitute tau (sigma a)) x"
  by (induction x) auto

lemma innovation_substitute_many_semantics:
  "map (innovation_eval env) (map (innovation_substitute sigma) xs) =
    map (innovation_eval (\<lambda>a. innovation_eval env (sigma a))) xs"
  by (simp add: map_map innovation_substitute_semantics)

ML \<open>
  val checked = @{thms innovation_reflect_neighbor
    innovation_reflect_neighbor_power innovation_translate_neighbor
    innovation_double_neighbor innovation_reflect_translate
    innovation_reflect_double innovation_double_translate
    innovation_add_negate innovation_residue_add innovation_residue_cancel
    innovation_substitute_semantics innovation_substitute_identity
    innovation_substitute_composition innovation_substitute_many_semantics};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Cylinder innovation transport depends on an oracle";
\<close>

end
