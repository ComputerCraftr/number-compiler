theory Comma_Recursive_Pair_Language
  imports Comma_Factored_Port_Carrier.Comma_Factored_Port_Carrier
begin

text \<open>This recursive observation reuses the physical carry monoid. It
retains a rightmost reset, two residues, and the first non-neutral center.
The first-defect option also supplies the all-neutral predicate. It does not
identify exact weighted comma actions or reconstruct their partial prefixes.
Concatenation length is an occurrence parameter, not another stored word.\<close>

datatype comma_pair_language =
  Comma_Pair_Language carry_domain nat nat "nat option"

fun comma_pair_first :: "comma_pair_language \<Rightarrow> nat option" where
  "comma_pair_first (Comma_Pair_Language D a b first)=first"

definition comma_pair_language_identity :: comma_pair_language where
  "comma_pair_language_identity=Comma_Pair_Language Equal 0 0 None"

fun comma_pair_language_merge ::
  "nat \<Rightarrow> comma_pair_language \<Rightarrow> comma_pair_language \<Rightarrow> comma_pair_language" where
  "comma_pair_language_merge n
     (Comma_Pair_Language D a b first) (Comma_Pair_Language E c d second)=
   Comma_Pair_Language (carry_then E D) ((a+c) mod 2)
     ((b+2^n*d) mod 5) (case first of None \<Rightarrow> second | Some v \<Rightarrow> first)"

fun comma_pair_language_admitted :: "comma_pair_language \<Rightarrow> bool" where
  "comma_pair_language_admitted (Comma_Pair_Language D a b first)=
    (a<2 \<and> b<5 \<and> (\<forall>v. first=Some v \<longrightarrow> v<5))"

lemma comma_pair_language_merge_closed:
  assumes "comma_pair_language_admitted A" "comma_pair_language_admitted B"
  shows "comma_pair_language_admitted (comma_pair_language_merge n A B)"
  using assms by (cases A; cases B; auto split: option.splits)

lemma comma_pair_affine_residue:
  fixes a b c k :: nat
  shows "(a+b*(c mod k)) mod k=(a+b*c) mod k"
  by (rule mod_add_cong[OF refl mod_mult_right_eq])

lemma comma_pair_language_merge_assoc:
  "comma_pair_language_merge (n+m) (comma_pair_language_merge n A B) C =
   comma_pair_language_merge n A (comma_pair_language_merge m B C)"
  by (cases A; cases B; cases C;
    auto simp: carry_then_def power_add mod_simps comma_pair_affine_residue algebra_simps split: option.splits)

lemma comma_pair_language_identity_left:
  assumes "comma_pair_language_admitted A"
  shows "comma_pair_language_merge 0 comma_pair_language_identity A=A"
  using assms by (cases A) (simp add: comma_pair_language_identity_def carry_then_def)

lemma comma_pair_language_identity_right:
  assumes "comma_pair_language_admitted A"
  shows "comma_pair_language_merge n A comma_pair_language_identity=A"
  using assms by (cases A) (simp add: comma_pair_language_identity_def carry_then_def split: option.splits)

lemma comma_pair_first_append:
  "comma_pair_first (comma_pair_language_merge n A B)=
    (case comma_pair_first A of None \<Rightarrow> comma_pair_first B | Some v \<Rightarrow> Some v)"
  by (cases A; cases B; simp split: option.splits)

lemma comma_pair_neutral_append:
  "(comma_pair_first (comma_pair_language_merge n A B)=None) =
    (comma_pair_first A=None \<and> comma_pair_first B=None)"
  by (simp add: comma_pair_first_append split: option.splits)

definition comma_pair_language_leaf :: "nat \<Rightarrow> comma_pair_language" where
  "comma_pair_language_leaf s=Comma_Pair_Language (domain s)
    ((s+1) mod 2) ((s+1) mod 5) (if s=9 then None else Some (s div 2 mod 5))"

lemma comma_pair_language_leaf_admitted:
  "comma_pair_language_admitted (comma_pair_language_leaf s)"
  by (simp add: comma_pair_language_leaf_def)

text \<open>Using s+1 is the exact signed defect s-9 in both residue fields.
Only this residue observation erases a multiple of ten.\<close>
lemma comma_pair_leaf_defect_residues:
  "(int s-9) mod 2=int ((s+1) mod 2)"
  "(int s-9) mod 5=int ((s+1) mod 5)"
proof -
  have mod2: "(int s-9) mod 2=(int s+1) mod 2"
    unfolding diff_conv_add_uminus by (rule mod_add_cong[OF refl]) simp
  have mod5: "(int s-9) mod 5=(int s+1) mod 5"
    unfolding diff_conv_add_uminus by (rule mod_add_cong[OF refl]) simp
  show "(int s-9) mod 2=int ((s+1) mod 2)"
    using mod2 by (simp add: zmod_int add.commute)
  show "(int s-9) mod 5=int ((s+1) mod 5)"
    using mod5 by (simp add: zmod_int add.commute)
qed

fun comma_pair_language_eval :: "nat list \<Rightarrow> comma_pair_language" where
  "comma_pair_language_eval []=comma_pair_language_identity"
| "comma_pair_language_eval (s#ss)=
    comma_pair_language_merge 1 (comma_pair_language_leaf s) (comma_pair_language_eval ss)"

lemma comma_pair_language_eval_admitted:
  "comma_pair_language_admitted (comma_pair_language_eval xs)"
  by (induction xs) (simp_all add: comma_pair_language_identity_def
    comma_pair_language_leaf_admitted comma_pair_language_merge_closed)

lemma comma_pair_language_eval_append:
  "comma_pair_language_eval (xs@ys)=
    comma_pair_language_merge (length xs) (comma_pair_language_eval xs) (comma_pair_language_eval ys)"
proof (induction xs)
  case Nil
  show ?case by (simp add: comma_pair_language_identity_left comma_pair_language_eval_admitted)
next
  case (Cons x xs)
  then show ?case using comma_pair_language_merge_assoc[of 1 "length xs"
      "comma_pair_language_leaf x" "comma_pair_language_eval xs" "comma_pair_language_eval ys"]
    by simp
qed

corollary comma_pair_language_eval_power2:
  "comma_pair_language_eval (xs@xs)=
    comma_pair_language_merge (length xs) (comma_pair_language_eval xs) (comma_pair_language_eval xs)"
  by (rule comma_pair_language_eval_append)

lemma comma_residue_power_phase:
  fixes a modulus period n :: nat
  assumes modulus: "1<modulus" and unit: "a^period mod modulus=1"
  shows "a^n mod modulus=a^(n mod period) mod modulus"
proof -
  have split: "n=n mod period+period*(n div period)" by simp
  have expanded: "a^n=a^(n mod period)*(a^period)^(n div period)"
  proof -
    have "a^n=a^(n mod period+period*(n div period))"
      by (rule arg_cong[OF split])
    also have "...=a^(n mod period)*(a^period)^(n div period)"
      by (simp only: power_add power_mult)
    finally show ?thesis .
  qed
  have repeated_unit: "(a^period)^(n div period) mod modulus=1"
    using power_mod[of "a^period" modulus "n div period"] unit modulus by simp
  show ?thesis
    by (simp only: expanded; subst mod_mult_eq[symmetric];
      simp only: repeated_unit mult_1_right mod_mod_trivial)
qed

lemma comma_pair_f5_length_phase:
  "(2::nat)^n mod 5=2^(n mod 4) mod 5"
  by (rule comma_residue_power_phase) simp_all

lemma comma_pair_language_merge_phase:
  "comma_pair_language_merge n A B=comma_pair_language_merge (n mod 4) A B"
proof (cases A; cases B)
  fix D a b first E c d second
  assume A: "A=Comma_Pair_Language D a b first"
    and B: "B=Comma_Pair_Language E c d second"
  have factor: "(2::nat)^n mod 5=2^(n mod 4) mod 5"
    by (rule comma_pair_f5_length_phase)
  have product: "(2^n*d) mod 5=(2^(n mod 4)*d) mod 5"
    by (rule mod_mult_cong[OF factor refl])
  have sum: "(b+2^n*d) mod 5=(b+2^(n mod 4)*d) mod 5"
    by (rule mod_add_cong[OF refl product])
  show ?thesis by (simp add: A B sum)
qed

ML \<open>
  val checked = @{thms comma_pair_language_merge_assoc comma_pair_language_merge_closed
    comma_pair_language_eval_append comma_pair_language_eval_power2
    comma_pair_first_append comma_pair_neutral_append comma_pair_leaf_defect_residues
    comma_pair_language_merge_phase};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Pair language depends on an oracle";
\<close>
end
