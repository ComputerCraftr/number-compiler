theory Comma_Reset_Germ
  imports
    Reverse_Residuals.Reverse_Threshold_Cocycle
    Reverse_Residuals.Reverse_Boundary_Germ_Local
begin

text \<open>
The germ records the complement-normalized F5 defect of the most recent
non-neutral pair sum.  It is an internal reset observer.  It is not a
replacement for the full native cocycle or for a fixed-orientation digit
action.
\<close>

type_synonym comma_reset_germ = "nat option"

definition comma_reset_I :: comma_reset_germ where
  "comma_reset_I = None"

definition comma_reset_R :: "nat \<Rightarrow> comma_reset_germ" where
  "comma_reset_R eta = Some (eta mod 5)"

definition comma_reset_germ_carrier :: "comma_reset_germ set" where
  "comma_reset_germ_carrier =
    insert None (Some ` {0..<5})"

lemma comma_reset_germ_carrier_card:
  "card comma_reset_germ_carrier = 6"
  by (simp add: comma_reset_germ_carrier_def card_image)

definition comma_reset_signed_defect :: "nat \<Rightarrow> int" where
  "comma_reset_signed_defect s =
    (if s < 9 then int s - 9 else 9 - int s)"

definition comma_reset_germ_encode :: "nat \<Rightarrow> comma_reset_germ" where
  "comma_reset_germ_encode s =
    (if s = 9 then comma_reset_I
     else comma_reset_R (nat (comma_reset_signed_defect s mod 5)))"

lemma comma_reset_germ_encode_range:
  "comma_reset_germ_encode s \<in> comma_reset_germ_carrier"
proof (cases "s = 9")
  case True
  then show ?thesis
    by (simp add: comma_reset_germ_encode_def comma_reset_germ_carrier_def
      comma_reset_I_def comma_reset_R_def)
next
  case False
  have residue_lt:
    "comma_reset_signed_defect s mod 5 < 5"
    by simp
  have eta_lt:
    "nat (comma_reset_signed_defect s mod 5) < 5"
    by (simp add: nat_less_iff)
  show ?thesis
    using False eta_lt
    by (auto simp: comma_reset_germ_encode_def comma_reset_germ_carrier_def
        comma_reset_I_def comma_reset_R_def)
qed

lemma comma_reset_germ_encode_below:
  assumes "s < 9"
  shows "comma_reset_germ_encode s = comma_reset_R (nat ((int s - 9) mod 5))"
  using assms
  by (simp add: comma_reset_germ_encode_def comma_reset_R_def
      comma_reset_signed_defect_def)

lemma comma_reset_germ_encode_above:
  assumes "9 < s"
  shows "comma_reset_germ_encode s = comma_reset_R (nat ((9 - int s) mod 5))"
  using assms
  by (simp add: comma_reset_germ_encode_def comma_reset_R_def
      comma_reset_signed_defect_def)

lemma comma_reset_germ_neutral_iff:
  assumes "s \<le> 18"
  shows "comma_reset_germ_encode s = comma_reset_I \<longleftrightarrow> s = 9"
  using assms by (auto simp: comma_reset_germ_encode_def comma_reset_I_def comma_reset_R_def)

lemma comma_reset_signed_defect_complement:
  assumes "s \<le> 18"
  shows "comma_reset_signed_defect (18 - s) = comma_reset_signed_defect s"
  using assms
  by (auto simp: comma_reset_signed_defect_def; presburger)

lemma comma_reset_germ_complement:
  assumes "s \<le> 18"
  shows "comma_reset_germ_encode (18 - s) = comma_reset_germ_encode s"
proof (cases "s = 9")
  case True
  then show ?thesis by (simp add: comma_reset_germ_encode_def comma_reset_I_def comma_reset_R_def)
next
  case False
  have complement_not_nine: "18 - s \<noteq> 9"
    using assms False by arith
  have defect:
    "comma_reset_signed_defect (18 - s) = comma_reset_signed_defect s"
    by (rule comma_reset_signed_defect_complement[OF assms])
  show ?thesis
    using False complement_not_nine defect
    by (simp add: comma_reset_germ_encode_def comma_reset_I_def comma_reset_R_def)
qed

text \<open>
For lower sums the signed defect is s-9; for upper sums it is 9-s.
These congruences connect the integer definition directly to the existing
F5 coordinate of `native_cocycle`, without reconstructing or enumerating
the nineteen possible sums.
\<close>

lemma comma_reset_signed_defect_below_residue:
  assumes "s < 9"
  shows "nat ((int s - 9) mod 5) = (s mod 5 + 1) mod 5"
proof -
  have residue: "(int s-9) mod 5=(int (s mod 5)+1) mod 5"
    unfolding diff_conv_add_uminus
    by (subst mod_add_eq[symmetric]; simp add: zmod_int)
  show ?thesis using arg_cong[OF residue, of nat]
    by (simp add: nat_mod_distrib nat_add_distrib)
qed

lemma comma_reset_signed_defect_above_residue:
  assumes "9 < s"
  shows "nat ((9 - int s) mod 5) = (4 - (s mod 5)) mod 5"
proof -
  have residue: "(9-int s) mod 5=(4-int (s mod 5)) mod 5"
    by (subst mod_diff_eq[symmetric]; simp add: zmod_int)
  have bound: "int (s mod 5)<5" by simp
  have nonnegative: "0\<le>4-int (s mod 5)" using bound by arith
  show ?thesis using arg_cong[OF residue, of nat] nonnegative
    by (simp add: nat_mod_distrib nat_diff_distrib)
qed

definition comma_reset_germ_from_native :: "native_cocycle \<Rightarrow> comma_reset_germ" where
  "comma_reset_germ_from_native q =
    (case q of (wire, alpha, parity) \<Rightarrow>
      (case wire of
        Below \<Rightarrow> Some ((alpha + 1) mod 5)
      | Equal \<Rightarrow> comma_reset_I
      | Above \<Rightarrow> Some ((4 - (alpha mod 5)) mod 5)))"

lemma comma_reset_germ_native_exact:
  assumes "s \<le> 18"
  shows "comma_reset_germ_from_native (encode_cocycle s) =
    comma_reset_germ_encode s"
proof (cases "s < 9")
  case True
  then show ?thesis
    by (simp add: comma_reset_germ_from_native_def comma_reset_germ_encode_def
        comma_reset_I_def comma_reset_R_def encode_cocycle_def domain_def
        comma_reset_signed_defect_def comma_reset_signed_defect_below_residue)
next
  case not_below: False
  show ?thesis
  proof (cases "s = 9")
    case True
    then show ?thesis
      by (simp add: comma_reset_germ_from_native_def comma_reset_germ_encode_def
          comma_reset_I_def comma_reset_R_def encode_cocycle_def domain_def)
  next
    case False
    have above: "9 < s" using not_below False by arith
    show ?thesis
      using above comma_reset_signed_defect_above_residue[OF above]
      by (simp add: comma_reset_germ_from_native_def comma_reset_germ_encode_def
          comma_reset_I_def comma_reset_R_def encode_cocycle_def domain_def
          comma_reset_signed_defect_def)
  qed
qed

text \<open>
The composition convention is `after` composed with `before`.  An identity
event preserves the previous germ; a reset event replaces it.  The neutral
wire therefore has no accumulated distance in this quotient.
\<close>

definition comma_reset_compose ::
    "comma_reset_germ \<Rightarrow> comma_reset_germ \<Rightarrow> comma_reset_germ" where
  "comma_reset_compose after before =
    (case after of None \<Rightarrow> before | Some eta \<Rightarrow> after)"

lemma comma_reset_compose_closed:
  assumes "a\<in>comma_reset_germ_carrier" "b\<in>comma_reset_germ_carrier"
  shows "comma_reset_compose a b\<in>comma_reset_germ_carrier"
  using assms by (cases a) (simp_all add: comma_reset_compose_def)

lemma comma_reset_compose_assoc:
  "comma_reset_compose a (comma_reset_compose b c) =
    comma_reset_compose (comma_reset_compose a b) c"
  by (cases a; cases b; cases c; simp add: comma_reset_compose_def)

lemma comma_reset_identity_left [simp]:
  "comma_reset_compose comma_reset_I g = g"
  by (simp add: comma_reset_compose_def comma_reset_I_def comma_reset_R_def)

lemma comma_reset_identity_right [simp]:
  "comma_reset_compose g comma_reset_I = g"
  by (cases g) (simp_all add: comma_reset_compose_def comma_reset_I_def comma_reset_R_def)

lemma comma_reset_compose_idempotent:
  "comma_reset_compose g g = g"
  by (cases g) (simp_all add: comma_reset_compose_def)

fun comma_reset_power :: "comma_reset_germ \<Rightarrow> nat \<Rightarrow> comma_reset_germ" where
  "comma_reset_power g 0 = comma_reset_I"
| "comma_reset_power g (Suc n) = comma_reset_compose g (comma_reset_power g n)"

lemma comma_reset_identity_run:
  "comma_reset_power comma_reset_I n = comma_reset_I"
  by (induction n) simp_all

lemma comma_reset_event_absorbs_prefix:
  "comma_reset_compose (comma_reset_R eta) prefix = comma_reset_R eta"
  by (simp add: comma_reset_compose_def comma_reset_R_def)

lemma comma_reset_event_after_neutral_run:
  "comma_reset_compose (comma_reset_R eta)
      (comma_reset_power comma_reset_I n) = comma_reset_R eta"
  by (simp add: comma_reset_identity_run)

lemma comma_last_non_neutral_reset_wins:
  "comma_reset_compose (comma_reset_R eta)
      (comma_reset_compose earlier prefix) = comma_reset_R eta"
  by (simp add: comma_reset_compose_def comma_reset_R_def)

text \<open>
This quotient records a canonical reset germ, not the complete output action.
In particular, complement-related sums have equal germs while their fixed
orientation carry actions and native F5 coordinates can differ.  Any later
erasure of the remaining native/F5 state requires a separate reconstruction
or dead-output theorem.
\<close>

lemma comma_reset_germ_is_not_complete_digit_state:
  "comma_reset_germ_encode 1 = comma_reset_germ_encode 17"
  "encode_cocycle 1 = (Below, 1, 1)"
  "encode_cocycle 17 = (Above, 2, 1)"
  "carry_apply (domain 1) False \<noteq> carry_apply (domain 17) False"
  "(1::nat) mod 10 \<noteq> 17 mod 10"
  by (simp_all add: comma_reset_germ_encode_def comma_reset_signed_defect_def
      comma_reset_I_def comma_reset_R_def encode_cocycle_def domain_def)

lemma comma_reset_germ_carry_complement_conjugacy:
  assumes "s \<le> 18"
  shows "carry_apply (domain (18 - s)) incoming =
    (\<not> carry_apply (domain s) (\<not> incoming))"
  by (rule decimal_pair_complement_carry[OF assms])

ML \<open>
  val checked = @{thms comma_reset_germ_carrier_card comma_reset_germ_encode_range
    comma_reset_germ_neutral_iff comma_reset_signed_defect_complement
    comma_reset_germ_complement comma_reset_signed_defect_below_residue
    comma_reset_signed_defect_above_residue comma_reset_germ_native_exact
    comma_reset_compose_closed comma_reset_compose_assoc comma_reset_identity_left comma_reset_identity_right
    comma_reset_compose_idempotent comma_reset_identity_run
    comma_reset_event_absorbs_prefix comma_reset_event_after_neutral_run
    comma_last_non_neutral_reset_wins comma_reset_germ_is_not_complete_digit_state
    comma_reset_germ_carry_complement_conjugacy};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reset germ proof depends on an oracle";
\<close>

end
