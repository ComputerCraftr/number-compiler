theory Comma_Even_Port_Action
  imports Comma_Recursive_Pair_Language
    Comma_Entry_Port.Comma_Entry_Port_Refinement
begin

text \<open>The four sector-five aliases share complete even-block weights,
not endpoint digits or partial-block selection. The existing weighted action
owns the semantics; this theory neither defines another trace evaluator nor
promotes this local equality to decade or all-future branch safety.\<close>

lemma comma_sector_five_pair:
  assumes "1\<le>d" "d\<le>4"
  shows "comma_port_next 5 d=d+5"
    "comma_port_next 5 (d+5)=d"
    "comma_port_dwell 5 d+comma_port_dwell 5 (d+5)=2*d+6"
proof -
  have small: "d+5<10" using assms by arith
  have large: "d+5+10-5=d+10" by simp
  show "comma_port_next 5 d=d+5"
    using assms small by (simp add: comma_port_next_def comma_port_previous_def Let_def)
  show "comma_port_next 5 (d+5)=d"
    using assms small by (simp add: comma_port_next_def comma_port_previous_def Let_def)
  show "comma_port_dwell 5 d+comma_port_dwell 5 (d+5)=2*d+6"
    using assms by (auto simp: comma_port_dwell_def; arith)
qed

lemma comma_sector_five_two_actions:
  assumes "1\<le>d" "d\<le>4"
  shows "comma_port_action_power 5 2 (d,w)=(d,w+(2*d+6))"
    "comma_port_action_power 5 2 (d+5,w)=(d+5,w+(2*d+6))"
proof -
  have two: "(2::nat)=Suc (Suc 0)" by simp
  have low: "comma_port_next 5 d=d+5"
    and high: "comma_port_next 5 (d+5)=d"
    and weight: "comma_port_dwell 5 d+comma_port_dwell 5 (d+5)=2*d+6"
    using comma_sector_five_pair[OF assms] by auto
  show "comma_port_action_power 5 2 (d,w)=(d,w+(2*d+6))"
    by (simp only: comma_port_action_power_def two funpow.simps comp_apply
      id_apply comma_port_action_def fst_conv snd_conv low high; simp add: add.assoc weight)
  show "comma_port_action_power 5 2 (d+5,w)=(d+5,w+(2*d+6))"
    by (simp only: comma_port_action_power_def two funpow.simps comp_apply
      id_apply comma_port_action_def fst_conv snd_conv low high; simp add: add.assoc add.left_commute add.commute weight)
qed

lemma comma_sector_five_even_actions:
  assumes "1\<le>d" "d\<le>4"
  shows "comma_port_action_power 5 (2*n) (d,w)=(d,w+n*(2*d+6))"
    "comma_port_action_power 5 (2*n) (d+5,w)=(d+5,w+n*(2*d+6))"
proof -
  have step: "comma_port_action_power 5 (2*(Suc k)) s=
    comma_port_action_power 5 2 (comma_port_action_power 5 (2*k) s)" for k s
  proof -
    have index: "2*(Suc k)=2+2*k" by arith
    show ?thesis by (simp only: index comma_port_action_power_def funpow_add comp_apply)
  qed
  have both: "comma_port_action_power 5 (2*n) (d,w)=(d,w+n*(2*d+6)) \<and>
      comma_port_action_power 5 (2*n) (d+5,w)=(d+5,w+n*(2*d+6))"
  proof (induction n)
    case 0
    show ?case by (simp add: comma_port_action_power_def)
  next
    case (Suc n)
    have low: "comma_port_action_power 5 (2*n) (d,w)=(d,w+n*(2*d+6))"
      and high: "comma_port_action_power 5 (2*n) (d+5,w)=(d+5,w+n*(2*d+6))"
      using Suc.IH by auto
    show ?case
      by (simp only: step low high comma_sector_five_two_actions[OF assms];
        simp add: algebra_simps)
  qed
  show "comma_port_action_power 5 (2*n) (d,w)=(d,w+n*(2*d+6))"
    using both by blast
  show "comma_port_action_power 5 (2*n) (d+5,w)=(d+5,w+n*(2*d+6))"
    using both by blast
qed

lemma comma_even_alias_retains_occurrence:
  "snd (comma_port_action_power 5 (2*n) (1,0))=
    snd (comma_port_action_power 5 (2*n) (6,0))"
  "fst (comma_port_action_power 5 (2*n) (1,0))\<noteq>
    fst (comma_port_action_power 5 (2*n) (6,0))"
  "comma_port_dwell 5 1=1 \<and> comma_port_dwell 5 6=7"
  using comma_sector_five_even_actions[where d=1 and n=n and w=0]
  by (simp_all add: comma_port_dwell_def)

text \<open>A canonical local key absorbs only these even-block aliases.
This is a right congruence for the fixed-sector complete even response; it
makes no claim about partial selection or a later decade re-entry.\<close>

definition comma_even_port_digit :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_even_port_digit f d=(if f=5 \<and> 5<d then d-5 else d)"

definition comma_even_port_response :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<times>nat" where
  "comma_even_port_response f n d=
    (let r=comma_port_action_power f (2*n) (d,0)
      in (comma_even_port_digit f (fst r),snd r))"

lemma comma_even_port_key_aliases:
  assumes "d\<le>9" "e\<le>9"
    "comma_even_port_digit f d=comma_even_port_digit f e"
  shows "d=e \<or> (f=5 \<and> 1\<le>d \<and> d\<le>4 \<and> e=d+5) \<or>
    (f=5 \<and> 1\<le>e \<and> e\<le>4 \<and> d=e+5)"
  using assms by (auto simp: comma_even_port_digit_def split: if_splits; arith)

lemma comma_even_port_alias_response:
  assumes "1\<le>d" "d\<le>4"
  shows "comma_even_port_response 5 n d=comma_even_port_response 5 n (d+5)"
  by (simp only: comma_even_port_response_def comma_sector_five_even_actions[OF assms]
      Let_def fst_conv snd_conv;
    use assms in \<open>simp add: comma_even_port_digit_def\<close>)

theorem comma_even_port_key_right_congruence:
  assumes "d\<le>9" "e\<le>9"
    "comma_even_port_digit f d=comma_even_port_digit f e"
  shows "comma_even_port_response f n d=comma_even_port_response f n e"
proof -
  have cases: "d=e \<or> (f=5 \<and> 1\<le>d \<and> d\<le>4 \<and> e=d+5) \<or>
    (f=5 \<and> 1\<le>e \<and> e\<le>4 \<and> d=e+5)"
    by (rule comma_even_port_key_aliases[OF assms])
  then show ?thesis
    using comma_even_port_alias_response[where d=d and n=n]
      comma_even_port_alias_response[where d=e and n=n] by auto
qed

ML \<open>
  val checked = @{thms comma_sector_five_pair comma_sector_five_two_actions
    comma_sector_five_even_actions comma_even_alias_retains_occurrence
    comma_even_port_key_right_congruence};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Even port action depends on an oracle";
\<close>
end
