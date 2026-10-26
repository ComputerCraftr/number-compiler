theory Comma_Semantic_Weighted_Action
  imports Comma_Semantic_B1
begin

text \<open>
The weighted action form separates terminal control from elapsed complete
decades.  The first component of Stop_At is the within-decade position J and
the second is the accumulated complete-decade count H.  It is an observation
payload: callers must still authenticate the source root, phase, and guard.
\<close>

datatype comma_semantic_b1_weighted_result =
    Comma_Semantic_B1_Continue nat
  | Comma_Semantic_B1_Stop_At nat nat
  | Comma_Semantic_B1_Weighted_Invalid

fun comma_semantic_b1_weighted_encode ::
    "comma_semantic_b1_weighted_result \<Rightarrow> comma_semantic_b1_result" where
  "comma_semantic_b1_weighted_encode (Comma_Semantic_B1_Continue root) =
    Comma_Semantic_B1_Live root"
| "comma_semantic_b1_weighted_encode (Comma_Semantic_B1_Stop_At J H) =
    Comma_Semantic_B1_Stop (9*H+J)"
| "comma_semantic_b1_weighted_encode Comma_Semantic_B1_Weighted_Invalid =
    Comma_Semantic_B1_Invalid"

fun comma_semantic_b1_weighted_result_admitted ::
    "comma_semantic_b1_weighted_result \<Rightarrow> bool" where
  "comma_semantic_b1_weighted_result_admitted (Comma_Semantic_B1_Continue root) =
    (root<46)"
| "comma_semantic_b1_weighted_result_admitted (Comma_Semantic_B1_Stop_At J H) =
    (J<9)"
| "comma_semantic_b1_weighted_result_admitted Comma_Semantic_B1_Weighted_Invalid =
    False"

fun comma_semantic_b1_weighted_word_then ::
    "nat \<Rightarrow>
     (nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_weighted_result) \<Rightarrow>
     (nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_weighted_result) \<Rightarrow>
     nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_weighted_result" where
  "comma_semantic_b1_weighted_word_then n A B phase root =
    (case A phase root of
       Comma_Semantic_B1_Continue next_root \<Rightarrow>
         (case B ((phase+n) mod 924) next_root of
            Comma_Semantic_B1_Stop_At J H \<Rightarrow>
              Comma_Semantic_B1_Stop_At J (n+H)
          | result \<Rightarrow> result)
     | result \<Rightarrow> result)"

lemma comma_semantic_b1_weighted_word_then_encode:
  "comma_semantic_b1_weighted_encode
      (comma_semantic_b1_weighted_word_then n A B phase root) =
    comma_semantic_word_then n
      (\<lambda>r i. comma_semantic_b1_weighted_encode (A r i))
      (\<lambda>r i. comma_semantic_b1_weighted_encode (B r i)) phase root"
  by (cases "A phase root")
    (auto simp: comma_semantic_word_then_def algebra_simps
      split: comma_semantic_b1_weighted_result.splits
        comma_semantic_b1_result.splits)

lemma comma_semantic_b1_weighted_word_then_admitted:
  assumes first: "comma_semantic_b1_weighted_result_admitted (A phase root)"
    and second: "\<And>next_root. next_root<46 \<Longrightarrow>
      comma_semantic_b1_weighted_result_admitted
        (B ((phase+n) mod 924) next_root)"
  shows "comma_semantic_b1_weighted_result_admitted
      (comma_semantic_b1_weighted_word_then n A B phase root)"
proof (cases "A phase root")
  case (Comma_Semantic_B1_Continue next_root)
  have next_root_bound: "next_root<46"
    using first Comma_Semantic_B1_Continue by simp
  have next_result_admitted:
    "comma_semantic_b1_weighted_result_admitted
      (B ((phase+n) mod 924) next_root)"
    by (rule second[OF next_root_bound])
  note first_choice = Comma_Semantic_B1_Continue
  show ?thesis
  proof (cases "B ((phase+n) mod 924) next_root")
    case (Comma_Semantic_B1_Continue child)
    then show ?thesis
      using first_choice next_result_admitted
      by (simp add: comma_semantic_b1_weighted_word_then.simps)
  next
    case (Comma_Semantic_B1_Stop_At terminal height)
    then show ?thesis
      using first_choice next_result_admitted
      by (simp add: comma_semantic_b1_weighted_word_then.simps)
  next
    case Comma_Semantic_B1_Weighted_Invalid
    then show ?thesis
      using next_result_admitted by simp
  qed
next
  case (Comma_Semantic_B1_Stop_At terminal height)
  show ?thesis
    using first Comma_Semantic_B1_Stop_At
    by (simp add: comma_semantic_b1_weighted_word_then.simps)
next
  case Comma_Semantic_B1_Weighted_Invalid
  show ?thesis
    using first Comma_Semantic_B1_Weighted_Invalid by simp
qed

fun comma_semantic_b1_weighted_action_power ::
    "nat \<Rightarrow>
     (nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_weighted_result) \<Rightarrow>
     nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_weighted_result" where
  "comma_semantic_b1_weighted_action_power 0 action phase root = action phase root"
| "comma_semantic_b1_weighted_action_power (Suc k) action phase root =
    comma_semantic_b1_weighted_word_then (2^k)
      (comma_semantic_b1_weighted_action_power k action)
      (comma_semantic_b1_weighted_action_power k action) phase root"

fun comma_semantic_b1_action_power_from ::
    "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result) \<Rightarrow>
     nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result" where
  "comma_semantic_b1_action_power_from 0 action phase root = action phase root"
| "comma_semantic_b1_action_power_from (Suc k) action phase root =
    comma_semantic_word_then (2^k)
      (comma_semantic_b1_action_power_from k action)
      (comma_semantic_b1_action_power_from k action) phase root"

lemma comma_semantic_b1_weighted_action_power_encode:
  "comma_semantic_b1_weighted_encode
      (comma_semantic_b1_weighted_action_power k action phase root) =
    comma_semantic_b1_action_power_from k
      (\<lambda>r i. comma_semantic_b1_weighted_encode (action r i)) phase root"
  by (induction k arbitrary: phase root)
    (simp_all only: comma_semantic_b1_weighted_action_power.simps
      comma_semantic_b1_weighted_word_then_encode
      comma_semantic_b1_action_power_from.simps)

lemma comma_semantic_b1_weighted_action_power_admitted:
  assumes base: "\<And>phase root. phase<924 \<Longrightarrow> root<46 \<Longrightarrow>
      comma_semantic_b1_weighted_result_admitted (action phase root)"
    and phase: "phase<924" and root: "root<46"
  shows "comma_semantic_b1_weighted_result_admitted
      (comma_semantic_b1_weighted_action_power k action phase root)"
  using phase root
proof (induction k arbitrary: phase root)
  case 0
  then show ?case
    by (simp add: comma_semantic_b1_weighted_action_power.simps base)
next
  case (Suc k)
  have first:
    "comma_semantic_b1_weighted_result_admitted
      (comma_semantic_b1_weighted_action_power k action phase root)"
    by (rule Suc.IH[OF Suc.prems])
  have second:
    "\<And>next_root. next_root<46 \<Longrightarrow>
      comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_weighted_action_power k action
          ((phase+2^k) mod 924) next_root)"
  proof -
    fix next_root :: nat
    assume next_root: "next_root<46"
    have next_phase: "((phase+2^k) mod 924)<924" by simp
    show "comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_weighted_action_power k action
          ((phase+2^k) mod 924) next_root)"
      by (rule Suc.IH[OF next_phase next_root])
  qed
  show ?case
    unfolding comma_semantic_b1_weighted_action_power.simps
    by (rule comma_semantic_b1_weighted_word_then_admitted
      [where n="2^k"
        and A="comma_semantic_b1_weighted_action_power k action"
        and B="comma_semantic_b1_weighted_action_power k action"
        and phase=phase and root=root, OF first second])
qed

ML \<open>
  val checked = @{thms comma_semantic_b1_weighted_word_then_encode
    comma_semantic_b1_weighted_word_then_admitted
    comma_semantic_b1_weighted_action_power_encode
    comma_semantic_b1_weighted_action_power_admitted};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Weighted B1 action composition" checked;
\<close>

end
