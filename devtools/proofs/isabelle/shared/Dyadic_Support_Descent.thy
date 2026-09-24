theory Dyadic_Support_Descent
  imports Dyadic_Prefix_Summary
begin

text \<open>A finite tree models the retained chronological support used by the
production first-failure consumer.  A leaf word is the mathematical decoding
of one bounded branch-word integer; a join is a published support record.
The datatype is acyclic, so this theory does not silently admit forged support
IDs or a cyclic arena.  Source and action authority remain separate.\<close>

datatype 'label dyadic_support =
    Support_Leaf "'label list" nat nat int int
  | Support_Join "'label dyadic_support" "'label dyadic_support" nat nat int int

fun support_word :: "'label dyadic_support \<Rightarrow> 'label list" where
  "support_word (Support_Leaf word width events delta minimum) = word"
| "support_word (Support_Join left right width events delta minimum) =
    support_word left @ support_word right"

fun support_width :: "'label dyadic_support \<Rightarrow> nat" where
  "support_width (Support_Leaf word width events delta minimum) = width"
| "support_width (Support_Join left right width events delta minimum) = width"

fun support_events :: "'label dyadic_support \<Rightarrow> nat" where
  "support_events (Support_Leaf word width events delta minimum) = events"
| "support_events (Support_Join left right width events delta minimum) = events"

fun support_delta :: "'label dyadic_support \<Rightarrow> int" where
  "support_delta (Support_Leaf word width events delta minimum) = delta"
| "support_delta (Support_Join left right width events delta minimum) = delta"

fun support_minimum :: "'label dyadic_support \<Rightarrow> int" where
  "support_minimum (Support_Leaf word width events delta minimum) = minimum"
| "support_minimum (Support_Join left right width events delta minimum) = minimum"

fun support_valid :: "('label \<Rightarrow> int) \<Rightarrow> ('label \<Rightarrow> nat) \<Rightarrow>
    'label dyadic_support \<Rightarrow> bool" where
  "support_valid weight event (Support_Leaf word width events delta minimum) =
    (width = length word \<and> events = sum_list (map event word) \<and>
     (delta, minimum) = prefix_summary weight word)"
| "support_valid weight event (Support_Join left right width events delta minimum) =
    (support_valid weight event left \<and> support_valid weight event right \<and>
     width = support_width left + support_width right \<and>
     events = support_events left + support_events right \<and>
     delta = support_delta left + support_delta right \<and>
     minimum = min (support_minimum left)
       (support_delta left + support_minimum right))"

lemma support_valid_semantics:
  assumes "support_valid weight event tree"
  shows "support_width tree = length (support_word tree)"
    and "support_events tree = sum_list (map event (support_word tree))"
    and "(support_delta tree, support_minimum tree) =
      prefix_summary weight (support_word tree)"
  using assms
  by (induction tree) (auto simp: prefix_summary_append prod_eq_iff)

definition make_support_leaf :: "('label \<Rightarrow> int) \<Rightarrow>
    ('label \<Rightarrow> nat) \<Rightarrow> 'label list \<Rightarrow> 'label dyadic_support" where
  "make_support_leaf weight event word =
    (let summary = prefix_summary weight word in
      Support_Leaf word (length word) (sum_list (map event word))
        (fst summary) (snd summary))"

definition make_support_join :: "'label dyadic_support \<Rightarrow>
    'label dyadic_support \<Rightarrow> 'label dyadic_support" where
  "make_support_join left right =
    Support_Join left right
      (support_width left + support_width right)
      (support_events left + support_events right)
      (support_delta left + support_delta right)
      (min (support_minimum left)
        (support_delta left + support_minimum right))"

lemma make_support_leaf_valid [simp]:
  "support_valid weight event (make_support_leaf weight event word)"
  by (simp add: make_support_leaf_def Let_def)

lemma make_support_join_valid:
  assumes "support_valid weight event left"
    and "support_valid weight event right"
  shows "support_valid weight event (make_support_join left right)"
  using assms by (simp add: make_support_join_def)

text \<open>The constructor grammar publishes cached summaries inductively.
Its join does not scan either child word.  Only the bounded leaf scans its own
word; the production mapping must still establish that those words come from
the admitted source cylinder.\<close>

datatype 'label support_program =
    Program_Leaf "'label list"
  | Program_Join "'label support_program" "'label support_program"

fun construct_support :: "('label \<Rightarrow> int) \<Rightarrow>
    ('label \<Rightarrow> nat) \<Rightarrow> 'label support_program \<Rightarrow>
    'label dyadic_support" where
  "construct_support weight event (Program_Leaf word) =
    make_support_leaf weight event word"
| "construct_support weight event (Program_Join left right) =
    make_support_join (construct_support weight event left)
      (construct_support weight event right)"

lemma construct_support_valid [simp]:
  "support_valid weight event (construct_support weight event program)"
  by (induction program) (auto intro: make_support_join_valid)

lemma prefix_summary_minimum_le_delta:
  "snd (prefix_summary weight word) \<le> fst (prefix_summary weight word)"
proof (induction word)
  case Nil
  then show ?case by simp
next
  case (Cons a word)
  obtain delta minimum where pair:
      "prefix_summary weight word = (delta, minimum)"
    by (cases "prefix_summary weight word") auto
  from Cons.IH pair have "minimum \<le> delta" by simp
  then have "min 0 (weight a + minimum) \<le> weight a + delta"
    by linarith
  then show ?case by (simp add: Let_def pair)
qed

fun support_first_failure :: "('label \<Rightarrow> int) \<Rightarrow> int \<Rightarrow>
    'label dyadic_support \<Rightarrow> nat option" where
  "support_first_failure weight balance (Support_Leaf word width events delta minimum) =
    (if balance + minimum < 0 then first_negative weight balance word else None)"
| "support_first_failure weight balance
      (Support_Join left right width events delta minimum) =
    (if balance + minimum \<ge> 0 then None
     else if balance + support_minimum left < 0 then
       support_first_failure weight balance left
     else map_option (\<lambda>index. support_width left + index)
       (support_first_failure weight (balance + support_delta left) right))"

text \<open>The outer option rejects a malformed cached summary.  The inner
option is `None` exactly when a valid support has no negative prefix.\<close>

definition checked_support_first_failure :: "('label \<Rightarrow> int) \<Rightarrow>
    ('label \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> 'label dyadic_support \<Rightarrow>
    nat option option" where
  "checked_support_first_failure weight event balance tree =
    (if support_valid weight event tree then
      Some (support_first_failure weight balance tree) else None)"

theorem support_first_failure_exact:
  assumes valid: "support_valid weight event tree" and initial: "0 \<le> balance"
  shows "support_first_failure weight balance tree =
    first_negative weight balance (support_word tree)"
  using valid initial
proof (induction tree arbitrary: balance)
  case (Support_Leaf word width events delta minimum)
  then have summary: "minimum = snd (prefix_summary weight word)"
    by (auto simp: prod_eq_iff)
  show ?case
  proof (cases "balance + minimum < 0")
    case True
    then show ?thesis by simp
  next
    case False
    have safe: "prefix_guard weight balance word"
      using False summary by (simp add: prefix_summary_guard_iff)
    have iff: "first_negative weight balance word = None \<longleftrightarrow>
        prefix_guard weight balance word"
      by (rule first_negative_none_iff[OF Support_Leaf.prems(2)])
    have none: "first_negative weight balance word = None"
      using safe iff by simp
    show ?thesis using False none by simp
  qed
next
  case (Support_Join left right width events delta minimum)
  then have left_valid: "support_valid weight event left"
    and right_valid: "support_valid weight event right" by auto
  have full_summary: "minimum =
      snd (prefix_summary weight (support_word left @ support_word right))"
    using support_valid_semantics(3)[OF Support_Join.prems(1)]
    by (auto simp: prod_eq_iff)
  show ?case
  proof (cases "balance + minimum < 0")
    case False
    have safe: "prefix_guard weight balance
        (support_word left @ support_word right)"
      using False full_summary by (simp add: prefix_summary_guard_iff)
    have iff: "first_negative weight balance
        (support_word left @ support_word right) = None \<longleftrightarrow>
        prefix_guard weight balance
          (support_word left @ support_word right)"
      by (rule first_negative_none_iff[OF Support_Join.prems(2)])
    have none: "first_negative weight balance
        (support_word left @ support_word right) = None"
      using safe iff by simp
    show ?thesis using False none by simp
  next
    case True
    note unsafe = True
    have raw_descent: "first_negative weight balance
        (support_word left @ support_word right) =
      (if balance + snd (prefix_summary weight (support_word left)) < 0 then
         first_negative weight balance (support_word left)
       else map_option (\<lambda>index. length (support_word left) + index)
         (first_negative weight
           (balance + fst (prefix_summary weight (support_word left)))
           (support_word right)))"
      by (rule first_negative_descent[OF Support_Join.prems(2)])
    have descent: "first_negative weight balance
        (support_word left @ support_word right) =
      (if balance + support_minimum left < 0 then
         first_negative weight balance (support_word left)
       else map_option (\<lambda>index. support_width left + index)
         (first_negative weight
           (balance + support_delta left) (support_word right)))"
      using raw_descent support_valid_semantics[OF left_valid]
      by (simp add: prod_eq_iff)
    show ?thesis
    proof (cases "balance + support_minimum left < 0")
      case True
      with Support_Join.IH(1)[OF left_valid Support_Join.prems(2)]
        descent unsafe show ?thesis by simp
    next
      case False
      have right_initial: "0 \<le> balance + support_delta left"
        using False support_valid_semantics(3)[OF left_valid]
          prefix_summary_minimum_le_delta[of weight "support_word left"]
        by (auto simp: prod_eq_iff; linarith)
      with Support_Join.IH(2)[OF right_valid] False descent unsafe
        support_valid_semantics(1)[OF left_valid]
        show ?thesis by simp
    qed
  qed
qed

corollary checked_support_first_failure_exact:
  assumes "support_valid weight event tree" "0 \<le> balance"
  shows "checked_support_first_failure weight event balance tree =
    Some (first_negative weight balance (support_word tree))"
  using assms support_first_failure_exact
  by (simp add: checked_support_first_failure_def)

corollary constructed_support_first_failure_exact:
  assumes "0 \<le> balance"
  shows "support_first_failure weight balance
    (construct_support weight event program) =
    first_negative weight balance
      (support_word (construct_support weight event program))"
  by (rule support_first_failure_exact[
      OF construct_support_valid[of weight event program] assms])

lemma checked_support_rejects_malformed:
  assumes "\<not> support_valid weight event tree"
  shows "checked_support_first_failure weight event balance tree = None"
  using assms by (simp add: checked_support_first_failure_def)

lemma checked_support_rejects_wrong_leaf_minimum:
  assumes "wrong \<noteq> snd (prefix_summary weight word)"
  shows "checked_support_first_failure weight event balance
    (Support_Leaf word (length word) (sum_list (map event word))
      (fst (prefix_summary weight word)) wrong) = None"
  using assms by (auto simp: checked_support_first_failure_def prod_eq_iff)

text \<open>This is a finite support-consumer theorem.  It does not certify
Python handle authentication, ledger cleanup, cycle compression, physical TM
roofs, or the constructor that produces a valid tree.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms support_valid_semantics make_support_leaf_valid
      make_support_join_valid construct_support_valid
      prefix_summary_minimum_le_delta
      support_first_failure_exact checked_support_first_failure_exact
      constructed_support_first_failure_exact
      checked_support_rejects_malformed
      checked_support_rejects_wrong_leaf_minimum})
    then () else error "Dyadic support descent depends on an oracle";
\<close>
end
