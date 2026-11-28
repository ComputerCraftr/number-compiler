theory Comma_Symbolic_Writer
  imports Comma_Arithmetic.Comma_Literal_Path
begin

text \<open>A symbolic writer keeps only a source-bound endpoint, its physical
  duration, and a point observation. Composition descends into the selected
  child without constructing intermediate event or fragment lists. The
  family issuer must independently certify its source and chosen action.\<close>

record 's comma_symbolic_writer_action =
  comma_writer_advance :: "'s \<Rightarrow> 's"
  comma_writer_duration :: "'s \<Rightarrow> nat"
  comma_writer_point :: "'s \<Rightarrow> nat \<Rightarrow> nat"

definition comma_symbolic_writer_action_sound ::
    "('s \<Rightarrow> nat) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow>
      's comma_symbolic_writer_action \<Rightarrow> bool" where
  "comma_symbolic_writer_action_sound value admitted action \<longleftrightarrow>
    (\<forall>s. admitted s \<longrightarrow>
      admitted (comma_writer_advance action s) \<and>
      comma_writer_point action s 0 = value s \<and>
      comma_writer_point action s (comma_writer_duration action s) =
        value (comma_writer_advance action s) \<and>
      (\<forall>i\<le>comma_writer_duration action s.
        comma_literal_path i (value s) (comma_writer_point action s i) \<and>
        comma_literal_path (comma_writer_duration action s - i)
          (comma_writer_point action s i) (value (comma_writer_advance action s))))"

definition comma_symbolic_writer_then ::
    "'s comma_symbolic_writer_action \<Rightarrow> 's comma_symbolic_writer_action \<Rightarrow>
      's comma_symbolic_writer_action" where
  "comma_symbolic_writer_then left right =
    \<lparr>comma_writer_advance = (\<lambda>s. comma_writer_advance right (comma_writer_advance left s)),
     comma_writer_duration = (\<lambda>s. comma_writer_duration left s +
       comma_writer_duration right (comma_writer_advance left s)),
     comma_writer_point = (\<lambda>s i. if i \<le> comma_writer_duration left s
       then comma_writer_point left s i
       else comma_writer_point right (comma_writer_advance left s)
         (i - comma_writer_duration left s))\<rparr>"

lemma comma_symbolic_writer_then_sound:
  assumes left: "comma_symbolic_writer_action_sound value admitted left"
    and right: "comma_symbolic_writer_action_sound value admitted right"
  shows "comma_symbolic_writer_action_sound value admitted (comma_symbolic_writer_then left right)"
  unfolding comma_symbolic_writer_action_sound_def
proof (intro allI impI)
  fix s
  assume source: "admitted s"
  let ?middle = "comma_writer_advance left s"
  let ?a = "comma_writer_duration left s"
  let ?b = "comma_writer_duration right ?middle"
  have l: "admitted ?middle"
    "comma_writer_point left s 0 = value s"
    "comma_writer_point left s ?a = value ?middle"
    "\<And>i. i \<le> ?a \<Longrightarrow> comma_literal_path i (value s) (comma_writer_point left s i)"
    "\<And>i. i \<le> ?a \<Longrightarrow> comma_literal_path (?a-i) (comma_writer_point left s i) (value ?middle)"
    using left source by (auto simp: comma_symbolic_writer_action_sound_def)
  have r: "admitted (comma_writer_advance right ?middle)"
    "comma_writer_point right ?middle 0 = value ?middle"
    "comma_writer_point right ?middle ?b = value (comma_writer_advance right ?middle)"
    "\<And>i. i \<le> ?b \<Longrightarrow> comma_literal_path i (value ?middle) (comma_writer_point right ?middle i)"
    "\<And>i. i \<le> ?b \<Longrightarrow> comma_literal_path (?b-i) (comma_writer_point right ?middle i) (value (comma_writer_advance right ?middle))"
    using right l(1) by (auto simp: comma_symbolic_writer_action_sound_def)
  have whole_left: "comma_literal_path ?a (value s) (value ?middle)"
    using l(4)[of ?a] l(3) by simp
  have whole_right: "comma_literal_path ?b (value ?middle) (value (comma_writer_advance right ?middle))"
    using r(4)[of ?b] r(3) by simp
  have observation:
    "comma_literal_path i (value s) (comma_writer_point (comma_symbolic_writer_then left right) s i) \<and>
     comma_literal_path (?a+?b-i) (comma_writer_point (comma_symbolic_writer_then left right) s i)
       (value (comma_writer_advance right ?middle))" if limit: "i \<le> ?a+?b" for i
  proof (cases "i \<le> ?a")
    case True
    have tail: "comma_literal_path ((?a-i)+?b) (comma_writer_point left s i)
      (value (comma_writer_advance right ?middle))"
      by (rule comma_literal_path_append[OF l(5)[OF True] whole_right])
    show ?thesis using l(4)[OF True] tail True
      by (simp add: comma_symbolic_writer_then_def; arith)
  next
    case False
    have right_bound: "i-?a \<le> ?b" using limit False by arith
    have prefix: "comma_literal_path (?a+(i-?a)) (value s)
      (comma_writer_point right ?middle (i-?a))"
      by (rule comma_literal_path_append[OF whole_left r(4)[OF right_bound]])
    have prefix_length: "?a + (i-?a) = i" using False by arith
    have suffix_length: "?b - (i-?a) = ?a+?b-i" using False limit by arith
    have prefix_exact: "comma_literal_path i (value s)
      (comma_writer_point right ?middle (i-?a))"
      using prefix prefix_length by simp
    have suffix_exact: "comma_literal_path (?a+?b-i)
      (comma_writer_point right ?middle (i-?a))
      (value (comma_writer_advance right ?middle))"
      using r(5)[OF right_bound] suffix_length by simp
    show ?thesis using prefix_exact suffix_exact False
      by (simp add: comma_symbolic_writer_then_def)
  qed
  show "admitted (comma_writer_advance (comma_symbolic_writer_then left right) s) \<and>
    comma_writer_point (comma_symbolic_writer_then left right) s 0 = value s \<and>
    comma_writer_point (comma_symbolic_writer_then left right) s
      (comma_writer_duration (comma_symbolic_writer_then left right) s) =
      value (comma_writer_advance (comma_symbolic_writer_then left right) s) \<and>
    (\<forall>i\<le>comma_writer_duration (comma_symbolic_writer_then left right) s.
      comma_literal_path i (value s) (comma_writer_point (comma_symbolic_writer_then left right) s i) \<and>
      comma_literal_path (comma_writer_duration (comma_symbolic_writer_then left right) s-i)
        (comma_writer_point (comma_symbolic_writer_then left right) s i)
        (value (comma_writer_advance (comma_symbolic_writer_then left right) s)))"
    using l(2,3) r(1,2,3) observation
    by (auto simp: comma_symbolic_writer_then_def)
qed

definition comma_symbolic_writer_follows ::
    "(nat \<Rightarrow> nat) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow>
      's comma_symbolic_writer_action \<Rightarrow> bool" where
  "comma_symbolic_writer_follows choice admitted action \<longleftrightarrow>
    (\<forall>s. admitted s \<longrightarrow> (\<forall>i<comma_writer_duration action s.
      comma_writer_point action s (Suc i) = choice (comma_writer_point action s i)))"

lemma comma_symbolic_writer_then_follows:
  assumes left_sound: "comma_symbolic_writer_action_sound value admitted left"
    and right_sound: "comma_symbolic_writer_action_sound value admitted right"
    and left: "comma_symbolic_writer_follows choice admitted left"
    and right: "comma_symbolic_writer_follows choice admitted right"
  shows "comma_symbolic_writer_follows choice admitted (comma_symbolic_writer_then left right)"
  unfolding comma_symbolic_writer_follows_def
proof (intro allI impI)
  fix s i
  assume source: "admitted s"
    and bound: "i < comma_writer_duration (comma_symbolic_writer_then left right) s"
  let ?a = "comma_writer_duration left s"
  let ?middle = "comma_writer_advance left s"
  let ?b = "comma_writer_duration right ?middle"
  have middle: "admitted ?middle"
    and seam: "comma_writer_point left s ?a = value ?middle"
    using left_sound source by (auto simp: comma_symbolic_writer_action_sound_def)
  have zero: "comma_writer_point right ?middle 0 = value ?middle"
    using right_sound middle by (auto simp: comma_symbolic_writer_action_sound_def)
  have lstep: "i < ?a \<Longrightarrow>
      comma_writer_point left s (Suc i) = choice (comma_writer_point left s i)"
    using left source by (auto simp: comma_symbolic_writer_follows_def)
  have rstep: "\<And>j. j < ?b \<Longrightarrow> comma_writer_point right ?middle (Suc j) =
      choice (comma_writer_point right ?middle j)"
    using right middle by (auto simp: comma_symbolic_writer_follows_def)
  have total: "i < ?a + ?b" using bound by (simp add: comma_symbolic_writer_then_def)
  show "comma_writer_point (comma_symbolic_writer_then left right) s (Suc i) =
    choice (comma_writer_point (comma_symbolic_writer_then left right) s i)"
  proof (cases "i < ?a")
    case True
    then show ?thesis using lstep[OF True]
      by (simp add: comma_symbolic_writer_then_def)
  next
    case False
    have not_left: "\<not> i < ?a" by (rule False)
    show ?thesis
    proof (cases "i = ?a")
      case True
      have "0 < ?b" using total True by simp
      then show ?thesis using rstep[of 0] seam zero True
        by (simp add: comma_symbolic_writer_then_def)
    next
      case False
      have beyond: "?a < i" using not_left False by arith
      have remain: "i - ?a < ?b" using total beyond by arith
      have step: "Suc i - ?a = Suc (i-?a)" using beyond by arith
      show ?thesis using rstep[OF remain] beyond step
        by (simp add: comma_symbolic_writer_then_def)
    qed
  qed
qed

theorem comma_symbolic_writer_checked_cut:
  assumes checked: "comma_symbolic_writer_action_sound value admitted action"
    and source: "admitted s" and bound: "i \<le> comma_writer_duration action s"
  shows "comma_literal_path i (value s) (comma_writer_point action s i)"
    and "comma_literal_path (comma_writer_duration action s-i)
      (comma_writer_point action s i) (value (comma_writer_advance action s))"
  using checked source bound by (auto simp: comma_symbolic_writer_action_sound_def)

lemma comma_symbolic_writer_cut_left:
  "i \<le> comma_writer_duration left s \<Longrightarrow>
    comma_writer_point (comma_symbolic_writer_then left right) s i = comma_writer_point left s i"
  by (simp add: comma_symbolic_writer_then_def)

lemma comma_symbolic_writer_cut_right:
  "comma_writer_duration left s < i \<Longrightarrow>
    comma_writer_point (comma_symbolic_writer_then left right) s i =
      comma_writer_point right (comma_writer_advance left s) (i-comma_writer_duration left s)"
  by (simp add: comma_symbolic_writer_then_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms comma_symbolic_writer_then_sound
    comma_symbolic_writer_cut_left comma_symbolic_writer_cut_right
    comma_symbolic_writer_then_follows comma_symbolic_writer_checked_cut}) then ()
    else error "Symbolic writer laws used an oracle";
  val _ = if Thm_Deps.has_skip_proof @{thms comma_symbolic_writer_then_sound comma_symbolic_writer_cut_left comma_symbolic_writer_cut_right comma_symbolic_writer_then_follows comma_symbolic_writer_checked_cut} then
    error "Symbolic writer theorem used a skipped proof" else ();
\<close>

end
