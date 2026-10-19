theory Temporal_Moment_Algebra
  imports Main
begin

text \<open>Source-aligned temporal moment laws.  These records compose exact
occurrences whose right endpoint is the next occurrence's left endpoint.
They do not select a recurrence branch, identify unrelated sources, or assert
that a moment word repeats because a finite border clock repeats.\<close>

record increment_moments =
  im_span :: nat
  im_sum :: int
  im_skew :: int

definition increment_moments_then ::
    "increment_moments \<Rightarrow> increment_moments \<Rightarrow>
      increment_moments" where
  "increment_moments_then first second =
    \<lparr>im_span = im_span first + im_span second,
      im_sum = im_sum first + im_sum second,
      im_skew = im_skew first + im_skew second +
        int (im_span second) * im_sum first\<rparr>"

definition increment_moments_weighted_exponent ::
    "int \<Rightarrow> increment_moments \<Rightarrow> int" where
  "increment_moments_weighted_exponent width action =
    int (im_span action) * (width - 1) + im_skew action"

lemma increment_moments_weighted_exponent_then:
  "increment_moments_weighted_exponent width
      (increment_moments_then first second) =
    increment_moments_weighted_exponent width first +
    increment_moments_weighted_exponent (width + im_sum first) second"
  by (cases first; cases second)
    (simp add: increment_moments_weighted_exponent_def
      increment_moments_then_def algebra_simps)

definition increment_moments_apply ::
    "increment_moments \<Rightarrow> int \<times> int \<Rightarrow> int \<times> int" where
  "increment_moments_apply action state =
    (fst state + int (im_span action) * snd state + im_skew action,
      snd state + im_sum action)"

theorem increment_moments_apply_then:
  "increment_moments_apply (increment_moments_then first second) state =
    increment_moments_apply second
      (increment_moments_apply first state)"
  by (cases state) (simp add: increment_moments_apply_def
      increment_moments_then_def algebra_simps)

theorem increment_moments_then_associative:
  "increment_moments_then (increment_moments_then first second) third =
    increment_moments_then first (increment_moments_then second third)"
  by (cases first; cases second; cases third)
    (simp add: increment_moments_then_def algebra_simps)

fun triangular_number :: "nat \<Rightarrow> nat" where
  "triangular_number 0 = 0"
| "triangular_number (Suc n) = n + triangular_number n"

lemma triangular_number_Suc:
  "triangular_number (Suc n) = triangular_number n + n"
  by simp

fun increment_moments_power :: "nat \<Rightarrow> increment_moments \<Rightarrow>
    increment_moments" where
  "increment_moments_power 0 action =
    \<lparr>im_span=0, im_sum=0, im_skew=0\<rparr>"
| "increment_moments_power (Suc n) action =
    increment_moments_then (increment_moments_power n action) action"

theorem increment_moments_power_closed:
  "increment_moments_power n action =
    \<lparr>im_span = n * im_span action,
      im_sum = int n * im_sum action,
      im_skew = int n * im_skew action +
        int (triangular_number n) * int (im_span action) * im_sum action\<rparr>"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
    using Suc.IH
    by (simp add: increment_moments_then_def triangular_number_Suc
        algebra_simps)
qed

text \<open>The endpoint matrix for a recurrence of the form
\(X_{i+1}=2R_i\) uses the last increment separately.  For two adjacent
nonempty intervals, the accumulated reverse increment \(U\) adds, while the
shortened moment \(H\) is the first interval's \(U\) plus the second
interval's \(H\).\<close>

record last_increment_moments =
  lim_span :: nat
  lim_sum :: int
  lim_shortened :: int

definition last_increment_moments_then ::
    "last_increment_moments \<Rightarrow> last_increment_moments \<Rightarrow>
      last_increment_moments" where
  "last_increment_moments_then first second =
    \<lparr>lim_span = lim_span first + lim_span second,
      lim_sum = lim_sum first + lim_sum second,
      lim_shortened = lim_sum first + lim_shortened second\<rparr>"

theorem last_increment_moments_then_associative:
  "last_increment_moments_then (last_increment_moments_then first second)
      third =
    last_increment_moments_then first
      (last_increment_moments_then second third)"
  by (cases first; cases second; cases third)
    (simp add: last_increment_moments_then_def algebra_simps)

definition last_increment_moments_apply ::
    "last_increment_moments \<Rightarrow> int \<times> int \<Rightarrow>
      int \<times> int" where
  "last_increment_moments_apply action state =
    (2 * (snd state + lim_shortened action),
      snd state + lim_sum action)"

theorem last_increment_moments_apply_then:
  "last_increment_moments_apply
      (last_increment_moments_then first second) state =
    last_increment_moments_apply second
      (last_increment_moments_apply first state)"
  by (cases state) (simp add: last_increment_moments_apply_def
      last_increment_moments_then_def algebra_simps)

text \<open>The two moment families deliberately have different composition
laws.  This prevents the reverse/add skew term from being reused as the
\(2rev10\) shortened endpoint moment.\<close>

ML \<open>
  val checked = @{thms increment_moments_apply_then
    increment_moments_weighted_exponent_then
    increment_moments_then_associative increment_moments_power_closed
    last_increment_moments_then_associative
    last_increment_moments_apply_then};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Temporal moment algebra depends on an oracle";
\<close>

end
