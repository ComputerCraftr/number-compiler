theory Ordered_Matrix_Program_Algebra
  imports Main
begin

text \<open>Column actions in chronological order. These laws concern supplied
words; they do not authorize repetition of a physical source trajectory.\<close>

datatype 'a ordered_matrix2 = Ordered_Matrix2 'a 'a 'a 'a

fun ordered_matrix2_multiply ::
  "'a::semiring_1 ordered_matrix2 \<Rightarrow> 'a ordered_matrix2 \<Rightarrow>
    'a ordered_matrix2" where
  "ordered_matrix2_multiply (Ordered_Matrix2 a b c d) (Ordered_Matrix2 e f g h) =
    Ordered_Matrix2 (a*e+b*g) (a*f+b*h) (c*e+d*g) (c*f+d*h)"

definition ordered_matrix2_identity :: "'a::semiring_1 ordered_matrix2" where
  "ordered_matrix2_identity = Ordered_Matrix2 1 0 0 1"

fun ordered_matrix2_apply ::
  "'a::semiring_1 ordered_matrix2 \<Rightarrow> 'a \<times> 'a \<Rightarrow>
    'a \<times> 'a" where
  "ordered_matrix2_apply (Ordered_Matrix2 a b c d) (p,q) =
    (a*p+b*q,c*p+d*q)"

lemma ordered_matrix2_multiply_associative:
  "ordered_matrix2_multiply (ordered_matrix2_multiply A B) C =
    ordered_matrix2_multiply A (ordered_matrix2_multiply B C)"
  by (cases A; cases B; cases C) (simp add: algebra_simps)

lemma ordered_matrix2_identity_left [simp]:
  "ordered_matrix2_multiply ordered_matrix2_identity A = A"
  by (cases A) (simp add: ordered_matrix2_identity_def)

lemma ordered_matrix2_identity_right [simp]:
  "ordered_matrix2_multiply A ordered_matrix2_identity = A"
  by (cases A) (simp add: ordered_matrix2_identity_def)

lemma ordered_matrix2_apply_identity [simp]:
  "ordered_matrix2_apply ordered_matrix2_identity v = v"
  by (cases v) (simp add: ordered_matrix2_identity_def)

lemma ordered_matrix2_apply_chronological:
  "ordered_matrix2_apply later (ordered_matrix2_apply earlier v) =
    ordered_matrix2_apply (ordered_matrix2_multiply later earlier) v"
  by (cases earlier; cases later; cases v) (simp add: algebra_simps)

fun ordered_matrix2_word ::
  "'a::semiring_1 ordered_matrix2 list \<Rightarrow> 'a ordered_matrix2" where
  "ordered_matrix2_word [] = ordered_matrix2_identity"
| "ordered_matrix2_word (first # later) =
    ordered_matrix2_multiply (ordered_matrix2_word later) first"

lemma ordered_matrix2_word_append:
  "ordered_matrix2_word (earlier @ later) =
    ordered_matrix2_multiply (ordered_matrix2_word later)
      (ordered_matrix2_word earlier)"
  by (induction earlier) (simp_all add: ordered_matrix2_multiply_associative)

lemma ordered_matrix2_word_execution:
  "ordered_matrix2_apply (ordered_matrix2_word word) v =
    fold ordered_matrix2_apply word v"
  by (induction word arbitrary: v)
    (simp_all add: ordered_matrix2_apply_chronological[symmetric])

fun ordered_matrix2_power ::
  "'a::semiring_1 ordered_matrix2 \<Rightarrow> nat \<Rightarrow> 'a ordered_matrix2" where
  "ordered_matrix2_power A 0 = ordered_matrix2_identity"
| "ordered_matrix2_power A (Suc n) =
    ordered_matrix2_multiply (ordered_matrix2_power A n) A"

lemma ordered_matrix2_word_repeat:
  "ordered_matrix2_word (concat (replicate n word)) =
    ordered_matrix2_power (ordered_matrix2_word word) n"
  by (induction n) (simp_all add: ordered_matrix2_word_append)

lemma ordered_matrix2_repeat_prefix:
  "ordered_matrix2_word (concat (replicate periods word) @ take remainder word) =
    ordered_matrix2_multiply (ordered_matrix2_word (take remainder word))
      (ordered_matrix2_power (ordered_matrix2_word word) periods)"
  by (simp add: ordered_matrix2_word_append ordered_matrix2_word_repeat)

lemma ordered_matrix2_prefix_remainder:
  "ordered_matrix2_word word =
    ordered_matrix2_multiply (ordered_matrix2_word (drop n word))
      (ordered_matrix2_word (take n word))"
  using ordered_matrix2_word_append[of "take n word" "drop n word"] by simp

definition ordered_matrix2_pullback ::
  "(('a::semiring_1 \<times> 'a) \<Rightarrow> 'b) \<Rightarrow>
    'a ordered_matrix2 \<Rightarrow> ('a \<times> 'a) \<Rightarrow> 'b" where
  "ordered_matrix2_pullback observer A v = observer (ordered_matrix2_apply A v)"

lemma ordered_matrix2_pullback_chronological:
  "ordered_matrix2_pullback (ordered_matrix2_pullback observer later) earlier =
    ordered_matrix2_pullback observer (ordered_matrix2_multiply later earlier)"
  by (rule ext)
    (simp add: ordered_matrix2_pullback_def ordered_matrix2_apply_chronological)

text \<open>The two spatial conventions use different sides of multiplication.
Appending an MSD-first digit to a spatial prefix is not chronological time.\<close>

lemma ordered_matrix2_lower_band_extension:
  "ordered_matrix2_word (lower @ [more_significant]) =
    ordered_matrix2_multiply more_significant (ordered_matrix2_word lower)"
  by (simp add: ordered_matrix2_word_append)

lemma ordered_matrix2_msd_prefix_extension:
  "ordered_matrix2_word (rev (prefix @ [next_digit])) =
    ordered_matrix2_multiply (ordered_matrix2_word (rev prefix)) next_digit"
  by simp

ML \<open>
  val checked = @{thms ordered_matrix2_multiply_associative
    ordered_matrix2_identity_left ordered_matrix2_identity_right
    ordered_matrix2_apply_identity ordered_matrix2_apply_chronological
    ordered_matrix2_word_append ordered_matrix2_word_execution
    ordered_matrix2_word_repeat ordered_matrix2_repeat_prefix
    ordered_matrix2_prefix_remainder ordered_matrix2_pullback_chronological
    ordered_matrix2_lower_band_extension ordered_matrix2_msd_prefix_extension};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Ordered matrix laws depend on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped ordered matrix proof" else ();
\<close>

end
