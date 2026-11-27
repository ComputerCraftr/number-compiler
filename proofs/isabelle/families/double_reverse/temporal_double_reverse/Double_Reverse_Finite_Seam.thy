theory Double_Reverse_Finite_Seam
  imports Double_Reverse_Temporal_Refinement
begin

text \<open>Ordered radius-one acceptance is compositional only after the two
crossing digits on each side of a concatenation have been checked.\<close>

fun double_reverse_local_windows :: "('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "double_reverse_local_windows P [] = True"
| "double_reverse_local_windows P [x] = True"
| "double_reverse_local_windows P [x,y] = True"
| "double_reverse_local_windows P (x#y#z#rest) =
    (P x y z \<and> double_reverse_local_windows P (y#z#rest))"

lemma double_reverse_local_windows_take_two [simp]:
  "double_reverse_local_windows P (take 2 xs)"
proof (cases xs)
  case Nil
  then show ?thesis by simp
next
  case (Cons x rest)
  note xs = Cons
  show ?thesis
  proof (cases rest)
    case Nil
    then show ?thesis using xs by simp
  next
    case (Cons y ys)
    then show ?thesis using xs by (simp add: numeral_2_eq_2)
  qed
qed

theorem double_reverse_local_windows_append:
  "double_reverse_local_windows P (left @ right) \<longleftrightarrow>
    double_reverse_local_windows P left \<and> double_reverse_local_windows P right \<and>
    double_reverse_local_windows P
      (drop (length left - 2) left @ take 2 right)"
proof (induction left arbitrary: right)
  case Nil
  then show ?case by simp
next
  case (Cons a tail)
  note IH = Cons.IH
  show ?case
  proof (cases tail)
    case Nil
    note tail_nil = Nil
    show ?thesis
    proof (cases right)
      case Nil
      then show ?thesis using tail_nil by simp
    next
      case (Cons x xs)
      note right_cons = Cons
      show ?thesis
      proof (cases xs)
        case Nil
        then show ?thesis using tail_nil right_cons by (simp add: conj_ac)
      next
        case (Cons y ys)
        then show ?thesis using tail_nil right_cons by (simp add: conj_ac)
      qed
    qed
  next
    case (Cons b rest)
    note tail_eq = Cons
    show ?thesis
    proof (cases rest)
      case Nil
      note rest_nil = Nil
      show ?thesis
      proof (cases right)
        case Nil
        then show ?thesis using tail_eq rest_nil by simp
      next
        case (Cons x xs)
        note right_cons = Cons
        show ?thesis
        proof (cases xs)
          case Nil
          then show ?thesis using tail_eq rest_nil right_cons by (simp add: conj_ac)
        next
          case (Cons y ys)
          then show ?thesis using tail_eq rest_nil right_cons by (simp add: conj_ac)
        qed
      qed
    next
      case (Cons c more)
      have drop: "drop (length (a # b # c # more) - 2) (a # b # c # more) =
          drop (length (b # c # more) - 2) (b # c # more)"
        by simp
      show ?thesis using IH[of right] tail_eq Cons
        by (simp only: append_Cons double_reverse_local_windows.simps drop conj_ac)
    qed
  qed
qed

theorem double_reverse_local_windows_repeat_seam:
  "double_reverse_local_windows P (concat (replicate (Suc n) word)) \<longleftrightarrow>
    double_reverse_local_windows P word \<and>
    double_reverse_local_windows P (concat (replicate n word)) \<and>
    double_reverse_local_windows P
      (drop (length word - 2) word @ take 2 (concat (replicate n word)))"
  using double_reverse_local_windows_append[of P word "concat (replicate n word)"]
  by (simp only: replicate.simps concat.simps)

definition double_reverse_shift_predicate :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "double_reverse_shift_predicate choice l c r \<longleftrightarrow>
    double_reverse_t2_digit l c r = (if choice = 0 then l else if choice = 1 then c else r)"

theorem double_reverse_shift_windows_append:
  "double_reverse_local_windows (double_reverse_shift_predicate choice) (left @ right) \<longleftrightarrow>
    double_reverse_local_windows (double_reverse_shift_predicate choice) left \<and>
    double_reverse_local_windows (double_reverse_shift_predicate choice) right \<and>
    double_reverse_local_windows (double_reverse_shift_predicate choice)
      (drop (length left - 2) left @ take 2 right)"
  by (rule double_reverse_local_windows_append)

ML \<open>
  val checked = @{thms double_reverse_local_windows_append
    double_reverse_local_windows_repeat_seam double_reverse_shift_windows_append};
  val _ = if null (Thm_Deps.all_oracles checked) andalso not (Thm_Deps.has_skip_proof checked)
    then () else error "Double-reverse finite seam proof audit failed";
\<close>

end
