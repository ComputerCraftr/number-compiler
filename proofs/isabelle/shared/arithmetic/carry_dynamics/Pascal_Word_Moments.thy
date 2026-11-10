theory Pascal_Word_Moments
  imports Main
begin

text \<open>Finite MSB-first order-zero/order-one Pascal moments.  For a digit
word \<open>x\<close> with a caller-supplied Boolean marker \<open>h\<close>, the four
channels are \<open>D_r = \<Sum>i. (-1)^i * binom(i,r) * x_i\<close> and the
corresponding marker moments for \<open>h_i\<close>, at \<open>r=0,1\<close>.
The carrier stores exact structural length and endpoint markers; the moment
fields may be projected modulo eleven.  Concatenation and reflection below
are finite-word laws only.  They do not identify a recurrence successor or
authorize repetition of a source action.  Higher Pascal orders are used by
Python finite-word tests but are not refined by this Isabelle theory yet.\<close>

record 'a finite_pascal_moments =
  fpm_length :: nat
  fpm_digit0 :: 'a
  fpm_digit1 :: 'a
  fpm_marker0 :: 'a
  fpm_marker1 :: 'a
  fpm_first_marker :: "bool option"
  fpm_last_marker :: "bool option"

definition fpm_valid :: "'a::comm_ring_1 finite_pascal_moments \<Rightarrow> bool" where
  "fpm_valid word \<longleftrightarrow>
    (fpm_length word = 0 \<longrightarrow>
      fpm_digit0 word = 0 \<and> fpm_digit1 word = 0 \<and>
      fpm_marker0 word = 0 \<and> fpm_marker1 word = 0 \<and>
      fpm_first_marker word = None \<and> fpm_last_marker word = None) \<and>
    (fpm_length word > 0 \<longrightarrow>
      fpm_first_marker word \<noteq> None \<and>
      fpm_last_marker word \<noteq> None)"

definition fpm_empty :: "'a::comm_ring_1 finite_pascal_moments" where
  "fpm_empty =
    \<lparr>fpm_length=0, fpm_digit0=0, fpm_digit1=0,
      fpm_marker0=0, fpm_marker1=0,
      fpm_first_marker=None, fpm_last_marker=None\<rparr>"

definition fpm_symbol :: "'a::comm_ring_1 \<Rightarrow> bool \<Rightarrow>
    'a finite_pascal_moments" where
  "fpm_symbol digit high =
    \<lparr>fpm_length=1, fpm_digit0=digit, fpm_digit1=0,
      fpm_marker0=(if high then 1 else 0), fpm_marker1=0,
      fpm_first_marker=Some high, fpm_last_marker=Some high\<rparr>"

definition fpm_then :: "'a::comm_ring_1 finite_pascal_moments \<Rightarrow>
    'a finite_pascal_moments \<Rightarrow> 'a finite_pascal_moments" where
  "fpm_then first second =
    (let sign = (-1::'a) ^ fpm_length first in
      \<lparr>fpm_length = fpm_length first + fpm_length second,
       fpm_digit0 = fpm_digit0 first + sign * fpm_digit0 second,
       fpm_digit1 = fpm_digit1 first + sign *
         (of_nat (fpm_length first) * fpm_digit0 second + fpm_digit1 second),
       fpm_marker0 = fpm_marker0 first + sign * fpm_marker0 second,
       fpm_marker1 = fpm_marker1 first + sign *
         (of_nat (fpm_length first) * fpm_marker0 second + fpm_marker1 second),
       fpm_first_marker = (if fpm_length first = 0
         then fpm_first_marker second else fpm_first_marker first),
       fpm_last_marker = (if fpm_length second = 0
         then fpm_last_marker first else fpm_last_marker second)\<rparr>)"

lemma fpm_empty_valid [simp]: "fpm_valid fpm_empty"
  by (simp add: fpm_valid_def fpm_empty_def)

lemma fpm_symbol_valid [simp]: "fpm_valid (fpm_symbol digit high)"
  by (simp add: fpm_valid_def fpm_symbol_def)

lemma fpm_then_valid:
  assumes "fpm_valid first" "fpm_valid second"
  shows "fpm_valid (fpm_then first second)"
proof -
  obtain n1 d10 d11 m10 m11 f1 l1 where first:
    "first = \<lparr>fpm_length=n1, fpm_digit0=d10, fpm_digit1=d11,
      fpm_marker0=m10, fpm_marker1=m11,
      fpm_first_marker=f1, fpm_last_marker=l1\<rparr>"
    by (cases first) simp
  obtain n2 d20 d21 m20 m21 f2 l2 where second:
    "second = \<lparr>fpm_length=n2, fpm_digit0=d20, fpm_digit1=d21,
      fpm_marker0=m20, fpm_marker1=m21,
      fpm_first_marker=f2, fpm_last_marker=l2\<rparr>"
    by (cases second) simp
  show ?thesis using assms first second
    by (cases n1; cases n2; simp add: fpm_valid_def fpm_then_def Let_def)
qed

lemma fpm_empty_then_left:
  assumes "fpm_valid word"
  shows "fpm_then fpm_empty word = word"
proof -
  obtain n d0 d1 m0 m1 fm lm where word:
    "word = \<lparr>fpm_length=n, fpm_digit0=d0, fpm_digit1=d1,
      fpm_marker0=m0, fpm_marker1=m1,
      fpm_first_marker=fm, fpm_last_marker=lm\<rparr>"
    by (cases word) simp
  have valid: "fpm_valid \<lparr>fpm_length=n, fpm_digit0=d0, fpm_digit1=d1,
      fpm_marker0=m0, fpm_marker1=m1,
      fpm_first_marker=fm, fpm_last_marker=lm\<rparr>"
    using assms word by simp
  show ?thesis
  proof (cases n)
    case 0
    have zero_conjunction:
      "d0=0 \<and> d1=0 \<and> m0=0 \<and> m1=0 \<and> fm=None \<and> lm=None"
      using valid 0 by (simp add: fpm_valid_def)
    have zero_fields:
      "d0=0" "d1=0" "m0=0" "m1=0" "fm=None" "lm=None"
      using zero_conjunction by blast+
    show ?thesis using word zero_fields 0
      by (simp add: fpm_then_def fpm_empty_def Let_def)
  next
    case (Suc n')
    show ?thesis using word Suc
      by (simp add: fpm_then_def fpm_empty_def Let_def)
  qed
qed

lemma fpm_empty_then_right:
  assumes "fpm_valid word"
  shows "fpm_then word fpm_empty = word"
proof -
  obtain n d0 d1 m0 m1 fm lm where word:
    "word = \<lparr>fpm_length=n, fpm_digit0=d0, fpm_digit1=d1,
      fpm_marker0=m0, fpm_marker1=m1,
      fpm_first_marker=fm, fpm_last_marker=lm\<rparr>"
    by (cases word) simp
  have valid: "fpm_valid \<lparr>fpm_length=n, fpm_digit0=d0, fpm_digit1=d1,
      fpm_marker0=m0, fpm_marker1=m1,
      fpm_first_marker=fm, fpm_last_marker=lm\<rparr>"
    using assms word by simp
  show ?thesis
  proof (cases n)
    case 0
    have zero_conjunction:
      "d0=0 \<and> d1=0 \<and> m0=0 \<and> m1=0 \<and> fm=None \<and> lm=None"
      using valid 0 by (simp add: fpm_valid_def)
    have zero_fields:
      "d0=0" "d1=0" "m0=0" "m1=0" "fm=None" "lm=None"
      using zero_conjunction by blast+
    show ?thesis using word zero_fields 0
      by (simp add: fpm_then_def fpm_empty_def Let_def)
  next
    case (Suc n')
    show ?thesis using word Suc
      by (simp add: fpm_then_def fpm_empty_def Let_def)
  qed
qed

theorem fpm_then_associative:
  "fpm_then (fpm_then first second) third =
    fpm_then first (fpm_then second third)"
proof (rule finite_pascal_moments.equality)
  show "fpm_length (fpm_then (fpm_then first second) third) =
      fpm_length (fpm_then first (fpm_then second third))"
    by (simp add: fpm_then_def Let_def)
  show "fpm_digit0 (fpm_then (fpm_then first second) third) =
      fpm_digit0 (fpm_then first (fpm_then second third))"
    by (simp add: fpm_then_def Let_def power_add algebra_simps)
  show "fpm_digit1 (fpm_then (fpm_then first second) third) =
      fpm_digit1 (fpm_then first (fpm_then second third))"
    by (simp add: fpm_then_def Let_def power_add algebra_simps)
  show "fpm_marker0 (fpm_then (fpm_then first second) third) =
      fpm_marker0 (fpm_then first (fpm_then second third))"
    by (simp add: fpm_then_def Let_def power_add algebra_simps)
  show "fpm_marker1 (fpm_then (fpm_then first second) third) =
      fpm_marker1 (fpm_then first (fpm_then second third))"
    by (simp add: fpm_then_def Let_def power_add algebra_simps)
  show "fpm_first_marker (fpm_then (fpm_then first second) third) =
      fpm_first_marker (fpm_then first (fpm_then second third))"
    by (cases "fpm_length first=0"; cases "fpm_length second=0";
        cases "fpm_length third=0"; simp add: fpm_then_def Let_def)
  show "fpm_last_marker (fpm_then (fpm_then first second) third) =
      fpm_last_marker (fpm_then first (fpm_then second third))"
    by (cases "fpm_length first=0"; cases "fpm_length second=0";
        cases "fpm_length third=0"; simp add: fpm_then_def Let_def)
  show "more (fpm_then (fpm_then first second) third) =
      more (fpm_then first (fpm_then second third))"
    by (simp add: fpm_then_def Let_def)
qed

lemma fpm_then_order0:
  "fpm_digit0 (fpm_then first second) = fpm_digit0 first +
    (-1::'a::comm_ring_1) ^ fpm_length first * fpm_digit0 second"
  by (simp add: fpm_then_def Let_def)

lemma fpm_then_order1:
  "fpm_digit1 (fpm_then first second) = fpm_digit1 first +
    (-1::'a::comm_ring_1) ^ fpm_length first *
      (of_nat (fpm_length first) * fpm_digit0 second + fpm_digit1 second)"
  by (simp add: fpm_then_def Let_def)

lemma fpm_then_marker_order0:
  "fpm_marker0 (fpm_then first second) = fpm_marker0 first +
    (-1::'a::comm_ring_1) ^ fpm_length first * fpm_marker0 second"
  by (simp add: fpm_then_def Let_def)

lemma fpm_then_marker_order1:
  "fpm_marker1 (fpm_then first second) = fpm_marker1 first +
    (-1::'a::comm_ring_1) ^ fpm_length first *
      (of_nat (fpm_length first) * fpm_marker0 second + fpm_marker1 second)"
  by (simp add: fpm_then_def Let_def)

definition fpm_reflect :: "'a::comm_ring_1 finite_pascal_moments \<Rightarrow>
    'a finite_pascal_moments" where
  "fpm_reflect word =
    (if fpm_length word = 0 then word else
      (let sign = (-1::'a) ^ (fpm_length word - 1) in
        \<lparr>fpm_length = fpm_length word,
         fpm_digit0 = sign * fpm_digit0 word,
         fpm_digit1 = sign *
           (of_nat (fpm_length word - 1) * fpm_digit0 word - fpm_digit1 word),
         fpm_marker0 = sign * fpm_marker0 word,
         fpm_marker1 = sign *
           (of_nat (fpm_length word - 1) * fpm_marker0 word - fpm_marker1 word),
         fpm_first_marker = fpm_last_marker word,
         fpm_last_marker = fpm_first_marker word\<rparr>))"

lemma fpm_reflect_valid:
  assumes "fpm_valid word"
  shows "fpm_valid (fpm_reflect word)"
  using assms unfolding fpm_valid_def
  by (cases "fpm_length word=0") (simp_all add: fpm_reflect_def Let_def)

lemma fpm_valid_empty_eq:
  assumes valid: "fpm_valid word" and empty: "fpm_length word=0"
  shows "word=fpm_empty"
  using valid empty
  unfolding fpm_valid_def fpm_empty_def
  by (cases word) (simp_all)

lemma fpm_minus_one_even_power:
  "(-1::'a::comm_ring_1)^(2*n)=1"
  by (simp add: power_mult)

lemma fpm_reflect_symbol [simp]:
  "fpm_reflect (fpm_symbol digit high) = fpm_symbol digit high"
  by (simp add: fpm_reflect_def fpm_symbol_def Let_def)

lemma fpm_reflect_empty [simp]:
  "fpm_reflect fpm_empty = fpm_empty"
  by (simp add: fpm_reflect_def fpm_empty_def Let_def)

theorem fpm_reflect_then:
  assumes "fpm_valid first" "fpm_valid second"
  shows "fpm_reflect (fpm_then first second) =
    fpm_then (fpm_reflect second) (fpm_reflect first)"
proof -
  have first_reflect_valid: "fpm_valid (fpm_reflect first)"
    by (rule fpm_reflect_valid[OF assms(1)])
  have second_reflect_valid: "fpm_valid (fpm_reflect second)"
    by (rule fpm_reflect_valid[OF assms(2)])
  show ?thesis
  proof (cases "fpm_length first=0")
    case True
    have first_empty: "first=fpm_empty"
      by (rule fpm_valid_empty_eq[OF assms(1) True])
    have left: "fpm_then first second=second"
      by (simp add: first_empty fpm_empty_then_left[OF assms(2)])
    have right: "fpm_then (fpm_reflect second) (fpm_reflect first)=
        fpm_reflect second"
      using first_empty second_reflect_valid
      by (simp add: fpm_empty_then_right)
    show ?thesis using left right by simp
  next
    case first_nonempty: False
    show ?thesis
    proof (cases "fpm_length second=0")
      case True
      have second_empty: "second=fpm_empty"
        by (rule fpm_valid_empty_eq[OF assms(2) True])
      have left: "fpm_then first second=first"
        by (simp add: second_empty fpm_empty_then_right[OF assms(1)])
      have right: "fpm_then (fpm_reflect second) (fpm_reflect first)=
          fpm_reflect first"
        using second_empty first_reflect_valid
        by (simp add: fpm_empty_then_left)
      show ?thesis using left right by simp
    next
      case second_nonempty: False
      have first_positive: "0<fpm_length first"
        using first_nonempty by simp
      have second_positive: "0<fpm_length second"
        using second_nonempty by simp
      have outer_exponent:
        "fpm_length first + fpm_length second - 1 =
          fpm_length second + (fpm_length first - 1)"
        using first_positive by arith
      have sign_outer:
        "(-1::'a::comm_ring_1)^(fpm_length first + fpm_length second - 1) =
         (-1)^(fpm_length second) * (-1)^(fpm_length first - 1)"
        by (simp only: outer_exponent power_add)
      have sign_inner:
        "(-1::'a::comm_ring_1)^(fpm_length first + fpm_length second - 1) *
            (-1)^(fpm_length first) =
         (-1)^(fpm_length second - 1)"
      proof -
        have exponent:
          "(fpm_length first + fpm_length second - 1) + fpm_length first =
            (fpm_length second - 1) + 2 * fpm_length first"
          using second_positive by arith
        have product:
          "(-1::'a::comm_ring_1)^(fpm_length first + fpm_length second - 1) *
              (-1)^(fpm_length first) =
            (-1)^(fpm_length first + fpm_length second - 1 + fpm_length first)"
          by (simp only: power_add[symmetric])
        also have "... = (-1)^(fpm_length second - 1) *
              (-1)^(2 * fpm_length first)"
          by (simp only: exponent power_add)
        also have "... = (-1)^(fpm_length second - 1)"
          by (simp add: fpm_minus_one_even_power)
        finally show ?thesis .
      qed
      show ?thesis
      proof (rule finite_pascal_moments.equality)
        show "fpm_length (fpm_reflect (fpm_then first second)) =
            fpm_length (fpm_then (fpm_reflect second) (fpm_reflect first))"
          using first_positive second_positive
          by (simp add: fpm_reflect_def fpm_then_def Let_def)
        show "fpm_digit0 (fpm_reflect (fpm_then first second)) =
            fpm_digit0 (fpm_then (fpm_reflect second) (fpm_reflect first))"
          using sign_outer sign_inner first_positive second_positive
          by (simp add: fpm_reflect_def fpm_then_def Let_def algebra_simps)
        show "fpm_digit1 (fpm_reflect (fpm_then first second)) =
            fpm_digit1 (fpm_then (fpm_reflect second) (fpm_reflect first))"
          using sign_outer sign_inner first_positive second_positive
          by (simp add: fpm_reflect_def fpm_then_def Let_def algebra_simps)
        show "fpm_marker0 (fpm_reflect (fpm_then first second)) =
            fpm_marker0 (fpm_then (fpm_reflect second) (fpm_reflect first))"
          using sign_outer sign_inner first_positive second_positive
          by (simp add: fpm_reflect_def fpm_then_def Let_def algebra_simps)
        show "fpm_marker1 (fpm_reflect (fpm_then first second)) =
            fpm_marker1 (fpm_then (fpm_reflect second) (fpm_reflect first))"
          using sign_outer sign_inner first_positive second_positive
          by (simp add: fpm_reflect_def fpm_then_def Let_def algebra_simps)
        show "fpm_first_marker (fpm_reflect (fpm_then first second)) =
            fpm_first_marker (fpm_then (fpm_reflect second) (fpm_reflect first))"
          using first_positive second_positive
          by (simp add: fpm_reflect_def fpm_then_def Let_def)
        show "fpm_last_marker (fpm_reflect (fpm_then first second)) =
            fpm_last_marker (fpm_then (fpm_reflect second) (fpm_reflect first))"
          using first_positive second_positive
          by (simp add: fpm_reflect_def fpm_then_def Let_def)
        show "more (fpm_reflect (fpm_then first second)) =
            more (fpm_then (fpm_reflect second) (fpm_reflect first))"
          using first_positive second_positive
          by (simp add: fpm_reflect_def fpm_then_def Let_def)
      qed
    qed
  qed
qed

fun fpm_power :: "nat \<Rightarrow> 'a::comm_ring_1 finite_pascal_moments \<Rightarrow>
    'a finite_pascal_moments" where
  "fpm_power 0 word = fpm_empty"
| "fpm_power (Suc n) word = fpm_then (fpm_power n word) word"

lemma fpm_power_valid:
  assumes "fpm_valid word"
  shows "fpm_valid (fpm_power n word)"
  using assms by (induction n) (simp_all add: fpm_then_valid)

lemma fpm_power_suc:
  "fpm_power (Suc n) word = fpm_then (fpm_power n word) word"
  by simp

fun fpm_repeated_word :: "nat \<Rightarrow> (int \<times> bool) list \<Rightarrow>
    (int \<times> bool) list" where
  "fpm_repeated_word 0 word = []"
| "fpm_repeated_word (Suc n) word = fpm_repeated_word n word @ word"

fun fpm_of_word :: "(int \<times> bool) list \<Rightarrow> int finite_pascal_moments" where
  "fpm_of_word [] = fpm_empty"
| "fpm_of_word ((digit, high) # rest) =
    fpm_then (fpm_symbol digit high) (fpm_of_word rest)"

definition fpm_digit_sum0 :: "(int \<times> bool) list \<Rightarrow> int" where
  "fpm_digit_sum0 word =
    (\<Sum>i\<in>{0..<length word}. (-1::int)^i * fst (word ! i))"

definition fpm_digit_sum1 :: "(int \<times> bool) list \<Rightarrow> int" where
  "fpm_digit_sum1 word =
    (\<Sum>i\<in>{0..<length word}. (-1::int)^i * int i * fst (word ! i))"

definition fpm_marker_sum0 :: "(int \<times> bool) list \<Rightarrow> int" where
  "fpm_marker_sum0 word =
    (\<Sum>i\<in>{0..<length word}. (-1::int)^i *
      (if snd (word ! i) then 1 else 0))"

definition fpm_marker_sum1 :: "(int \<times> bool) list \<Rightarrow> int" where
  "fpm_marker_sum1 word =
    (\<Sum>i\<in>{0..<length word}. (-1::int)^i * int i *
      (if snd (word ! i) then 1 else 0))"

lemma fpm_digit_sum0_cons:
  "fpm_digit_sum0 ((digit, high) # rest) =
    digit - fpm_digit_sum0 rest"
  unfolding fpm_digit_sum0_def
  apply (simp only: length_Cons sum.atLeast0_lessThan_Suc_shift
      nth_Cons_0 nth_Cons_Suc)
  by (simp add: power_Suc algebra_simps sum.distrib sum_negf sum_subtractf)

lemma fpm_digit_sum1_cons:
  "fpm_digit_sum1 ((digit, high) # rest) =
    - fpm_digit_sum0 rest - fpm_digit_sum1 rest"
  unfolding fpm_digit_sum1_def fpm_digit_sum0_def
  apply (simp only: length_Cons sum.atLeast0_lessThan_Suc_shift
      nth_Cons_0 nth_Cons_Suc)
  by (simp add: power_Suc algebra_simps sum.distrib sum_negf sum_subtractf)

lemma fpm_marker_sum0_cons:
  "fpm_marker_sum0 ((digit, high) # rest) =
    (if high then 1 else 0) - fpm_marker_sum0 rest"
  unfolding fpm_marker_sum0_def
  apply (simp only: length_Cons sum.atLeast0_lessThan_Suc_shift
      nth_Cons_0 nth_Cons_Suc)
  by (simp add: power_Suc algebra_simps sum.distrib sum_negf sum_subtractf)

lemma fpm_marker_sum1_cons:
  "fpm_marker_sum1 ((digit, high) # rest) =
    - fpm_marker_sum0 rest - fpm_marker_sum1 rest"
  unfolding fpm_marker_sum1_def fpm_marker_sum0_def
  apply (simp only: length_Cons sum.atLeast0_lessThan_Suc_shift
      nth_Cons_0 nth_Cons_Suc)
  by (simp add: power_Suc algebra_simps sum.distrib sum_negf sum_subtractf)

lemma fpm_of_word_valid [simp]: "fpm_valid (fpm_of_word word)"
proof (induction word)
  case Nil
  then show ?case by simp
next
  case (Cons item rest)
  obtain digit high where item: "item=(digit,high)" by (cases item) auto
  show ?case
    using item Cons.IH fpm_then_valid[OF fpm_symbol_valid]
    by simp
qed

lemma fpm_of_word_order0:
  "fpm_digit0 (fpm_of_word ((digit, high) # rest)) =
      digit - fpm_digit0 (fpm_of_word rest)"
  by (simp add: fpm_then_def fpm_symbol_def Let_def)

lemma fpm_of_word_order1:
  "fpm_digit1 (fpm_of_word ((digit, high) # rest)) =
      - fpm_digit0 (fpm_of_word rest) - fpm_digit1 (fpm_of_word rest)"
  by (simp add: fpm_then_def fpm_symbol_def Let_def)

lemma fpm_of_word_marker_order0:
  "fpm_marker0 (fpm_of_word ((digit, high) # rest)) =
      (if high then 1 else 0) - fpm_marker0 (fpm_of_word rest)"
  by (simp add: fpm_then_def fpm_symbol_def Let_def)

lemma fpm_of_word_marker_order1:
  "fpm_marker1 (fpm_of_word ((digit, high) # rest)) =
      - fpm_marker0 (fpm_of_word rest) - fpm_marker1 (fpm_of_word rest)"
  by (simp add: fpm_then_def fpm_symbol_def Let_def)

theorem fpm_of_word_signed_positional_sums:
  "fpm_digit0 (fpm_of_word word) = fpm_digit_sum0 word \<and>
   fpm_digit1 (fpm_of_word word) = fpm_digit_sum1 word \<and>
   fpm_marker0 (fpm_of_word word) = fpm_marker_sum0 word \<and>
   fpm_marker1 (fpm_of_word word) = fpm_marker_sum1 word"
proof (induction word)
  case Nil
  then show ?case
    by (simp add: fpm_empty_def fpm_digit_sum0_def fpm_digit_sum1_def
      fpm_marker_sum0_def fpm_marker_sum1_def)
next
  case (Cons item rest)
  obtain digit high where item: "item=(digit,high)" by (cases item) auto
  have ih_digit0:
    "fpm_digit0 (fpm_of_word rest) = fpm_digit_sum0 rest"
    using Cons.IH by blast
  have ih_digit1:
    "fpm_digit1 (fpm_of_word rest) = fpm_digit_sum1 rest"
    using Cons.IH by blast
  have ih_marker0:
    "fpm_marker0 (fpm_of_word rest) = fpm_marker_sum0 rest"
    using Cons.IH by blast
  have ih_marker1:
    "fpm_marker1 (fpm_of_word rest) = fpm_marker_sum1 rest"
    using Cons.IH by blast
  have digit0:
    "fpm_digit0 (fpm_of_word ((digit,high)#rest)) =
      fpm_digit_sum0 ((digit,high)#rest)"
    by (simp only: fpm_of_word_order0 fpm_digit_sum0_cons ih_digit0)
  have digit1:
    "fpm_digit1 (fpm_of_word ((digit,high)#rest)) =
      fpm_digit_sum1 ((digit,high)#rest)"
    by (simp only: fpm_of_word_order1 fpm_digit_sum1_cons ih_digit0 ih_digit1)
  have marker0:
    "fpm_marker0 (fpm_of_word ((digit,high)#rest)) =
      fpm_marker_sum0 ((digit,high)#rest)"
    by (simp only: fpm_of_word_marker_order0 fpm_marker_sum0_cons ih_marker0)
  have marker1:
    "fpm_marker1 (fpm_of_word ((digit,high)#rest)) =
      fpm_marker_sum1 ((digit,high)#rest)"
    by (simp only: fpm_of_word_marker_order1 fpm_marker_sum1_cons
        ih_marker0 ih_marker1)
  show ?case
    using digit0 digit1 marker0 marker1 item
    by (simp only: item; blast)
qed

lemma fpm_of_word_append:
  "fpm_of_word (first @ second) =
    fpm_then (fpm_of_word first) (fpm_of_word second)"
proof (induction first)
  case Nil
  then show ?case by (simp add: fpm_empty_then_left fpm_of_word_valid)
next
  case (Cons item rest)
  obtain digit high where item: "item=(digit,high)" by (cases item) auto
  show ?case
    using item Cons.IH fpm_then_associative[symmetric]
    by simp
qed

theorem fpm_of_word_reflect:
  "fpm_of_word (rev word) = fpm_reflect (fpm_of_word word)"
proof (induction word)
  case Nil
  then show ?case by (simp add: fpm_reflect_def fpm_empty_def)
next
  case (Cons item rest)
  obtain digit high where item: "item = (digit, high)" by (cases item) auto
  have append:
    "fpm_of_word (rev rest @ [item]) =
      fpm_then (fpm_of_word (rev rest)) (fpm_symbol digit high)"
    using fpm_of_word_append[of "rev rest" "[item]"] item
    by (simp add: fpm_of_word.simps fpm_empty_then_right)
  show ?case
    using append Cons.IH item
    by (simp add: fpm_reflect_then fpm_reflect_symbol)
qed

definition fpm_mod11 :: "int finite_pascal_moments \<Rightarrow>
    int finite_pascal_moments" where
  "fpm_mod11 word =
    word\<lparr>fpm_digit0 := fpm_digit0 word mod 11,
      fpm_digit1 := fpm_digit1 word mod 11,
      fpm_marker0 := fpm_marker0 word mod 11,
      fpm_marker1 := fpm_marker1 word mod 11\<rparr>"

definition fpm_then_mod11 :: "int finite_pascal_moments \<Rightarrow>
    int finite_pascal_moments \<Rightarrow> int finite_pascal_moments" where
  "fpm_then_mod11 first second = fpm_mod11 (fpm_then first second)"

definition fpm_reflect_mod11 :: "int finite_pascal_moments \<Rightarrow>
    int finite_pascal_moments" where
  "fpm_reflect_mod11 word = fpm_mod11 (fpm_reflect word)"

lemma fpm_mod11_idempotent:
  "fpm_mod11 (fpm_mod11 word) = fpm_mod11 word"
  by (cases word) (simp add: fpm_mod11_def)

fun fpm_word_mod11 :: "(int \<times> bool) list \<Rightarrow>
    int finite_pascal_moments" where
  "fpm_word_mod11 [] = fpm_mod11 fpm_empty"
| "fpm_word_mod11 ((digit, high) # rest) =
    fpm_then_mod11 (fpm_mod11 (fpm_symbol digit high))
      (fpm_word_mod11 rest)"

lemma fpm_mod11_scaled_sum:
  fixes a x b :: int
  shows "(a mod 11 + x * (b mod 11)) mod 11 = (a + x * b) mod 11"
proof -
  have first: "(a mod 11) mod 11 = a mod 11" by simp
  have second: "(x * (b mod 11)) mod 11 = (x * b) mod 11"
    by (rule mod_mult_right_eq)
  show ?thesis by (rule mod_add_cong[OF first second])
qed

lemma fpm_mod11_nested_scaled_sum:
  fixes a x n b c :: int
  shows "(a mod 11 + x * (n * (b mod 11) + c mod 11)) mod 11 =
      (a + x * (n * b + c)) mod 11"
proof -
  have product: "(n * (b mod 11)) mod 11 = (n * b) mod 11"
    by (rule mod_mult_right_eq)
  have constant_mod: "(c mod 11) mod 11 = c mod 11" by simp
  have inside:
    "(n * (b mod 11) + c mod 11) mod 11 = (n * b + c) mod 11"
    by (rule mod_add_cong[OF product constant_mod])
  have outside: "(x * (n * (b mod 11) + c mod 11)) mod 11 =
      (x * (n * b + c)) mod 11"
    by (rule mod_mult_cong[OF refl inside])
  have first: "(a mod 11) mod 11 = a mod 11" by simp
  show ?thesis by (rule mod_add_cong[OF first outside])
qed

lemma fpm_mod11_nested_scaled_difference:
  fixes x n a b :: int
  shows "(x * (n * (a mod 11) - b mod 11)) mod 11 =
      (x * (n * a - b)) mod 11"
proof -
  have product: "(n * (a mod 11)) mod 11 = (n * a) mod 11"
    by (rule mod_mult_right_eq)
  have constant_mod: "(b mod 11) mod 11 = b mod 11" by simp
  have difference: "(n * (a mod 11) - b mod 11) mod 11 =
      (n * a - b) mod 11"
    by (rule mod_diff_cong[OF product constant_mod])
  show ?thesis by (rule mod_mult_cong[OF refl difference])
qed

theorem fpm_mod11_then:
  "fpm_mod11 (fpm_then first second) =
    fpm_then_mod11 (fpm_mod11 first) (fpm_mod11 second)"
proof (rule finite_pascal_moments.equality)
  have digit0_transfer:
    "(fpm_digit0 first + (-1::int) ^ fpm_length first *
        fpm_digit0 second) mod 11 =
      (fpm_digit0 first mod 11 + (-1::int) ^ fpm_length first *
        (fpm_digit0 second mod 11)) mod 11"
    by (rule fpm_mod11_scaled_sum[symmetric])
  have digit1_transfer:
    "(fpm_digit1 first + (-1::int) ^ fpm_length first *
        (int (fpm_length first) * fpm_digit0 second + fpm_digit1 second)) mod 11 =
      (fpm_digit1 first mod 11 + (-1::int) ^ fpm_length first *
        (int (fpm_length first) * (fpm_digit0 second mod 11) +
          fpm_digit1 second mod 11)) mod 11"
    by (rule fpm_mod11_nested_scaled_sum[symmetric])
  have marker0_transfer:
    "(fpm_marker0 first + (-1::int) ^ fpm_length first *
        fpm_marker0 second) mod 11 =
      (fpm_marker0 first mod 11 + (-1::int) ^ fpm_length first *
        (fpm_marker0 second mod 11)) mod 11"
    by (rule fpm_mod11_scaled_sum[symmetric])
  have marker1_transfer:
    "(fpm_marker1 first + (-1::int) ^ fpm_length first *
        (int (fpm_length first) * fpm_marker0 second + fpm_marker1 second)) mod 11 =
      (fpm_marker1 first mod 11 + (-1::int) ^ fpm_length first *
        (int (fpm_length first) * (fpm_marker0 second mod 11) +
          fpm_marker1 second mod 11)) mod 11"
    by (rule fpm_mod11_nested_scaled_sum[symmetric])
  show "fpm_length (fpm_mod11 (fpm_then first second)) =
      fpm_length (fpm_then_mod11 (fpm_mod11 first) (fpm_mod11 second))"
    by (simp add: fpm_mod11_def fpm_then_mod11_def fpm_then_def Let_def)
  show "fpm_digit0 (fpm_mod11 (fpm_then first second)) =
      fpm_digit0 (fpm_then_mod11 (fpm_mod11 first) (fpm_mod11 second))"
    using digit0_transfer
    by (simp add: fpm_mod11_def fpm_then_mod11_def fpm_then_order0 Let_def)
  show "fpm_digit1 (fpm_mod11 (fpm_then first second)) =
      fpm_digit1 (fpm_then_mod11 (fpm_mod11 first) (fpm_mod11 second))"
    using digit1_transfer
    by (simp add: fpm_mod11_def fpm_then_mod11_def fpm_then_order1 Let_def)
  show "fpm_marker0 (fpm_mod11 (fpm_then first second)) =
      fpm_marker0 (fpm_then_mod11 (fpm_mod11 first) (fpm_mod11 second))"
    using marker0_transfer
    by (simp add: fpm_mod11_def fpm_then_mod11_def fpm_then_marker_order0 Let_def)
  show "fpm_marker1 (fpm_mod11 (fpm_then first second)) =
      fpm_marker1 (fpm_then_mod11 (fpm_mod11 first) (fpm_mod11 second))"
    using marker1_transfer
    by (simp add: fpm_mod11_def fpm_then_mod11_def fpm_then_marker_order1 Let_def)
  show "fpm_first_marker (fpm_mod11 (fpm_then first second)) =
      fpm_first_marker (fpm_then_mod11 (fpm_mod11 first) (fpm_mod11 second))"
    by (simp add: fpm_mod11_def fpm_then_mod11_def fpm_then_def Let_def)
  show "fpm_last_marker (fpm_mod11 (fpm_then first second)) =
      fpm_last_marker (fpm_then_mod11 (fpm_mod11 first) (fpm_mod11 second))"
    by (simp add: fpm_mod11_def fpm_then_mod11_def fpm_then_def Let_def)
  show "more (fpm_mod11 (fpm_then first second)) =
      more (fpm_then_mod11 (fpm_mod11 first) (fpm_mod11 second))"
    by (simp add: fpm_mod11_def fpm_then_mod11_def fpm_then_def Let_def)
qed

theorem fpm_mod11_reflect:
  "fpm_mod11 (fpm_reflect word) = fpm_reflect_mod11 (fpm_mod11 word)"
  by (cases word)
    (simp add: fpm_mod11_def fpm_reflect_mod11_def fpm_reflect_def Let_def
      ac_simps mod_simps fpm_mod11_scaled_sum
      fpm_mod11_nested_scaled_difference split: if_splits)

theorem fpm_mod11_word:
  "fpm_mod11 (fpm_of_word word) = fpm_word_mod11 word"
proof (induction word)
  case Nil
  then show ?case by simp
next
  case (Cons item rest)
  obtain digit high where item: "item=(digit,high)" by (cases item) auto
  show ?case
    using item Cons.IH fpm_mod11_then[of "fpm_symbol digit high" "fpm_of_word rest"]
    by (simp add: fpm_then_mod11_def)
qed

lemma fpm_word_mod11_idempotent:
  "fpm_mod11 (fpm_word_mod11 word) = fpm_word_mod11 word"
proof -
  have "fpm_mod11 (fpm_word_mod11 word) =
      fpm_mod11 (fpm_mod11 (fpm_of_word word))"
    by (simp only: fpm_mod11_word[symmetric])
  also have "... = fpm_mod11 (fpm_of_word word)"
    by (rule fpm_mod11_idempotent)
  also have "... = fpm_word_mod11 word"
    by (rule fpm_mod11_word)
  finally show ?thesis .
qed

theorem fpm_word_mod11_append:
  "fpm_word_mod11 (first @ second) =
    fpm_then_mod11 (fpm_word_mod11 first) (fpm_word_mod11 second)"
proof -
  have exact:
    "fpm_of_word (first @ second) =
      fpm_then (fpm_of_word first) (fpm_of_word second)"
    by (rule fpm_of_word_append)
  have "fpm_word_mod11 (first @ second) =
      fpm_mod11 (fpm_of_word (first @ second))"
    by (rule fpm_mod11_word[symmetric])
  also have "... = fpm_then_mod11 (fpm_mod11 (fpm_of_word first))
        (fpm_mod11 (fpm_of_word second))"
    by (simp only: fpm_mod11_then exact)
  also have "... = fpm_then_mod11 (fpm_word_mod11 first)
        (fpm_word_mod11 second)"
    by (simp only: fpm_mod11_word)
  finally show ?thesis .
qed

theorem fpm_word_mod11_reflect:
  "fpm_word_mod11 (rev word) = fpm_reflect_mod11 (fpm_word_mod11 word)"
proof -
  have "fpm_word_mod11 (rev word) = fpm_mod11 (fpm_of_word (rev word))"
    by (rule fpm_mod11_word[symmetric])
  also have "... = fpm_mod11 (fpm_reflect (fpm_of_word word))"
    by (simp only: fpm_of_word_reflect)
  also have "... = fpm_reflect_mod11 (fpm_mod11 (fpm_of_word word))"
    by (rule fpm_mod11_reflect)
  also have "... = fpm_reflect_mod11 (fpm_word_mod11 word)"
    by (simp only: fpm_mod11_word)
  finally show ?thesis .
qed

fun fpm_power_mod11 :: "nat \<Rightarrow> int finite_pascal_moments \<Rightarrow>
    int finite_pascal_moments" where
  "fpm_power_mod11 0 word = fpm_mod11 fpm_empty"
| "fpm_power_mod11 (Suc n) word =
    fpm_then_mod11 (fpm_power_mod11 n word) (fpm_mod11 word)"

theorem fpm_mod11_power:
  "fpm_mod11 (fpm_power n word) = fpm_power_mod11 n (fpm_mod11 word)"
proof (induction n)
  case 0
  then show ?case by (simp only: fpm_power.simps fpm_power_mod11.simps)
next
  case (Suc n)
  then show ?case
    by (simp only: fpm_power_suc fpm_mod11_then
        fpm_power_mod11.simps fpm_mod11_idempotent)
qed

theorem fpm_word_mod11_repeat:
  "fpm_word_mod11 (fpm_repeated_word n word) =
    fpm_power_mod11 n (fpm_word_mod11 word)"
proof (induction n)
  case 0
  then show ?case by (simp only: fpm_repeated_word.simps fpm_word_mod11.simps
      fpm_power_mod11.simps)
next
  case (Suc n)
  then show ?case
    by (simp only: fpm_repeated_word.simps fpm_word_mod11_append
        fpm_power_mod11.simps fpm_word_mod11_idempotent)
qed

ML \<open>
  val checked = @{thms fpm_then_associative fpm_then_order0 fpm_then_order1
    fpm_then_marker_order0 fpm_then_marker_order1 fpm_reflect_then
    fpm_of_word_order0 fpm_of_word_order1 fpm_of_word_marker_order0
    fpm_of_word_marker_order1 fpm_of_word_signed_positional_sums
    fpm_of_word_append fpm_of_word_reflect fpm_power_suc
    fpm_mod11_idempotent fpm_mod11_then fpm_mod11_reflect fpm_mod11_word
    fpm_word_mod11_idempotent
    fpm_word_mod11_append fpm_word_mod11_reflect fpm_mod11_power
    fpm_word_mod11_repeat};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Finite Pascal word moments depend on an oracle";
\<close>

end
