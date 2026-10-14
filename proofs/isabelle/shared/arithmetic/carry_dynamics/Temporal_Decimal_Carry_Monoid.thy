theory Temporal_Decimal_Carry_Monoid
  imports Shared_Carry_Tape
begin

text \<open>A threshold carry tape whose digit predicate resets the outgoing
carry independently of its incoming value.  Its weighted emission is the
decimal integer represented by the Boolean tape in most-significant-first
order.  This is the shared algebra used by source-specific digit machines;
it does not certify a recurrence or its selected branch word.\<close>

definition threshold5_domain :: "nat \<Rightarrow> carry_domain" where
  "threshold5_domain d = (if d < 5 then Below else Above)"

definition threshold5_bits :: "nat list \<Rightarrow> bool list" where
  "threshold5_bits ds = map (\<lambda>d. 5 \<le> d) ds"

lemma threshold5_carry_reset:
  "carry_apply (threshold5_domain d) incoming = (5 \<le> d)"
  by (simp add: threshold5_domain_def)

lemma threshold5_word_carry_reset:
  assumes nonempty: "ds \<noteq> []"
  shows "carry_finish incoming (map threshold5_domain ds) =
    (5 \<le> last ds)"
proof -
  obtain prefix d where split: "ds = prefix @ [d]"
    using nonempty by (metis append_butlast_last_id)
  show ?thesis
    using split
    by (simp add: carry_finish_append threshold5_carry_reset)
qed

fun threshold5_weight :: "nat list \<Rightarrow> nat" where
  "threshold5_weight [] = 0"
| "threshold5_weight (d # ds) =
    (if 5 \<le> d then 10 ^ length ds else 0) + threshold5_weight ds"

lemma threshold5_weight_append:
  "threshold5_weight (left @ right) =
    10 ^ length right * threshold5_weight left +
      threshold5_weight right"
proof (induction left)
  case Nil
  then show ?case by simp
next
  case (Cons d left)
  then show ?case
    by (simp add: algebra_simps power_add)
qed

fun threshold5_repeat_factor :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "threshold5_repeat_factor 0 width = 0"
| "threshold5_repeat_factor (Suc n) width =
    1 + 10 ^ width * threshold5_repeat_factor n width"

fun threshold5_repeat_word :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "threshold5_repeat_word 0 word = []"
| "threshold5_repeat_word (Suc n) word =
    threshold5_repeat_word n word @ word"

lemma threshold5_repeat_word_length:
  "length (threshold5_repeat_word n word) = n * length word"
  by (induction n) (simp_all add: algebra_simps)

theorem threshold5_weight_repeat:
  "threshold5_weight (threshold5_repeat_word n word) =
    threshold5_weight word *
      threshold5_repeat_factor n (length word)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have joined:
    "threshold5_weight
        (threshold5_repeat_word n word @ word) =
      10 ^ length word * threshold5_weight
        (threshold5_repeat_word n word) + threshold5_weight word"
    by (rule threshold5_weight_append)
  show ?case
    using joined Suc.IH
    by (simp add: algebra_simps)
qed

lemma threshold5_weight_foldl:
  "foldl (\<lambda>value bit. 10 * value + (if bit then 1 else 0))
      initial (threshold5_bits ds) =
    10 ^ length ds * initial + threshold5_weight ds"
proof (induction ds arbitrary: initial)
  case Nil
  then show ?case by (simp add: threshold5_bits_def)
next
  case (Cons digit ds)
  then show ?case
    by (simp add: threshold5_bits_def algebra_simps power_Suc)
qed

theorem threshold5_weight_is_bit_tape_value:
  "threshold5_weight ds =
    foldl (\<lambda>value bit. 10 * value + (if bit then 1 else 0))
      0 (threshold5_bits ds)"
  using threshold5_weight_foldl[of 0 ds] by simp

ML \<open>
  val checked = @{thms threshold5_carry_reset threshold5_word_carry_reset
    threshold5_weight_append threshold5_weight_repeat
    threshold5_weight_foldl threshold5_weight_is_bit_tape_value};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Temporal decimal carry algebra depends on an oracle";
\<close>

end
