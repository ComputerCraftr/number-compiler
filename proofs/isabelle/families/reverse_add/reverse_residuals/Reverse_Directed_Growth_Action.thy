theory Reverse_Directed_Growth_Action
  imports Reverse_Carry_Harmonic_Ports
    Shared_Carry_Dynamics.Port_Valued_Mealy
begin

text \<open>A supplied pair of reverse/add growth tapes has two independent
growth counters and a signed P/N diagonal. Each input bit shifts the finite
P/N masks and adds its growth to the corresponding counter. These results
prove the per-letter update and chronological count composition only; they do
not select future source bits or authorize a repeated physical input word.\<close>

type_synonym reverse_growth_letter = "bool \<times> bool"
type_synonym reverse_growth_mask = "nat \<times> nat"
type_synonym reverse_growth_count = "nat \<times> nat"

definition reverse_growth_count_add ::
    "reverse_growth_count \<Rightarrow> reverse_growth_count \<Rightarrow>
      reverse_growth_count" where
  "reverse_growth_count_add left right =
    (fst left + fst right, snd left + snd right)"

lemma reverse_growth_count_add_assoc:
  "reverse_growth_count_add (reverse_growth_count_add a b) c =
    reverse_growth_count_add a (reverse_growth_count_add b c)"
  by (cases a; cases b; cases c) (simp add: reverse_growth_count_add_def)

lemma reverse_growth_count_add_left_zero:
  "reverse_growth_count_add (0,0) count = count"
  by (cases count) (simp add: reverse_growth_count_add_def)

definition reverse_growth_mask_step ::
    "nat \<Rightarrow> reverse_growth_mask \<Rightarrow> reverse_growth_letter \<Rightarrow>
      reverse_growth_mask" where
  "reverse_growth_mask_step width state letter =
    ((2 * fst state + (if \<not> fst letter \<and> snd letter then 1 else 0)) mod 2^width,
     (2 * snd state + (if fst letter \<and> \<not> snd letter then 1 else 0)) mod 2^width)"

definition reverse_growth_letter_count ::
    "reverse_growth_letter \<Rightarrow> reverse_growth_count" where
  "reverse_growth_letter_count letter =
    (if fst letter then 1 else 0, if snd letter then 1 else 0)"

definition reverse_growth_letter_action ::
    "nat \<Rightarrow> reverse_growth_letter \<Rightarrow>
      (reverse_growth_mask, reverse_growth_count) partial_count_action" where
  "reverse_growth_letter_action width letter = \<lparr>
    partial_count_steps = 1,
    partial_count_run = (\<lambda>state.
      Some (reverse_growth_mask_step width state letter,
        reverse_growth_letter_count letter))\<rparr>"

definition reverse_growth_tape_action ::
    "nat \<Rightarrow> reverse_growth_letter list \<Rightarrow>
      (reverse_growth_mask, reverse_growth_count) partial_count_action" where
  "reverse_growth_tape_action width letters =
    partial_count_word reverse_growth_count_add (0,0)
      (map (reverse_growth_letter_action width) letters)"

fun reverse_growth_mask_run ::
    "nat \<Rightarrow> reverse_growth_letter list \<Rightarrow>
      reverse_growth_mask \<Rightarrow> reverse_growth_mask" where
  "reverse_growth_mask_run width [] state = state"
| "reverse_growth_mask_run width (letter # letters) state =
    reverse_growth_mask_run width letters
      (reverse_growth_mask_step width state letter)"

lemma reverse_growth_mask_shift_suffix_component:
  fixes x e power tail modulus :: nat
  shows "(((2*x + e) mod modulus) * power + tail) mod modulus =
    (x * (2*power) + ((e mod modulus) * power + tail) mod modulus)
      mod modulus"
proof -
  have scaled:
    "(((2*x + e) mod modulus) * power) mod modulus =
      ((2*x + e) * power) mod modulus"
    by (rule mod_mult_cong; simp)
  have shifted:
    "(((2*x + e) mod modulus) * power + tail) mod modulus =
      ((2*x + e) * power + tail) mod modulus"
    by (rule mod_add_cong[OF scaled refl])
  have digit_scaled:
    "(e * power) mod modulus = ((e mod modulus) * power) mod modulus"
    by (rule mod_mult_cong; simp)
  have replaced:
    "((x * (2*power) + e*power) + tail) mod modulus =
      ((x * (2*power) + (e mod modulus)*power) + tail) mod modulus"
  proof -
    have inner:
      "(x * (2*power) + e*power) mod modulus =
        (x * (2*power) + (e mod modulus)*power) mod modulus"
      by (rule mod_add_cong[OF refl digit_scaled])
    show ?thesis by (rule mod_add_cong[OF inner refl])
  qed
  have polynomial:
    "(2*x + e) * power + tail =
      ((x * (2*power) + e*power) + tail)"
    by (simp add: algebra_simps)
  have suffix_reduced:
    "(x * (2*power) + ((e mod modulus)*power + tail) mod modulus)
        mod modulus =
      (x * (2*power) + ((e mod modulus)*power + tail)) mod modulus"
    by (rule mod_add_cong[OF refl]) simp
  show ?thesis
    using shifted polynomial replaced suffix_reduced
    by (simp add: add.assoc)
qed

text \<open>The low-to-high mask update has the same shift/suffix form used by
the Python directed action: the old mask is shifted by the elapsed length,
then the suffix produced from zero state is added modulo the window. This is
an algebraic action on a supplied tape, not a claim that the tape repeats in
the source recurrence.\<close>

theorem reverse_growth_mask_run_shift_suffix:
  "fst initial_state < 2^width \<Longrightarrow>
   snd initial_state < 2^width \<Longrightarrow>
   reverse_growth_mask_run width letters initial_state =
     ((fst initial_state * 2^(length letters) +
        fst (reverse_growth_mask_run width letters (0,0))) mod 2^width,
      (snd initial_state * 2^(length letters) +
        snd (reverse_growth_mask_run width letters (0,0))) mod 2^width)"
proof (induction letters arbitrary: initial_state)
  case Nil
  then show ?case by (cases initial_state) simp
next
  case (Cons letter letters)
  have state_bounds:
    "fst (reverse_growth_mask_step width initial_state letter) < 2^width"
    "snd (reverse_growth_mask_step width initial_state letter) < 2^width"
    by (simp_all add: reverse_growth_mask_step_def)
  have zero_bounds:
    "fst (reverse_growth_mask_step width (0,0) letter) < 2^width"
    "snd (reverse_growth_mask_step width (0,0) letter) < 2^width"
    by (simp_all add: reverse_growth_mask_step_def)
  have state_run:
    "reverse_growth_mask_run width letters
        (reverse_growth_mask_step width initial_state letter) =
      ((fst (reverse_growth_mask_step width initial_state letter) *
          2^(length letters) +
          fst (reverse_growth_mask_run width letters (0,0))) mod 2^width,
       (snd (reverse_growth_mask_step width initial_state letter) *
          2^(length letters) +
          snd (reverse_growth_mask_run width letters (0,0))) mod 2^width)"
    using Cons.IH[of "reverse_growth_mask_step width initial_state letter"]
      state_bounds by simp
  have zero_run:
    "reverse_growth_mask_run width letters
        (reverse_growth_mask_step width (0,0) letter) =
      ((fst (reverse_growth_mask_step width (0,0) letter) *
          2^(length letters) +
          fst (reverse_growth_mask_run width letters (0,0))) mod 2^width,
       (snd (reverse_growth_mask_step width (0,0) letter) *
          2^(length letters) +
          snd (reverse_growth_mask_run width letters (0,0))) mod 2^width)"
    using Cons.IH[of "reverse_growth_mask_step width (0,0) letter"]
      zero_bounds by simp
  show ?case
    using state_run zero_run
    by (cases initial_state; cases letter;
        simp add: reverse_growth_mask_run.simps reverse_growth_mask_step_def
          reverse_growth_mask_shift_suffix_component power_Suc)
qed

theorem reverse_growth_letter_action_exact:
  "partial_count_run (reverse_growth_letter_action width letter) state =
    Some (reverse_growth_mask_step width state letter,
      reverse_growth_letter_count letter)"
  by (simp add: reverse_growth_letter_action_def)

theorem reverse_growth_tape_action_exact:
  "partial_count_run (reverse_growth_tape_action width letters) initial_state =
    Some (reverse_growth_mask_run width letters initial_state,
      (count_list (map fst letters) True,
       count_list (map snd letters) True))"
proof (induction letters arbitrary: initial_state)
  case Nil
  then show ?case
    by (simp add: reverse_growth_tape_action_def
        reverse_growth_mask_run.simps partial_count_identity_def)
next
  case (Cons letter letters)
  have head:
    "partial_count_run (reverse_growth_letter_action width letter) initial_state =
      Some (reverse_growth_mask_step width initial_state letter,
        reverse_growth_letter_count letter)"
    by (rule reverse_growth_letter_action_exact)
  have tail:
    "partial_count_run (reverse_growth_tape_action width letters)
        (reverse_growth_mask_step width initial_state letter) =
      Some (reverse_growth_mask_run width letters
          (reverse_growth_mask_step width initial_state letter),
        (count_list (map fst letters) True,
         count_list (map snd letters) True))"
    by (rule Cons.IH)
  show ?case
    using head tail
    by (simp add: reverse_growth_tape_action_def reverse_growth_count_add_def
        partial_count_then_def reverse_growth_letter_count_def
        reverse_growth_mask_run.simps split: prod.splits)
qed

theorem reverse_growth_tape_action_chronological:
  assumes prefix:
      "partial_count_run (reverse_growth_tape_action width prefix) initial =
        Some (middle, prefix_count)"
      and suffix:
      "partial_count_run (reverse_growth_tape_action width suffix) middle =
        Some (target, suffix_count)"
  shows "partial_count_run (reverse_growth_tape_action width (prefix @ suffix))
    initial = Some (target,
      reverse_growth_count_add prefix_count suffix_count)"
proof -
  have append:
    "reverse_growth_tape_action width (prefix @ suffix) =
      partial_count_then reverse_growth_count_add
        (reverse_growth_tape_action width prefix)
        (reverse_growth_tape_action width suffix)"
    unfolding reverse_growth_tape_action_def
    using partial_count_word_append[OF reverse_growth_count_add_assoc
        reverse_growth_count_add_left_zero,
        of "map (reverse_growth_letter_action width) prefix"
          "map (reverse_growth_letter_action width) suffix"]
    by (simp add: map_append)
  show ?thesis
    unfolding append
    by (rule partial_count_run_then_admitted[OF prefix suffix])
qed

theorem reverse_growth_diagonal_signed_count:
  "int (count_list
      (map (\<lambda>letter. \<not> fst letter \<and> snd letter) letters) True) -
    int (count_list
      (map (\<lambda>letter. fst letter \<and> \<not> snd letter) letters) True) =
    int (count_list (map snd letters) True) -
      int (count_list (map fst letters) True)"
proof (induction letters)
  case Nil
  then show ?case by simp
next
  case (Cons letter letters)
  obtain first second where letter: "letter = (first, second)"
    by (cases letter)
  show ?case
    using Cons.IH
    by (cases first; cases second;
        simp add: letter; linarith)
qed

corollary reverse_growth_tape_width_count:
  assumes run:
    "partial_count_run (reverse_growth_tape_action width letters) initial =
      Some (target, counts)"
  shows "(first_width + fst counts, second_width + snd counts) =
    (first_width + count_list (map fst letters) True,
     second_width + count_list (map snd letters) True)"
proof -
  have exact:
    "partial_count_run (reverse_growth_tape_action width letters) initial =
      Some (reverse_growth_mask_run width letters initial,
        (count_list (map fst letters) True,
         count_list (map snd letters) True))"
    by (rule reverse_growth_tape_action_exact)
  have pair:
    "(target, counts) = (reverse_growth_mask_run width letters initial,
      (count_list (map fst letters) True,
       count_list (map snd letters) True))"
  proof -
    have "Some (target, counts) =
        Some (reverse_growth_mask_run width letters initial,
          (count_list (map fst letters) True,
           count_list (map snd letters) True))"
      by (rule trans[OF run[symmetric] exact])
    then show ?thesis by simp
  qed
  show ?thesis using pair by simp
qed

ML \<open>
  val checked = @{thms reverse_growth_letter_action_exact
    reverse_growth_tape_action_exact reverse_growth_tape_action_chronological
    reverse_growth_mask_run_shift_suffix reverse_growth_diagonal_signed_count
    reverse_growth_tape_width_count};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reverse directed growth action depends on an oracle";
\<close>

end
