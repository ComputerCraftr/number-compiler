theory Double_Reverse_Four_Port_SLP_Repeat
  imports Double_Reverse_Group_Ring_Four_Port
begin

text \<open>This bridge gives the existing EMPTY/TERM/CONCAT/REPEAT source grammar
an exact four-port denotation.  REPEAT uses binary grammar doubling, so its
proof does not expand the repeated word.  The theorem is finite SLP semantics;
it grants no temporal-orbit or source-period authority.\<close>

type_synonym double_reverse_four_port_action =
  "nat \<Rightarrow> nat \<Rightarrow> double_reverse_four_port_row"

lemma double_reverse_source_repeat_word_append:
  "double_reverse_source_repeat_word word (first + second) =
    double_reverse_source_repeat_word word first @
      double_reverse_source_repeat_word word second"
  by (induction first) (simp_all add: append_assoc)

lemma double_reverse_source_repeat_word_doubled:
  "double_reverse_source_repeat_word (word @ word) count =
    double_reverse_source_repeat_word word (2 * count)"
proof (induction count)
  case 0
  then show ?case by simp
next
  case (Suc count)
  have split:
    "double_reverse_source_repeat_word word (2 * count + 2) =
      double_reverse_source_repeat_word word (2 * count) @
        double_reverse_source_repeat_word word 2"
    by (rule double_reverse_source_repeat_word_append)
  show ?case
    using Suc.IH split
    by (simp add: algebra_simps append_assoc)
qed

function double_reverse_four_port_binary_repeat ::
    "double_reverse_source_slp \<Rightarrow> nat \<Rightarrow> double_reverse_four_port_action"
  where
  "double_reverse_four_port_binary_repeat source count =
    (if count = 0 then double_reverse_four_port_action []
     else if even count then
       double_reverse_four_port_binary_repeat
         (Double_Reverse_Source_Concat source source) (count div 2)
     else
       double_reverse_four_port_then
         (double_reverse_four_port_action
           (double_reverse_source_slp_word source))
         (double_reverse_four_port_binary_repeat
           (Double_Reverse_Source_Concat source source) (count div 2)))"
  by pat_completeness auto
termination
  by (relation "measure snd") auto

declare double_reverse_four_port_binary_repeat.simps [simp del]

theorem double_reverse_four_port_binary_repeat_exact:
  "double_reverse_four_port_binary_repeat source count =
    double_reverse_four_port_action
      (double_reverse_source_repeat_word
        (double_reverse_source_slp_word source) count)"
proof (induction count arbitrary: source rule: less_induct)
  case (less count)
  show ?case
  proof (cases "count = 0")
    case True
    then show ?thesis
      by (subst double_reverse_four_port_binary_repeat.simps) simp
  next
    case False
    let ?half = "count div 2"
    let ?doubled = "Double_Reverse_Source_Concat source source"
    have half_less: "?half < count"
      using False by simp
    have recursive:
      "double_reverse_four_port_binary_repeat ?doubled ?half =
       double_reverse_four_port_action
         (double_reverse_source_repeat_word
           (double_reverse_source_slp_word ?doubled) ?half)"
      using less.IH[OF half_less, of ?doubled] .
    have word_double:
      "double_reverse_source_slp_word ?doubled =
        double_reverse_source_slp_word source @
          double_reverse_source_slp_word source"
      by simp
    have decompose:
      "count = 2 * ?half + count mod 2"
      by (metis div_mult_mod_eq mult.commute)
    have step:
      "double_reverse_four_port_binary_repeat source count =
       (if even count then
          double_reverse_four_port_binary_repeat ?doubled ?half
        else
          double_reverse_four_port_then
            (double_reverse_four_port_action
              (double_reverse_source_slp_word source))
            (double_reverse_four_port_binary_repeat ?doubled ?half))"
      using False
      by (subst double_reverse_four_port_binary_repeat.simps) simp
    show ?thesis
    proof (cases "even count")
      case True
      have remainder: "count mod 2 = 0"
        using True by (simp add: even_iff_mod_2_eq_zero)
      have count_even: "count = 2 * ?half"
        using decompose remainder by simp
      have even_step:
        "double_reverse_four_port_binary_repeat source count =
         double_reverse_four_port_binary_repeat ?doubled ?half"
        using step True by simp
      have even_count_transport:
        "double_reverse_four_port_action
           (double_reverse_source_repeat_word
             (double_reverse_source_slp_word source) (2 * ?half)) =
         double_reverse_four_port_action
           (double_reverse_source_repeat_word
             (double_reverse_source_slp_word source) count)"
        by (rule arg_cong[where
              f="\<lambda>n. double_reverse_four_port_action
                (double_reverse_source_repeat_word
                  (double_reverse_source_slp_word source) n)"])
          (rule count_even[symmetric])
      have "double_reverse_four_port_binary_repeat source count =
          double_reverse_four_port_binary_repeat ?doubled ?half"
        by (rule even_step)
      also have "... = double_reverse_four_port_action
          (double_reverse_source_repeat_word
            (double_reverse_source_slp_word ?doubled) ?half)"
        by (rule recursive)
      also have "... = double_reverse_four_port_action
          (double_reverse_source_repeat_word
            (double_reverse_source_slp_word source @
              double_reverse_source_slp_word source) ?half)"
        by (simp only: word_double)
      also have "... = double_reverse_four_port_action
          (double_reverse_source_repeat_word
            (double_reverse_source_slp_word source) (2 * ?half))"
        by (rule arg_cong[where f="double_reverse_four_port_action"])
          (rule double_reverse_source_repeat_word_doubled)
      also have "... = double_reverse_four_port_action
          (double_reverse_source_repeat_word
            (double_reverse_source_slp_word source) count)"
        by (rule even_count_transport)
      finally show ?thesis .
    next
      case False
      have remainder: "count mod 2 = 1"
        using False by (simp add: odd_iff_mod_2_eq_one)
      have count_odd: "count = 2 * ?half + 1"
        using decompose remainder by simp
      have odd_word:
        "double_reverse_source_repeat_word
            (double_reverse_source_slp_word source) count =
          double_reverse_source_slp_word source @
            double_reverse_source_repeat_word
              (double_reverse_source_slp_word source) (2 * ?half)"
      proof -
        have odd_count_transport:
          "double_reverse_source_repeat_word
             (double_reverse_source_slp_word source) count =
           double_reverse_source_repeat_word
             (double_reverse_source_slp_word source) (2 * ?half + 1)"
          by (rule arg_cong[where
                f="\<lambda>n. double_reverse_source_repeat_word
                  (double_reverse_source_slp_word source) n"])
            (rule count_odd)
        have odd_split_count: "2 * ?half + 1 = 1 + (2 * ?half)"
          by (simp add: add.commute)
        have odd_split_transport:
          "double_reverse_source_repeat_word
             (double_reverse_source_slp_word source) (2 * ?half + 1) =
           double_reverse_source_repeat_word
             (double_reverse_source_slp_word source) (1 + (2 * ?half))"
          by (rule arg_cong[where
                f="\<lambda>n. double_reverse_source_repeat_word
                  (double_reverse_source_slp_word source) n"])
            (rule odd_split_count)
        have "double_reverse_source_repeat_word
            (double_reverse_source_slp_word source) count =
          double_reverse_source_repeat_word
            (double_reverse_source_slp_word source) (2 * ?half + 1)"
          by (rule odd_count_transport)
        also have "... = double_reverse_source_repeat_word
            (double_reverse_source_slp_word source) (1 + (2 * ?half))"
          by (rule odd_split_transport)
        also have "... = double_reverse_source_repeat_word
            (double_reverse_source_slp_word source) 1 @
          double_reverse_source_repeat_word
            (double_reverse_source_slp_word source) (2 * ?half)"
          by (rule double_reverse_source_repeat_word_append)
        also have "... = double_reverse_source_slp_word source @
          double_reverse_source_repeat_word
            (double_reverse_source_slp_word source) (2 * ?half)"
          by simp
        finally show ?thesis .
      qed
      have odd_count_transport:
        "double_reverse_four_port_action
           (double_reverse_source_repeat_word
             (double_reverse_source_slp_word source) count) =
         double_reverse_four_port_action
           (double_reverse_source_repeat_word
             (double_reverse_source_slp_word source) (2 * ?half + 1))"
        by (rule arg_cong[where
              f="\<lambda>n. double_reverse_four_port_action
                (double_reverse_source_repeat_word
                  (double_reverse_source_slp_word source) n)"])
          (rule count_odd)
      have "double_reverse_four_port_binary_repeat source count =
          double_reverse_four_port_then
            (double_reverse_four_port_action
              (double_reverse_source_slp_word source))
            (double_reverse_four_port_binary_repeat ?doubled ?half)"
        using step False by simp
      also have "... = double_reverse_four_port_then
          (double_reverse_four_port_action
            (double_reverse_source_slp_word source))
          (double_reverse_four_port_action
            (double_reverse_source_repeat_word
              (double_reverse_source_slp_word ?doubled) ?half))"
        by (simp only: recursive)
      also have "... = double_reverse_four_port_then
          (double_reverse_four_port_action
            (double_reverse_source_slp_word source))
          (double_reverse_four_port_action
            (double_reverse_source_repeat_word
              (double_reverse_source_slp_word source @
                double_reverse_source_slp_word source) ?half))"
        by (simp only: word_double)
      also have "... = double_reverse_four_port_then
          (double_reverse_four_port_action
            (double_reverse_source_slp_word source))
          (double_reverse_four_port_action
            (double_reverse_source_repeat_word
              (double_reverse_source_slp_word source) (2 * ?half)))"
        by (simp only: double_reverse_source_repeat_word_doubled)
      also have "... = double_reverse_four_port_action
          (double_reverse_source_slp_word source @
            double_reverse_source_repeat_word
              (double_reverse_source_slp_word source) (2 * ?half))"
        by (rule double_reverse_four_port_action_append[symmetric])
      also have "... = double_reverse_four_port_action
          (double_reverse_source_repeat_word
            (double_reverse_source_slp_word source) count)"
        by (rule arg_cong[where f="double_reverse_four_port_action"])
          (rule odd_word[symmetric])
      finally show ?thesis .
    qed
  qed
qed

fun double_reverse_four_port_slp_action ::
    "double_reverse_source_slp \<Rightarrow> double_reverse_four_port_action"
  where
  "double_reverse_four_port_slp_action Double_Reverse_Source_Empty =
    double_reverse_four_port_action []"
| "double_reverse_four_port_slp_action (Double_Reverse_Source_Term digit) =
    double_reverse_four_port_action [digit]"
| "double_reverse_four_port_slp_action
      (Double_Reverse_Source_Concat left right) =
    double_reverse_four_port_then
      (double_reverse_four_port_slp_action left)
      (double_reverse_four_port_slp_action right)"
| "double_reverse_four_port_slp_action
      (Double_Reverse_Source_Repeat child count) =
    double_reverse_four_port_binary_repeat child count"

theorem double_reverse_four_port_slp_action_exact:
  "double_reverse_four_port_slp_action source =
    double_reverse_four_port_action
      (double_reverse_source_slp_word source)"
  by (induction source)
    (simp_all add: double_reverse_four_port_action_append
      double_reverse_four_port_binary_repeat_exact)

ML \<open>
  val checked = @{thms double_reverse_source_repeat_word_append
    double_reverse_source_repeat_word_doubled
    double_reverse_four_port_binary_repeat_exact
    double_reverse_four_port_slp_action_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Four-port SLP repetition depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped four-port SLP repetition proof" else ();
\<close>

end
