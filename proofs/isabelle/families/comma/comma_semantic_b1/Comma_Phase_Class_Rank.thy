theory Comma_Phase_Class_Rank
  imports Comma_Decade_Residual_Core.Comma_Decade_Residual_Core
begin

text \<open>
A phase-indexed class rank is a proof payload separate from the class
identifier.  The phase remains explicit at both ends of a continuation.
This generic bridge assumes a checked class transition and an exact source
control refinement; it does not construct or infer either certificate.
\<close>

datatype 'c comma_phase_class_action =
    Comma_Phase_Class_Invalid
  | Comma_Phase_Class_Fork nat nat
  | Comma_Phase_Class_Landmine nat
  | Comma_Phase_Class_Continue nat 'c

fun comma_phase_classify_decade_control ::
    "(nat \<Rightarrow> 'c) \<Rightarrow> comma_decade_outcome \<Rightarrow>
      'c comma_phase_class_action"
where
  "comma_phase_classify_decade_control class_of (Comma_Decade_Fork a d) =
    Comma_Phase_Class_Fork a d"
| "comma_phase_classify_decade_control class_of (Comma_Decade_Landmine d) =
    Comma_Phase_Class_Landmine d"
| "comma_phase_classify_decade_control class_of
      (Comma_Decade_Continue (Comma_Decade phase x)) =
    Comma_Phase_Class_Continue phase (class_of x)"
| "comma_phase_classify_decade_control class_of Comma_Decade_Invalid =
    Comma_Phase_Class_Invalid"

lemma comma_phase_classify_invalid_iff:
  "comma_phase_classify_decade_control class_of outcome =
      Comma_Phase_Class_Invalid \<longleftrightarrow>
    outcome = Comma_Decade_Invalid"
proof (cases outcome)
  case (Comma_Decade_Continue target)
  then show ?thesis by (cases target) simp
qed simp_all

lemma comma_phase_classify_continue_iff:
  "comma_phase_classify_decade_control class_of outcome =
      Comma_Phase_Class_Continue next_phase next_class \<longleftrightarrow>
    (\<exists>next_offset. outcome =
      Comma_Decade_Continue (Comma_Decade next_phase next_offset) \<and>
      next_class = class_of next_offset)"
proof (cases outcome)
  case (Comma_Decade_Continue target)
  then show ?thesis by (cases target) auto
qed auto

definition comma_phase_class_rank_check ::
    "(nat \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow>
     (nat \<Rightarrow> 'c \<Rightarrow> nat) \<Rightarrow>
     (nat \<Rightarrow> 'c \<Rightarrow> 'c comma_phase_class_action) \<Rightarrow> bool"
where
  "comma_phase_class_rank_check valid rank step \<longleftrightarrow>
    (\<forall>phase c. valid phase c \<longrightarrow>
      (case step phase c of
         Comma_Phase_Class_Invalid \<Rightarrow> False
       | Comma_Phase_Class_Fork a d \<Rightarrow> True
       | Comma_Phase_Class_Landmine d \<Rightarrow> True
       | Comma_Phase_Class_Continue next_phase next_class \<Rightarrow>
           valid next_phase next_class \<and>
           rank next_phase next_class < rank phase c))"

text \<open>
The bounded survival rank is a proof construction, not an asserted rank
table.  `survives n` records whether the first n actions are all Continue;
the rank is the cardinality of the surviving prefix lengths 1 through 26.
The only global termination obligation is that no admitted state has 27
consecutive Continue actions.  A source-specific consumer must still prove
that its concrete action agrees with this step and that admitted sources map
to valid classes.
\<close>

fun comma_phase_class_survives ::
    "(nat \<Rightarrow> 'c \<Rightarrow> 'c comma_phase_class_action) \<Rightarrow>
     nat \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> bool"
where
  "comma_phase_class_survives step 0 phase c = True"
| "comma_phase_class_survives step (Suc n) phase c =
    (case step phase c of
       Comma_Phase_Class_Continue next_phase next_class \<Rightarrow>
         comma_phase_class_survives step n next_phase next_class
     | _ \<Rightarrow> False)"

declare comma_phase_class_survives.simps [simp del]

lemma comma_phase_class_survives_continue:
  assumes move:
      "step phase c = Comma_Phase_Class_Continue next_phase next_class"
  shows "comma_phase_class_survives step (Suc n) phase c =
    comma_phase_class_survives step n next_phase next_class"
  using move
  by (cases "step phase c")
    (simp_all add: comma_phase_class_survives.simps)

definition comma_phase_class_survival_lengths ::
    "(nat \<Rightarrow> 'c \<Rightarrow> 'c comma_phase_class_action) \<Rightarrow>
     nat \<Rightarrow> 'c \<Rightarrow> nat set"
where
  "comma_phase_class_survival_lengths step phase c =
    {n. n \<in> {1..26} \<and> comma_phase_class_survives step n phase c}"

definition comma_phase_class_survival_rank ::
    "(nat \<Rightarrow> 'c \<Rightarrow> 'c comma_phase_class_action) \<Rightarrow>
     nat \<Rightarrow> 'c \<Rightarrow> nat"
where
  "comma_phase_class_survival_rank step phase c =
    card (comma_phase_class_survival_lengths step phase c)"

lemma comma_phase_class_survival_lengths_finite:
  "finite (comma_phase_class_survival_lengths step phase c)"
proof -
  have finite_range: "finite {1..26::nat}" by simp
  have subset:
    "comma_phase_class_survival_lengths step phase c \<subseteq> {1..26}"
    by (auto simp: comma_phase_class_survival_lengths_def)
  show ?thesis by (rule finite_subset[OF subset finite_range])
qed

lemma comma_phase_class_survival_rank_bound:
  "comma_phase_class_survival_rank step phase c \<le> 26"
proof -
  have finite_range: "finite {1..26::nat}" by simp
  have subset:
    "comma_phase_class_survival_lengths step phase c \<subseteq> {1..26}"
    by (auto simp: comma_phase_class_survival_lengths_def)
  have bounded:
    "card (comma_phase_class_survival_lengths step phase c) \<le> card {1..26::nat}"
    by (rule card_mono[OF finite_range subset])
  show ?thesis using bounded
    by (simp add: comma_phase_class_survival_rank_def)
qed

lemma comma_phase_class_survival_lengths_continue:
  assumes move:
      "step phase c = Comma_Phase_Class_Continue next_phase next_class"
    and no_27: "\<not> comma_phase_class_survives step 27 phase c"
  shows "comma_phase_class_survival_lengths step phase c =
    insert 1 (Suc ` comma_phase_class_survival_lengths step next_phase next_class)"
proof -
  have no_26_child:
    "\<not> comma_phase_class_survives step 26 next_phase next_class"
  proof -
    have first_step:
      "comma_phase_class_survives step 27 phase c =
        comma_phase_class_survives step 26 next_phase next_class"
    proof -
      have numeral: "27 = Suc 26" by simp
      show ?thesis
        unfolding numeral
        by (rule comma_phase_class_survives_continue
          [where step=step and phase=phase and c=c and n=26, OF move])
    qed
    show ?thesis using no_27 first_step by simp
  qed
  show ?thesis
  proof (rule set_eqI)
    fix n
    show "n \<in> comma_phase_class_survival_lengths step phase c \<longleftrightarrow>
        n \<in> insert 1
          (Suc ` comma_phase_class_survival_lengths step next_phase next_class)"
    proof (cases n)
      case 0
      then show ?thesis
        by (simp add: comma_phase_class_survival_lengths_def)
    next
      case (Suc k)
      note n_eq = Suc
      show ?thesis
      proof (cases k)
        case 0
        then show ?thesis
          using move n_eq
          by (simp add: comma_phase_class_survival_lengths_def
              comma_phase_class_survives.simps)
      next
        case (Suc j)
        note k_eq = Suc
        have parent_survival:
          "comma_phase_class_survives step (Suc (Suc j)) phase c =
            comma_phase_class_survives step (Suc j) next_phase next_class"
          by (rule comma_phase_class_survives_continue
            [where step=step and phase=phase and c=c and n="Suc j", OF move])
        have child_bound:
          "Suc j \<le> 26 \<Longrightarrow>
            comma_phase_class_survives step (Suc j) next_phase next_class
            \<Longrightarrow> Suc j \<le> 25"
        proof -
          assume bound: "Suc j \<le> 26"
            and survives: "comma_phase_class_survives step (Suc j)
              next_phase next_class"
          show "Suc j \<le> 25"
          proof (cases "Suc j = 26")
            case True
            then show ?thesis
              using survives no_26_child by simp
          next
            case False
            then show ?thesis using bound by arith
          qed
        qed
        then show ?thesis
          using move no_26_child n_eq k_eq parent_survival child_bound
          by (auto simp: comma_phase_class_survival_lengths_def)
      qed
    qed
  qed
qed

lemma comma_phase_class_survival_rank_continue:
  assumes move:
      "step phase c = Comma_Phase_Class_Continue next_phase next_class"
    and no_27: "\<not> comma_phase_class_survives step 27 phase c"
  shows "Suc (comma_phase_class_survival_rank step next_phase next_class) =
    comma_phase_class_survival_rank step phase c"
proof -
  have decomposition:
    "comma_phase_class_survival_lengths step phase c =
      insert 1 (Suc ` comma_phase_class_survival_lengths step next_phase next_class)"
    by (rule comma_phase_class_survival_lengths_continue
      [where step=step and phase=phase and c=c, OF move no_27])
  have child_finite:
    "finite (comma_phase_class_survival_lengths step next_phase next_class)"
    by (rule comma_phase_class_survival_lengths_finite)
  have one_not_shifted:
    "1 \<notin> Suc ` comma_phase_class_survival_lengths step next_phase next_class"
    by (auto simp: comma_phase_class_survival_lengths_def)
  have shifted_card:
    "card (Suc ` comma_phase_class_survival_lengths step next_phase next_class) =
      card (comma_phase_class_survival_lengths step next_phase next_class)"
  proof -
    have injective:
      "inj_on Suc (comma_phase_class_survival_lengths step next_phase next_class)"
      by (auto simp: inj_on_def)
    show ?thesis by (rule card_image[OF injective])
  qed
  show ?thesis
    using decomposition child_finite one_not_shifted shifted_card
    by (simp add: comma_phase_class_survival_rank_def card_insert_disjoint)
qed

lemma comma_phase_class_survival_rank_check:
  assumes no_invalid:
      "\<And>phase c. valid phase c \<Longrightarrow>
        step phase c \<noteq> Comma_Phase_Class_Invalid"
    and continue_closed:
      "\<And>phase c next_phase next_class. valid phase c \<Longrightarrow>
        step phase c = Comma_Phase_Class_Continue next_phase next_class
        \<Longrightarrow> valid next_phase next_class"
    and no_27:
      "\<And>phase c. valid phase c \<Longrightarrow>
        \<not> comma_phase_class_survives step 27 phase c"
  shows "comma_phase_class_rank_check valid
      (comma_phase_class_survival_rank step) step"
    and "\<And>phase c. valid phase c \<Longrightarrow>
      comma_phase_class_survival_rank step phase c \<le> 26"
proof -
  show "comma_phase_class_rank_check valid
      (comma_phase_class_survival_rank step) step"
    unfolding comma_phase_class_rank_check_def
  proof (intro allI impI)
    fix phase c
    assume state_valid: "valid phase c"
    show "case step phase c of
        Comma_Phase_Class_Invalid \<Rightarrow> False
      | Comma_Phase_Class_Fork a d \<Rightarrow> True
      | Comma_Phase_Class_Landmine d \<Rightarrow> True
      | Comma_Phase_Class_Continue next_phase next_class \<Rightarrow>
          valid next_phase next_class \<and>
          comma_phase_class_survival_rank step next_phase next_class <
            comma_phase_class_survival_rank step phase c"
    proof (cases "step phase c")
      case Comma_Phase_Class_Invalid
      then show ?thesis using no_invalid[OF state_valid] by simp
    next
      case (Comma_Phase_Class_Fork a d)
      then show ?thesis by simp
    next
      case (Comma_Phase_Class_Landmine d)
      then show ?thesis by simp
    next
      case (Comma_Phase_Class_Continue next_phase next_class)
      have target_valid: "valid next_phase next_class"
        by (rule continue_closed[OF state_valid Comma_Phase_Class_Continue])
      have descending:
        "Suc (comma_phase_class_survival_rank step next_phase next_class) =
          comma_phase_class_survival_rank step phase c"
        by (rule comma_phase_class_survival_rank_continue
          [where step=step and phase=phase and c=c,
           OF Comma_Phase_Class_Continue no_27[OF state_valid]])
      show ?thesis using Comma_Phase_Class_Continue target_valid descending by simp
    qed
  qed
  show "\<And>phase c. valid phase c \<Longrightarrow>
      comma_phase_class_survival_rank step phase c \<le> 26"
    by (rule comma_phase_class_survival_rank_bound)
qed

definition comma_decade_rank_from_phase_class ::
    "(nat \<Rightarrow> 'c) \<Rightarrow>
     (nat \<Rightarrow> 'c \<Rightarrow> nat) \<Rightarrow>
     comma_decade_state \<Rightarrow> nat"
where
  "comma_decade_rank_from_phase_class class_of rank s =
    (case s of Comma_Decade phase x \<Rightarrow> rank phase (class_of x))"

lemma comma_phase_class_rank_lifts_to_decade_rank_check:
  fixes class_of :: "nat \<Rightarrow> 'c"
    and valid :: "nat \<Rightarrow> 'c \<Rightarrow> bool"
    and rank :: "nat \<Rightarrow> 'c \<Rightarrow> nat"
    and step :: "nat \<Rightarrow> 'c \<Rightarrow> 'c comma_phase_class_action"
  assumes checked: "comma_phase_class_rank_check valid rank step"
    and source_valid: "\<And>phase x. comma_decade_admitted (Comma_Decade phase x) \<Longrightarrow>
      valid phase (class_of x)"
    and source_control: "\<And>phase x. comma_decade_admitted (Comma_Decade phase x) \<Longrightarrow>
      step phase (class_of x) = comma_phase_classify_decade_control class_of
        (comma_decade_control (Comma_Decade phase x))"
  shows "comma_decade_rank_check (comma_decade_rank_from_phase_class class_of rank)"
proof (unfold comma_decade_rank_check_def, intro allI impI)
  fix s
  assume admitted: "comma_decade_admitted s"
  obtain phase x where state: "s = Comma_Decade phase x"
    by (cases s) auto
  have source_admitted: "comma_decade_admitted (Comma_Decade phase x)"
    using admitted state by simp
  have class_ok: "valid phase (class_of x)"
    by (rule source_valid[OF source_admitted])
  have row:
    "case step phase (class_of x) of
       Comma_Phase_Class_Invalid \<Rightarrow> False
       | Comma_Phase_Class_Fork a d \<Rightarrow> True
       | Comma_Phase_Class_Landmine d \<Rightarrow> True
     | Comma_Phase_Class_Continue next_phase next_class \<Rightarrow>
         valid next_phase next_class \<and>
         rank next_phase next_class < rank phase (class_of x)"
    using checked class_ok
    by (simp add: comma_phase_class_rank_check_def)
  have exact_step:
    "step phase (class_of x) = comma_phase_classify_decade_control class_of
      (comma_decade_control (Comma_Decade phase x))"
    by (rule source_control[OF source_admitted])
  show "case comma_decade_control s of
      Comma_Decade_Continue q \<Rightarrow>
        comma_decade_admitted q \<and>
          comma_decade_rank_from_phase_class class_of rank q <
            comma_decade_rank_from_phase_class class_of rank s
    | Comma_Decade_Invalid \<Rightarrow> False
    | _ \<Rightarrow> True"
  proof (cases "comma_decade_control (Comma_Decade phase x)")
    case (Comma_Decade_Fork a d)
    then show ?thesis
      using exact_step row state
      by (simp add: comma_decade_rank_from_phase_class_def)
  next
    case (Comma_Decade_Landmine d)
    then show ?thesis
      using exact_step row state
      by (simp add: comma_decade_rank_from_phase_class_def)
  next
    case (Comma_Decade_Continue q)
    obtain next_phase next_x where target: "q = Comma_Decade next_phase next_x"
      by (cases q) auto
    have target_admitted: "comma_decade_admitted q"
      by (rule comma_decade_control_closed(2)[OF source_admitted Comma_Decade_Continue]; simp)
    have class_target:
      "valid next_phase (class_of next_x) \<and>
        rank next_phase (class_of next_x) < rank phase (class_of x)"
      using row exact_step Comma_Decade_Continue target by simp
    show ?thesis
      using target_admitted class_target Comma_Decade_Continue target state
      by (simp add: comma_decade_rank_from_phase_class_def)
  next
    case Comma_Decade_Invalid
    have invalid: "False"
      using row exact_step Comma_Decade_Invalid by simp
    then show ?thesis by simp
  qed
qed

lemma comma_phase_class_rank_bound_lifts:
  fixes class_of :: "nat \<Rightarrow> 'c"
    and valid :: "nat \<Rightarrow> 'c \<Rightarrow> bool"
    and rank :: "nat \<Rightarrow> 'c \<Rightarrow> nat"
  assumes source_valid: "\<And>phase x. comma_decade_admitted (Comma_Decade phase x) \<Longrightarrow>
      valid phase (class_of x)"
    and bounded: "\<And>phase c. valid phase c \<Longrightarrow> rank phase c \<le> 26"
  shows "comma_decade_admitted s \<Longrightarrow>
      comma_decade_rank_from_phase_class class_of rank s \<le> 26"
proof -
  assume admitted: "comma_decade_admitted s"
  obtain phase x where state: "s = Comma_Decade phase x"
    by (cases s) auto
  have source_admitted: "comma_decade_admitted (Comma_Decade phase x)"
    using admitted state by simp
  have class_ok: "valid phase (class_of x)"
    by (rule source_valid[OF source_admitted])
  show "comma_decade_rank_from_phase_class class_of rank s \<le> 26"
    using bounded[OF class_ok] state
    by (simp add: comma_decade_rank_from_phase_class_def)
qed

theorem comma_phase_class_rank_B32:
  fixes class_of :: "nat \<Rightarrow> 'c"
    and valid :: "nat \<Rightarrow> 'c \<Rightarrow> bool"
    and rank :: "nat \<Rightarrow> 'c \<Rightarrow> nat"
    and step :: "nat \<Rightarrow> 'c \<Rightarrow> 'c comma_phase_class_action"
  assumes checked: "comma_phase_class_rank_check valid rank step"
    and source_valid: "\<And>phase x. comma_decade_admitted (Comma_Decade phase x) \<Longrightarrow>
      valid phase (class_of x)"
    and source_control: "\<And>phase x. comma_decade_admitted (Comma_Decade phase x) \<Longrightarrow>
      step phase (class_of x) = comma_phase_classify_decade_control class_of
        (comma_decade_control (Comma_Decade phase x))"
    and bounded: "\<And>phase c. valid phase c \<Longrightarrow> rank phase c \<le> 26"
    and admitted: "comma_decade_admitted s"
  shows "\<exists>h tau. h \<le> 26 \<and>
    comma_decade_block_power 5 s = Comma_Block_Stop h tau \<and>
    comma_residual_block 32 (h,tau) = Comma_Residual_Stop h tau \<and>
    comma_decade_exact_summary s h tau"
proof -
  have rank_check:
    "comma_decade_rank_check (comma_decade_rank_from_phase_class class_of rank)"
    by (rule comma_phase_class_rank_lifts_to_decade_rank_check
      [where class_of=class_of and valid=valid and rank=rank and step=step,
       OF checked source_valid source_control])
  have rank_bound:
    "comma_decade_rank_from_phase_class class_of rank s \<le> 26"
    by (rule comma_phase_class_rank_bound_lifts
      [where class_of=class_of and valid=valid and rank=rank and s=s,
       OF source_valid bounded admitted])
  show ?thesis
    by (rule comma_decade_checked_rank_B32
      [where rank="comma_decade_rank_from_phase_class class_of rank" and s=s,
       OF rank_check admitted rank_bound])
qed

theorem comma_phase_class_survival_rank_B32:
  fixes class_of :: "nat \<Rightarrow> 'c"
    and valid :: "nat \<Rightarrow> 'c \<Rightarrow> bool"
    and step :: "nat \<Rightarrow> 'c \<Rightarrow> 'c comma_phase_class_action"
    and s :: comma_decade_state
  assumes no_invalid:
      "\<And>phase c. valid phase c \<Longrightarrow>
        step phase c \<noteq> Comma_Phase_Class_Invalid"
    and continue_closed:
      "\<And>phase c next_phase next_class. valid phase c \<Longrightarrow>
        step phase c = Comma_Phase_Class_Continue next_phase next_class
        \<Longrightarrow> valid next_phase next_class"
    and no_27:
      "\<And>phase c. valid phase c \<Longrightarrow>
        \<not> comma_phase_class_survives step 27 phase c"
    and source_valid:
      "\<And>phase x. comma_decade_admitted (Comma_Decade phase x) \<Longrightarrow>
        valid phase (class_of x)"
    and source_control:
      "\<And>phase x. comma_decade_admitted (Comma_Decade phase x) \<Longrightarrow>
        step phase (class_of x) = comma_phase_classify_decade_control class_of
          (comma_decade_control (Comma_Decade phase x))"
    and admitted: "comma_decade_admitted s"
  shows "\<exists>h tau. h \<le> 26 \<and>
    comma_decade_block_power 5 s = Comma_Block_Stop h tau \<and>
    comma_residual_block 32 (h,tau) = Comma_Residual_Stop h tau \<and>
    comma_decade_exact_summary s h tau"
proof -
  have checked:
    "comma_phase_class_rank_check valid
      (comma_phase_class_survival_rank step) step"
    by (rule comma_phase_class_survival_rank_check(1)
      [where step=step and valid=valid, OF no_invalid continue_closed no_27])
  have bounded:
    "\<And>phase c. valid phase c \<Longrightarrow>
      comma_phase_class_survival_rank step phase c \<le> 26"
    by (rule comma_phase_class_survival_rank_check(2)
      [where step=step and valid=valid, OF no_invalid continue_closed no_27])
  show ?thesis
    by (rule comma_phase_class_rank_B32
      [where class_of=class_of and valid=valid
        and rank="comma_phase_class_survival_rank step"
        and step=step and s=s,
       OF checked source_valid source_control bounded admitted])
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_phase_class_rank_lifts_to_decade_rank_check
      comma_phase_class_rank_bound_lifts comma_phase_class_rank_B32
      comma_phase_class_survives.simps
      comma_phase_class_survival_lengths_continue
      comma_phase_class_survival_rank_continue
      comma_phase_class_survival_rank_check
      comma_phase_class_survival_rank_B32})
    then () else error "Phase-class rank bridge depends on an oracle";
\<close>

end
