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

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_phase_class_rank_lifts_to_decade_rank_check
      comma_phase_class_rank_bound_lifts comma_phase_class_rank_B32})
    then () else error "Phase-class rank bridge depends on an oracle";
\<close>

end
