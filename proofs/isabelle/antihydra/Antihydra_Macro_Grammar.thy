theory Antihydra_Macro_Grammar
  imports Antihydra_Affine_Certificate
begin

text \<open>The compressed support grammar is retained before any prime or
cyclotomic evaluation.  F/0 is an observation with zero physical ticks.\<close>

datatype ah_port = PA0 | PA1 | PB0 | PB1 | PC0 | PC1 |
  PD0 | PD1 | PE0 | PE1 | PF0 | PF1

fun port_move :: "ah_port \<Rightarrow> int" where
  "port_move PA0 = 1" | "port_move PA1 = 1"
| "port_move PB0 = -1" | "port_move PB1 = -1"
| "port_move PC0 = -1" | "port_move PC1 = -1"
| "port_move PD0 = -1" | "port_move PD1 = -1"
| "port_move PE0 = -1" | "port_move PE1 = 1"
| "port_move PF0 = 0" | "port_move PF1 = 1"

type_synonym port_run = "ah_port \<times> nat"
type_synonym port_word = "port_run list"

fun run_ticks :: "port_run \<Rightarrow> nat" where
  "run_ticks (p,n) = (if p=PF0 then 0 else n)"

fun run_shift :: "port_run \<Rightarrow> int" where
  "run_shift (p,n) = port_move p * int n"

definition word_ticks :: "port_word \<Rightarrow> nat" where
  "word_ticks w = sum_list (map run_ticks w)"

definition word_shift :: "port_word \<Rightarrow> int" where
  "word_shift w = sum_list (map run_shift w)"

lemma word_effect_append [simp]:
  "word_ticks (u@v) = word_ticks u + word_ticks v"
  "word_shift (u@v) = word_shift u + word_shift v"
  by (simp_all add: word_ticks_def word_shift_def)

definition run_port :: "port_run \<Rightarrow> int \<times> nat \<Rightarrow> int \<times> nat" where
  "run_port r ht = (fst ht + run_shift r, snd ht + run_ticks r)"

lemma run_same_port_composes:
  "run_port (p,m+n) ht = run_port (p,n) (run_port (p,m) ht)"
  by (cases ht; cases p; simp add: run_port_def algebra_simps)

definition sweep_word :: "nat \<Rightarrow> port_word" where
  "sweep_word j = [(PE0,1),(PF1,1),(PA1,3*j+1),(PA0,1),(PB0,1),
    (PC1,3*j+2),(PC0,1),(PD1,1),(PB1,1),(PE1,2)]"

fun sweep_prefix :: "nat \<Rightarrow> port_word" where
  "sweep_prefix 0 = []"
| "sweep_prefix (Suc c) = sweep_prefix c @ sweep_word c"

lemma one_sweep_effect:
  "word_ticks (sweep_word j) = 6*j+12"
  "word_shift (sweep_word j) = -2"
  by (simp_all add: sweep_word_def word_ticks_def word_shift_def algebra_simps)

theorem repeated_sweep_effect:
  "word_ticks (sweep_prefix c) = 3*c^2+9*c"
  "word_shift (sweep_prefix c) = -2*int c"
proof (induct c)
  case 0
  then show "word_ticks (sweep_prefix 0) = 3*0^2+9*0"
    "word_shift (sweep_prefix 0) = -2*int 0"
    by (simp_all add: word_ticks_def word_shift_def)
next
  case (Suc c)
  show "word_ticks (sweep_prefix (Suc c)) = 3*(Suc c)^2+9*(Suc c)"
    using Suc one_sweep_effect[of c] by (simp add: algebra_simps power2_eq_square)
  show "word_shift (sweep_prefix (Suc c)) = -2*int (Suc c)"
    using Suc one_sweep_effect[of c] by simp
qed

definition suffix_v :: "nat \<Rightarrow> port_word" where
  "suffix_v k = [(PE0,1),(PF1,1),(PA1,3*k-2),(PA0,1),(PB0,1),
    (PC1,3*k-1),(PC0,1),(PD1,1)]"

definition suffix_w :: "bool \<Rightarrow> nat \<Rightarrow> port_word" where
  "suffix_w odd_branch k = [(PE0,1),(PF1,1),
    (PA1,if odd_branch then 2 else 1),(PA0,1),(PB1,1),(PE1,3*k+1)]"

definition odd_suffix :: "nat \<Rightarrow> port_word" where
  "odd_suffix k = suffix_v k @ [(PB1,1)] @ suffix_w True k"

definition odd_terminal_suffix :: "nat \<Rightarrow> port_word" where
  "odd_terminal_suffix k = suffix_v k @ [(PB1,1),(PE0,1),(PF0,1)]"

definition even_suffix :: "nat \<Rightarrow> nat \<Rightarrow> port_word" where
  "even_suffix a k = suffix_v k @
    [(PB0,1),(PC1,a),(PC0,1),(PD0,1),(PA0,1),(PB1,1),(PE1,a+3)] @
    suffix_w False k"

lemma suffix_effects:
  assumes "1 \<le> k"
  shows "word_ticks (odd_suffix k) = 9*k+11"
    "word_shift (odd_suffix k) = 3*int k-1"
    "word_ticks (odd_terminal_suffix k) = 6*k+5"
    "word_shift (odd_terminal_suffix k) = -5"
    "word_ticks (even_suffix a k) = 2*a+9*k+17"
    "word_shift (even_suffix a k) = 3*int k-1"
  using assms
  by (simp_all add: odd_suffix_def odd_terminal_suffix_def even_suffix_def
      suffix_v_def suffix_w_def word_ticks_def word_shift_def algebra_simps)

definition odd_macro_word :: "nat \<Rightarrow> port_word" where
  "odd_macro_word k = sweep_prefix (k-1) @ odd_suffix k"

definition odd_terminal_word :: "nat \<Rightarrow> port_word" where
  "odd_terminal_word k = sweep_prefix (k-1) @ odd_terminal_suffix k"

definition even_macro_word :: "nat \<Rightarrow> nat \<Rightarrow> port_word" where
  "even_macro_word a k = sweep_prefix (k-1) @ even_suffix a k"

theorem macro_grammar_clock_roofs:
  assumes "1 \<le> k"
  shows "word_ticks (odd_macro_word k) = 3*k^2+12*k+5"
    "word_shift (odd_macro_word k) = int k+1"
    "word_ticks (odd_terminal_word k) = 3*k^2+9*k-1"
    "word_shift (odd_terminal_word k) = 2-int (2*k+5)"
    "word_ticks (even_macro_word a k) = 2*a+3*k^2+12*k+11"
    "word_shift (even_macro_word a k) = int k+1"
proof -
  obtain c where k: "k = Suc c"
    using assms by (cases k) auto
  show "word_ticks (odd_macro_word k) = 3*k^2+12*k+5"
    "word_shift (odd_macro_word k) = int k+1"
    "word_ticks (odd_terminal_word k) = 3*k^2+9*k-1"
    "word_shift (odd_terminal_word k) = 2-int (2*k+5)"
    "word_ticks (even_macro_word a k) = 2*a+3*k^2+12*k+11"
    "word_shift (even_macro_word a k) = int k+1"
    using repeated_sweep_effect[of c]
      suffix_effects[of "Suc c"]
    by (simp_all add: k odd_macro_word_def odd_terminal_word_def
        even_macro_word_def power2_eq_square algebra_simps)
qed

fun port_control :: "ah_port \<Rightarrow> ah_state" where
  "port_control PA0 = StateA" | "port_control PA1 = StateA"
| "port_control PB0 = StateB" | "port_control PB1 = StateB"
| "port_control PC0 = StateC" | "port_control PC1 = StateC"
| "port_control PD0 = StateD" | "port_control PD1 = StateD"
| "port_control PE0 = StateE" | "port_control PE1 = StateE"
| "port_control PF0 = StateF" | "port_control PF1 = StateF"

fun port_symbol :: "ah_port \<Rightarrow> ah_symbol" where
  "port_symbol PA0 = Blank" | "port_symbol PA1 = Mark"
| "port_symbol PB0 = Blank" | "port_symbol PB1 = Mark"
| "port_symbol PC0 = Blank" | "port_symbol PC1 = Mark"
| "port_symbol PD0 = Blank" | "port_symbol PD1 = Mark"
| "port_symbol PE0 = Blank" | "port_symbol PE1 = Mark"
| "port_symbol PF0 = Blank" | "port_symbol PF1 = Mark"

fun observed_port :: "ah_configuration \<Rightarrow> ah_port" where
  "observed_port c = (case (ah_control c, ah_read c) of
      (StateA,Blank) \<Rightarrow> PA0 | (StateA,Mark) \<Rightarrow> PA1
    | (StateB,Blank) \<Rightarrow> PB0 | (StateB,Mark) \<Rightarrow> PB1
    | (StateC,Blank) \<Rightarrow> PC0 | (StateC,Mark) \<Rightarrow> PC1
    | (StateD,Blank) \<Rightarrow> PD0 | (StateD,Mark) \<Rightarrow> PD1
    | (StateE,Blank) \<Rightarrow> PE0 | (StateE,Mark) \<Rightarrow> PE1
    | (StateF,Blank) \<Rightarrow> PF0 | (StateF,Mark) \<Rightarrow> PF1)"

lemma observed_port_components [simp]:
  "port_control (observed_port c) = ah_control c"
  "port_symbol (observed_port c) = ah_read c"
  by (cases "ah_control c"; cases "ah_read c"; simp)+

lemma literal_table_has_port_move:
  assumes "\<not> ah_halted c"
  shows "ah_head (ah_step c) = ah_head c + port_move (observed_port c)"
  using assms
  by (cases "ah_control c"; cases "ah_read c";
      simp add: ah_step_def ah_read_def)

definition port_left :: "ah_port \<Rightarrow> nat" where
  "port_left p = (if port_move p < 0 then 1 else 0)"

definition port_right :: "ah_port \<Rightarrow> nat" where
  "port_right p = (if 0 < port_move p then 1 else 0)"

lemma literal_table_has_directional_clock:
  assumes "\<not> ah_halted c" "observed_port c \<noteq> PF0"
  shows "ah_left (ah_step c) = ah_left c + port_left (observed_port c) \<and>
    ah_right (ah_step c) = ah_right c + port_right (observed_port c)"
  using assms
  by (cases "ah_control c"; cases "ah_read c";
      simp_all add: ah_step_def port_left_def port_right_def ah_read_def)

fun expand_run :: "port_run \<Rightarrow> ah_port list" where
  "expand_run (p,n) = (if p=PF0 then [] else replicate n p)"

definition expand_word :: "port_word \<Rightarrow> ah_port list" where
  "expand_word w = concat (map expand_run w)"

lemma expand_run_has_no_halt_port:
  "PF0 \<notin> set (expand_run r)"
  by (cases r; simp)

lemma expand_word_has_no_halt_port:
  "PF0 \<notin> set (expand_word w)"
  by (induct w; simp_all add: expand_word_def expand_run_has_no_halt_port)

lemma expand_run_length [simp]:
  "length (expand_run r) = run_ticks r"
  by (cases r; simp)

lemma sum_replicated_port:
  "sum_list (map port_move (replicate n p)) = int n * port_move p"
  by (induct n) (simp_all add: algebra_simps)

lemma expand_run_shift [simp]:
  "sum_list (map port_move (expand_run r)) = run_shift r"
proof (cases r)
  case (Pair p n)
  then show ?thesis
  proof (cases "p = PF0")
    case True
    then show ?thesis using Pair by simp
  next
    case False
    have "sum_list (map port_move (expand_run r)) =
        sum_list (map port_move (replicate n p))"
      using Pair False by simp
    also have "... = int n * port_move p"
      by (rule sum_replicated_port)
    also have "... = run_shift r"
      using Pair by (simp add: mult.commute)
    finally show ?thesis .
  qed
qed

lemma expand_word_length:
  "length (expand_word w) = word_ticks w"
  by (induct w; simp_all add: expand_word_def word_ticks_def)

lemma expand_word_shift:
  "sum_list (map port_move (expand_word w)) = word_shift w"
  by (induct w;
      simp_all add: expand_word_def word_shift_def sum_list_append)

fun literal_replay ::
  "ah_port list \<Rightarrow> ah_configuration \<Rightarrow> ah_configuration option" where
  "literal_replay [] c = Some c"
| "literal_replay (p#ps) c =
    (if ah_halted c \<or> observed_port c \<noteq> p then None
     else literal_replay ps (ah_step c))"

lemma literal_replay_head:
  assumes "literal_replay ps c = Some c'"
  shows "ah_head c' = ah_head c + sum_list (map port_move ps)"
  using assms
proof (induct ps arbitrary: c)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  from Cons.prems have live: "\<not> ah_halted c"
    and port: "observed_port c = p"
    and tail: "literal_replay ps (ah_step c) = Some c'"
    by (auto split: if_splits)
  have "ah_head c' = ah_head (ah_step c) +
      sum_list (map port_move ps)"
    using Cons.hyps[OF tail] .
  also have "... = ah_head c + port_move p +
      sum_list (map port_move ps)"
    using literal_table_has_port_move[OF live] port by simp
  finally show ?case by simp
qed

lemma literal_replay_directional_clock:
  assumes replay: "literal_replay ps c = Some c'"
    and no_halt_port: "PF0 \<notin> set ps"
  shows "ah_left c' = ah_left c + sum_list (map port_left ps) \<and>
    ah_right c' = ah_right c + sum_list (map port_right ps)"
  using replay no_halt_port
proof (induct ps arbitrary: c)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  from Cons.prems(1) have live: "\<not> ah_halted c"
    and port: "observed_port c = p"
    and tail: "literal_replay ps (ah_step c) = Some c'"
    by (auto split: if_splits)
  have pne: "p \<noteq> PF0" and tail_no_halt: "PF0 \<notin> set ps"
    using Cons.prems(2) by auto
  have left_step: "ah_left (ah_step c) = ah_left c + port_left p"
    and right_step: "ah_right (ah_step c) = ah_right c + port_right p"
    using literal_table_has_directional_clock[OF live] port pne
    by auto
  have tail_clock:
      "ah_left c' = ah_left (ah_step c) + sum_list (map port_left ps) \<and>
       ah_right c' = ah_right (ah_step c) + sum_list (map port_right ps)"
    using Cons.hyps[OF tail tail_no_halt] .
  show ?case using tail_clock left_step right_step by simp
qed

lemma one_nonhalt_port_direction:
  assumes "p \<noteq> PF0"
  shows "port_left p + port_right p = 1"
  using assms by (cases p; simp add: port_left_def port_right_def)

lemma nonhalt_port_direction_count:
  assumes "PF0 \<notin> set ps"
  shows "sum_list (map port_left ps) + sum_list (map port_right ps) = length ps"
  using assms
  by (induct ps) (auto simp: one_nonhalt_port_direction algebra_simps)

theorem admitted_literal_macro_has_length_and_shift:
  assumes admitted: "literal_replay (expand_word w) c = Some c'"
  shows "length (expand_word w) = word_ticks w"
    "ah_head c' = ah_head c + word_shift w"
  using expand_word_length expand_word_shift literal_replay_head[OF admitted]
  by simp_all

theorem admitted_literal_macro_has_physical_clock:
  assumes admitted: "literal_replay (expand_word w) c = Some c'"
  shows "ah_left c' = ah_left c +
      sum_list (map port_left (expand_word w))"
    "ah_right c' = ah_right c +
      sum_list (map port_right (expand_word w))"
    "(ah_left c' - ah_left c) + (ah_right c' - ah_right c) =
      word_ticks w"
proof -
  have left: "ah_left c' = ah_left c +
      sum_list (map port_left (expand_word w))"
    and right: "ah_right c' = ah_right c +
      sum_list (map port_right (expand_word w))"
    using literal_replay_directional_clock[OF admitted expand_word_has_no_halt_port]
    by auto
  then show "ah_left c' = ah_left c +
      sum_list (map port_left (expand_word w))"
    "ah_right c' = ah_right c +
      sum_list (map port_right (expand_word w))" by simp_all
  show "(ah_left c' - ah_left c) + (ah_right c' - ah_right c) =
      word_ticks w"
    using left right nonhalt_port_direction_count[OF expand_word_has_no_halt_port[of w]]
      expand_word_length[of w]
    by simp
qed

definition literal_terminal_admitted ::
  "port_word \<Rightarrow> ah_configuration \<Rightarrow> ah_configuration \<Rightarrow> bool"
where
  "literal_terminal_admitted w c c' \<longleftrightarrow>
    literal_replay (expand_word w) c = Some c' \<and>
    observed_port c' = PF0 \<and> \<not> ah_halted c'"

lemma terminal_admission_reaches_exact_halt:
  assumes "literal_terminal_admitted w c c'"
  shows "ah_halted (ah_step c')"
    "ah_head (ah_step c') = ah_head c'"
  using assms observed_port_components[of c']
  by (simp_all add: literal_terminal_admitted_def halt_boundary_does_not_move_or_write)

lemma right_mark_run_admitted:
  assumes qp: "(q,p) = (StateA,PA1) \<or> (q,p) = (StateE,PE1)"
    and control: "ah_control c = q"
    and live: "\<not> ah_halted c"
    and cells: "\<And>i. i<n \<Longrightarrow> ah_head c + int i \<in> ah_ones c"
  shows "\<exists>c'. literal_replay (replicate n p) c = Some c' \<and>
    ah_control c' = q \<and> ah_ones c' = ah_ones c \<and>
    ah_head c' = ah_head c + int n \<and> \<not> ah_halted c'"
  using control live cells
proof (induct n arbitrary: c)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have marked: "ah_read c = Mark"
    using Suc.prems(3)[of 0] by (simp add: ah_read_def)
  have cell: "ah_head c \<in> ah_ones c"
    using marked by (auto simp: ah_read_def split: if_splits)
  have obs: "observed_port c = p"
    using qp Suc.prems(1) marked
    by (elim disjE; simp add: observed_port.simps)
  have core: "ah_control (ah_step c) = q \<and>
      ah_ones (ah_step c) = ah_ones c \<and>
      ah_head (ah_step c) = ah_head c + 1 \<and>
      \<not> ah_halted (ah_step c)"
    using qp Suc.prems(1,2) marked cell
    by (auto simp: ah_step_def ah_write_def)
  then have step_control: "ah_control (ah_step c) = q"
    and step_tape: "ah_ones (ah_step c) = ah_ones c"
    and step_head: "ah_head (ah_step c) = ah_head c + 1"
    and step_live: "\<not> ah_halted (ah_step c)"
    by auto
  have rest: "\<And>i. i<n \<Longrightarrow>
      ah_head (ah_step c) + int i \<in> ah_ones (ah_step c)"
  proof -
    fix i assume "i<n"
    then have "Suc i < Suc n" by simp
    then have "ah_head c + int (Suc i) \<in> ah_ones c"
      by (rule Suc.prems(3))
    then show "ah_head (ah_step c) + int i \<in> ah_ones (ah_step c)"
      using step_head step_tape by (simp add: algebra_simps)
  qed
  obtain c' where tail:
      "literal_replay (replicate n p) (ah_step c) = Some c'"
    and ccontrol: "ah_control c' = q" and ctape: "ah_ones c' = ah_ones (ah_step c)"
    and chead: "ah_head c' = ah_head (ah_step c) + int n"
    and clive: "\<not> ah_halted c'"
    using Suc.hyps[OF step_control step_live rest] by blast
  have replay: "literal_replay (replicate (Suc n) p) c = Some c'"
    using Suc.prems(2) obs tail by simp
  show ?case
    using replay ccontrol ctape chead clive step_tape step_head
    by (intro exI[of _ c']) (simp add: algebra_simps)
qed

lemma left_C1_mark_run_admitted:
  assumes control: "ah_control c = StateC"
    and live: "\<not> ah_halted c"
    and cells: "\<And>i. i<n \<Longrightarrow> ah_head c - int i \<in> ah_ones c"
  shows "\<exists>c'. literal_replay (replicate n PC1) c = Some c' \<and>
    ah_control c' = StateC \<and> ah_ones c' = ah_ones c \<and>
    ah_head c' = ah_head c - int n \<and> \<not> ah_halted c'"
  using control live cells
proof (induct n arbitrary: c)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have marked: "ah_read c = Mark"
    using Suc.prems(3)[of 0] by (simp add: ah_read_def)
  have cell: "ah_head c \<in> ah_ones c"
    using marked by (auto simp: ah_read_def split: if_splits)
  have obs: "observed_port c = PC1"
    using Suc.prems(1) marked by simp
  have step_control: "ah_control (ah_step c) = StateC"
    and step_tape: "ah_ones (ah_step c) = ah_ones c"
    and step_head: "ah_head (ah_step c) = ah_head c - 1"
    and step_live: "\<not> ah_halted (ah_step c)"
    using Suc.prems(1,2) marked cell
    by (simp_all add: ah_step_def ah_write_def insert_absorb)
  have rest: "\<And>i. i<n \<Longrightarrow>
      ah_head (ah_step c) - int i \<in> ah_ones (ah_step c)"
  proof -
    fix i assume "i<n"
    then have "Suc i < Suc n" by simp
    then have next_cell: "ah_head c - int (Suc i) \<in> ah_ones c"
      by (rule Suc.prems(3))
    have shift_eq: "ah_head (ah_step c) - int i =
        ah_head c - int (Suc i)"
      using step_head by arith
    show "ah_head (ah_step c) - int i \<in> ah_ones (ah_step c)"
      using next_cell by (simp only: step_tape shift_eq)
  qed
  obtain c' where tail:
      "literal_replay (replicate n PC1) (ah_step c) = Some c'"
    and ccontrol: "ah_control c' = StateC"
    and ctape: "ah_ones c' = ah_ones (ah_step c)"
    and chead: "ah_head c' = ah_head (ah_step c) - int n"
    and clive: "\<not> ah_halted c'"
    using Suc.hyps[OF step_control step_live rest] by blast
  have replay: "literal_replay (replicate (Suc n) PC1) c = Some c'"
    using Suc.prems(2) obs tail by simp
  show ?case
    using replay ccontrol ctape chead clive step_tape step_head
    by (intro exI[of _ c']) (simp add: algebra_simps)
qed

text \<open>The clock and displacement formulas are now consequences of the
literal port grammar, including the corrected even suffix PA1 run of length
one.  The executable literal-replay predicate checks every advertised port
against the actual six-state table; an admitted word therefore has the proved
physical left/right clock and head displacement, and terminal admission reaches the exact F/0
boundary.  The remaining refinement obligation is spatial: prove by induction on
the tape intervals of A(a,b) that each advertised run reads its port symbol,
and that a sweep maps the corresponding interval shape to the next shape.
This theory does not assume that admission fact.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms word_effect_append run_same_port_composes one_sweep_effect
      repeated_sweep_effect suffix_effects macro_grammar_clock_roofs
      literal_table_has_port_move expand_word_length expand_word_shift
      literal_table_has_directional_clock literal_replay_head
      literal_replay_directional_clock admitted_literal_macro_has_length_and_shift
      admitted_literal_macro_has_physical_clock
      terminal_admission_reaches_exact_halt right_mark_run_admitted
      left_C1_mark_run_admitted}) then ()
    else error "Antihydra macro grammar proof depends on an oracle";
\<close>

end
