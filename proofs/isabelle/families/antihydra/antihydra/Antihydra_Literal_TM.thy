theory Antihydra_Literal_TM
  imports Main
begin

text \<open>The literal six-state machine is the semantic source.  The
undefined StateF/0 entry records a halt observation and performs no tape update or
head move.\<close>

datatype ah_state = StateA | StateB | StateC | StateD | StateE | StateF
datatype ah_symbol = Blank | Mark

type_synonym ah_instruction = "ah_symbol \<times> int \<times> ah_state option"

fun ah_transition :: "ah_state \<Rightarrow> ah_symbol \<Rightarrow> ah_instruction" where
  "ah_transition StateA Blank = (Mark, 1, Some StateB)"
| "ah_transition StateA Mark = (Mark, 1, Some StateA)"
| "ah_transition StateB Blank = (Blank, -1, Some StateC)"
| "ah_transition StateB Mark = (Mark, -1, Some StateE)"
| "ah_transition StateC Blank = (Mark, -1, Some StateD)"
| "ah_transition StateC Mark = (Mark, -1, Some StateC)"
| "ah_transition StateD Blank = (Mark, -1, Some StateA)"
| "ah_transition StateD Mark = (Blank, -1, Some StateB)"
| "ah_transition StateE Blank = (Mark, -1, Some StateF)"
| "ah_transition StateE Mark = (Mark, 1, Some StateE)"
| "ah_transition StateF Blank = (Blank, 0, None)"
| "ah_transition StateF Mark = (Blank, 1, Some StateA)"

record ah_configuration =
  ah_control :: ah_state
  ah_ones :: "int set"
  ah_head :: int
  ah_left :: nat
  ah_right :: nat
  ah_halted :: bool

definition ah_blank :: ah_configuration where
  "ah_blank = \<lparr>ah_control=StateA, ah_ones={}, ah_head=0,
    ah_left=0, ah_right=0, ah_halted=False\<rparr>"

definition ah_read :: "ah_configuration \<Rightarrow> ah_symbol" where
  "ah_read c = (if ah_head c \<in> ah_ones c then Mark else Blank)"

definition ah_write :: "int set \<Rightarrow> int \<Rightarrow> ah_symbol \<Rightarrow> int set" where
  "ah_write tape p s = (if s=Mark then insert p tape else tape - {p})"

definition ah_step :: "ah_configuration \<Rightarrow> ah_configuration" where
  "ah_step c =
    (if ah_halted c then c else
      (case ah_transition (ah_control c) (ah_read c) of (w,m,q) \<Rightarrow>
        case q of None \<Rightarrow> c\<lparr>ah_halted := True\<rparr>
        | Some q' \<Rightarrow> c\<lparr>ah_control := q',
            ah_ones := ah_write (ah_ones c) (ah_head c) w,
            ah_head := ah_head c + m,
            ah_left := ah_left c + (if m < 0 then 1 else 0),
            ah_right := ah_right c + (if 0 < m then 1 else 0)\<rparr>))"

lemma zero_move_is_exact_halt_boundary:
  "ah_transition q s = (w, 0, None) \<longleftrightarrow> q=StateF \<and> s=Blank \<and> Blank=w"
  by (cases q; cases s; simp)

lemma halt_boundary_does_not_move_or_write:
  assumes "ah_control c = StateF" "ah_read c = Blank" "\<not> ah_halted c"
  shows "ah_head (ah_step c) = ah_head c"
    "ah_ones (ah_step c) = ah_ones c"
    "ah_left (ah_step c) = ah_left c"
    "ah_right (ah_step c) = ah_right c"
    "ah_halted (ah_step c)"
  using assms by (simp_all add: ah_step_def)

definition ah_startup_section :: ah_configuration where
  "ah_startup_section = \<lparr>ah_control=StateE,
    ah_ones={-3,-2,-1,0}, ah_head=1,
    ah_left=5, ah_right=6, ah_halted=False\<rparr>"

definition ah_c1 :: ah_configuration where
  "ah_c1 = \<lparr>ah_control=StateB, ah_ones={0}, ah_head=1,
    ah_left=0, ah_right=1, ah_halted=False\<rparr>"
definition ah_c2 :: ah_configuration where
  "ah_c2 = \<lparr>ah_control=StateC, ah_ones={0}, ah_head=0,
    ah_left=1, ah_right=1, ah_halted=False\<rparr>"
definition ah_c3 :: ah_configuration where
  "ah_c3 = \<lparr>ah_control=StateC, ah_ones={0}, ah_head=-1,
    ah_left=2, ah_right=1, ah_halted=False\<rparr>"
definition ah_c4 :: ah_configuration where
  "ah_c4 = \<lparr>ah_control=StateD, ah_ones={-1,0}, ah_head=-2,
    ah_left=3, ah_right=1, ah_halted=False\<rparr>"
definition ah_c5 :: ah_configuration where
  "ah_c5 = \<lparr>ah_control=StateA, ah_ones={-2,-1,0}, ah_head=-3,
    ah_left=4, ah_right=1, ah_halted=False\<rparr>"
definition ah_c6 :: ah_configuration where
  "ah_c6 = \<lparr>ah_control=StateB, ah_ones={-3,-2,-1,0}, ah_head=-2,
    ah_left=4, ah_right=2, ah_halted=False\<rparr>"
definition ah_c7 :: ah_configuration where
  "ah_c7 = \<lparr>ah_control=StateE, ah_ones={-3,-2,-1,0}, ah_head=-3,
    ah_left=5, ah_right=2, ah_halted=False\<rparr>"
definition ah_c8 :: ah_configuration where
  "ah_c8 = \<lparr>ah_control=StateE, ah_ones={-3,-2,-1,0}, ah_head=-2,
    ah_left=5, ah_right=3, ah_halted=False\<rparr>"
definition ah_c9 :: ah_configuration where
  "ah_c9 = \<lparr>ah_control=StateE, ah_ones={-3,-2,-1,0}, ah_head=-1,
    ah_left=5, ah_right=4, ah_halted=False\<rparr>"
definition ah_c10 :: ah_configuration where
  "ah_c10 = \<lparr>ah_control=StateE, ah_ones={-3,-2,-1,0}, ah_head=0,
    ah_left=5, ah_right=5, ah_halted=False\<rparr>"

lemma blank_startup_literal_steps:
  "ah_step ah_blank = ah_c1"
  "ah_step ah_c1 = ah_c2"
  "ah_step ah_c2 = ah_c3"
  "ah_step ah_c3 = ah_c4"
  "ah_step ah_c4 = ah_c5"
  "ah_step ah_c5 = ah_c6"
  "ah_step ah_c6 = ah_c7"
  "ah_step ah_c7 = ah_c8"
  "ah_step ah_c8 = ah_c9"
  "ah_step ah_c9 = ah_c10"
  "ah_step ah_c10 = ah_startup_section"
  by (auto simp: ah_step_def ah_blank_def ah_read_def ah_write_def
      ah_c1_def ah_c2_def ah_c3_def ah_c4_def ah_c5_def ah_c6_def
      ah_c7_def ah_c8_def ah_c9_def ah_c10_def ah_startup_section_def)

theorem blank_startup_is_eleven_steps:
  "(ah_step ^^ 11) ah_blank = ah_startup_section"
proof -
  have duration: "11 = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc
      (Suc (Suc (Suc 0))))))))))" by simp
  show ?thesis
    unfolding duration
    by (simp only: funpow.simps comp_apply id_apply blank_startup_literal_steps)
qed

corollary blank_startup_physical_clock:
  "ah_left ((ah_step ^^ 11) ah_blank) = 5 \<and>
   ah_right ((ah_step ^^ 11) ah_blank) = 6 \<and>
   ah_head ((ah_step ^^ 11) ah_blank) = 1"
  using blank_startup_is_eleven_steps by (simp add: ah_startup_section_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms zero_move_is_exact_halt_boundary
      halt_boundary_does_not_move_or_write
      blank_startup_literal_steps
      blank_startup_is_eleven_steps blank_startup_physical_clock}) then ()
    else error "Antihydra literal TM proof depends on an oracle";
\<close>

end
