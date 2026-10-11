theory Comma_Source_Continuation_DAG
  imports Comma_Decisive_Endpoint_Quotient
begin

ML \<open>Comma_Decisive_Endpoint_Profile.report "Source continuation DAG stage=entered"\<close>

text \<open>
An occurrence's decimal shift is carried by application, not by the
continuation identifier.  The identifier is the complete finite local-phase
action, including exact successor source addresses and terminal payloads.
Successor addresses are references, so this is a DAG interface rather than
an expanded recursively copied tree.  Equality is conservative: this theory
does not assert that distinct successor addresses with equal futures merge.
\<close>

fun comma_source_continuation_base :: "comma_finite_position \<Rightarrow> comma_finite_position" where
  "comma_source_continuation_base (Comma_Entry f delta x)=Comma_Entry f 0 x"
| "comma_source_continuation_base (Comma_Near f delta h)=Comma_Near f 0 h"

fun comma_source_continuation_shift :: "comma_finite_position \<Rightarrow> nat" where
  "comma_source_continuation_shift (Comma_Entry f delta x)=delta"
| "comma_source_continuation_shift (Comma_Near f delta h)=delta"

lemma comma_source_continuation_reconstruct:
  "source=comma_shift_position (comma_source_continuation_shift source)
    (comma_source_continuation_base source)"
  by (cases source) simp_all

lemma comma_source_continuation_base_idempotent [simp]:
  "comma_source_continuation_base (comma_source_continuation_base source)=
    comma_source_continuation_base source"
  by (cases source) simp_all

lemma comma_source_continuation_base_sector [simp]:
  "comma_sector_number (comma_source_continuation_base source)=comma_sector_number source"
  by (cases source) simp_all

ML \<open>
  Thm.consolidate @{thms comma_source_continuation_reconstruct
    comma_source_continuation_base_idempotent comma_source_continuation_base_sector};
  Comma_Decisive_Endpoint_Profile.report "Source continuation DAG stage=base facts consolidated"
\<close>

datatype comma_source_continuation_action =
    Comma_Continuation_Goto comma_finite_position nat
  | Comma_Continuation_Exit comma_finite_position nat
  | Comma_Continuation_Fork nat nat
  | Comma_Continuation_Landmine nat
  | Comma_Continuation_Invalid

fun comma_source_continuation_action_of_packet ::
    "comma_finite_position \<times> comma_finite_move \<Rightarrow>
      comma_source_continuation_action" where
  "comma_source_continuation_action_of_packet (target,Comma_Next next) =
    (if comma_round_crossing target next then
       Comma_Continuation_Exit (comma_source_continuation_base next)
         (comma_source_continuation_shift next)
     else Comma_Continuation_Goto (comma_source_continuation_base next)
         (comma_source_continuation_shift next))"
| "comma_source_continuation_action_of_packet (target,Comma_Fork a delta) =
    Comma_Continuation_Fork a delta"
| "comma_source_continuation_action_of_packet (target,Comma_Landmine delta) =
    Comma_Continuation_Landmine delta"
| "comma_source_continuation_action_of_packet (target,Comma_Invalid) =
    Comma_Continuation_Invalid"

fun comma_source_continuation_transport ::
    "nat \<Rightarrow> comma_source_continuation_action \<Rightarrow>
      comma_source_continuation_action" where
  "comma_source_continuation_transport k (Comma_Continuation_Goto source delta) =
    Comma_Continuation_Goto source (delta+k)"
| "comma_source_continuation_transport k (Comma_Continuation_Exit source delta) =
    Comma_Continuation_Exit source (delta+k)"
| "comma_source_continuation_transport k (Comma_Continuation_Fork a delta) =
    Comma_Continuation_Fork a (delta+k)"
| "comma_source_continuation_transport k (Comma_Continuation_Landmine delta) =
    Comma_Continuation_Landmine (delta+k)"
| "comma_source_continuation_transport k Comma_Continuation_Invalid =
    Comma_Continuation_Invalid"

lemma comma_source_continuation_base_shift_position:
  "comma_source_continuation_base (comma_shift_position k source)=
    comma_source_continuation_base source"
  by (cases source) simp_all

lemma comma_source_continuation_shift_position:
  "comma_source_continuation_shift (comma_shift_position k source)=
    comma_source_continuation_shift source+k"
  by (cases source) simp_all

lemma comma_source_continuation_action_shift:
  "comma_source_continuation_action_of_packet
      (comma_shift_position k target,comma_shift_move k move) =
    comma_source_continuation_transport k
      (comma_source_continuation_action_of_packet (target,move))"
  by (cases move)
    (simp_all add: comma_source_continuation_base_shift_position
      comma_source_continuation_shift_position comma_round_crossing_shift
      split: if_splits)

ML \<open>
  Thm.consolidate @{thms comma_source_continuation_base_shift_position
    comma_source_continuation_shift_position comma_source_continuation_action_shift};
  Comma_Decisive_Endpoint_Profile.report "Source continuation DAG stage=action shift consolidated"
\<close>

lemma comma_source_continuation_target_transport:
  "comma_decisive_sector_target r source =
    comma_shift_position (comma_source_continuation_shift source)
      (comma_decisive_sector_target
        ((r+comma_source_continuation_shift source) mod 924)
        (comma_source_continuation_base source))"
proof (cases source)
  case (Comma_Entry f delta x)
  let ?phase = "(r+delta) mod 924"
  have base_phase: "(?phase+0) mod 924=?phase"
    by (simp only: add_0_right mod_mod_trivial)
  then show ?thesis using Comma_Entry base_phase
    by (simp add: comma_source_continuation_shift.simps
      comma_source_continuation_base.simps comma_decisive_sector_target.simps
      comma_shift_position.simps Let_def add_0_left base_phase
      split: option.splits prod.splits)
next
  case (Comma_Near f delta h)
  then show ?thesis
    by (simp only: comma_source_continuation_shift.simps
      comma_source_continuation_base.simps comma_decisive_sector_target.simps
      comma_shift_position.simps add_0_left)
qed

ML \<open>
  Thm.consolidate @{thms comma_source_continuation_target_transport};
  Comma_Decisive_Endpoint_Profile.report "Source continuation DAG stage=target transport consolidated"
\<close>

lemma comma_source_continuation_packet_transport:
  "comma_decisive_endpoint_packet r source =
    (comma_shift_position (comma_source_continuation_shift source)
       (fst (comma_decisive_endpoint_packet
         ((r+comma_source_continuation_shift source) mod 924)
         (comma_source_continuation_base source))),
     comma_shift_move (comma_source_continuation_shift source)
       (snd (comma_decisive_endpoint_packet
         ((r+comma_source_continuation_shift source) mod 924)
         (comma_source_continuation_base source))))"
proof -
  let ?delta = "comma_source_continuation_shift source"
  let ?phase = "(r+?delta) mod 924"
  let ?base = "comma_source_continuation_base source"
  let ?target = "comma_decisive_sector_target ?phase ?base"
  have target:
    "comma_decisive_sector_target r source=comma_shift_position ?delta ?target"
    by (rule comma_source_continuation_target_transport)
  have phase: "(r mod 924+?delta) mod 924=?phase"
    by (simp add: mod_add_left_eq)
  have phase_bound: "?phase<924" by simp
  have step:
    "comma_fast_step (r mod 924) (comma_shift_position ?delta ?target)=
      comma_shift_move ?delta (comma_fast_step ?phase ?target)"
  proof -
    have finite_step:
      "comma_finite_step (r mod 924) (comma_shift_position ?delta ?target)=
        comma_shift_move ?delta
          (comma_finite_step (((r mod 924)+?delta) mod 924) ?target)"
      by (rule comma_finite_step_phase_shift)
    show ?thesis using finite_step phase
      by (simp only: comma_fast_step_correct)
  qed
  show ?thesis using target step
    by (simp only: comma_decisive_endpoint_packet_def Let_def target step
      phase_bound mod_less fst_conv snd_conv)
qed

ML \<open>
  Thm.consolidate @{thms comma_source_continuation_packet_transport};
  Comma_Decisive_Endpoint_Profile.report "Source continuation DAG stage=packet transport consolidated"
\<close>

definition comma_source_continuation_id ::
    "comma_finite_position \<Rightarrow> nat \<times> comma_source_continuation_action list" where
  "comma_source_continuation_id source =
    (let base=comma_source_continuation_base source;
         period=comma_decisive_sector_period base
     in (period,map (\<lambda>r. comma_source_continuation_action_of_packet
          (comma_decisive_endpoint_packet r base)) [0..<period]))"

definition comma_source_continuation_action_at ::
    "comma_finite_position \<Rightarrow> nat \<Rightarrow>
      comma_source_continuation_action" where
  "comma_source_continuation_action_at source r =
    (let (period,actions)=comma_source_continuation_id source
     in actions ! (r mod period))"

lemma comma_source_continuation_id_base [simp]:
  "comma_source_continuation_id (comma_source_continuation_base source)=
    comma_source_continuation_id source"
  by (simp add: comma_source_continuation_id_def)

lemma comma_source_continuation_id_shift:
  "comma_source_continuation_id (comma_shift_position delta source)=
    comma_source_continuation_id source"
  by (simp add: comma_source_continuation_id_def
    comma_source_continuation_base_shift_position)

ML \<open>
  Thm.consolidate @{thms comma_source_continuation_id_base
    comma_source_continuation_id_shift};
  Comma_Decisive_Endpoint_Profile.report "Source continuation DAG stage=identifier facts consolidated"
\<close>

lemma comma_source_continuation_equal_id_action:
  assumes "comma_source_continuation_id left=comma_source_continuation_id right"
  shows "comma_source_continuation_action_at left r=comma_source_continuation_action_at right r"
  using assms by (simp add: comma_source_continuation_action_at_def)

lemma comma_source_continuation_base_admitted:
  assumes "comma_round_admitted source"
  shows "comma_round_admitted (comma_source_continuation_base source)"
  using assms by (cases source) simp_all

lemma comma_source_continuation_signature_slot:
  assumes admitted: "comma_round_admitted source"
  shows "comma_source_continuation_action_at source r =
    comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet r
        (comma_source_continuation_base source))"
proof -
  let ?base = "comma_source_continuation_base source"
  let ?period = "comma_decisive_sector_period ?base"
  have base_admitted:
    "comma_round_admitted ?base"
    by (rule comma_source_continuation_base_admitted[OF admitted])
  have positive: "0<?period"
    by (rule comma_decisive_sector_period_admitted(1)[OF base_admitted])
  have index: "r mod ?period<?period" using positive by simp
  have slot:
    "comma_source_continuation_action_at source r =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet (r mod ?period) ?base)"
    using index by (simp add: comma_source_continuation_action_at_def
      comma_source_continuation_id_def Let_def)
  have period:
    "comma_decisive_endpoint_packet (r mod ?period) ?base =
      comma_decisive_endpoint_packet r ?base"
    by (rule comma_decisive_endpoint_packet_period[OF base_admitted]) simp
  show ?thesis using slot period by simp
qed

lemma comma_source_continuation_apply_exact:
  assumes admitted: "comma_round_admitted source"
  shows "comma_source_continuation_transport
      (comma_source_continuation_shift source)
      (comma_source_continuation_action_at
        (comma_source_continuation_base source)
        ((r+comma_source_continuation_shift source) mod 924)) =
    comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet r source)"
proof -
  let ?base = "comma_source_continuation_base source"
  let ?shift = "comma_source_continuation_shift source"
  have base_admitted: "comma_round_admitted ?base"
    by (rule comma_source_continuation_base_admitted[OF admitted])
  have slot:
    "comma_source_continuation_action_at ?base ((r+?shift) mod 924) =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet ((r+?shift) mod 924) ?base)"
    using comma_source_continuation_signature_slot[OF base_admitted,
      of "(r+?shift) mod 924"] by simp
  have packet:
    "comma_decisive_endpoint_packet r source =
      (comma_shift_position ?shift
         (fst (comma_decisive_endpoint_packet ((r+?shift) mod 924) ?base)),
       comma_shift_move ?shift
         (snd (comma_decisive_endpoint_packet ((r+?shift) mod 924) ?base)))"
    by (rule comma_source_continuation_packet_transport)
  have packet_action:
    "comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet r source) =
      comma_source_continuation_transport ?shift
        (comma_source_continuation_action_of_packet
          (fst (comma_decisive_endpoint_packet ((r+?shift) mod 924) ?base),
           snd (comma_decisive_endpoint_packet ((r+?shift) mod 924) ?base)))"
  proof -
    have packet_cong:
      "comma_source_continuation_action_of_packet
          (comma_decisive_endpoint_packet r source) =
        comma_source_continuation_action_of_packet
          (comma_shift_position ?shift
             (fst (comma_decisive_endpoint_packet ((r+?shift) mod 924) ?base)),
           comma_shift_move ?shift
             (snd (comma_decisive_endpoint_packet ((r+?shift) mod 924) ?base)))"
      by (rule arg_cong[where f=comma_source_continuation_action_of_packet,
        OF packet])
    have action_shift:
      "comma_source_continuation_action_of_packet
          (comma_shift_position ?shift
             (fst (comma_decisive_endpoint_packet ((r+?shift) mod 924) ?base)),
           comma_shift_move ?shift
             (snd (comma_decisive_endpoint_packet ((r+?shift) mod 924) ?base))) =
        comma_source_continuation_transport ?shift
          (comma_source_continuation_action_of_packet
            (fst (comma_decisive_endpoint_packet ((r+?shift) mod 924) ?base),
             snd (comma_decisive_endpoint_packet ((r+?shift) mod 924) ?base)))"
      by (rule comma_source_continuation_action_shift)
    show ?thesis using packet_cong action_shift by simp
  qed
  show ?thesis using slot packet_action by simp
qed

ML \<open>
  Thm.consolidate @{thms comma_source_continuation_base_admitted
    comma_source_continuation_signature_slot comma_source_continuation_apply_exact};
  Comma_Decisive_Endpoint_Profile.report "Source continuation DAG stage=application facts consolidated"
\<close>

lemma comma_source_continuation_goto_decreases:
  assumes source: "comma_round_admitted source"
    and action:
      "comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet r source) =
        Comma_Continuation_Goto next shift"
  shows "comma_round_admitted next \<and>
    9-comma_sector_number next < 9-comma_sector_number source"
proof -
  obtain target move where raw_packet:
    "comma_decisive_endpoint_packet r source=(target,move)"
    by (cases "comma_decisive_endpoint_packet r source") simp
  have packet_components:
    "fst (comma_decisive_endpoint_packet r source)=target"
    "snd (comma_decisive_endpoint_packet r source)=move"
    using raw_packet by simp_all
  obtain successor where move_eq: "move=Comma_Next successor"
    and internal: "\<not> comma_round_crossing target successor"
    and base_next: "next=comma_source_continuation_base successor"
    using action by (cases move)
      (auto simp: raw_packet split: if_splits)
  have target_admitted: "comma_round_admitted target"
    using comma_decisive_packet_target_admitted[OF source, of r]
      packet_components(1) by simp
  have target_eq: "target=comma_decisive_sector_target r source"
    using packet_components(1)
    by (simp only: comma_decisive_endpoint_packet_def Let_def fst_conv)
  have fast_step_eq:
    "comma_fast_step (r mod 924) target=move"
    using packet_components(2)
    by (simp only: comma_decisive_endpoint_packet_def Let_def snd_conv target_eq)
  have move:
    "comma_fast_step (r mod 924) target=Comma_Next successor"
    using fast_step_eq move_eq by simp
  have decrease:
    "9-comma_sector_number successor<9-comma_sector_number source"
    by (rule comma_decisive_endpoint_successor_decreases[OF source, where r=r])
      (use move internal in \<open>simp_all add: target_eq\<close>)
  have successor_admitted: "comma_round_admitted successor"
    using comma_round_next_admitted[OF target_admitted, of r successor] move
    by (simp only: comma_fast_step_correct)
  show ?thesis using decrease successor_admitted base_next target_eq
    by (cases successor) simp_all
qed

ML \<open>
  Thm.consolidate @{thms comma_source_continuation_goto_decreases};
  Comma_Decisive_Endpoint_Profile.report "Source continuation DAG stage=goto decrease consolidated"
\<close>

ML \<open>
  Comma_Decisive_Endpoint_Profile.report "Source continuation DAG stage=oracle audit entered";
  val checked = @{thms comma_source_continuation_reconstruct
    comma_source_continuation_base_idempotent comma_source_continuation_base_sector
    comma_source_continuation_base_shift_position comma_source_continuation_shift_position
    comma_source_continuation_action_shift
    comma_source_continuation_target_transport comma_source_continuation_packet_transport
    comma_source_continuation_id_base comma_source_continuation_id_shift
    comma_source_continuation_equal_id_action
    comma_source_continuation_base_admitted comma_source_continuation_signature_slot
    comma_source_continuation_apply_exact comma_source_continuation_goto_decreases}
  val _ = Thm.consolidate checked
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Source continuation transport depends on an oracle"
  val _ = Comma_Decisive_Endpoint_Profile.report "Source continuation DAG stage=oracle audit checked"
\<close>

end
