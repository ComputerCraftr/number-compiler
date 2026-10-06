theory Comma_Source_Continuation_DAG
  imports Comma_Decisive_Endpoint_Quotient
begin

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

lemma comma_source_continuation_target_transport:
  "comma_decisive_sector_target r source =
    comma_shift_position (comma_source_continuation_shift source)
      (comma_decisive_sector_target
        ((r+comma_source_continuation_shift source) mod 924)
        (comma_source_continuation_base source))"
  by (cases source)
    (simp_all add: comma_decisive_sector_target.simps Let_def
      comma_shift_position.simps split: option.splits prod.splits)

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
  have step:
    "comma_fast_step (r mod 924) (comma_shift_position ?delta ?target)=
      comma_shift_move ?delta (comma_fast_step ?phase ?target)"
    using comma_finite_step_phase_shift[of "r mod 924" ?delta ?target]
    by (simp only: comma_fast_step_correct; simp add: phase)
  show ?thesis using target step
    by (simp add: comma_decisive_endpoint_packet_def Let_def)
qed

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
  show ?thesis using slot packet
    by (simp add: comma_source_continuation_action_shift)
qed

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
  obtain successor where move_eq: "move=Comma_Next successor"
    and internal: "\<not> comma_round_crossing target successor"
    and base_next: "next=comma_source_continuation_base successor"
    using action by (cases move)
      (auto simp: raw_packet split: if_splits)
  have packet:
    "comma_decisive_endpoint_packet r source=(target,Comma_Next successor)"
    using raw_packet move_eq by simp
  have target_admitted: "comma_round_admitted target"
    using comma_decisive_packet_target_admitted[OF source, of r] packet by simp
  have move:
    "comma_fast_step (r mod 924) target=Comma_Next successor"
    using packet by (auto simp: comma_decisive_endpoint_packet_def Let_def)
  have fast_target:
    "target=comma_decisive_sector_target r source"
    using packet by (auto simp: comma_decisive_endpoint_packet_def Let_def)
  have decrease:
    "9-comma_sector_number successor<9-comma_sector_number source"
    by (rule comma_decisive_endpoint_successor_decreases[OF source])
      (use move internal fast_target in simp_all)
  have successor_admitted: "comma_round_admitted successor"
    using comma_round_next_admitted[OF target_admitted, of r successor] move
    by (simp only: comma_fast_step_correct)
  show ?thesis using decrease successor_admitted base_next
    by (cases successor) simp_all
qed

ML \<open>
  val checked = @{thms comma_source_continuation_reconstruct
    comma_source_continuation_base_idempotent comma_source_continuation_base_sector
    comma_source_continuation_base_shift_position comma_source_continuation_shift_position
    comma_source_continuation_action_shift
    comma_source_continuation_target_transport comma_source_continuation_packet_transport
    comma_source_continuation_id_base comma_source_continuation_id_shift
    comma_source_continuation_equal_id_action
    comma_source_continuation_base_admitted comma_source_continuation_signature_slot
    comma_source_continuation_apply_exact comma_source_continuation_goto_decreases}
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Source continuation transport depends on an oracle"
\<close>

end
