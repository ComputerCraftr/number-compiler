theory Comma_Orbit_Words
  imports Comma_Decade_Orbit.Comma_Endpoint_Orbit_Interface
begin

text \<open>The packed recurrence below powers already constructed words.
Only its base refers to the semantic one-decade specification. It does not
evaluate representative raw blocks again at higher powers. A concrete base
mask certificate and its sharing/cost bound are separate obligations.\<close>
primrec comma_orbit_live_masks :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_orbit_live_masks 0 = (\<lambda>i j.
    comma_phase_mask (\<lambda>r. comma_orbit_word 0 r i=Comma_Word_Live j))"
| "comma_orbit_live_masks (Suc k) =
    comma_live_mask_compose 46 (2^k) (comma_orbit_live_masks k) (comma_orbit_live_masks k)"

primrec comma_orbit_stop_masks ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_decade_terminal \<Rightarrow> nat" where
  "comma_orbit_stop_masks 0 = (\<lambda>i h terminal.
    comma_phase_mask (\<lambda>r. comma_orbit_word 0 r i=Comma_Word_Stop h terminal))"
| "comma_orbit_stop_masks (Suc k) =
    comma_stop_mask_compose 46 (2^k) (comma_orbit_live_masks k)
      (comma_orbit_stop_masks k) (comma_orbit_stop_masks k)"

theorem comma_orbit_masks_refine:
  "comma_word_masks_correct (comma_orbit_word k)
    (comma_orbit_live_masks k) (comma_orbit_stop_masks k)"
proof (induction k)
  case 0
  show ?case by (simp add: comma_word_masks_correct_def comma_phase_mask_member)
next
  case (Suc k)
  have composed: "comma_word_masks_correct
      (comma_word_then (2^k) (comma_orbit_word k) (comma_orbit_word k))
      (comma_live_mask_compose 46 (2^k) (comma_orbit_live_masks k) (comma_orbit_live_masks k))
      (comma_stop_mask_compose 46 (2^k) (comma_orbit_live_masks k)
        (comma_orbit_stop_masks k) (comma_orbit_stop_masks k))"
    by (rule comma_word_masks_compose_correct[OF Suc.IH Suc.IH])
      (rule comma_orbit_word_live_bound, assumption)
  show ?case using composed
    by (auto simp: comma_word_masks_correct_def comma_orbit_word_square_all)
qed

text \<open>This discharges the generic word-square refinement premise for
all admitted sources and all powers. It supplies no concrete base masks,
all-stop coverage, constructor bound, future-safety rank, or live-cycle check.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_decade_atom_orbit_congruent comma_decade_power_orbit_congruent
      comma_orbit_word_refines comma_orbit_word_square comma_orbit_masks_refine})
    then () else error "Orbit word refinement depends on an oracle";
\<close>

end
