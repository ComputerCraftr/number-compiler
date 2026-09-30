theory Comma_Sector_Alphabet
  imports Comma_Fast_Control
begin

text \<open>The Entry arithmetic key contains only its leading sector, admitted
local offset and short cyclotomic phase. Absolute phase and exponent transport
remain application data. Near already has the phase-independent (f,h) owner.
These equations let the shared kernel memoize the endpoint before rebuilding
its occurrence wrapper; they introduce neither a table of assumed successors
nor a second evaluator.\<close>

definition comma_entry_alphabet_phase ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_entry_alphabet_phase f r delta x =
    (((r mod 924 + delta) mod 924 + 919) mod
      comma_short_period (comma_finite_period_fast f (x mod 10)))"

definition comma_entry_alphabet_endpoint ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_entry_alphabet_endpoint f x k =
    (let P=comma_finite_period_fast f (x mod 10);
         e=if f<9 then 1 else 0;
         power=comma_power_table P ! k;
         h=1+e+nat ((int power-int x-int (1+e)) mod int P)
     in snd (comma_near_closed_germ f h))"

lemma comma_entry_alphabet_endpoint_exact:
  "comma_entry_alphabet_endpoint f x (comma_entry_alphabet_phase f r delta x) =
    snd (comma_near_closed_germ f
      (comma_finite_headroom_fast f (r mod 924) delta x))"
  by (simp add: comma_entry_alphabet_endpoint_def comma_entry_alphabet_phase_def
      comma_finite_headroom_fast_def comma_power_residue_fast_def Let_def)

text \<open>The headroom returned by the Entry arithmetic is an occurrence value,
but its cache identity is only the short phase. The exact offset remains in
the key because it is subtracted from the modular power; the linear exponent
and absolute phase are transported into one residue modulo the short period.\<close>
lemma comma_finite_headroom_fast_phase_normalized:
  assumes f: "1\<le>f" "f\<le>9"
  shows "comma_finite_headroom_fast f residue delta offset =
    comma_finite_headroom_fast f
      ((residue + delta) mod
        comma_short_period (comma_finite_period_fast f (offset mod 10)))
      0 offset"
proof -
  let ?P = "comma_finite_period f (offset mod 10)"
  let ?T = "comma_short_period ?P"
  have fast_period:
    "comma_finite_period_fast f (offset mod 10) = ?P"
    by (rule comma_finite_period_fast_correct[OF f]) simp
  have phase:
    "(residue + delta) mod ?T =
      (((residue + delta) mod ?T) + 0) mod ?T"
    by simp
  have exact:
    "comma_finite_headroom f residue delta offset =
      comma_finite_headroom f ((residue + delta) mod ?T) 0 offset"
    by (rule comma_entry_headroom_short_phase[OF f phase])
  show ?thesis
    using comma_finite_headroom_fast_correct[OF f, of residue delta offset]
      comma_finite_headroom_fast_correct[OF f,
        of "(residue + delta) mod
          comma_short_period (comma_finite_period_fast f (offset mod 10))" 0 offset]
      exact fast_period
    by simp
qed

lemma comma_sector_entry_alphabet:
  "comma_fast_sector_target r (Comma_Entry f delta x) =
    (if f<1 \<or> 9<f \<or> 98<x then Comma_Entry f delta x
     else Comma_Near f delta
       (comma_entry_alphabet_endpoint f x (comma_entry_alphabet_phase f r delta x)))"
  by (simp add: comma_entry_alphabet_endpoint_exact Let_def)

lemma comma_sector_near_alphabet:
  "comma_fast_sector_target r (Comma_Near f delta h) =
    Comma_Near f delta (snd (comma_near_closed_germ f h))"
  by simp

lemma comma_entry_alphabet_phase_bound:
  assumes "1\<le>f" "f\<le>9"
  shows "comma_entry_alphabet_phase f r delta x <
    comma_short_period (comma_finite_period_fast f (x mod 10))"
proof -
  have period: "comma_finite_period_fast f (x mod 10) =
      comma_finite_period f (x mod 10)"
    by (rule comma_finite_period_fast_correct[OF assms]) simp
  have catalog: "comma_finite_period_fast f (x mod 10)\<in>comma_cycle_displacements"
    using comma_finite_period_in_catalog[rule_format, of f "x mod 10"] assms
    by (auto simp: period)
  have positive: "0<comma_short_period (comma_finite_period_fast f (x mod 10))"
    using comma_short_period_catalog[OF catalog] by blast
  show ?thesis using positive by (simp add: comma_entry_alphabet_phase_def)
qed

lemma comma_entry_alphabet_refines:
  assumes valid: "comma_round_admitted (Comma_Entry f delta x)"
  shows "snd (comma_sector_control r (Comma_Entry f delta x)) =
    Comma_Near f delta
      (comma_entry_alphabet_endpoint f x (comma_entry_alphabet_phase f r delta x))"
  using comma_fast_sector_refines[OF valid, of r]
    comma_fast_sector_target_correct[of r "Comma_Entry f delta x"] valid
  by (simp add: comma_sector_entry_alphabet comma_entry_alphabet_endpoint_exact)

text \<open>Transported occurrences can share an endpoint equation only when
the complete arithmetic key agrees. The output occurrence retains its own
exponent delta. This is local endpoint reuse, not a decade termination theorem
or a weighted-sector theorem.\<close>
lemma comma_entry_alphabet_transport:
  assumes f: "1\<le>f" "f\<le>9" and x: "x\<le>98"
    and phase: "comma_entry_alphabet_phase f r delta x =
      comma_entry_alphabet_phase f r' delta' x"
  shows "comma_fast_sector_target r' (Comma_Entry f delta' x) =
    Comma_Near f delta'
      (comma_entry_alphabet_endpoint f x (comma_entry_alphabet_phase f r delta x))"
  using assms
  by (simp only: comma_sector_entry_alphabet; simp)

lemma comma_near_alphabet_phase_independent:
  "comma_fast_sector_target r (Comma_Near f delta h) =
    comma_fast_sector_target r' (Comma_Near f delta h)"
  by (simp only: comma_sector_near_alphabet)

text \<open>The seam event is shared at zero exponent delta. Occurrence
transport is applied after that canonical event has been checked and reused.\<close>
lemma comma_fast_near_event_alphabet:
  "comma_fast_step r (Comma_Near f delta h)=
    comma_shift_move delta (comma_near_event f h)"
  using comma_near_step_delta_transport[of r f 0 delta h 0]
  by (simp only: add_0_left comma_fast_step_correct comma_near_event_def)

lemma comma_near_event_fast:
  "comma_near_event f h=comma_fast_step 0 (Comma_Near f 0 h)"
  by (simp only: comma_near_event_def comma_fast_step_correct)

lemmas comma_near_event_alphabet_eval =
  comma_near_event_fast[unfolded comma_fast_step.simps]

text \<open>A complete local jump includes the seam decision, not only the
endpoint. Its semantic key is (sector, offset, short phase). The receiving
absolute phase and remaining round depth belong to the continuation.\<close>
definition comma_entry_jump ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_round_result + comma_finite_position" where
  "comma_entry_jump f x k =
    (let t=Comma_Near f 0 (comma_entry_alphabet_endpoint f x k) in
      case comma_fast_step 0 t of
        Comma_Next target \<Rightarrow>
          if comma_round_crossing t target then Inl (Comma_Round_Cross target)
          else Inr target
      | Comma_Fork a d \<Rightarrow> Inl (Comma_Round_Fork a d)
      | Comma_Landmine d \<Rightarrow> Inl (Comma_Round_Landmine d)
      | Comma_Invalid \<Rightarrow> Inl Comma_Round_Invalid)"

lemma comma_entry_jump_transport:
  assumes "comma_entry_alphabet_phase f r 0 x=comma_entry_alphabet_phase f s 0 x"
  shows "comma_entry_jump f x (comma_entry_alphabet_phase f r 0 x)=
    comma_entry_jump f x (comma_entry_alphabet_phase f s 0 x)"
  using assms by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_entry_alphabet_endpoint_exact
      comma_finite_headroom_fast_phase_normalized comma_sector_entry_alphabet
      comma_sector_near_alphabet comma_entry_alphabet_phase_bound
      comma_entry_alphabet_refines comma_entry_alphabet_transport
      comma_near_alphabet_phase_independent comma_fast_near_event_alphabet
      comma_near_event_alphabet_eval}) then ()
    else error "Sector alphabet refinement depends on an oracle";
\<close>
end
