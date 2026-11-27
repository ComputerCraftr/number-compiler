theory Reverse_Native_Hinge_Physical_Clock
  imports Reverse_Native_Slab_Collars "Reverse_Residuals.Reverse_Native_Hinge_Center"
    "Reverse_Residuals.Reverse_Native_Hinge_Successor"
begin

text \<open>The native cell pull reads the first return bit at the original
column and the second at its compiled successor. Only the two returned
bits at the outside edge are physical width births.\<close>

fun hinge_cell_pull :: "nat list \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<times> bool" where
  "hinge_cell_pull [] b e = (b,e)"
| "hinge_cell_pull (s#rs) b e =
    (let inlet = carry_apply (domain s) b;
         (a,high) = reverse_native_hinge1_compile (rev rs) inlet;
         low = (s + (if a then 1 else 0)) mod 10;
         next = low + (if high=0 then (s+(if b then 1 else 0)) mod 10 else high-1)
     in hinge_cell_pull rs inlet (carry_apply (domain next) e))"

lemma hinge_cell_pull_exact:
  "hinge_cell_pull rs b e =
    (carry_out b rs, carry_out e (reverse_native_hinge_next_half_rev rs b))"
  by (induction rs arbitrary: b e) (simp_all add: carry_out_def Let_def split: prod.splits)

theorem reverse_native_compiled_hinge_width_clock:
  fixes half :: "nat list" and center :: "nat option"
    and first successor middle :: "nat list" and b0 b1 :: bool
    and edge :: "bool \<times> nat" and child :: reverse_hinge1
  defines "first \<equiv> reverse_native_hinge_source half center"
    and "b0 \<equiv> reverse_native_hinge_inner_inlet half center"
    and "edge \<equiv> fst (reverse_native_hinge2_compile half b0)"
    and "child \<equiv> snd (reverse_native_hinge2_compile half b0)"
    and "successor \<equiv> reverse_native_hinge_next_half half b0"
    and "middle \<equiv> reverse_native_hinge2_middle center (fst edge) (snd edge)"
    and "b1 \<equiv> reverse_native_hinge2_second_inlet child center (fst edge) (snd edge)"
  shows "step first = successor @ middle @ rev successor"
    and "hinge_cell_pull (rev half) b0 b1 = (carry_out False first, carry_out False (step first))"
    and "length (step (step first)) = length first +
      (if fst (hinge_cell_pull (rev half) b0 b1) then 1 else 0) +
      (if snd (hinge_cell_pull (rev half) b0 b1) then 1 else 0)"
proof -
  let ?mid = "case center of None \<Rightarrow> [] | Some d \<Rightarrow> [2*d]"
  let ?n = "length half"
  let ?a = "carry_out False half"
  let ?extra = "\<lambda>h::nat. if h=0 then [] else [h-1]"
  have src: "first = half @ ?mid @ rev half" by (simp add: first_def reverse_native_hinge_source_def)
  have inlet: "b0 = carry_out ?a ?mid"
    by (cases center) (simp_all add: b0_def reverse_native_hinge_inner_inlet_def
       carry_out_def reverse_native_center_inlet_exact)
  have e: "edge = reverse_native_hinge1_compile half b0"
    using reverse_native_hinge2_compiled_child[of half b0] by (simp add: edge_def)
  have a: "fst edge = ?a" using reverse_native_hinge1_source_response[of half b0] e by simp
  have high: "snd edge = snd (reverse_native_hinge1_compile half (carry_out ?a ?mid))"
    by (simp only: e inlet)
  have clock: "carry_out False first = (snd edge \<noteq> 0)"
    using reverse_native_hinge_middle_word(1)[where half = half and middle = "?mid"] by (simp only: src high)
  have clen: "length (digits first) - 2*?n = length ?mid + (if snd edge=0 then 0 else 1)"
    using clock by (simp add: src length_digits_exact)
  have word: "slab_center ?n (digits first) = emit ?a ?mid @ ?extra (snd edge)"
    unfolding slab_center_def apply (subst clen) using reverse_native_hinge_middle_word(2)[where half = half and middle = "?mid"]
    by (simp only: clen high src)
  have center: "slab_center ?n (step first) = middle"
    unfolding slab_center_step using word
    by (cases center; cases "snd edge=0"; cases ?a)
       (simp_all add: middle_def reverse_native_hinge2_middle_def slab_pair_digits_def a Let_def)
  have prefix: "take ?n (step first) = successor"
    unfolding first_def successor_def b0_def by (rule reverse_native_hinge_physical_half[symmetric])
  have room: "2*?n \<le> length (step first)" by (simp add: src length_digits_exact)
  show decomposition: "step first = successor @ middle @ rev successor"
    using slab_source_split[OF room step_symmetric] by (simp only: prefix center)
  have child: "child = reverse_native_hinge1_compile successor"
    using reverse_native_hinge2_compiled_child[of half b0] by (simp add: child_def successor_def)
  have second: "carry_out b1 (rev successor) = carry_out False (step first)"
    unfolding decomposition b1_def middle_def child
    by (simp add: reverse_native_hinge2_second_inlet_exact carry_out_append)
  have born: "carry_out b0 (rev half) = carry_out False first"
    by (simp add: src inlet carry_out_append)
  show bits: "hinge_cell_pull (rev half) b0 b1 = (carry_out False first, carry_out False (step first))"
    using second born by (simp add: hinge_cell_pull_exact successor_def reverse_native_hinge_next_half_def)
  show "length (step (step first)) = length first +
      (if fst (hinge_cell_pull (rev half) b0 b1) then 1 else 0) +
      (if snd (hinge_cell_pull (rev half) b0 b1) then 1 else 0)"
    by (simp add: bits length_digits_exact)
qed

ML \<open>
  val checked = @{thms reverse_native_compiled_hinge_width_clock};
  val _ = if null (Thm_Deps.all_oracles checked) then () else error "Compiled hinge clock oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped compiled hinge clock proof" else ();
\<close>
end
