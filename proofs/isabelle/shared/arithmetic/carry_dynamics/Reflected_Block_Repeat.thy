theory Reflected_Block_Repeat
  imports Reflected_Padded_Digit_Word
begin

text \<open>Nonempty decimal tiles erase the inlet carry for multipliers two and
five. Their first emitted tile can therefore differ from the steady tile.\<close>

lemma reflected_nonempty_tile_exit_independent:
  assumes multiplier: "m = 2 \<or> m = 5"
      and decimal: "list_all (\<lambda>d. d < 10) tile"
      and nonempty: "tile \<noteq> []"
      and left: "c < m" and right: "c' < m"
  shows "snd (decimal_block_run m tile c) = snd (decimal_block_run m tile c')"
proof -
  obtain d ds where tile: "tile = d # ds" using nonempty by (cases tile) auto
  have digit: "d < 10" using decimal tile by simp
  have a: "(m*d+c) div 10 = m*d div 10"
    by (rule reflected_multiplier_incoming_carry_independent[OF multiplier digit left])
  have b: "(m*d+c') div 10 = m*d div 10"
    by (rule reflected_multiplier_incoming_carry_independent[OF multiplier digit right])
  show ?thesis by (simp only: tile decimal_block_run_simps Let_def a b snd_conv)
qed

lemma decimal_steady_tile_repeats:
  assumes stable: "snd (decimal_block_run m tile c) = c"
  shows "decimal_block_run m (concat (replicate n tile)) c =
    (concat (replicate n (fst (decimal_block_run m tile c))), c)"
  using stable
  by (induction n) (simp_all add: decimal_block_run_append Let_def)

theorem reflected_first_steady_tile:
  assumes multiplier: "m = 2 \<or> m = 5"
      and decimal: "list_all (\<lambda>d. d < 10) tile"
      and nonempty: "tile \<noteq> []" and inlet: "c < m"
  defines "steady \<equiv> snd (decimal_block_run m tile c)"
  shows "decimal_block_run m (concat (replicate (Suc n) tile)) c =
    (fst (decimal_block_run m tile c) @
      concat (replicate n (fst (decimal_block_run m tile steady))), steady)"
proof -
  have bound: "steady < m"
    unfolding steady_def by (rule reflected_digit_pass_carry_bound[OF multiplier decimal inlet])
  have stable: "snd (decimal_block_run m tile steady) = steady"
    using reflected_nonempty_tile_exit_independent[OF multiplier decimal nonempty bound inlet]
    by (simp only: steady_def)
  have repeated:
    "decimal_block_run m (concat (replicate n tile)) steady =
      (concat (replicate n (fst (decimal_block_run m tile steady))), steady)"
    by (rule decimal_steady_tile_repeats[OF stable])
  show ?thesis
    by (simp only: decimal_block_repeat_step steady_def[symmetric] repeated Let_def
        fst_conv snd_conv)
qed

theorem reflected_head_first_steady_tail:
  fixes h first steady
  assumes multiplier: "m = 2 \<or> m = 5"
      and head: "list_all (\<lambda>d. d < 10) head"
      and tile: "list_all (\<lambda>d. d < 10) tile"
      and nonempty: "tile \<noteq> []" and inlet: "c < m"
      and h_def: "h = decimal_block_run m head c"
      and first_def: "first = decimal_block_run m tile (snd h)"
      and steady_def: "steady = snd first"
  shows "decimal_block_run m (head @ concat (replicate (Suc n) tile) @ tail) c =
    (let last = decimal_block_run m tail steady in
      (fst h @ fst first @
        concat (replicate n (fst (decimal_block_run m tile steady))) @ fst last,
       snd last))"
proof -
  have head_carry: "snd h < m"
    unfolding h_def by (rule reflected_digit_pass_carry_bound[OF multiplier head inlet])
  have tile_run:
    "decimal_block_run m (concat (replicate (Suc n) tile)) (snd h) =
      (fst first @ concat (replicate n (fst (decimal_block_run m tile steady))), steady)"
    using reflected_first_steady_tile[OF multiplier tile nonempty head_carry, of n]
    by (simp only: first_def steady_def)
  show ?thesis
    unfolding decimal_head_tile_tail h_def[symmetric]
    by (simp only: tile_run Let_def fst_conv snd_conv append_assoc)
qed

end
