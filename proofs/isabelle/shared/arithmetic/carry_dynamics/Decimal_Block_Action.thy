theory Decimal_Block_Action
  imports Decimal_Normalization_Morphism
begin

text \<open>Digits are supplied in multiplication-input order. The output list is
in the same order and the carry is passed to the next column.\<close>

definition decimal_block_run :: "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat" where
  "decimal_block_run m ds c = decimal_multiplier_columns m c ds"

lemma decimal_block_run_simps [simp]:
  "decimal_block_run m [] c = ([], c)"
  "decimal_block_run m (d # ds) c =
    (let z = m * d + c;
         result = decimal_block_run m ds (z div 10)
     in (z mod 10 # fst result, snd result))"
  by (simp_all add: decimal_block_run_def Let_def split: prod.splits)

lemma decimal_block_run_append:
  "decimal_block_run m (xs @ ys) c =
    (let left = decimal_block_run m xs c;
         right = decimal_block_run m ys (snd left)
     in (fst left @ fst right, snd right))"
  by (induction xs arbitrary: c) (auto simp: Let_def split: prod.splits)

lemma decimal_block_repeat_step:
  "decimal_block_run m (concat (replicate (Suc n) tile)) c =
    (let first = decimal_block_run m tile c;
         rest = decimal_block_run m (concat (replicate n tile)) (snd first)
     in (fst first @ fst rest, snd rest))"
  by (simp only: replicate.simps concat.simps decimal_block_run_append)

lemma decimal_head_tile_tail:
  "decimal_block_run m (head @ concat (replicate n tile) @ tail) c =
    (let left = decimal_block_run m head c;
         middle = decimal_block_run m (concat (replicate n tile)) (snd left);
         right = decimal_block_run m tail (snd middle)
     in (fst left @ fst middle @ fst right, snd right))"
  by (simp add: decimal_block_run_append Let_def split: prod.splits)

end
