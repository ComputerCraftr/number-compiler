theory Reverse_Two_Cell_Equations
  imports Reverse_Invariant
begin

text \<open>Ground transition equations, independently checked by simplification
against the arithmetic definitions. Generated using the canonical pair_step
oracle only to propose statements; no proposed value is trusted.\<close>

lemma two_cell_steps [simp]:
  "step [0,0] = [0,0]"
  "step [1,1] = [2,2]"
  "step [1,2,1] = [2,4,2]"
  "step [1,9,16,9,1] = [3,9,12,9,3]"
  "step [2,2] = [4,4]"
  "step [2,2,2,2] = [4,4,4,4]"
  "step [2,4,2] = [4,8,4]"
  "step [3,3] = [6,6]"
  "step [3,6,3] = [6,12,6]"
  "step [4,4] = [8,8]"
  "step [4,8,4] = [8,16,8]"
  "step [4,8,8,4] = [8,16,16,8]"
  "step [5,5] = [10,10]"
  "step [5,10,5] = [11,0,11]"
  "step [6,6] = [12,12]"
  "step [6,12,6] = [13,4,13]"
  "step [6,14,14,6] = [13,9,9,13]"
  "step [7,7] = [14,14]"
  "step [7,14,7] = [15,8,15]"
  "step [8,8] = [16,16]"
  "step [8,11,11,8] = [17,3,3,17]"
  "step [8,16,8] = [17,12,17]"
  "step [9,9] = [18,18]"
  "step [9,18,9] = [10,8,8,10]"
  "step [10,8,8,10] = [1,9,16,9,1]"
  "step [10,10] = [1,2,1]"
  "step [11,0,11] = [2,2,2,2]"
  "step [11,11] = [2,4,2]"
  "step [12,12] = [3,6,3]"
  "step [13,4,13] = [4,8,8,4]"
  "step [13,13] = [4,8,4]"
  "step [14,14] = [5,10,5]"
  "step [15,8,15] = [6,14,14,6]"
  "step [15,15] = [6,12,6]"
  "step [16,16] = [7,14,7]"
  "step [17,12,17] = [8,11,11,8]"
  "step [17,17] = [8,16,8]"
  "step [18,18] = [9,18,9]"
  by (simp_all add: step_def digits_def carry_out_def domain_def)

lemma observation_intervals:
  "[0..<19] = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]"
  "[0..<5] = [0,1,2,3,4]"
  by code_simp+

lemma first_four_runs:
  "run step 0 ss = ss"
  "run step 1 ss = step ss"
  "run step 2 ss = step (step ss)"
  "run step 3 ss = step (step (step ss))"
  "run step 4 ss = step (step (step (step ss)))"
  by (simp_all add: eval_nat_numeral)

end
