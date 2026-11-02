theory Double_Reverse_Group_Ring_Four_Port
  imports Double_Reverse_Source_Window_Refinement
    Double_Reverse_Group_Ring_Carry_Cut
begin

section \<open>Four-port two-pass word action\<close>

record double_reverse_four_port_row =
  double_reverse_forward_out :: nat
  double_reverse_reverse_out :: nat
  double_reverse_output_word :: "nat list"

fun double_reverse_forward_pass ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat" where
  "double_reverse_forward_pass [] incoming = ([], incoming)"
| "double_reverse_forward_pass (digit#digits) incoming =
    (let total = 2*digit + incoming;
         (rest, outgoing) = double_reverse_forward_pass digits (total div 10)
     in (total mod 10 # rest, outgoing))"

fun double_reverse_reverse_pass ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat list \<times> nat" where
  "double_reverse_reverse_pass [] incoming = ([], incoming)"
| "double_reverse_reverse_pass (digit#digits) incoming =
    (let (rest, carry) = double_reverse_reverse_pass digits incoming;
         total = 2*digit + carry
     in (total mod 10 # rest, total div 10))"

definition double_reverse_four_port_row ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      double_reverse_four_port_row" where
  "double_reverse_four_port_row source forward_in reverse_in =
    (let (middle, forward_out) =
           double_reverse_forward_pass source forward_in;
         (output, reverse_out) =
           double_reverse_reverse_pass middle reverse_in
     in \<lparr>double_reverse_forward_out=forward_out,
          double_reverse_reverse_out=reverse_out,
          double_reverse_output_word=output\<rparr>)"

definition double_reverse_four_port_action ::
    "nat list \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow>
      double_reverse_four_port_row)" where
  "double_reverse_four_port_action source = double_reverse_four_port_row source"

lemma double_reverse_forward_pass_append:
  "double_reverse_forward_pass (left @ right) incoming =
    (let (left_output, middle) = double_reverse_forward_pass left incoming;
         (right_output, outgoing) = double_reverse_forward_pass right middle
     in (left_output @ right_output, outgoing))"
  by (induction left arbitrary: incoming)
     (simp_all add: Let_def split: prod.splits)

lemma double_reverse_reverse_pass_append:
  "double_reverse_reverse_pass (left @ right) incoming =
    (let (right_output, middle) = double_reverse_reverse_pass right incoming;
         (left_output, outgoing) = double_reverse_reverse_pass left middle
     in (left_output @ right_output, outgoing))"
  by (induction left arbitrary: incoming)
     (simp_all add: Let_def split: prod.splits)

definition double_reverse_four_port_then ::
    "(nat \<Rightarrow> nat \<Rightarrow> double_reverse_four_port_row) \<Rightarrow>
     (nat \<Rightarrow> nat \<Rightarrow> double_reverse_four_port_row) \<Rightarrow>
      (nat \<Rightarrow> nat \<Rightarrow> double_reverse_four_port_row)" where
  "double_reverse_four_port_then left right =
    (\<lambda>forward_in reverse_in.
      (let left_first = left forward_in reverse_in;
           right_row = right (double_reverse_forward_out left_first) reverse_in;
           left_row = left forward_in (double_reverse_reverse_out right_row)
       in \<lparr>double_reverse_forward_out=double_reverse_forward_out right_row,
            double_reverse_reverse_out=double_reverse_reverse_out left_row,
            double_reverse_output_word=
      double_reverse_output_word left_row @
                double_reverse_output_word right_row\<rparr>))"

theorem double_reverse_four_port_action_append:
  "double_reverse_four_port_action (left @ right) =
    double_reverse_four_port_then
      (double_reverse_four_port_action left)
      (double_reverse_four_port_action right)"
proof (rule ext)+
  fix forward_in reverse_in
  obtain left_middle left_forward where left_forward:
    "double_reverse_forward_pass left forward_in =
      (left_middle,left_forward)"
    by (cases "double_reverse_forward_pass left forward_in") auto
  obtain right_middle right_forward where right_forward:
    "double_reverse_forward_pass right left_forward =
      (right_middle,right_forward)"
    by (cases "double_reverse_forward_pass right left_forward") auto
  obtain right_output middle_reverse where right_reverse:
    "double_reverse_reverse_pass right_middle reverse_in =
      (right_output,middle_reverse)"
    by (cases "double_reverse_reverse_pass right_middle reverse_in") auto
  obtain left_output final_reverse where left_reverse:
    "double_reverse_reverse_pass left_middle middle_reverse =
      (left_output,final_reverse)"
    by (cases "double_reverse_reverse_pass left_middle middle_reverse") auto
  have forward:
    "double_reverse_forward_pass (left @ right) forward_in =
      (left_middle @ right_middle,right_forward)"
    using double_reverse_forward_pass_append[of left right forward_in]
      left_forward right_forward by (simp add: Let_def)
  have reverse:
    "double_reverse_reverse_pass (left_middle @ right_middle) reverse_in =
      (left_output @ right_output,final_reverse)"
    using double_reverse_reverse_pass_append[of left_middle right_middle reverse_in]
      right_reverse left_reverse by (simp add: Let_def)
  have combined:
    "double_reverse_four_port_action (left @ right) forward_in reverse_in =
      \<lparr>double_reverse_forward_out=right_forward,
        double_reverse_reverse_out=final_reverse,
        double_reverse_output_word=left_output @ right_output\<rparr>"
    unfolding double_reverse_four_port_action_def
      double_reverse_four_port_row_def
    using forward reverse by (simp add: Let_def)
  have left_first_forward:
    "double_reverse_forward_out
       (double_reverse_four_port_action left forward_in reverse_in) =
       left_forward"
    unfolding double_reverse_four_port_action_def
      double_reverse_four_port_row_def
    using left_forward
    by (cases "double_reverse_reverse_pass left_middle reverse_in")
       (simp add: Let_def)
  have right_row:
    "double_reverse_four_port_action right left_forward reverse_in =
      \<lparr>double_reverse_forward_out=right_forward,
        double_reverse_reverse_out=middle_reverse,
        double_reverse_output_word=right_output\<rparr>"
    unfolding double_reverse_four_port_action_def
      double_reverse_four_port_row_def
    using right_forward right_reverse by (simp add: Let_def)
  have left_row:
    "double_reverse_four_port_action left forward_in middle_reverse =
      \<lparr>double_reverse_forward_out=left_forward,
        double_reverse_reverse_out=final_reverse,
        double_reverse_output_word=left_output\<rparr>"
    unfolding double_reverse_four_port_action_def
      double_reverse_four_port_row_def
    using left_forward left_reverse by (simp add: Let_def)
  show "double_reverse_four_port_action (left @ right) forward_in reverse_in =
      double_reverse_four_port_then
        (double_reverse_four_port_action left)
        (double_reverse_four_port_action right) forward_in reverse_in"
    unfolding double_reverse_four_port_then_def
    using combined left_first_forward right_row left_row
    by (simp add: Let_def)
qed

theorem double_reverse_four_port_action_join_associative:
  "double_reverse_four_port_then
      (double_reverse_four_port_then
        (double_reverse_four_port_action first)
        (double_reverse_four_port_action middle))
      (double_reverse_four_port_action final) =
    double_reverse_four_port_then
      (double_reverse_four_port_action first)
      (double_reverse_four_port_then
        (double_reverse_four_port_action middle)
        (double_reverse_four_port_action final))"
  by (simp only: double_reverse_four_port_action_append[symmetric]
      append_assoc)

lemma double_reverse_forward_single_digit:
  assumes digit: "digit < 10" and incoming: "incoming \<le> 1"
  shows "double_reverse_forward_pass [digit] incoming =
    ([(2*digit+incoming) mod 10], if 5 \<le> digit then 1 else 0)"
proof -
  note balance = decimal_double_digit_carry[OF digit incoming]
  have division:
    "2*digit+incoming =
      10*((2*digit+incoming) div 10) + (2*digit+incoming) mod 10"
    by (simp add: div_mult_mod_eq mult.commute)
  have quotient:
    "(2*digit+incoming) div 10 = (if 5 \<le> digit then 1 else 0)"
    using balance division by linarith
  show ?thesis
    by (simp add: double_reverse_forward_pass.simps Let_def quotient)
qed

lemma double_reverse_reverse_single_digit:
  assumes digit: "digit < 10" and incoming: "incoming \<le> 1"
  shows "double_reverse_reverse_pass [digit] incoming =
    ([(2*digit+incoming) mod 10], if 5 \<le> digit then 1 else 0)"
proof -
  note balance = decimal_double_digit_carry[OF digit incoming]
  have division:
    "2*digit+incoming =
      10*((2*digit+incoming) div 10) + (2*digit+incoming) mod 10"
    by (simp add: div_mult_mod_eq mult.commute)
  have quotient:
    "(2*digit+incoming) div 10 = (if 5 \<le> digit then 1 else 0)"
    using balance division by linarith
  show ?thesis
    by (simp add: double_reverse_reverse_pass.simps Let_def quotient)
qed

lemma double_reverse_digit_quotient:
  assumes digit: "digit < 10" and incoming: "incoming \<le> 1"
  shows "(2*digit + incoming) div 10 = threshold5_digit digit"
proof -
  note balance = decimal_double_digit_carry[OF digit incoming]
  have division:
    "2*digit + incoming =
      10*((2*digit + incoming) div 10) +
        (2*digit + incoming) mod 10"
    by (simp add: div_mult_mod_eq mult.commute)
  show ?thesis
    using balance division
    by (simp add: threshold5_digit_def; arith)
qed

fun double_reverse_four_port_stencil_word ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "double_reverse_four_port_stencil_word previous [] = []"
| "double_reverse_four_port_stencil_word previous (digit#digits) =
    double_reverse_two_pass_cell previous digit
      (if digits = [] then 0 else hd digits) #
      double_reverse_four_port_stencil_word digit digits"

lemma double_reverse_forward_pass_final_carry:
  assumes digits: "list_all (\<lambda>digit. digit < 10) source"
      and incoming: "incoming \<le> 1"
  shows "snd (double_reverse_forward_pass source incoming) =
    (if source = [] then incoming else threshold5_digit (last source))"
  using digits incoming
proof (induction source arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons digit digits)
  have digit_bound: "digit < 10" using Cons.prems(1) by simp
  have tail_digits: "list_all (\<lambda>d. d < 10) digits"
    using Cons.prems(1) by simp
  have quotient: "(2*digit + incoming) div 10 = threshold5_digit digit"
    by (rule double_reverse_digit_quotient[OF digit_bound Cons.prems(2)])
  have carry_bound: "threshold5_digit digit \<le> 1"
    by (simp add: threshold5_digit_def)
  have tail_carry:
    "snd (double_reverse_forward_pass digits (threshold5_digit digit)) =
      (if digits = [] then threshold5_digit digit
       else threshold5_digit (last digits))"
    using Cons.IH[OF tail_digits carry_bound] .
  obtain tail_output tail_outgoing where tail_pass:
    "double_reverse_forward_pass digits (threshold5_digit digit) =
       (tail_output,tail_outgoing)"
    by (cases "double_reverse_forward_pass digits (threshold5_digit digit)") auto
  have pass:
    "double_reverse_forward_pass (digit#digits) incoming =
      ((2*digit+incoming) mod 10 # tail_output,tail_outgoing)"
    using quotient tail_pass
    by (simp add: double_reverse_forward_pass.simps Let_def)
  have pass_out:
    "snd (double_reverse_forward_pass (digit#digits) incoming) = tail_outgoing"
    using pass by simp
  have tail_outgoing_exact:
    "tail_outgoing = (if digits = [] then threshold5_digit digit
       else threshold5_digit (last digits))"
    using tail_carry tail_pass by simp
  show ?case
    using pass_out tail_outgoing_exact by (cases digits) simp_all
qed

lemma double_reverse_forward_pass_output_digits:
  assumes digits: "list_all (\<lambda>digit. digit < 10) source"
      and incoming: "incoming \<le> 1"
  shows "list_all (\<lambda>digit. digit < 10)
      (fst (double_reverse_forward_pass source incoming))"
  using digits incoming
proof (induction source arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons digit digits)
  have digit_bound: "digit < 10" using Cons.prems(1) by simp
  have tail_digits: "list_all (\<lambda>d. d < 10) digits"
    using Cons.prems(1) by simp
  have first:
    "double_reverse_forward_pass [digit] incoming =
       ([(2*digit + incoming) mod 10], threshold5_digit digit)"
    unfolding threshold5_digit_def
    by (rule double_reverse_forward_single_digit[OF digit_bound Cons.prems(2)])
  have tail_carry: "threshold5_digit digit \<le> 1"
    by (simp add: threshold5_digit_def)
  have rest:
    "list_all (\<lambda>d. d < 10)
      (fst (double_reverse_forward_pass digits (threshold5_digit digit)))"
    using Cons.IH[OF tail_digits tail_carry] .
  have split:
    "double_reverse_forward_pass (digit # digits) incoming =
      (let (first_digits, middle) =
          double_reverse_forward_pass [digit] incoming;
           (rest_digits, outgoing) =
          double_reverse_forward_pass digits middle
       in (first_digits @ rest_digits, outgoing))"
    using double_reverse_forward_pass_append[of "[digit]" digits incoming]
    by simp
  have output_exact:
    "fst (double_reverse_forward_pass (digit#digits) incoming) =
      [(2*digit + incoming) mod 10] @
        fst (double_reverse_forward_pass digits (threshold5_digit digit))"
    using first split by (simp add: Let_def split: prod.splits)
  show ?case
    unfolding output_exact
    using digit_bound rest by simp
qed

lemma double_reverse_reverse_pass_final_carry:
  assumes digits: "list_all (\<lambda>digit. digit < 10) source"
      and incoming: "incoming \<le> 1"
  shows "snd (double_reverse_reverse_pass source incoming) =
    (if source = [] then incoming else threshold5_digit (hd source))"
  using digits incoming
proof (induction source arbitrary: incoming)
  case Nil
  then show ?case by simp
next
  case (Cons digit digits)
  have digit_bound: "digit < 10" using Cons.prems(1) by simp
  have tail_digits: "list_all (\<lambda>d. d < 10) digits"
    using Cons.prems(1) by simp
  have tail_carry:
    "snd (double_reverse_reverse_pass digits incoming) =
      (if digits = [] then incoming else threshold5_digit (hd digits))"
    using Cons.IH[OF tail_digits Cons.prems(2)] .
  have tail_bound:
    "snd (double_reverse_reverse_pass digits incoming) \<le> 1"
    using tail_carry Cons.prems(2)
    by (cases digits) (simp_all add: threshold5_digit_def)
  have quotient:
    "(2*digit + snd (double_reverse_reverse_pass digits incoming)) div 10 =
      threshold5_digit digit"
    by (rule double_reverse_digit_quotient[OF digit_bound tail_bound])
  obtain tail_output tail_carry where tail_pass:
    "double_reverse_reverse_pass digits incoming = (tail_output,tail_carry)"
    by (cases "double_reverse_reverse_pass digits incoming") auto
  have quotient_tail:
    "(2*digit + tail_carry) div 10 = threshold5_digit digit"
    using quotient tail_pass by simp
  have step:
    "double_reverse_reverse_pass (digit#digits) incoming =
      ((2*digit + tail_carry) mod 10 # tail_output,
        threshold5_digit digit)"
    using tail_pass quotient_tail
    by (simp add: double_reverse_reverse_pass.simps Let_def)
  show ?case using step by simp
qed

lemma double_reverse_four_port_two_pass_stencil:
  assumes digits: "list_all (\<lambda>digit. digit < 10) source"
      and previous: "previous < 10"
  shows "double_reverse_reverse_pass
      (fst (double_reverse_forward_pass source
        (threshold5_digit previous))) 0 =
    (double_reverse_four_port_stencil_word previous source,
     if source = [] then 0 else threshold5_digit
       (hd (fst (double_reverse_forward_pass source
         (threshold5_digit previous)))))"
  using digits previous
proof (induction source arbitrary: previous)
  case Nil
  then show ?case by simp
next
  case (Cons digit digits)
  have digit_bound: "digit < 10" using Cons.prems(1) by simp
  have tail_digits: "list_all (\<lambda>d. d < 10) digits"
    using Cons.prems(1) by simp
  have previous_carry: "threshold5_digit previous \<le> 1"
    by (simp add: threshold5_digit_def)
  have first_pass_raw:
    "double_reverse_forward_pass [digit] (threshold5_digit previous) =
       ([(2*digit + threshold5_digit previous) mod 10],
         (if 5 \<le> digit then 1 else 0))"
    using double_reverse_forward_single_digit[OF digit_bound previous_carry]
    by (simp add: threshold5_digit_def)
  have first_pass:
    "double_reverse_forward_pass [digit] (threshold5_digit previous) =
       ([(2*digit + threshold5_digit previous) mod 10],
         threshold5_digit digit)"
    using first_pass_raw by (simp add: threshold5_digit_def)
  have forward_split:
    "double_reverse_forward_pass (digit # digits)
       (threshold5_digit previous) =
     (let (first, middle) = double_reverse_forward_pass [digit]
          (threshold5_digit previous);
          (rest, outgoing) = double_reverse_forward_pass digits
            (threshold5_digit digit)
      in (first @ rest, outgoing))"
    using double_reverse_forward_pass_append
      [of "[digit]" digits "threshold5_digit previous"] first_pass
    by (simp add: Let_def)
  have middle:
    "fst (double_reverse_forward_pass (digit # digits)
       (threshold5_digit previous)) =
     [(2*digit + threshold5_digit previous) mod 10] @
       fst (double_reverse_forward_pass digits (threshold5_digit digit))"
    using forward_split first_pass
    by (cases "double_reverse_forward_pass digits (threshold5_digit digit)")
       (simp add: Let_def)
  have tail_stencil:
    "double_reverse_reverse_pass
       (fst (double_reverse_forward_pass digits (threshold5_digit digit))) 0 =
     (double_reverse_four_port_stencil_word digit digits,
       if digits = [] then 0 else threshold5_digit
         (hd (fst (double_reverse_forward_pass digits
           (threshold5_digit digit)))))"
    by (rule Cons.IH[OF tail_digits digit_bound])
  obtain tail_output tail_carry where tail_pass:
    "double_reverse_reverse_pass
       (fst (double_reverse_forward_pass digits (threshold5_digit digit))) 0 =
     (tail_output, tail_carry)"
    by (cases "double_reverse_reverse_pass
       (fst (double_reverse_forward_pass digits (threshold5_digit digit))) 0")
       auto
  have tail_output_exact:
    "tail_output = double_reverse_four_port_stencil_word digit digits"
    using tail_pass tail_stencil by simp
  have tail_carry_exact:
    "tail_carry = (if digits = [] then 0 else threshold5_digit
      (hd (fst (double_reverse_forward_pass digits
        (threshold5_digit digit)))))"
    using tail_pass tail_stencil by simp
  have tail_carry_bound: "tail_carry \<le> 1"
    using tail_carry_exact by (cases digits) (simp_all add: threshold5_digit_def)
  let ?first_digit = "(2*digit + threshold5_digit previous) mod 10"
  have first_digit_bound: "?first_digit < 10" by simp
  have first_reverse:
    "double_reverse_reverse_pass [?first_digit] tail_carry =
      ([(2*?first_digit + tail_carry) mod 10],
        threshold5_digit ?first_digit)"
    using double_reverse_reverse_single_digit
      [OF first_digit_bound tail_carry_bound]
    by (simp add: threshold5_digit_def)
  have reverse_split:
    "double_reverse_reverse_pass
       ([?first_digit] @
          fst (double_reverse_forward_pass digits (threshold5_digit digit))) 0 =
     (let (rest, middle_carry) = double_reverse_reverse_pass
          (fst (double_reverse_forward_pass digits (threshold5_digit digit))) 0;
          (first, outgoing) = double_reverse_reverse_pass [?first_digit]
            middle_carry
      in (first @ rest, outgoing))"
    using double_reverse_reverse_pass_append
      [of "[?first_digit]"
        "fst (double_reverse_forward_pass digits (threshold5_digit digit))" 0]
    by (simp add: Let_def)
  have right_digit:
    "(if digits = [] then 0 else
       hd (fst (double_reverse_forward_pass digits (threshold5_digit digit)))) =
     (if digits = [] then 0 else
       (2*hd digits + threshold5_digit digit) mod 10)"
    by (cases digits)
      (simp_all add: double_reverse_forward_pass.simps Let_def
        split: prod.splits)
  have head_exact:
    "(2*?first_digit + tail_carry) mod 10 =
      double_reverse_two_pass_cell previous digit
        (if digits = [] then 0 else hd digits)"
    using tail_carry_exact right_digit
    by (cases digits)
      (simp_all add: double_reverse_two_pass_cell_def
        double_reverse_first_pass_cell_def threshold5_digit_def)
  show ?case
    using middle tail_pass tail_output_exact tail_carry_exact
      first_reverse reverse_split head_exact
    by (simp add: Let_def double_reverse_four_port_stencil_word.simps)
qed

theorem double_reverse_four_port_row_open_stencil:
  assumes digits: "list_all (\<lambda>digit. digit < 10) source"
      and previous: "previous < 10"
  shows "double_reverse_output_word
      (double_reverse_four_port_row source
        (threshold5_digit previous) 0) =
    double_reverse_four_port_stencil_word previous source"
proof -
  have two_pass:
    "double_reverse_reverse_pass
      (fst (double_reverse_forward_pass source (threshold5_digit previous))) 0 =
      (double_reverse_four_port_stencil_word previous source,
       if source = [] then 0 else threshold5_digit
         (hd (fst (double_reverse_forward_pass source
           (threshold5_digit previous)))))"
    by (rule double_reverse_four_port_two_pass_stencil[OF digits previous])
  obtain middle forward_out where pass:
    "double_reverse_forward_pass source (threshold5_digit previous) =
      (middle,forward_out)"
    by (cases "double_reverse_forward_pass source
        (threshold5_digit previous)") auto
  obtain out_digits reverse_out where reverse_pass:
    "double_reverse_reverse_pass middle 0 = (out_digits,reverse_out)"
    by (cases "double_reverse_reverse_pass middle 0") auto
  have output_word:
    "out_digits = double_reverse_four_port_stencil_word previous source"
    using two_pass pass reverse_pass by simp
  have row_value:
    "double_reverse_four_port_row source (threshold5_digit previous) 0 =
      \<lparr>double_reverse_forward_out=forward_out,
        double_reverse_reverse_out=reverse_out,
        double_reverse_output_word=out_digits\<rparr>"
    unfolding double_reverse_four_port_row_def
    using pass reverse_pass
    by (simp add: Let_def split: prod.splits)
  have projected:
    "double_reverse_output_word
        (double_reverse_four_port_row source (threshold5_digit previous) 0) =
      out_digits"
    using row_value by simp
  show ?thesis using projected output_word by simp
qed

fun double_reverse_four_port_t2_stencil_word ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "double_reverse_four_port_t2_stencil_word previous [] = []"
| "double_reverse_four_port_t2_stencil_word previous (digit#digits) =
    double_reverse_t2_digit previous digit
      (if digits = [] then 0 else hd digits) #
      double_reverse_four_port_t2_stencil_word digit digits"

lemma double_reverse_four_port_stencil_kernel:
  assumes digits: "list_all (\<lambda>digit. digit < 10) source"
      and previous: "previous < 10"
  shows "double_reverse_four_port_stencil_word previous source =
    double_reverse_four_port_t2_stencil_word previous source"
  using digits previous
proof (induction source arbitrary: previous)
  case Nil
  then show ?case by simp
next
  case (Cons digit digits)
  have digit_bound: "digit < 10" using Cons.prems(1) by simp
  have tail_digits: "list_all (\<lambda>d. d < 10) digits"
    using Cons.prems(1) by simp
  have next_bound: "(if digits = [] then 0 else hd digits) < 10"
    using tail_digits by (cases digits) auto
  have cell:
    "double_reverse_two_pass_cell previous digit
       (if digits = [] then 0 else hd digits) =
     double_reverse_t2_digit previous digit
       (if digits = [] then 0 else hd digits)"
    by (rule double_reverse_two_pass_cell_refines_kernel)
       (use Cons.prems(2) digit_bound next_bound in auto)
  show ?case
    using Cons.IH[OF tail_digits digit_bound] cell by simp
qed

theorem double_reverse_four_port_row_t2_stencil:
  assumes digits: "list_all (\<lambda>digit. digit < 10) source"
      and previous: "previous < 10"
  shows "double_reverse_output_word
      (double_reverse_four_port_row source
        (threshold5_digit previous) 0) =
    double_reverse_four_port_t2_stencil_word previous source"
proof -
  have row:
    "double_reverse_output_word
      (double_reverse_four_port_row source
        (threshold5_digit previous) 0) =
      double_reverse_four_port_stencil_word previous source"
    by (rule double_reverse_four_port_row_open_stencil[OF digits previous])
  show ?thesis
    using row double_reverse_four_port_stencil_kernel[OF digits previous]
    by simp
qed

fun double_reverse_four_port_radix5_stencil_word ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "double_reverse_four_port_radix5_stencil_word previous [] = []"
| "double_reverse_four_port_radix5_stencil_word previous (digit#digits) =
    ((4 * digit + 2 * (if 5 \<le> previous then 1 else 0) +
      (if (if digits = [] then 0 else hd digits) mod 5 = 3 \<or>
          (if digits = [] then 0 else hd digits) mod 5 = 4
       then 1 else 0) +
      (if 5 \<le> digit \<and>
          (if digits = [] then 0 else hd digits) mod 5 = 2
       then 1 else 0)) mod 10) #
    double_reverse_four_port_radix5_stencil_word digit digits"

theorem double_reverse_four_port_stencil_radix5_selector:
  assumes digits: "list_all (\<lambda>digit. digit < 10) source"
      and previous: "previous < 10"
  shows "double_reverse_four_port_t2_stencil_word previous source =
    double_reverse_four_port_radix5_stencil_word previous source"
  using digits previous
proof (induction source arbitrary: previous)
  case Nil
  then show ?case by simp
next
  case (Cons digit digits)
  have digit_bound: "digit < 10" using Cons.prems(1) by simp
  have tail_digits: "list_all (\<lambda>d. d < 10) digits"
    using Cons.prems(1) by simp
  have right_bound: "(if digits = [] then 0 else hd digits) < 10"
    using tail_digits by (cases digits) auto
  have cell:
    "double_reverse_t2_digit previous digit
       (if digits = [] then 0 else hd digits) =
     (4 * digit + 2 * (if 5 \<le> previous then 1 else 0) +
       (if (if digits = [] then 0 else hd digits) mod 5 = 3
          \<or> (if digits = [] then 0 else hd digits) mod 5 = 4
        then 1 else 0) +
       (if 5 \<le> digit \<and>
           (if digits = [] then 0 else hd digits) mod 5 = 2
        then 1 else 0)) mod 10"
    by (rule double_reverse_t2_open_stencil_exact[OF Cons.prems(2)
      digit_bound right_bound])
  have tail:
    "double_reverse_four_port_t2_stencil_word digit digits =
      double_reverse_four_port_radix5_stencil_word digit digits"
    by (rule Cons.IH[OF tail_digits digit_bound])
  show ?case using cell tail by simp
qed

definition double_reverse_canonical_source :: "nat list \<Rightarrow> bool" where
  "double_reverse_canonical_source source \<longleftrightarrow>
    source \<noteq> [] \<and>
    list_all (\<lambda>digit. digit < 10) source \<and>
    hd source > 0 \<and> last source > 0"

definition double_reverse_four_port_closed_word ::
    "double_reverse_four_port_row \<Rightarrow> nat list" where
  "double_reverse_four_port_closed_word row =
    (if double_reverse_reverse_out row = 1 then [1] else []) @
      double_reverse_output_word row @
    (if double_reverse_forward_out row = 1 then [2] else [])"

lemma double_reverse_four_port_row_carries_bounded:
  assumes digits: "list_all (\<lambda>digit. digit < 10) source"
      and previous: "previous < 10"
  shows "double_reverse_forward_out
      (double_reverse_four_port_row source (threshold5_digit previous) 0) \<le> 1"
    and "double_reverse_reverse_out
      (double_reverse_four_port_row source (threshold5_digit previous) 0) \<le> 1"
proof -
  have incoming: "threshold5_digit previous \<le> 1"
    by (simp add: threshold5_digit_def)
  have forward_carry:
    "snd (double_reverse_forward_pass source (threshold5_digit previous)) \<le> 1"
    using double_reverse_forward_pass_final_carry[OF digits incoming]
    by (cases source) (simp_all add: threshold5_digit_def)
  have middle_digits:
    "list_all (\<lambda>digit. digit < 10)
      (fst (double_reverse_forward_pass source (threshold5_digit previous)))"
    by (rule double_reverse_forward_pass_output_digits[OF digits incoming])
  have no_reverse_incoming: "(0::nat) \<le> 1" by simp
  have reverse_carry:
    "snd (double_reverse_reverse_pass
      (fst (double_reverse_forward_pass source (threshold5_digit previous))) 0)
       \<le> 1"
    using double_reverse_reverse_pass_final_carry
      [OF middle_digits no_reverse_incoming]
    by (cases "fst (double_reverse_forward_pass source
      (threshold5_digit previous))")
       (simp_all add: threshold5_digit_def)
  obtain middle forward_out where pass:
    "double_reverse_forward_pass source (threshold5_digit previous) =
      (middle,forward_out)"
    by (cases "double_reverse_forward_pass source
        (threshold5_digit previous)") auto
  obtain result_digits reverse_out where reverse_pass:
    "double_reverse_reverse_pass middle 0 = (result_digits,reverse_out)"
    by (cases "double_reverse_reverse_pass middle 0") auto
  have row_value:
    "double_reverse_four_port_row source (threshold5_digit previous) 0 =
      \<lparr>double_reverse_forward_out=forward_out,
        double_reverse_reverse_out=reverse_out,
        double_reverse_output_word=result_digits\<rparr>"
    unfolding double_reverse_four_port_row_def
    using pass reverse_pass by (simp add: Let_def)
  show forward:
    "double_reverse_forward_out
      (double_reverse_four_port_row source (threshold5_digit previous) 0) \<le> 1"
    using forward_carry pass row_value by simp
  show reverse:
    "double_reverse_reverse_out
      (double_reverse_four_port_row source (threshold5_digit previous) 0) \<le> 1"
    using reverse_carry pass reverse_pass row_value by simp
qed

theorem double_reverse_four_port_canonical_birth_word:
  assumes canonical: "double_reverse_canonical_source source"
  shows "double_reverse_four_port_closed_word
      (double_reverse_four_port_row source 0 0) =
    (if double_reverse_reverse_out
         (double_reverse_four_port_row source 0 0) = 1 then [1] else []) @
      double_reverse_four_port_radix5_stencil_word 0 source @
    (if double_reverse_forward_out
         (double_reverse_four_port_row source 0 0) = 1 then [2] else [])"
proof -
  have digits: "list_all (\<lambda>digit. digit < 10) source"
    using canonical unfolding double_reverse_canonical_source_def by simp
  have previous: "(0::nat) < 10" by simp
  have core:
    "double_reverse_output_word
       (double_reverse_four_port_row source 0 0) =
     double_reverse_four_port_radix5_stencil_word 0 source"
    using double_reverse_four_port_row_t2_stencil[OF digits previous]
      double_reverse_four_port_stencil_radix5_selector[OF digits previous]
    by (simp add: threshold5_digit_def)
  show ?thesis
    using core by (simp add: double_reverse_four_port_closed_word_def)
qed

lemma double_reverse_four_port_closed_word_length:
  assumes forward: "double_reverse_forward_out row \<le> 1"
      and reverse: "double_reverse_reverse_out row \<le> 1"
  shows "length (double_reverse_four_port_closed_word row) =
      length (double_reverse_output_word row) +
        double_reverse_forward_out row + double_reverse_reverse_out row"
  using forward reverse
  by (simp add: double_reverse_four_port_closed_word_def;
      cases "double_reverse_forward_out row";
      cases "double_reverse_reverse_out row"; simp_all)

theorem double_reverse_four_port_canonical_birth_width:
  assumes canonical: "double_reverse_canonical_source source"
  shows "length (double_reverse_four_port_closed_word
      (double_reverse_four_port_row source 0 0)) =
    length (double_reverse_four_port_radix5_stencil_word 0 source) +
      double_reverse_forward_out
        (double_reverse_four_port_row source 0 0) +
      double_reverse_reverse_out
        (double_reverse_four_port_row source 0 0)"
proof -
  have digits: "list_all (\<lambda>digit. digit < 10) source"
    using canonical unfolding double_reverse_canonical_source_def by simp
  have previous: "(0::nat) < 10" by simp
  have bounds:
    "double_reverse_forward_out
        (double_reverse_four_port_row source 0 0) \<le> 1 \<and>
     double_reverse_reverse_out
        (double_reverse_four_port_row source 0 0) \<le> 1"
    using double_reverse_four_port_row_carries_bounded[OF digits previous]
    by (simp add: threshold5_digit_def)
  have forward:
    "double_reverse_forward_out
      (double_reverse_four_port_row source 0 0) \<le> 1"
    using bounds by simp
  have reverse:
    "double_reverse_reverse_out
      (double_reverse_four_port_row source 0 0) \<le> 1"
    using bounds by simp
  have closed_expression:
    "double_reverse_four_port_closed_word
        (double_reverse_four_port_row source 0 0) =
      (if double_reverse_reverse_out
           (double_reverse_four_port_row source 0 0) = 1 then [1] else []) @
        double_reverse_four_port_radix5_stencil_word 0 source @
      (if double_reverse_forward_out
           (double_reverse_four_port_row source 0 0) = 1 then [2] else [])"
    by (rule double_reverse_four_port_canonical_birth_word[OF canonical])
  have output_length:
    "length (double_reverse_four_port_closed_word
        (double_reverse_four_port_row source 0 0)) =
      length (double_reverse_output_word
        (double_reverse_four_port_row source 0 0)) +
        double_reverse_forward_out
          (double_reverse_four_port_row source 0 0) +
        double_reverse_reverse_out
          (double_reverse_four_port_row source 0 0)"
    by (rule double_reverse_four_port_closed_word_length[OF forward reverse])
  have reverse_prefix_length:
    "length (if double_reverse_reverse_out
        (double_reverse_four_port_row source 0 0) = 1 then [1::nat] else []) =
      double_reverse_reverse_out (double_reverse_four_port_row source 0 0)"
    using reverse
    by (cases "double_reverse_reverse_out
        (double_reverse_four_port_row source 0 0)") simp_all
  have forward_suffix_length:
    "length (if double_reverse_forward_out
        (double_reverse_four_port_row source 0 0) = 1 then [2::nat] else []) =
      double_reverse_forward_out (double_reverse_four_port_row source 0 0)"
    using forward
    by (cases "double_reverse_forward_out
        (double_reverse_four_port_row source 0 0)") simp_all
  have closed_length_parts:
    "length (double_reverse_four_port_closed_word
        (double_reverse_four_port_row source 0 0)) =
      length (if double_reverse_reverse_out
          (double_reverse_four_port_row source 0 0) = 1
        then [1::nat] else []) +
      length (double_reverse_four_port_radix5_stencil_word 0 source) +
      length (if double_reverse_forward_out
          (double_reverse_four_port_row source 0 0) = 1
        then [2::nat] else [])"
    using closed_expression
    by (simp only: closed_expression length_append)
  have closed_length_from_stencil:
    "length (double_reverse_four_port_closed_word
        (double_reverse_four_port_row source 0 0)) =
      length (double_reverse_four_port_radix5_stencil_word 0 source) +
        double_reverse_forward_out
          (double_reverse_four_port_row source 0 0) +
        double_reverse_reverse_out
          (double_reverse_four_port_row source 0 0)"
    using closed_length_parts reverse_prefix_length forward_suffix_length
    by arith
  show ?thesis
    using output_length closed_length_from_stencil by arith
qed

theorem double_reverse_four_port_single_digit:
  assumes digit: "digit < 10" and forward_in: "forward_in \<le> 1"
      and reverse_in: "reverse_in \<le> 1"
  defines "first_digit \<equiv> (2*digit+forward_in) mod 10"
  shows "double_reverse_four_port_row [digit] forward_in reverse_in =
    \<lparr>double_reverse_forward_out=(if 5 \<le> digit then 1 else 0),
      double_reverse_reverse_out=(if 5 \<le> first_digit then 1 else 0),
      double_reverse_output_word=[(2*first_digit+reverse_in) mod 10]\<rparr>"
proof -
  have first:
    "double_reverse_forward_pass [digit] forward_in =
      ([first_digit],if 5 \<le> digit then 1 else 0)"
    using double_reverse_forward_single_digit[OF digit forward_in]
    unfolding first_digit_def by simp
  have first_bound: "first_digit < 10"
    unfolding first_digit_def by simp
  have second:
    "double_reverse_reverse_pass [first_digit] reverse_in =
      ([(2*first_digit+reverse_in) mod 10],
        if 5 \<le> first_digit then 1 else 0)"
    by (rule double_reverse_reverse_single_digit[OF first_bound reverse_in])
  show ?thesis
    unfolding double_reverse_four_port_row_def
    using first second by (simp add: Let_def)
qed

corollary double_reverse_four_port_single_digit_defect_alphabet:
  assumes digit: "digit < 10" and forward_in: "forward_in \<le> 1"
      and reverse_in: "reverse_in \<le> 1"
  shows "4 * double_reverse_forward_out
          (double_reverse_four_port_row [digit] forward_in reverse_in) +
        double_reverse_reverse_out
          (double_reverse_four_port_row [digit] forward_in reverse_in)
      \<in> {0,1,4,5}"
proof -
  let ?first = "(2*digit+forward_in) mod 10"
  have row:
    "double_reverse_four_port_row [digit] forward_in reverse_in =
      \<lparr>double_reverse_forward_out=(if 5 \<le> digit then 1 else 0),
       double_reverse_reverse_out=(if 5 \<le> ?first then 1 else 0),
       double_reverse_output_word=[(2*?first+reverse_in) mod 10]\<rparr>"
    by (rule double_reverse_four_port_single_digit
      [OF digit forward_in reverse_in])
  show ?thesis using row
    by (auto simp add: threshold5_digit_def split: if_splits)
qed

text \<open>A four-port row is a finite two-wave action on an explicit source
word.  Its join theorem is chronological and output-preserving; it does not
merge equal carry totals, erase digit order, or claim a period beyond the
supplied word.  The mod-32 theorem applies to each actual physical
normalization cut separately, with its own width and overflow carry.\<close>

ML \<open>
  val checked = @{thms double_reverse_cut_column_balance
    double_reverse_cut_columns_normalize
    double_reverse_cut_mod32_carry_projection
    double_reverse_cut_integer_carry_projection
    double_reverse_forward_pass_append
    double_reverse_reverse_pass_append
    double_reverse_forward_pass_final_carry
    double_reverse_reverse_pass_final_carry
    double_reverse_forward_pass_output_digits
    double_reverse_four_port_two_pass_stencil
    double_reverse_four_port_row_open_stencil
    double_reverse_four_port_row_t2_stencil
    double_reverse_four_port_stencil_radix5_selector
    double_reverse_four_port_row_carries_bounded
    double_reverse_four_port_canonical_birth_word
    double_reverse_four_port_closed_word_length
    double_reverse_four_port_canonical_birth_width
    double_reverse_four_port_action_append
    double_reverse_four_port_action_join_associative
    double_reverse_four_port_single_digit
    double_reverse_four_port_single_digit_defect_alphabet};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse group-ring/four-port refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped double-reverse group-ring/four-port proof" else ();
\<close>

end
