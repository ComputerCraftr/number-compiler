theory Bilateral_Cascade_Scan
  imports Main
begin

text \<open>A two-port action scans one boundary state from each direction and
emits a symbol only after the two states meet.  Temporal composition therefore
cannot evaluate either direction first.  The cascade below retains, in each
directional state, a function of the still-unknown opposite state.\<close>

record ('symbol, 'left, 'right) bilateral_action =
  bilateral_left_initial :: 'left
  bilateral_right_initial :: 'right
  bilateral_left_step :: "'left \<Rightarrow> 'symbol \<Rightarrow> 'left"
  bilateral_right_step :: "'right \<Rightarrow> 'symbol \<Rightarrow> 'right"
  bilateral_emit :: "'left \<Rightarrow> 'symbol \<Rightarrow> 'right \<Rightarrow> 'symbol"

fun bilateral_left_fold ::
    "('symbol, 'left, 'right) bilateral_action \<Rightarrow>
      'left \<Rightarrow> 'symbol list \<Rightarrow> 'left" where
  "bilateral_left_fold action left [] = left"
| "bilateral_left_fold action left (symbol # rest) =
    bilateral_left_fold action
      (bilateral_left_step action left symbol) rest"

fun bilateral_right_fold ::
    "('symbol, 'left, 'right) bilateral_action \<Rightarrow>
      'right \<Rightarrow> 'symbol list \<Rightarrow> 'right" where
  "bilateral_right_fold action right [] = right"
| "bilateral_right_fold action right (symbol # rest) =
    bilateral_right_step action
      (bilateral_right_fold action right rest) symbol"

fun bilateral_emit_between ::
    "('symbol, 'left, 'right) bilateral_action \<Rightarrow>
      'left \<Rightarrow> 'right \<Rightarrow> 'symbol list \<Rightarrow> 'symbol list" where
  "bilateral_emit_between action left right [] = []"
| "bilateral_emit_between action left right (symbol # rest) =
    (let opposite = bilateral_right_fold action right rest;
         output = bilateral_emit action left symbol opposite
     in output # bilateral_emit_between action
          (bilateral_left_step action left symbol) right rest)"

definition bilateral_run ::
    "('symbol, 'left, 'right) bilateral_action \<Rightarrow>
      'symbol list \<Rightarrow> 'symbol list" where
  "bilateral_run action source =
    bilateral_emit_between action
      (bilateral_left_initial action)
      (bilateral_right_initial action) source"

definition bilateral_cascade ::
    "('symbol, 'left_a, 'right_a) bilateral_action \<Rightarrow>
      ('symbol, 'left_b, 'right_b) bilateral_action \<Rightarrow>
      ('symbol,
        'left_a \<times> ('right_a \<Rightarrow> 'left_b),
        'right_a \<times> ('left_a \<Rightarrow> 'right_b)) bilateral_action" where
  "bilateral_cascade before after = \<lparr>
    bilateral_left_initial =
      (bilateral_left_initial before,
        (\<lambda>_. bilateral_left_initial after)),
    bilateral_right_initial =
      (bilateral_right_initial before,
        (\<lambda>_. bilateral_right_initial after)),
    bilateral_left_step = (\<lambda>(left, continuation) symbol.
      (bilateral_left_step before left symbol,
       (\<lambda>right. bilateral_left_step after
          (continuation (bilateral_right_step before right symbol))
          (bilateral_emit before left symbol right)))),
    bilateral_right_step = (\<lambda>(right, continuation) symbol.
      (bilateral_right_step before right symbol,
       (\<lambda>left. bilateral_right_step after
          (continuation (bilateral_left_step before left symbol))
          (bilateral_emit before left symbol right)))),
    bilateral_emit = (\<lambda>(left, left_continuation) symbol
        (right, right_continuation).
      (let middle = bilateral_emit before left symbol right;
           transported_left = left_continuation
             (bilateral_right_step before right symbol);
           transported_right = right_continuation
             (bilateral_left_step before left symbol)
       in bilateral_emit after transported_left middle transported_right))
  \<rparr>"

text \<open>The directional invariants state exactly what a retained
continuation means.  After scanning a prefix from the left, applying its
continuation to the remaining right boundary gives the second action's left
state after the first action's emitted prefix.  The right invariant is the
mirror statement.\<close>

theorem bilateral_cascade_left_fold:
  "bilateral_left_fold (bilateral_cascade before after)
      (left, continuation) source =
    (bilateral_left_fold before left source,
      (\<lambda>right. bilateral_left_fold after
        (continuation (bilateral_right_fold before right source))
        (bilateral_emit_between before left right source)))"
proof (induct source arbitrary: left continuation)
  case Nil
  then show ?case by simp
next
  case (Cons symbol rest)
  show ?case
    using Cons.hyps[of "bilateral_left_step before left symbol"
        "\<lambda>right. bilateral_left_step after
          (continuation (bilateral_right_step before right symbol))
          (bilateral_emit before left symbol right)"]
    by (simp add: bilateral_cascade_def fun_eq_iff Let_def)
qed

theorem bilateral_cascade_right_fold:
  "bilateral_right_fold (bilateral_cascade before after)
      (right, continuation) source =
    (bilateral_right_fold before right source,
      (\<lambda>left. bilateral_right_fold after
        (continuation (bilateral_left_fold before left source))
        (bilateral_emit_between before left right source)))"
proof (induct source arbitrary: right continuation)
  case Nil
  then show ?case by simp
next
  case (Cons symbol rest)
  show ?case
    using Cons.hyps[of right continuation]
    by (simp add: bilateral_cascade_def fun_eq_iff Let_def)
qed

text \<open>Both transported opposite ports are substituted at the same
emission.  The proof is an induction on the actual finite source word and does
not construct the intermediate word as an executable input to the second
scan.  The intermediate list appears only in the extensional specification on
the right-hand side.\<close>

theorem bilateral_cascade_emit_between:
  "bilateral_emit_between (bilateral_cascade before after)
      (left, left_continuation) (right, right_continuation) source =
    bilateral_emit_between after
      (left_continuation (bilateral_right_fold before right source))
      (right_continuation (bilateral_left_fold before left source))
      (bilateral_emit_between before left right source)"
proof (induct source arbitrary:
    left left_continuation right right_continuation)
  case Nil
  then show ?case by simp
next
  case (Cons symbol rest)
  show ?case
    using Cons.hyps[of
        "bilateral_left_step before left symbol"
        "\<lambda>opposite. bilateral_left_step after
          (left_continuation
            (bilateral_right_step before opposite symbol))
          (bilateral_emit before left symbol opposite)"
        right right_continuation]
      bilateral_cascade_right_fold[of before after right right_continuation rest]
    by (simp add: bilateral_cascade_def Let_def)
qed

theorem bilateral_cascade_run:
  "bilateral_run (bilateral_cascade before after) source =
    bilateral_run after (bilateral_run before source)"
  using bilateral_cascade_emit_between[of before after
      "bilateral_left_initial before" "\<lambda>_. bilateral_left_initial after"
      "bilateral_right_initial before" "\<lambda>_. bilateral_right_initial after"
      source]
  by (simp add: bilateral_run_def bilateral_cascade_def)

text \<open>This is the complete finite emitted-word theorem for the bilateral
state product.  It does not define the production thirteen-channel publisher,
admissibility, source occurrence chronology, a canonical rebracketing normal
form, or constructor work and retention bounds.  Those require concrete
family channel laws and the authenticated recursive occurrence splitter.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms bilateral_cascade_left_fold bilateral_cascade_right_fold
      bilateral_cascade_emit_between bilateral_cascade_run}) then ()
    else error "bilateral cascade scan proof depends on an oracle";
\<close>

end
