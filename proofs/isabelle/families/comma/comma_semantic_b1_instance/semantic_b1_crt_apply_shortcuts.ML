(* Shallow, kernel-checked Boolean rewrites for admitted CRT apply requests. *)
signature COMMA_SEMANTIC_B1_CRT_APPLY_SHORTCUTS =
sig
  type owner =
   {candidate: cterm -> bool,
    rewrite: cterm -> thm option,
    applications: unit -> int}
  val make: Proof.context -> owner
end

structure Comma_Semantic_B1_CRT_Apply_Shortcuts:
  COMMA_SEMANTIC_B1_CRT_APPLY_SHORTCUTS =
struct
  type owner =
   {candidate: cterm -> bool,
    rewrite: cterm -> thm option,
    applications: unit -> int}

  fun make (_: Proof.context) : owner =
    let
      val applications = Synchronized.var
        "semantic_b1_crt_apply_shortcuts" 0
      val and_name = @{const_name Comma_CRT_And}
      val or_name = @{const_name Comma_CRT_Or}
      val boolean_column_name = @{const_name Comma_CRT_Bool}
      val apply_name = @{const_name comma_crt_apply_shifted_from}

      fun is_const name term =
        (case term of Const (actual, _) => actual = name | _ => false)
      fun is_boolean_column expected term =
        (case Term.strip_comb term of
          (Const (name, _), [flag]) =>
            name = boolean_column_name andalso flag aconv expected
        | _ => false)
      fun is_zero term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) => typ = @{typ nat} andalso value = 0
        | NONE => false)
      fun same left right = left aconv right

      val rules =
       {and_false_left = @{thm comma_crt_apply_shifted_from_and_false_left}
          RS @{thm eq_reflection},
        and_false_right = @{thm comma_crt_apply_shifted_from_and_false_right}
          RS @{thm eq_reflection},
        or_true_left = @{thm comma_crt_apply_shifted_from_or_true_left}
          RS @{thm eq_reflection},
        or_true_right = @{thm comma_crt_apply_shifted_from_or_true_right}
          RS @{thm eq_reflection},
        and_true_right = @{thm comma_crt_apply_shifted_from_and_true_right}
          RS @{thm eq_reflection},
        or_false_right = @{thm comma_crt_apply_shifted_from_or_false_right}
          RS @{thm eq_reflection},
        zero_and_true_left = @{thm comma_crt_apply_shifted_from_zero_and_true_left}
          RS @{thm eq_reflection},
        zero_or_false_left = @{thm comma_crt_apply_shifted_from_zero_or_false_left}
          RS @{thm eq_reflection},
        zero_equal = @{thm comma_crt_apply_shifted_from_zero_equal}
          RS @{thm eq_reflection}};

      fun select (Const (name, _), shift, operation, left, right) =
            if name <> apply_name then NONE
            else if is_const and_name operation andalso
                is_boolean_column @{term False} left then SOME (#and_false_left rules)
            else if is_const and_name operation andalso
                is_boolean_column @{term False} right then SOME (#and_false_right rules)
            else if is_const or_name operation andalso
                is_boolean_column @{term True} left then SOME (#or_true_left rules)
            else if is_const or_name operation andalso
                is_boolean_column @{term True} right then SOME (#or_true_right rules)
            else if is_const and_name operation andalso
                is_boolean_column @{term True} right then SOME (#and_true_right rules)
            else if is_const or_name operation andalso
                is_boolean_column @{term False} right then SOME (#or_false_right rules)
            else if is_zero shift andalso is_const and_name operation andalso
                is_boolean_column @{term True} left then SOME (#zero_and_true_left rules)
            else if is_zero shift andalso is_const or_name operation andalso
                is_boolean_column @{term False} left then SOME (#zero_or_false_left rules)
            else if is_zero shift andalso same left right
              then SOME (#zero_equal rules)
            else NONE
        | select _ = NONE

      fun selected_rule request =
        (case Term.strip_comb request of
          (head as Const (_, _), [_, shift, operation, left, right]) =>
            select (head, shift, operation, left, right)
        | _ => NONE)

      fun candidate request = Option.isSome (selected_rule (Thm.term_of request))

      fun rewrite request =
        (case selected_rule (Thm.term_of request) of
          NONE => NONE
        | SOME rule =>
            (case try (Conv.rewr_conv rule) request of
              NONE => NONE
            | SOME theorem =>
                (Synchronized.change applications (fn count => count + 1);
                 SOME theorem)))
    in
      {candidate = candidate,
       rewrite = rewrite,
       applications = fn () => Synchronized.value applications}
    end
end
