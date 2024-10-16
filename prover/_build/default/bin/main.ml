open Prover.Logic.Logic

let rec propEq p p' =
  match (p, p') with
      (Atomic s, Atomic s') -> String.compare s s' = 0
    | (Not a, Not a') -> propEq a a'
    | (And (a, b), And (a', b')) -> (propEq a a') && (propEq b b')
    | (Or (a, b), Or (a', b')) -> (propEq a a') && (propEq b b')
    | (Implies (a, b), Implies (a', b')) -> (propEq a a') && (propEq b b')
    | (True, True) -> true
    | (False, False) -> true
    | _ -> false

let rec inList p l =
  match l with
      [] -> false
    | x :: l' -> (propEq x p) || (inList p l')

let rec proveRight gammaS gamma deltaS delta =
  match delta with
      [] -> proveLeft gammaS gamma deltaS delta
    | d :: delta' ->
        if applyRight d gammaS gamma deltaS delta'
        then true
        else proveRight gammaS gamma (d :: deltaS) delta'
and proveLeft gammaS gamma deltaS delta =
  match gamma with
      [] -> false
    | g :: gamma' ->
        if applyLeft g gammaS gamma' deltaS delta
        then true
        else proveLeft (g :: gammaS) gamma' deltaS delta
and applyRight d gammaS gamma deltaS delta =
  match d with
      Atomic s -> inList (Atomic s) (gammaS @ gamma)
    | Not p -> proveRight [] (p :: (gammaS @ gamma)) [] (deltaS @ delta)
    | And (a, b) -> (proveRight [] (gammaS @ gamma) [] (a :: (deltaS @ delta)))
                    &&
                    (proveRight [] (gammaS @ gamma) [] (b :: (deltaS @ delta)))
    | Or (a, b) -> proveRight [] (gammaS @ gamma) [] (a :: b :: (deltaS @ delta))
    | Implies (a, b) -> proveRight [] (a :: (gammaS @ gamma)) [] (b :: (deltaS @ delta))
    | True -> true
    | _ -> false
  and applyLeft g gammaS gamma deltaS delta =
    match g with
        Not p -> proveRight [] (gammaS @ gamma) [] (p :: (deltaS @ delta))
      | And (a, b) -> proveRight [] (a :: b :: (gammaS @ gamma)) [] (deltaS @ delta)
      | Or (a, b) -> (proveRight [] (a :: (gammaS @ gamma)) [] (deltaS @ delta))
                     &&
                     (proveRight [] (b :: (gammaS @ gamma)) [] (deltaS @ delta))
      (* | Implies (a', c) -> (match a' with
            True -> proveRight [] (c :: (gammaS @ gamma)) [] (deltaS @ delta)
          | False -> proveRight [] (gammaS @ gamma) [] (deltaS @ delta)
          | And (a, b) -> proveRight [] (Implies (a, Implies (b, c)) :: (gammaS @ gamma)) [] (deltaS @ delta)
          | Or (a, b) -> proveRight [] (Implies (a, c) :: Implies (b, c) :: (gammaS @ gamma)) [] (deltaS @ delta)
          | Implies (a, b) -> (proveRight [] (a :: Implies (b, c) :: (gammaS @ gamma)) [] (b :: []))
                              &&
                              (proveRight [] (c :: (gammaS @ gamma)) [] (deltaS @ delta))
          | Atomic s -> (inList (Atomic s) (gammaS @ gamma))
                        &&
                        (proveRight [] (c :: (gammaS @ gamma)) [] (deltaS @ delta))
          | Not a -> proveRight [] (Or (a, c) :: (gammaS @ gamma)) [] (deltaS @ delta)
      ) *)
      | Implies (a, b) -> (proveRight [] (gammaS @ gamma) [] (a :: (deltaS @ delta)))
                          &&
                          (proveRight [] (b :: (gammaS @ gamma)) [] (deltaS @ delta))
      | False -> true
      | _ -> false

let prove p = proveRight [] [] [] (p :: [])

(* tests *)
(* exception Fail of string

let rec testProver l =
  match l with
      [] -> print_endline "All tests passed!\n"
    | (p, expected) :: tests -> let result = prove (parse p) in
        if result = expected
        then testProver tests
        else if expected
             then raise (Fail ("Couldn't prove provable proposition " ^ p ^ "\n"))
             else raise (Fail ("Proved unprovable proposition " ^ p ^ "\n"))

let tests = [
  (* Simple tests *)
  ("T", true);
  ("F", false);
  ("T => F", false);
  ("F => T", true);
  ("A => A", true);
  ("A /\\ B => B /\\ A", true);
  ("A \\/ B => B \\/ A", true);
  ("A /\\ A => A", true);
  ("A /\\ A => A /\\ A /\\ A /\\ A", true);
  ("P \\/ (P => F)", true);
  ("((P => F) => F) => P", true);
  ("(A => B) => (A => B)", true);
  ("A /\\ (A => F) => B", true);
  ("(A => B) => (A => B => C) => (A => C)", true);
  ("((A \\/ B) => F) => ((A => F) /\\ (B => F))", true);
  ("((A => F) /\\ (B => F)) => ((A \\/ B) => F)", true);
  ("((A => A) /\\ (A => A)) => (A => A)", true);
  ("(A => F) /\\ (B => F) => ((A \\/ B) => F)", true);
  ("(A => T) /\\ (F => A)", true);
  ("((A => B) /\\ (A => C)) => (A => (B /\\ C))", true);
  ("((A \\/ B) => C) => (A => C) /\\ (B => C)", true);
  ("(A /\\ B => C) => A => B => C", true);
  ("((A => B) => B) => A", false);
  ("(A => B) => ((B => F) => (A => F))", true);
  ("((A \\/ B) /\\ (A => F)) => B", true);
  ("((A => B) /\\ (B => C)) => (A => C)", true);
  ("A => (T => A)", true);
  ("((A \\/ (A => F)) => F) => F", true);
  ("((P => F) /\\ Q) => ((P => Q) => ((P => F) => (Q => F))) => F", true);
  ("(A => F) \\/ (B => F) => ((A /\\ B) => F)", true);
  ("((P => F) \\/ Q) => (P => Q)", true);
  ("((P => R) /\\ (Q => R)) => ((P \\/ Q) => R)", true);
  ("(P => (Q => R)) => ((P => Q) => (P => R))", true);
  ("(R => (P \\/ Q)) /\\ ((P /\\ Q) => R) => (P => (Q => R))", true);
  ("(R => (P \\/ Q)) /\\ ((P /\\ Q) => R) => (P => (Q => R))", true);
  ("(A \\/ B \\/ C) => (B \\/ A \\/ C)", true);
  ("(A \\/ B \\/ C) => (B \\/ A \\/ D)", false);

  (* All tests passed! *)
  ("T", true);

  (* ChatGPT cases *)
  ("A => T", true);
  ("A /\\ T => A", true);
  ("A /\\ F => A", true);
  ("A => A \\/ B", true);
  ("(A => B) /\\ (B => C) => (A => C)", true);
  ("A \\/ F => A", true);
  ("T /\\ A => A", true);
  ("T /\\ F => F", true);
  ("(A => B) => ((B => C) => (A => C))", true);
  ("(A => B) /\\ (B => F) => (A => F)", true);
  ("A => (A => B) => B", true);
  ("(A /\\ B) => (A \\/ B)", true);
  ("(A \\/ B) => (B \\/ A)", true);
  ("(A => B) => (B => A)", false);
  ("A => (A => A)", true);
  ("A \\/ (B /\\ C) => (A \\/ B) /\\ (A \\/ C)", true);
  ("A /\\ (A => B) => B", true);
  ("A => (A => A /\\ A)", true);
  ("A => (A /\\ A) => A", true);
  ("A => (A => B) /\\ (A => C)", false);
  ("A => (B => A)", true);
  ("A /\\ B /\\ C => (A /\\ (B /\\ C))", true);
  ("((A => F) /\\ B) => (A \\/ B => B)", true);
  ("A \\/ (B => C) => (A \\/ B) => (A \\/ C)", true);
  ("((A => B) /\\ C) => (A => (B /\\ C))", true);
  ("A /\\ (B => A) => A", true);
  ("(A /\\ B) \\/ C => A \\/ (B \\/ C)", true);
  ("((A => B) /\\ (B => C)) => A => C", true);
  ("A /\\ ((A => B) /\\ (B => C)) => C", true);
  ("(A \\/ B) => A \\/ (A /\\ B)", false);
  ("A => ((A => B) => (A /\\ B))", true)

]

let () = testProver tests *)

let rec loop () =
  let input_line = read_line () in
    (try (if prove (parse input_line) then print_endline "true" else print_endline "false")
    with SyntaxError -> let () = print_endline "SyntaxError" in loop ());
  loop ()

let () =
  print_endline "Enter text (Ctrl+D to exit):";
  loop ()

let theorem = "(A => B) => (A => B => C) => A"

let () = Format.print_string "\n"
let () = Format.print_string theorem
let () = Format.print_string " is "
let () = Format.print_bool (prove (parse theorem))
let () = Format.print_string "\n\n"