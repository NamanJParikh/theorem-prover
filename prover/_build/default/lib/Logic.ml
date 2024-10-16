module type LOGIC = sig

  type prop =
      Atomic of string
    | Not of prop
    | And of prop * prop
    | Or of prop * prop
    | Implies of prop * prop
    | True
    | False

  val print : prop -> string

  exception SyntaxError

  val parse : string -> prop

end

module Logic : LOGIC = struct

  type prop =
      Atomic of string
    | Not of prop
    | And of prop * prop
    | Or of prop * prop
    | Implies of prop * prop
    | True
    | False

  let notf p = Not p
  let andf (p1, p2) = And (p1, p2)
  let orf (p1, p2) = Or (p1, p2)
  let impliesf (p1, p2) = Implies (p1, p2)

  let rec print' p =
    match p with
        Atomic str -> str :: []
      | Not p' -> ("not (" :: (print' p')) @ (")" :: [])
      | And (p1, p2) -> ("(" :: (print' p1)) @ ((") /\\ (" :: (print' p2)) @ (")" :: []))
      | Or (p1, p2) -> ("(" :: (print' p1)) @ ((") \\/ (" :: (print' p2)) @ (")" :: []))
      | Implies (p1, p2) -> ("(" :: (print' p1)) @ ((") -> (" :: (print' p2)) @ (")" :: []))
      | True -> "T" :: []
      | False -> "F" :: []

  let print p = String.concat "" (print' p)

  exception SyntaxError

  let precNot = 4
  let precAnd = 3
  let precOr = 2
  let precImplies = 1
  let precMin = 0

  type element = 
      Oper of (prop * prop -> prop) * int 
    | OperN of (prop -> prop) * int 
    | Term of prop 
    | Paren

  let rec flush prec stack =
    match stack with
        [Term _] -> stack
      | OperN (_, _) :: _ -> stack
      | Term _ :: Paren :: _ -> stack
      | Term q :: Oper (f, prec') :: Term p :: stack' ->
          if prec >= prec' then stack
          else flush prec (Term (f (p, q)) :: stack')
      | Term q :: OperN (f, prec') :: stack' ->
          if prec >= prec' then stack
          else flush prec (Term (f q) :: stack')
      | _ -> raise SyntaxError

  let ready stack =
    match stack with
        [] -> stack
      | Paren :: _ -> stack
      | Oper _ :: _ -> stack
      | OperN _ :: _ -> stack
      | _ -> raise SyntaxError

  let rec parse' stack l =
    match l with
        [] ->
            (match flush precMin stack with
                [Term p] -> (p, [])
              | _ -> raise SyntaxError)
      | '~' :: rest ->
            parse' (OperN (notf, precNot) :: ready stack) rest
      | '/' :: '\\' :: rest ->
            parse' (Oper (andf, precAnd) :: flush precAnd stack) rest
      | '\\' :: '/' :: rest ->
            parse' (Oper (orf, precOr) :: flush precOr stack) rest
      | '=' :: '>' :: rest ->
            parse' (Oper (impliesf, precImplies) :: flush precImplies stack) rest
      | 'T' :: rest ->
            parse' (Term True :: ready stack) rest
      | 'F' :: rest ->
            parse' (Term False :: ready stack) rest
      | '(' :: rest ->
            parse' (Paren :: ready stack) rest
      | ')' :: rest ->
            (match flush precMin stack with
                Term p :: Paren :: stack' ->
                  parse' (Term p :: stack') rest
              | _ -> raise SyntaxError)
      | ch :: rest ->
            if Char.compare ch ' ' = 0 then
              parse' stack rest
            else if ((64 < Char.code ch) && (Char.code ch < 91)) then
              parse' (Term (Atomic (String.make 1 ch)) :: ready stack) rest
            else
              (match flush precMin stack with
                  [Term p] -> (p, l)
                | _ -> raise SyntaxError)

  let explode str =
    let rec exp i l =
      if i < 0 then l else exp (i - 1) (str.[i] :: l) in
    exp (String.length str - 1) []

  let parse str =
    match parse' [] (explode str) with
        (p, []) -> p
      | _ -> raise SyntaxError

end