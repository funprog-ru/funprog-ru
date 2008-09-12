let hd l = match l with
    [] -> failwith "Empty list"
  | h::_ ->h;;

let tl l = match l with
    [] -> failwith "Empty list"
  | _::t -> t;;

let rec length l = if l = [] then 0 else 1 + length(tl l);;

let rec itlist f l b = match l with 
  [] -> b
  | (h::t) -> f h (itlist f t b);;

let uncurry f(x,y) = f x y;;

let k x y = x;;

let c f x y = f y x;;

(* o replaced with ++++ *)
let ( ++++ ) f g x  = f(g x);;

let explode s =
  let rec exap n l =
      if n < 0 then l else
      exap (n - 1) ((String.sub s n 1)::l) in
  exap (String.length s - 1) [];;

type term = Var of string
          | Const of string
          | Fn of string * (term list);;

(* check ? *)
let rec assoc a ((x,y)::rest) = match a with
    [] -> []
  | _ -> if a = x then y else assoc a rest;;

let infixes = ref ["+",10; "-",10; "*",20; "/",20];;

(* OCaml checked *)
let get_precedence s = assoc s (!infixes);;

infixes := ("^",30)::(!infixes);;

let can f x = try f x; true with _ -> false;;

let is_infix = can get_precedence;;

let rec string_of_term prec =
  fun (Var s) -> s
    | (Const c) -> c
    | (Fn(f,args)) ->
        if length args = 2 & is_infix f then
          let prec' = get_precedence f in
          let s1 = string_of_term prec' (hd args)

          and s2 = string_of_term prec' (hd(tl args)) in
          let ss = s1^" "^f^" "^s2 in
          if prec' <= prec then "("^ss^")" else ss
        else
          f^"("^(string_of_terms args)^")"

and string_of_terms t =
  match t with
      [] -> ""
    | [t] -> string_of_term 0 t
    | (h::t) -> (string_of_term 0 h)^","^(string_of_terms t);;

let t =
    Fn("-",[Fn("/",[Fn("sin",[Fn("+",[Var "x"; Var "y"])]);
                    Fn("cos",[Fn("-",[Var "x";
                                      Fn("exp",[Var "y"])])])]);
            Fn("ln",[Fn("+",[Const "1"; Var "x"])])]);;

#open "format";;

let print_term s =
  open_hvbox 0;
  print_string("`"^(string_of_term 0 s)^"`");
  close_box();;

(* install_printer "print_term";; *)

let rec differentiate x tm = match tm with
    Var y -> if y = x then Const "1" else Const "0"
  | Const c -> Const "0"
  | Fn("-",[t]) -> Fn("-",[differentiate x t])
  | Fn("+",[t1;t2]) -> Fn("+",[differentiate x t1;
                                differentiate x t2])
  | Fn("-",[t1;t2]) -> Fn("-",[differentiate x t1;
                                differentiate x t2])
  | Fn("*",[t1;t2]) ->
     Fn("+",[Fn("*",[differentiate x t1; t2]);
             Fn("*",[t1; differentiate x t2])])
  | Fn("inv",[t]) -> chain x t
     (Fn("-",[Fn("inv",[Fn("^",[t;Const "2"])])]))
  | Fn("^",[t;n]) -> chain x t
    (Fn("*",[n; Fn("^",[t; Fn("-",[n; Const "1"])])]))
  | Fn("exp",[t]) -> chain x t tm
  | Fn("ln",[t]) -> chain x t (Fn("inv",[t]))
  | Fn("sin",[t]) -> chain x t (Fn("cos",[t]))
  | Fn("cos",[t]) -> chain x t
     (Fn("-",[Fn("sin",[t])]))
  | Fn("/",[t1;t2]) -> differentiate x
     (Fn("*",[t1; Fn("inv",[t2])]))
  | Fn("tan",[t]) -> differentiate x
     (Fn("/",[Fn("sin",[t]); Fn("cos",[t])]))
and chain x t u =  Fn("*",[differentiate x t; u]);;

let simp =
  fun (Fn("+",[Const "0"; t])) -> t
    | (Fn("+",[t; Const "0"])) -> t
    | (Fn("-",[t; Const "0"])) -> t
    | (Fn("-",[Const "0"; t])) -> Fn("-",[t])
    | (Fn("+",[t1; Fn("-",[t2])])) -> Fn("-",[t1; t2])
    | (Fn("*",[Const "0"; t])) -> Const "0"
    | (Fn("*",[t; Const "0"])) -> Const "0"
    | (Fn("*",[Const "1"; t])) -> t
    | (Fn("*",[t; Const "1"])) -> t
    | (Fn("*",[Fn("-",[t1]); Fn("-",[t2])])) -> Fn("*",[t1; t2])
    | (Fn("*",[Fn("-",[t1]); t2])) -> Fn("-",[Fn("*",[t1; t2])])
    | (Fn("*",[t1; Fn("-",[t2])])) -> Fn("-",[Fn("*",[t1; t2])])
    | (Fn("-",[Fn("-",[t])])) -> t
    | t -> t;;

let rec dsimp =
  fun (Fn(fn,args)) -> simp(Fn(fn,map dsimp args))
    | t -> simp t;;

exception Noparse;;

let prefix || parser1 parser2 input =
  try parser1 input
  with Noparse -> parser2 input;;

let prefix ++ parser1 parser2 input =
  let result1,rest1 = parser1 input in
  let result2,rest2 = parser2 rest1 in
  (result1,result2),rest2;;

let rec many parser input =
  try let result,next = parser input in
      let results,rest = many parser next in
      (result::results),rest
  with Noparse -> [],input;;

let prefix >> parser treatment input =
  let result,rest = parser input in
  treatment(result),rest;;

let some p =
  fun [] -> raise Noparse
    | (h::t) -> if p h then (h,t) else raise Noparse;;

let a tok = some (fun item -> item = tok);;

let finished input =
  if input = [] then 0,input else raise Noparse;;

type lexeme = Name of string | Num of string | Other of string;;

let lex =
  let several p = many (some p) in
  let lowercase_letter s = "a" <= s & s <= "z" in
  let uppercase_letter s = "A" <= s & s <= "Z" in
  let letter s = lowercase_letter s or uppercase_letter s in
  let alpha s = letter s or s = "_" or s = "'" in
  let digit s = "0" <= s & s <= "9" in
  let alphanum s = alpha s or digit s in
  let space s = s = " " or s = "\n" or s = "\t" in
  let collect(h,t) = h^(itlist (prefix ^) t "") in
  let rawname =
     some alpha ++ several alphanum >> (Name o collect) in
  let rawnumeral =
     some digit ++ several digit >> (Num o collect) in
  let rawother = some (K true) >> Other in
  let token =
    (rawname || rawnumeral || rawother) ++ several space >> fst in
  let tokens = (several space ++ many token) >> snd in
  let alltokens = (tokens ++ finished) >> fst in
  fst o alltokens o explode;;

let name =
  fun (Name s::rest) -> s,rest
    | _ -> raise Noparse;;

let numeral =
  fun (Num s::rest) -> s,rest
    | _ -> raise Noparse;;

let other =
  fun (Other s::rest) -> s,rest
    | _ -> raise Noparse;;

let rec atom input
       = (name ++ a (Other "(") ++ termlist ++ a (Other ")")
              >> (fun (((name,_),args),_) -> Fn(name,args))
       || name
              >> (fun s -> Var s)
       || numeral
              >> (fun s -> Const s)
       || a (Other "(") ++ term ++ a (Other ")")
              >> (snd o fst)
       || a (Other "-") ++ atom
              >> snd) input
  and mulexp input
       = (atom ++ a(Other "*") ++ mulexp
              >> (fun ((a,_),m) -> Fn("*",[a;m]))
       || atom) input
  and term input
       = (mulexp ++ a(Other "+") ++ term
              >> (fun ((a,_),m) -> Fn("+",[a;m]))
       || mulexp) input
  and termlist input
       = (term ++ a (Other ",") ++ termlist
              >> (fun ((h,_),t) -> h::t)
       || term
              >> (fun h -> [h])) input;;

let parser = fst o (term ++ finished >> fst) o lex;;

let findmin l =
  itlist (fun (_,pr1 as p1) (_,pr2 as p2) -> if pr1 <= pr2 then p1 else p2)
      (tl l) (hd l);;

let rec delete x (h::t) = if h = x then t else h::(delete x t);;

let ilist = !infixes;;

let rec binop op parser input =
  let atom1,rest1 as result = parser input in
  if not rest1 = [] & hd rest1 = Other op then
    let atom2,rest2 = binop op parser (tl rest1) in
    Fn(op,[atom1; atom2]),rest2
  else result;;

let rec precedence ilist parser input =
  if ilist = [] then parser input else
  let opp = findmin ilist in
  let ilist' = delete opp ilist in
  binop (fst opp) (precedence ilist' parser) input;;

precedence ilist atom (lex "x ^ 2 * y * z^2 + a * b - c + d");;

let rec atom input
       = (name ++ a (Other "(") ++ termlist ++ a (Other ")")
              >> (fun (((name,_),args),_) -> Fn(name,args))
       || name
              >> (fun s -> Var s)
       || numeral
              >> (fun s -> Const s)
       || a (Other "(") ++ term ++ a (Other ")")
              >> (snd o fst)
       || a (Other "-") ++ atom
              >> snd) input
  and term input = precedence (!infixes) atom input
  and termlist input
       = (term ++ a (Other ",") ++ termlist
              >> (fun ((h,_),t) -> h::t)
       || term
              >> (fun h -> [h])) input;;

let parser = fst o (term ++ finished >> fst) o lex;;

parser "sin(x + y) * cos(2 * x + y)";;

parser "2 * sin(x)^2 + 2 * sin(y)^2 - 2";;

let rec atom input
       = (name ++ a (Other "(") ++ termlist ++ a (Other ")")
              >> (fun (((name,_),args),_) -> Fn(name,args))
       || name
              >> (fun s -> Var s)
       || numeral
              >> (fun s -> Const s)
       || a (Other "(") ++ term ++ a (Other ")")
              >> (snd o fst)
       || a (Other "-") ++ atom
              >> snd) input
  and term input = precedence (!infixes) atom input
  and termlist input
        = (term ++ many (a (Other ",") ++ term >> snd)
                >> (fun (h,t) -> h::t)) input;;

parser "sin(x + y) * cos(2 * x + y)";;

parser "2 * sin(x)^2 + 2 * sin(y)^2 - 2";;

parser "f(n - 1,r - 1) + r * f(n - 1,r)";;


die;;

#open "num";;

let prefix + = add_num;;

let prefix - = sub_num;;

let prefix * = mult_num;;

let prefix / = quo_num;;

let prefix mod = mod_num;;

let prefix ** = power_num;;

let prefix < = lt_num;;

let prefix <= = le_num;;

let prefix > = gt_num;;

let prefix >= = ge_num;;

let neg = minus_num;;

let real_of_num k = fun n -> (Int 2 ** n) * k;;

let real_neg f = fun n -> neg(f n);;

let real_abs f = fun n -> abs_num (f n);;

let ndiv x y =
 let q = x / y and r = x mod y in
 if (abs_num(Int 2 * r)) <= (abs_num y) then q
 else if (abs_num(Int 2 * (r - y))) <= (abs_num y) then q + Int 1
 else q - Int 1;;

#infix "ndiv";;

let real_add f g =
  fun n -> (f(n + Int 2) + g(n + Int 2)) ndiv (Int 4);;

let real_sub f g = real_add f (real_neg g);;
