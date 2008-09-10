(* ------------------------------------------------------------------------- *)
(* The underlying type of terms.                                             *)
(* ------------------------------------------------------------------------- *)

type term = Var of string
          | Fn of string * (term list);;

(* ------------------------------------------------------------------------- *)
(* General exception                                                         *)
(* ------------------------------------------------------------------------- *)

exception error of string;;

(* ------------------------------------------------------------------------- *)
(* Auxiliary functions.                                                      *)
(* ------------------------------------------------------------------------- *)

let rec length l = if l = [] then 0 else 1 + length(tl l);;

let rec itlist f =
     fun [] b -> b
       | (h::t) b -> f h (itlist f t b);;

let rec itlist2 f =
  fun [] [] b -> b
    | (h1::t1) (h2::t2) b -> f h1 h2 (itlist2 f t1 t2 b);;

let K x y = x;;

let o f g x = f(g x);;
#infix "o";;

let explode s =
  let rec exap n l =
      if n < 0 then l else
      exap (n - 1) ((sub_string s n 1)::l) in
  exap (string_length s - 1) [];;

let partition p l =
    itlist (fun a (yes,no) -> if p a then a::yes,no else yes,a::no) l ([],[]);;

let filter p l = itlist (fun x s -> if p x then x::s else s) l [];;         

(* ------------------------------------------------------------------------- *)
(* General parser combinators.                                               *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* Lexer.                                                                    *)
(* ------------------------------------------------------------------------- *)

type token = Variable of string | Constant of string | Punct of string;;

let lex =
  let several p = many (some p) in
  let collect(h,t) = h^(itlist (prefix ^) t "") in
  let upper_alpha s = "A" <= s & s <= "Z" or s = "_"
  and lower_alpha s = "a" <= s & s <= "z" or "0" <= s & s <= "9"
  and punct s = s = "(" or s = ")" or s = "[" or s = "]"
                or s = "," or s = "."
  and space s = s = " " or s = "\n" or s = "\t" in
  let alnum s = upper_alpha s or lower_alpha s in
  let symbolic s = not space s & not alnum s & not punct s in
  let rawvariable =
    some upper_alpha ++ several alnum >> (Variable o collect)
  and rawconstant =
    (some lower_alpha ++ several alnum ||
     some symbolic ++ several symbolic) >> (Constant o collect)
  and rawpunct = some punct >>  Punct in
  let token =
    (rawvariable || rawconstant || rawpunct) ++ several space >> fst in
  let tokens = (several space ++ many token) >> snd in
  let alltokens = (tokens ++ finished) >> fst in
  fst o alltokens o explode;;

(* ------------------------------------------------------------------------- *)
(* Precedence parsing.                                                       *)
(* ------------------------------------------------------------------------- *)

let infixes =
  ref [".",4; "is",5; "+",10; "-",10; "*",20; "/",20];;

let findmin l =
  itlist (fun (_,pr1 as p1) (_,pr2 as p2) -> if pr1 <= pr2 then p1 else p2)
      (tl l) (hd l);;

let rec delete x (h::t) = if h = x then t else h::(delete x t);;

let rec binop op parser input =
  let atom1,rest1 as result = parser input in
  if not rest1 = [] & hd rest1 = Constant op then
    let atom2,rest2 = binop op parser (tl rest1) in
    Fn(op,[atom1; atom2]),rest2
  else result;;

let rec precedence ilist parser input =
  if ilist = [] then parser input else
  let opp = findmin ilist in
  let ilist' = delete opp ilist in
  binop (fst opp) (precedence ilist' parser) input;;

(* ------------------------------------------------------------------------- *)
(* The general parser.                                                       *)
(* ------------------------------------------------------------------------- *)

let variable =
  fun (Variable s::rest) -> s,rest
    | _ -> raise Noparse;;

let constant =
  fun (Constant s::rest) -> s,rest
    | _ -> raise Noparse;;

let rec atom input
       = (constant ++ a (Punct "(") ++ termlist ++ a (Punct ")")
              >> (fun (((name,_),args),_) -> Fn(name,args))
       || constant
              >> (fun s -> Fn(s,[]))
       || variable
              >> (fun s -> Var s)
       || a (Punct "(") ++ term ++ a (Punct ")")
              >> (snd o fst)
       || a (Punct "[") ++ list
              >> snd) input
  and term input = precedence (!infixes) atom input
  and termlist input
       = (term ++ a (Punct ",") ++ termlist
              >> (fun ((h,_),t) -> h::t)
       || term
              >> (fun h -> [h])) input
  and list input
       = (term ++ (a (Constant "|") ++ term ++ a (Punct "]")
                        >> (snd o fst)
                || a (Punct ",") ++ list
                         >> snd
                || a (Punct "]")
                        >> (K (Fn("[]",[]))))
              >> (fun (h,t) -> Fn(".",[h; t]))
       || a (Punct "]")
              >> (K (Fn("[]",[])))) input
  and rule input 
      = (term ++ (a (Punct ".") 
                        >> (K [])
               || a (Constant ":-") ++ term ++
                  many (a (Punct ",") ++ term >> snd) ++ a (Punct ".")
                        >> (fun (((_,h),t),_) -> h::t))) input;;

let parse_term = fst o (term ++ finished >> fst) o lex;;       

let parse_rules = fst o (many rule ++ finished >> fst) o lex;;       

(* ------------------------------------------------------------------------- *)
(* Printer.                                                                  *)
(* ------------------------------------------------------------------------- *)

let get_precedence s = assoc s (!infixes);;

infixes := ("^",30)::(!infixes);;

let can f x = try f x; true with _ -> false;;

let is_infix = can get_precedence;;

let rec string_of_term prec =
  fun (Var s) -> s
    | (Fn(f,[])) -> f
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

#open "format";;

let print_term s =
  open_hvbox 0;
  print_string("`"^(string_of_term 0 s)^"`");
  close_box();;

install_printer "print_term";;

(* ------------------------------------------------------------------------- *)
(* Simple unification.                                                       *)
(* ------------------------------------------------------------------------- *)

let rec occurs_in x =
  fun (Var y) -> x = y
    | (Fn(_,args)) -> exists (occurs_in x) args;;

let rec subst insts tm =
  match tm with
    Var y -> (try assoc y insts with Not_found -> tm)
  | Fn(f,args) -> Fn(f,map (subst insts) args);;

let raw_augment =
  let augment1 theta (x,s) =
    let s' = subst theta s in
    if occurs_in x s & not(s = Var(x)) then raise (error "Occurs check")
    else (x,s') in
  fun p insts -> p::(map (augment1 [p]) insts);;

let augment (v,t) insts =
  let t' = subst insts t in
  match t' with
    Var(w) -> if w <= v then
                if w = v then insts
                else raw_augment (v,t') insts
              else raw_augment (w,Var(v)) insts
  | _ -> if occurs_in v t' then raise (error "Occurs check")
         else raw_augment (v,t') insts;;

let rec unify tm1 tm2 insts =
  match tm1 with
    Var(x) ->
      (try let tm1' = assoc x insts in
           unify tm1' tm2 insts
       with Not_found ->
           augment (x,tm2) insts)
  | Fn(f1,args1) ->
      match tm2 with
        Var(y) ->
          (try let tm2' = assoc y insts in
               unify tm1 tm2' insts
           with Not_found ->
               augment (y,tm1) insts)
      | Fn(f2,args2) ->
          if f1 = f2 then itlist2 unify args1 args2 insts
          else raise (error "functions do not match");;

(* ------------------------------------------------------------------------- *)
(* Renaming of a clause, appending a given string to variables.              *)
(* ------------------------------------------------------------------------- *)

let rec rename s =
  fun (Var v) -> Var("~"^v^s)
    | (Fn(f,args)) -> Fn(f,map (rename s) args);;

let rename_rule s (conc,asms) = (rename s conc,map (rename s) asms);;

(* ------------------------------------------------------------------------- *)
(* Basic Prolog engine.                                                      *)
(* ------------------------------------------------------------------------- *)

let rec first f =
  fun [] -> raise (error "No rules applicable")
    | (h::t) -> try f h with error _ -> first f t;;

let rec expand n rules insts goals =
  first (fun rule ->
    if goals = [] then insts else
    let conc,asms = rename_rule (string_of_int n) rule in
    let insts' = unify conc (hd goals) insts in 
    let local,global = partition 
      (fun (v,_) -> occurs_in v conc or exists (occurs_in v) asms) insts' in
    let goals' = (map (subst local) asms) @ (tl goals) in
    expand (n + 1) rules global goals') rules;;

(* ------------------------------------------------------------------------- *)
(* User interface.                                                           *)
(* ------------------------------------------------------------------------- *)

type outcome = No | Yes of (string * term) list;;

let prolog rules goal =
  try let insts = expand 0 rules [] [goal] in
      Yes(filter (fun (v,_) -> occurs_in v goal) insts)
  with error _ -> No;;

(* ------------------------------------------------------------------------- *)
(* Definition of append.                                                     *)
(* ------------------------------------------------------------------------- *)

let rules = parse_rules 
  "append([],L,L).
   append([H|T],L,[H|A]) :- append(T,L,A).";;

let goal = parse_term "append([1,2],[3],[1,2,3])" in prolog rules goal;;        
                                      
let goal = parse_term "append([1,2],[3,4],X)" in prolog rules goal;;   

(*** let goal = parse_term "append(X,[3,4],X)" in prolog rules goal;;   ***)

let goal = parse_term "append([3,4],X,X)" in prolog rules goal;;   

let goal = parse_term "append([1,2],X,Y)" in prolog rules goal;;   

let goal = parse_term "append([1,2,3,4,5],[6,7,8],X)" in prolog rules goal;;    

(* ------------------------------------------------------------------------- *)
(* An example from Clocksin & Mellish (pp. 15-16).                           *)
(* ------------------------------------------------------------------------- *)

let rules = parse_rules
  "male(albert).
   male(edward).
   female(alice).
   female(victoria).
   parents(edward,victoria,albert).
   parents(alice,victoria,albert).
   sister_of(X,Y) :-
     female(X),
     parents(X,M,F),
     parents(Y,M,F).";;

let goal = parse_term "sister_of(alice,edward)" in prolog rules goal;;

let goal = parse_term "sister_of(alice,X)" in prolog rules goal;;

let goal = parse_term "sister_of(X,Y)" in prolog rules goal;;

(* ------------------------------------------------------------------------- *)
(* Creation of new variable.                                                 *)
(* ------------------------------------------------------------------------- *)

let mkvar = 
  let rn = ref 0 in
  fun () -> let s = "~"^(string_of_int(!rn)) in
            rn := !rn + 1; s;;

(* ------------------------------------------------------------------------- *)
(* Creation of NNF.                                                          *)
(* ------------------------------------------------------------------------- *)

infixes := !infixes @ ["&",4; "|",3; "-->",2; "<->",1];;

let rec proc tm =  
  match tm with
    Fn("~",[t]) -> Fn("~",[proc t])
  | Fn("&",[t1; t2]) -> Fn("&",[proc t1; proc t2])
  | Fn("|",[t1; t2]) -> Fn("|",[proc t1; proc t2])
  | Fn("-->",[t1; t2]) -> proc (Fn("|",[Fn("~",[t1]); t2]))
  | Fn("<->",[t1; t2]) -> proc (Fn("&",[Fn("-->",[t1; t2]);
                                           Fn("-->",[t2; t1])]))
  | Fn("forall",[x; t]) -> Fn("forall",[x; proc t])
  | Fn("exists",[x; t]) -> Fn("exists",[x; proc t])
  | t -> t;;

let rec nnf_p tm =
  match tm with
    Fn("~",[t]) -> nnf_n t
  | Fn("&",[t1; t2]) -> Fn("&",[nnf_p t1; nnf_p t2])
  | Fn("|",[t1; t2]) -> Fn("|",[nnf_p t1; nnf_p t2])
  | Fn("forall",[x; t]) -> Fn("forall",[x; nnf_p t])
  | Fn("exists",[x; t]) -> Fn("exists",[x; nnf_p t])
  | t -> t

and nnf_n tm =
  match tm with
    Fn("~",[t]) -> nnf_p t 
  | Fn("&",[t1; t2]) -> Fn("|",[nnf_n t1; nnf_n t2])
  | Fn("|",[t1; t2]) -> Fn("&",[nnf_n t1; nnf_n t2])
  | Fn("forall",[x; t]) -> Fn("exists",[x; nnf_n t])
  | Fn("exists",[x; t]) -> Fn("forall",[x; nnf_n t])
  | t -> Fn("~",[t]);;

(* ------------------------------------------------------------------------- *)
(* Tableau prover.                                                           *)
(* ------------------------------------------------------------------------- *)

let rec prove fm unexp pl nl n cont i =                                        
  if n < 0 then raise (error "No proof") else                      
  match fm with                                                       
    Fn("&",[p;q]) ->                                                            
        prove p (q::unexp) pl nl n cont i                            
  | Fn("|",[p;q]) ->                                                           
        prove p unexp pl nl n                                            
        (prove q unexp pl nl n cont) i                    
  | Fn("forall",[Var x; p]) ->                                                 
        let v = mkvar() in                                                     
        prove (subst [x,Var v] p) (unexp@[fm]) pl nl (n - 1) cont i  
  | Fn("exists",[Var x; p]) ->                    
        let v = mkvar() in                                                      
        prove (subst [x,Fn(v,[])] p) unexp pl nl (n - 1) cont i
  | Fn("~",[t]) ->                                                     
        (try first (fun t' -> let i' = unify t t' i in
                              cont i') pl
         with error _ -> 
            prove (hd unexp) (tl unexp) pl (t::nl) n cont i)                   
  | t ->                                                                       
        (try first (fun t' -> let i' = unify t t' i in             
                              cont i') nl                             
         with error _ ->                                                        
            prove (hd unexp) (tl unexp) (t::pl) nl n cont i);;       

(* ------------------------------------------------------------------------- *)
(* Final front end.                                                          *)
(* ------------------------------------------------------------------------- *)

let prover =
  let rec prove_iter n t =          
    try let insts = prove t [] [] [] n (fun x -> x) [] in
        let globinsts = filter (fun (v,_) -> occurs_in v t) insts in
        n,globinsts
    with error _ -> prove_iter (n + 1) t in
  fun t -> prove_iter 0 (nnf_n(proc(parse_term t)));;

(* ------------------------------------------------------------------------- *)
(* Propositional logic.                                                      *)
(* ------------------------------------------------------------------------- *)

let PROP_1 = prover "p --> q <-> ~(q) --> ~(p)";;

let PROP_13 = prover "p | q & r <-> (p | q) & (p | r)";;

let PROP_16 = prover "(p --> q) | (q --> p)";;

(* ------------------------------------------------------------------------- *)
(* Monadic Predicate Logic.                                                  *)
(* ------------------------------------------------------------------------- *)

let MPRED_18 = prover "exists(Y,forall(X,p(Y) --> p(X)))";;

let MPRED_19 = prover 
  "exists(X,forall(Y,forall(Z,(p(Y) --> q(Z)) --> p(X) --> q(X))))";;

(* ------------------------------------------------------------------------- *)
(* The Agatha example, optionally with a Whodunit.                           *)
(* ------------------------------------------------------------------------- *)

let P55 = prover
  "lives(agatha) & lives(butler) & lives(charles) &
   (killed(agatha,agatha) | killed(butler,agatha) |
    killed(charles,agatha)) &
   (forall(X,forall(Y,
        killed(X,Y) --> hates(X,Y) & ~(richer(X,Y))))) &
   (forall(X,hates(agatha,X) --> ~(hates(charles,X)))) &
   (hates(agatha,agatha) & hates(agatha,charles)) &
   (forall(X,
        lives(X) & ~(richer(X,agatha)) --> hates(butler,X))) &
   (forall(X,hates(agatha,X) --> hates(butler,X))) &
   (forall(X,
        ~(hates(X,agatha)) | ~(hates(X,butler)) | ~(hates(X,charles)))) 
   --> killed(agatha,agatha)";;

let P55' = prover
  "lives(agatha) & lives(butler) & lives(charles) &
   (killed(agatha,agatha) | killed(butler,agatha) |
    killed(charles,agatha)) &
   (forall(X,forall(Y,
        killed(X,Y) --> hates(X,Y) & ~(richer(X,Y))))) &
   (forall(X,hates(agatha,X) --> ~(hates(charles,X)))) &
   (hates(agatha,agatha) & hates(agatha,charles)) &
   (forall(X,
        lives(X) & ~(richer(X,agatha)) --> hates(butler,X))) &
   (forall(X,hates(agatha,X) --> hates(butler,X))) &
   (forall(X,
        ~(hates(X,agatha)) | ~(hates(X,butler)) | ~(hates(X,charles)))) 
   --> killed(X,agatha)";;
