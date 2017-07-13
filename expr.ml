(* 
			 CS 51 Final Project
			MiniML -- Expressions
			     Spring 2017
*)

(* Abstract syntax of MiniML expressions *)

type unop =
  | Negate
;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
;;
      
type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
 and varid = string ;;
  
(* Sets of varids *)
module SS = Set.Make (struct
		       type t = varid
		       let compare = String.compare
		     end ) ;;

type varidset = SS.t ;;

(* Test to see if two sets have the same elements (for
    testing purposes) *)
let same_vars = SS.equal;;

(* Generate a set of variable names from a list of strings (for
    testing purposes) *)
let vars_of_list = SS.of_list ;;
  
(* Return a set of the variable names free in [exp] *)
let rec free_vars (exp : expr) : varidset =
  match exp wit
  | Var v -> SS.singleton v
  | Num _ | Bool _ | Raise | Unassigned -> SS.empty
  | Unop (u, exp1) -> free_vars exp1 
  | Binop (b, exp1, exp2) -> SS.union (free_vars exp1) (free_vars exp2)
  | Conditional (exp1, exp2, exp3) -> 
      SS.union (SS.union (free_vars exp1) (free_vars exp2)) (free_vars exp3)
  | Fun (v, exp1) -> SS.remove v (free_vars exp1)
  | Let (v, exp1, exp2) -> 
      SS.union (SS.remove v (free_vars exp2)) (free_vars exp1)
  | Letrec (v, exp1, exp2) -> 
      SS.union (SS.remove v (free_vars exp2)) (free_vars exp1)
  | App (exp1, exp2) ->
      SS.union (free_vars exp1) (free_vars exp2) ;; *)


let n = ref 0 ;;
(* Return a fresh variable, constructed with a running counter a la
    gensym. Assumes no variable names use the prefix "var". *)
let new_varname () : varid =
  let id = !n in 
  incr n;
  "x" ^ (string_of_int !n) ;;
  
(* Substitute [repl] for free occurrences of [var_name] in [exp] *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  let partial = subst var_name repl in
  match exp with 
  | Var v -> if v = var_name then repl else exp
  | Unop (neg, exp1) -> Unop (neg, partial exp1)
  | Binop (b, exp1, exp2) -> Binop (b, partial exp1, partial exp2)
  | Conditional (exp1, exp2, exp3) ->
      Conditional (partial exp1, partial exp2, partial exp3) 
  | Fun (v, exp1) ->
      if v = var_name then exp
      else
        let v_set = free_vars repl in 
        if not (SS.mem v v_set) then 
          Fun (v, partial exp1)
        else 
          let z = new_varname () in
          Fun (z, partial (subst v (Var z) exp1)) 
  | Let (v, exp1, exp2) ->
        if v = var_name then Let (v, partial exp1, exp2)
        else
          let v_set = free_vars repl in
          if SS.mem v v_set then
            let z = new_varname () in
            Let (z, partial exp1, partial (subst v (Var z) exp2))
          else
            Let (v, partial exp1, partial exp2) 
            
  | Letrec (v, exp1, exp2) ->
      if v = var_name then Letrec (v, partial exp1, exp2)
      else
        let v_set = free_vars repl in
        if SS.mem v v_set then
          let z = new_varname () in
          Letrec (z, partial exp1, partial (subst v (Var z) exp2))
        else 
          Letrec (v, partial exp1, partial exp2)
  | App (exp1, exp2) -> App (partial exp1, partial exp2) 
  | _ -> exp
    
(* exp_to_string -- Returns a string representation of the expr *)
let rec exp_to_string (exp : expr) : string =
  match exp with 
  | Var v -> v
  | Num i -> string_of_int i
  | Bool b -> if b then "true" else "false"
  | Unop (u, exp1) -> "~- " ^ exp_to_string exp1
  | Binop (b, exp1, exp2) ->
      (match b with 
       | Plus -> exp_to_string exp1 ^ " + " ^ exp_to_string exp2
       | Minus -> exp_to_string exp1 ^ " - " ^ exp_to_string exp2
       | Times -> exp_to_string exp1 ^ " * " ^ exp_to_string exp2
       | Equals -> exp_to_string exp1 ^ " = " ^ exp_to_string exp2
       | LessThan -> exp_to_string exp1 ^ " < " ^ exp_to_string exp2)
  | Conditional (exp1, exp2, exp3) ->
      "if " ^ exp_to_string exp1 ^ " then " ^
        exp_to_string exp2 ^
      " else " ^
        exp_to_string exp3
  | Fun (v, exp1) -> 
      "fun " ^ v ^ " -> " ^ exp_to_string exp1
  | Let (v, exp1, exp2) -> 
      "let " ^ v ^ " = " ^ exp_to_string exp1 ^ " in " ^ exp_to_string exp2
  | Letrec (v, exp1, exp2) -> 
      "let rec " ^ v ^ " = " ^ exp_to_string exp1 ^ " in " ^ exp_to_string exp2
  | Raise -> "raise"
  | Unassigned -> "Unassigned"
  | App (exp1, exp2) -> "(" ^ exp_to_string exp1 ^ ")" ^ " (" ^
                        exp_to_string exp2 ^ ")"

(* exp_to_abstract_string: Returns a string representation of the abstract
   syntax of the expr *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with
  | Var v ->
      "Var" ^ "(" ^ v ^ ")"
  | Num i ->
      "Num" ^ "(" ^ string_of_int i ^ ")"
  | Bool b ->
      if b then "true" else "false"
  | Unop (un, exp1) ->
      "Unop(~-, " ^ exp_to_abstract_string exp1 ^ ")"
  | Binop (bin, exp1, exp2) -> 
      (match bin with 
       | Plus ->
           "Binop(+, " ^ exp_to_abstract_string exp1 ^ ", " ^
           exp_to_abstract_string exp2 ^ ")"
       | Minus -> 
           "Binop(-, " ^ exp_to_abstract_string exp1 ^ ", " ^
           exp_to_abstract_string exp2 ^ ")"
       | Times ->
           "Binop(*, " ^ exp_to_abstract_string exp1 ^ ", " ^
           exp_to_abstract_string exp2 ^ ")"
       | Equals -> 
           "Binop(=, " ^ exp_to_abstract_string exp1 ^ ", " ^
           exp_to_abstract_string exp2 ^ ")"
       | LessThan ->
           "Binop(<, " ^ exp_to_abstract_string exp1 ^ ", " ^
           exp_to_abstract_string exp2 ^ ")")
  | Conditional (exp1, exp2, exp3) ->
      "Conditional(" ^ exp_to_abstract_string exp1 ^ ", " ^
      exp_to_abstract_string exp2  ^ ", " ^ exp_to_abstract_string exp3 ^ ")"
  | Fun (v, exp) -> 
      "Fun(" ^ v ^ ", " ^ exp_to_abstract_string exp ^ ")"
  | Let (v, exp1, exp2) -> 
      "Let(" ^ v ^ ", " ^ exp_to_abstract_string exp1 ^ ", " ^
      exp_to_abstract_string exp2 ^ ")"
  | Letrec (v, exp1, exp2) -> 
      "Letrec(" ^ v ^ ", " ^ exp_to_abstract_string exp1 ^ ", " ^
      exp_to_abstract_string exp2 ^ ")"
  | Raise -> 
      "Raise"
  | Unassigned -> 
      "Unassigned"
  | App (exp1, exp2) -> 
      "App(" ^ exp_to_abstract_string exp1 ^ ", " ^ exp_to_abstract_string exp2 ^ ")" ;;





