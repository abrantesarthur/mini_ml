open Expr
open Evaluation

let assert_raises f = 
		try
			f (); 
			false
		with
		| _ -> true ;;

let test_exp_to_abstract_string () =  
	let f = exp_to_abstract_string in 
	let exp1 = Var "x" in 
	assert (f exp1 = "Var(x)") ;
	let exp2 = Num 2 in 
	assert (f exp2 = "Num(2)") ;
	let exp3 = Bool true in 
	assert (f exp3 = "true") ;
	let exp4 = Unop (Negate, Var "x") in 
	assert (f exp4 = "Unop(~-, Var(x))") ;
	let exp5 = Binop (Plus, Unop (Negate, Num 4), Num 5) in 
	assert (f exp5 = "Binop(+, Unop(~-, Num(4)), Num(5))") ;
	let exp6 = Binop (Minus, Binop (Plus, Var "a", Var "b"), Num 10) in 
	assert (f exp6 = "Binop(-, Binop(+, Var(a), Var(b)), Num(10))") ;
	let exp7 = Binop (Times, Binop (Minus, Unop (Negate, Num 3), Var "y"),
			   Num 6)
	in 
	assert (f exp7 = "Binop(*, Binop(-, Unop(~-, Num(3)), Var(y)), Num(6))") ; 
	let exp8 = Binop (Equals, Num 3, Num 3) in 
	assert (f exp8 = "Binop(=, Num(3), Num(3))") ;
	let exp9 = Binop (LessThan, Num 4, Num 5) in 
	assert (f exp9 = "Binop(<, Num(4), Num(5))") ;
	let exp10 = Conditional (Binop (Equals, Num 1, Num 1), Num 3, Var "x") in 
	assert (f exp10 = "Conditional(Binop(=, Num(1), Num(1)), Num(3), Var(x))") ;
	let exp11 = Fun ("x", Binop (Plus, Var "x", Num 3)) in 
	assert (f exp11 = "Fun(x, Binop(+, Var(x), Num(3)))") ;
	let exp12 = Let("f", Fun ("x", Var "x"), App (Var "f", Num 3)) in 
	assert (f exp12 = "Let(f, Fun(x, Var(x)), App(Var(f), Num(3)))") ;
	let exp13 = Letrec("f", Fun ("x", Var "x"), App (Var "f", Num 3)) in 
	assert (f exp13 = "Letrec(f, Fun(x, Var(x)), App(Var(f), Num(3)))") ;
	let exp14 = Raise in 
	assert (f exp14 = "Raise") ;
	let exp15 = Unassigned in 
	assert (f exp15 = "Unassigned") ;
	let exp16 = App (Var "f", Num 4) in 
	assert (f exp16 = "App(Var(f), Num(4))") ;;

let test_free_vars () = 
	let f = free_vars in 
	let exp1 = Var "x" in 
	assert (same_vars (f exp1) (SS.add "x" SS.empty)) ;
	let exp2 = Num 1 in 
	assert (SS.is_empty (f exp2)) ;
	let exp3 = Bool true in 
	assert (SS.is_empty (f exp3)) ;
	let exp4 = Raise in 
	assert (SS.is_empty (f exp4)) ;
	let exp5 = Unassigned in 
	assert (SS.is_empty (f exp5)) ;
	let exp6 = Unop (Negate, Binop (Plus, Num 5, Num 6)) in 
	assert (same_vars (f exp6) (SS.empty)) ;
	let exp7 = Binop (Minus, Unop (Negate, Var "y"),
			   Binop (Times, Var "a", Var "b")) 
	in 
	assert (f exp7 = SS.union (SS.add "y" SS.empty)
		   (SS.union (SS.add "a" SS.empty) (SS.add "b" SS.empty))) ;
	let exp8 = Conditional (Binop (Equals, Var "x", Num 2), Var "y", Raise) in 
	assert (same_vars (f exp8) (SS.union (SS.add "x" SS.empty) (SS.add "y"
			SS.empty))) ;
	let exp9 = Fun ("x", Binop (Plus, Var "x", Num 1)) in
	assert (same_vars (f exp9) SS.empty) ;
	let exp10 = Let ("f", Fun("x", Binop (Plus, Var "x", Num 2)),
				App(Var "f", Num 3))
	in
	assert (same_vars (f exp10) (SS.empty)) ;
	let exp11 = Letrec ("f", Fun("x", Binop (Plus, Var "x", Num 2)),
				App(Var "f", Num 3))
	in
	assert (same_vars (f exp11) (SS.empty)) ;
	let exp13 = Letrec ("f", Fun ("x", Conditional (Binop (Equals, Var "x",
				Num 0), Num 1, Binop (Times, Var "x", App (Var "f",
				Binop (Minus, Var "x", Num 1))))), App (Var "f", Num 4))
	in 
	assert (same_vars (f exp13) SS.empty) ;
	let exp12 = App (Fun ("x", Binop (Minus, Num 10, Var "a")), Var "x") in 
	assert (f exp12 = SS.union (SS.add "a" SS.empty) (SS.add "x" SS.empty)) ;;

let test_subst () = 
	let print = exp_to_abstract_string in 
	let repl_list = 
		[Var "x"; Num 0; Unop (Negate, Var "x");
		 Binop (Plus, Var "x", Var "x");
		 Conditional (Binop (Equals, Num 2, Var "b"), Num 1, Num 0); 
		 Fun ("x", Binop (Times, Var "x", Num 10)); 
		 Let ("x", Num 2, Binop (Minus, Var "x", Num 2));
  		 Letrec ("x", Num 2, Binop (Minus, Var "x", Num 2));
  		 App (Var "x", Num 5)]
	in 
	let exp1 = Var "a" in 
	let truth_list1 =
	  List.map (fun repl -> print (subst "a" repl exp1) = print repl) repl_list
	in 
	let truth_list2 =
	  List.map (fun repl -> print (subst "b" repl exp1) = print repl) repl_list
	in 
	assert (List.mem false truth_list1 = false) ;
	assert (List.mem false truth_list2 = true) ;
	let exp2 = Num 1 in 
	let truth_list3 = 
	  List.map (fun repl -> print (subst "x" repl exp2) = print exp2) repl_list
  	in 
  	assert (List.mem false truth_list3 = false) ;
  	let exp3 = Unop (Negate, Num 0) in 
  	let exp4 = Unop (Negate, Var "x") in
  	let truth_list4 = 
  	  List.map (fun repl -> print (subst "x" repl exp3) = print exp3) repl_list
  	in 
  	let truth_list5 = 
  	  List.map (fun repl ->
  	  			 print (subst "x" repl exp4) = print (Unop (Negate, repl)))
  	  repl_list
  	in 
  	let truth_list6 = 
  	  List.map (fun repl ->
  	  			 print (subst "y" repl exp4) = print (Unop (Negate, repl)))
  	  repl_list
  	in 
  	assert (List.mem false truth_list4 = false) ;
  	assert (List.mem false truth_list5 = false) ;
  	assert (List.mem false truth_list6 = true) ;
  	let exp5 = Binop (Plus, Num 4, Var "x") in 
  	let truth_list7 = 
  	  List.map (fun repl ->
  	  			 print (subst "x" repl exp5) =
  	  			 print (Binop (Plus, Num 4, repl))) repl_list
  	in 
  	assert (List.mem false truth_list7 = false) ;
  	let exp6 = Conditional (Binop (Equals, Var "x", Num 5), Var "y",
  				Var "x")
  	in 
  	let truth_list8 = 
  	  List.map (fun repl ->
  	  			 print (subst "x" repl exp6) =
  	  			 print (Conditional 
  	  			 	   (Binop (Equals, repl, Num 5), Var "y", repl))) repl_list
  	in 
  	assert (List.mem false truth_list8 = false) ;
  	let exp7 = Fun ("y", Binop (Plus, Var "x", Num 4)) in 
  	let exp8 = Fun ("x", Binop (Plus, Var "x", Num 4)) in 
  	let truth_list9 =
  	  List.map (fun repl ->
  	  			 print (subst "y" repl exp7) = print exp7) repl_list
    in 
    let truth_list10 =
  	  List.map (fun repl ->
  	  			 print (subst "x" repl exp7) =
  	  			 print (Fun ("y", Binop(Plus, repl, Num 4)))) repl_list
    in 
    assert (List.mem false truth_list9 = false) ;
    assert (List.mem false truth_list10 = false) ;
    let exp9 = Let("x", Num 4, Binop (Times, Var "x", Num 5)) in 
    let exp10 = Let("x", Binop (Plus, Var "x", Num 2), Var "x") in 
    let exp11 = Let("y", Binop (Plus, Var "y", Var "a"), Var "a") in 
    let truth_list11 = 
    	List.map (fun repl ->
  	  			 print (subst "x" repl exp9) = print exp9) repl_list
	in 
	let truth_list12 = 
    	List.map (fun repl ->
  	  			 print (subst "x" repl exp10) =
  	  			 print (Let ("x", Binop (Plus, repl, Num 2), Var "x")))
    	repl_list
	in 
	let truth_list13 = 
    	List.map (fun repl ->
  	  			 print (subst "a" repl exp11) =
  	  			 print (Let ("y", Binop (Plus, Var "y", repl), repl)))
    	repl_list
	in 
	assert (List.mem false truth_list11 = false) ;
	assert (List.mem false truth_list12 = false) ;
	assert (List.mem false truth_list13 = false) ;
	let exp12 = Letrec("x", Num 4, Binop (Times, Var "x", Num 5)) in 
    let exp13 = Letrec("x", Binop (Plus, Var "x", Num 2), Var "x") in 
    let exp14 = Letrec("y", Binop (Plus, Var "y", Var "a"), Var "a") in 
    let truth_list14 = 
    	List.map (fun repl ->
  	  			 print (subst "x" repl exp12) = print exp12) repl_list
	in 
	let truth_list15 = 
    	List.map (fun repl ->
  	  			 print (subst "x" repl exp13) =
  	  			 print (Letrec ("x", Binop (Plus, repl, Num 2), Var "x")))
    	repl_list
	in 
	let truth_list16 = 
    	List.map (fun repl ->
  	  			 print (subst "a" repl exp14) =
  	  			 print (Letrec ("y", Binop (Plus, Var "y", repl), repl)))
    	repl_list
	in 
	assert (List.mem false truth_list14 = false) ;
	assert (List.mem false truth_list15 = false) ;
	assert (List.mem false truth_list16 = false) ;
	let exp15 = App (Fun ("x", Binop (Times, Var "x", Num 2)), Num 10) in 
	let exp16 = App (Var "x", Num 3) in
	let truth_list17 = 
		List.map (fun repl ->
		            print (subst "x" repl exp15) = print exp15) repl_list
	in
	let truth_list18 = 
		List.map (fun repl ->
		            print (subst "x" repl exp16) = print (App (repl, Num 3)))
		repl_list
	in 	
	assert (List.mem false truth_list17 = false) ;
	assert (List.mem false truth_list18 = false) ;
	let exp_list = [Num 10; Bool true; Raise; Unassigned] in 
	let truth_list19 = 
		List.concat ((List.map (fun repl -> 
								List.map (fun exp ->
								   			print (subst "x" repl exp) =
								   			print exp) exp_list)) repl_list)
	in 
	assert (List.mem false truth_list19 = false) ;;

let test_exp_to_string () = 
	let exp1 = Var "x" in 
	assert (exp_to_string exp1 = "x") ;
	let exp2 = Num 3 in 
	assert (exp_to_string exp2 = "3") ;
	let exp3 = Bool true in 
	assert (exp_to_string exp3 = "true") ;
	let exp4 = Bool false in 
	assert (exp_to_string exp4 = "false") ;
	let exp5 = Unop (Negate, Num 3) in 
	assert (exp_to_string exp5 = "~- 3") ;
	let exp6 = Binop (Plus, Var "x", Num 10) in 
	assert (exp_to_string exp6 = "x + 10") ;
	let exp7 = Binop (Minus, Unop (Negate, Num 3), Num 10) in 
	assert (exp_to_string exp7 = "~- 3 - 10") ;
	let exp8 = Binop (Times, Var "x", Num 10) in 
	assert (exp_to_string exp8 = "x * 10") ;
	let exp9 = Binop (Equals, Var "x", Num 10) in 
	assert (exp_to_string exp9 = "x = 10") ;
	let exp10 = Binop (LessThan, Var "x", Num 10) in 
	assert (exp_to_string exp10 = "x < 10") ;
	let exp11 = Conditional (Binop (Equals, Var "x", Num 0), Let ("x", Num 1,
				Var "x"), Var "x") in 
	assert (exp_to_string exp11 = "if x = 0 then let x = 1 in x else x") ; 
	let exp12 = Fun ("x", Binop (Plus, Var "x", Num 1)) in 
	assert (exp_to_string exp12 = "fun x -> x + 1") ;
	let exp13 = Let ("x", Num 2, Var "x") in 
	assert (exp_to_string exp13 = "let x = 2 in x") ;
	let exp14 = Letrec ("f", Fun ("x", Binop (Plus, Var "x", Num 10)),
				App (Var "f", Num 2)) in 
	assert (exp_to_string exp14 = "let rec f = fun x -> x + 10 in (f) (2)") ;
	let exp15 = Raise in 
	assert (exp_to_string exp15 = "raise") ; 
	let exp16 = Unassigned in 
	assert (exp_to_string exp16 = "Unassigned") ;;

(*run tests*)
let _ =  
	test_exp_to_abstract_string ();
	test_free_vars ();
	test_subst () ;
	test_exp_to_string () ;;
	(*test_eval_s () ;;*)

Printf.printf "All tests passed!"





