open Evaluation
open Expr

let assert_raises f = 
		assert 
		(try
			f (); 
			false
		with
		| _ -> true) ;;

let test eval_method (is_eval_l : bool) = 
	let env = Env.create () in 
	let eval exp = eval_method exp env in 
	let exp1 = Num 2 in 
	assert (eval exp1 = Env.Val exp1) ;
	let exp2 = Bool true in 
	assert (eval exp2 = Val exp2) ;
	let exp3 = Var "x" in  
	assert_raises (fun () -> eval exp3) ;
	let exp4 = Raise in
	let exp5 = Unassigned in 
	assert_raises (fun () -> eval exp4) ;
	assert_raises (fun () -> eval exp5) ;
	let exp6 = Fun ("x", Binop (Plus, Var "x", Num 1)) in 
	assert (eval exp6 = Closure (exp6, env) || eval exp6 = Val exp6 );
	let exp7 = Unop (Negate, Num 10) in 
	assert (eval exp7 = Val (Num (-10))) ;
	let exp8 = Unop (Negate, Num (-1)) in 
	assert (eval exp8 = Val (Num 1)) ;
	let exp9 = Unop (Negate, Var "x") in 
	assert_raises (fun () -> eval exp9) ;
	let exp10 = Unop (Negate, Bool true) in 
	assert_raises (fun () -> eval exp10) ;
	let exp11 = Unop (Negate, Fun ("x", Unop (Negate, Var "x"))) in 
	assert_raises (fun () -> eval exp11) ;
	let exp12 = Unop (Negate, App (Fun ("x", Unop (Negate, Var "x")),
				Num 1)) in 
	assert (eval exp12 = Val (Num 1)) ;
	let exp13 = Binop (Plus, Num 10, Num 10) in 
	assert (eval exp13 = Val (Num 20)) ;
	let exp14 = Binop (Plus, Num 10, Fun ("x", Binop (Plus, Var "x",
				Num 10))) in 
	assert_raises (fun () -> eval exp14) ;
	let exp15 = Binop (Plus, Num 10, App (Fun ("x", Binop (Plus, Var "x",
			    Num 10)), Num 10)) in 
	assert (eval exp15 = Val (Num 30)) ;
	let exp16 = Binop (Plus, Num 10, Let ("x", Num 5, Var "x")) in 
	assert (eval exp16 = Val (Num 15)) ;
	let exp17 = Binop (Plus, Num 10, Let ("x", Num 5, Var "y")) in 
	assert_raises (fun () -> eval exp17) ;
	let exp18 = Binop (Minus, Num 3, Num 2) in 
	assert (eval exp18 = Val (Num 1)) ;
	let exp19 = Binop (Minus, Num 10, Fun ("x", Binop (Plus, Var "x",
				Num 10)))
	in 
	assert_raises (fun () -> eval exp19) ;
	let exp20 = Binop (Minus, Num 5, App (Fun ("x", Binop (Plus, Var "x",
				Num 10)), Num 10))
	in 
	assert (eval exp20 = Val (Num (-15))) ;
	let exp21 = Binop (Minus, Num 10, Let ("x", Num 5, Var "x")) in 
	assert (eval exp21 = Val (Num 5)) ;
	let exp22 = Binop (Minus, Num 10, Let ("x", Num 5, Var "y")) in 
	assert_raises (fun () -> eval exp22) ;
	let exp23 = Binop (Times, Num 10, Num 10) in 
	assert (eval exp23 = Val (Num 100)) ;
	let exp24 = Binop (Times, Num 10, Fun ("x", Binop (Plus, Var "x", 
				Num 10)))
	in 
	assert_raises (fun () -> eval exp24) ;
	let exp25 = Binop (Equals, Num 10, Num 10) in 
	assert (eval exp25 = Val (Bool true)) ;
	let exp26 = Binop (Equals, Num 10, Num 20) in 
	assert (eval exp26 = Val (Bool false)) ;
	let exp27 = Binop (Equals, Num 10, Var "x") in 
	assert_raises (fun () -> eval exp27) ;
	let exp28 = Binop (LessThan, Num 10, Num 20) in 
	assert (eval exp28 = Val (Bool true)) ;
	let exp29 = Binop (LessThan, Num 10, Num 5) in
	assert (eval exp29 = Val (Bool false)) ; 
	let exp30 = Binop (LessThan, Var "x", Bool true) in
	assert_raises (fun () -> eval exp30) ;
	let exp31 = Conditional (Bool true, App (Fun ("x", Var "x"), Num 1),
				Num 0)
	in 
	assert (eval exp31 = Val (Num 1)) ;
	let exp32 = Conditional (Bool false, Num 1, Num 0) in 
	assert (eval exp32 = Val (Num 0)) ;
	let exp33 = Conditional (Num 10, Num 1, Num 0) in 
	assert_raises (fun () -> eval exp33) ;
	let exp34 = Let ("x", Num 10, Var "x") in 
	assert (eval exp34 = Val (Num 10)) ;
	let exp35 = Let ("x", Fun ("y", Binop (Plus, Var "y", Num 6)),
				App (Var "x", Num 5))
	in 
	assert (eval exp35 = Val (Num 11)) ; 
	let exp36 = Let ("x", Num 0, Var "y") in 
	assert_raises (fun () -> eval exp36) ;
	let exp37 = Let ("x", Bool true, Var "x") in 
	assert (eval exp37 = Val (Bool true)) ;
	let exp38 = Letrec ("f", Fun ("x", Conditional (Binop (Equals, Var "x",
				Num 0), Num 1, Binop (Times, Var "x", App (Var "f", Binop
				(Minus, Var "x", Num 1))))), App (Var "f",
				Num 4))
	in 
	assert (eval exp38 = Val (Num 24)) ;
	let exp39 = App (Fun ("x", Binop (Plus, Var "x", Num 1)), Num 1) in 
	assert (eval exp39 = Val (Num 2)) ;
	let exp40 = App (Var "x", Num 1) in 
	assert_raises (fun () -> eval exp40) ;
	let exp41 = App (Fun ("x", Conditional (Var "x", Num 1, Num 0)), Bool true) in 
	assert (eval exp41 = Val (Num 1)) ;;

let test_eval_s () = 
	test eval_s false ;;			
	
let test_eval_d () = 
	test eval_d false ;
	let exp1 = Var "x" in 
	let env1 = Env.extend (Env.create ()) "x" (ref (Env.Val (Num 10))) in 
	assert (eval_d exp1 env1 = Val (Num 10)) ;;

let test_eval_l () = 
	test eval_l true ;;

let test_env () = 
	let test_extend () = 
		let e1 = Env.create () in 
		let ext1 = Env.extend e1 "x" (ref (Env.Val (Num 0))) in 
		assert (Env.env_to_string ext1 = "[(x, ref (Val (Num(0))))]") ;
		let ext2 = Env.extend ext1 "y" (ref (Env.Val (Num 1))) in 
		assert (Env.env_to_string ext2 =
				"[(y, ref (Val (Num(1)))); (x, ref (Val (Num(0))))]") ;
		let ext3 = Env.extend ext2 "x" (ref (Env.Val (Num 2))) in 
		assert (Env.env_to_string ext3 = 
				"[(x, ref (Val (Num(2)))); (y, ref (Val (Num(1))))]") 
	in
	let test_close () = 
		let exp1 = Num 0 in 
		let env1 = Env.create () in 
		assert (Env.close exp1 env1 = Env.Closure (exp1, env1)) ;
		let env2 = Env.extend env1 "x" (ref (Env.Val (Num 10))) in 
		assert (Env.close exp1 env2 = Env.Closure (exp1, env2))
	in 
	let test_lookup () = 
		let e1 = Env.create () in
		assert_raises (fun () -> Env.lookup e1 "x") ;
		let e2 = Env.extend e1 "x" (ref (Env.Val (Num 0))) in 
		assert (Env.value_to_string (Env.lookup e2 "x") = 
				"Val (Num(0))") ;
		let e3 = Env.extend e2 "y" (ref (Env.Val (Binop (Plus, Var "x", Num 2)))) in 
		assert (Env.value_to_string (Env.lookup e3 "y") = 
				"Val (Binop(+, Var(x), Num(2)))")
	in
	let test_env_to_string () = 
		let to_string = Env.env_to_string in
		let e1 = Env.create () in 
		assert (to_string e1 = "[]") ;
		let e2 = Env.extend e1 "x" (ref (Env.Val (Num 0))) in 
		assert (to_string e2 = "[(x, ref (Val (Num(0))))]") ;
		let e3 = Env.extend e2 "y" (ref (Env.Val (Unop (Negate, Num 10)))) in 
		assert (to_string e3 = 
				"[(y, ref (Val (Unop(~-, Num(10))))); (x, ref (Val (Num(0))))]")
	in
	let test_value_to_string () = 
		let to_string_true = Env.value_to_string ~printenvp:true in 
		let to_string_false = Env.value_to_string ~printenvp:false in 
		let v1 = Env.Val (Num 0) in 
		assert (to_string_true v1 = "Val (Num(0))") ;
		assert (to_string_false v1 = "Val (Num(0))") ;
		let v2 = Env.Val (Binop (Plus, Num 1, Num 2)) in 
		assert (to_string_true v2 = "Val (Binop(+, Num(1), Num(2)))") ;
		assert (to_string_false v2 = "Val (Binop(+, Num(1), Num(2)))") ;
		let e1 = Env.create () in
		let v3 = Env.Closure ((Num 0), e1) in 
		assert (to_string_true v3 = "Closure (Num(0), [])") ;
		assert (to_string_false v3 = "Closure (Num(0))") ;
		let e2 = Env.extend e1 "x" (ref (Env.Val (Num 0))) in 
		let v4 = Env.Closure ((Num 1), e2) in 
		assert (to_string_true v4 = "Closure (Num(1), [(x, ref (Val (Num(0))))])") ;
		assert (to_string_false v4 = "Closure (Num(1))") 
	in
	test_close () ;
	test_extend () ;
	test_lookup () ;
	test_env_to_string () ;
	test_value_to_string () ;;

(*run tests*)
let _ = 
	test_eval_s () ;
	test_eval_d () ;
	test_eval_l () ;
	test_env () ;;


Printf.printf "All tests passed!"