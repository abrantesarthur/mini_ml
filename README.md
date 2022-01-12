
Mini ML
============

This is Mini ML, a small, turing-complete, functional programming language built for Harvard's [CS51]

Instructions
------------

1. Install OCamlbuild compiler with `brew install ocaml`
2. Install Opam, the Ocaml package manager with `brew install opam`

Make Targets
------------

Run `make build` to compile the project

Run `make run` to run the project

Now, you can play around writing expressions accepted by our grammar so the interpreter can evaluate them. For example, try writing `let f = fun x -> x + 2 in f f 3 ;;`. Can you guess what the result should be? Play around :)

Source files
------------

| File                | Description                      |
| ------------------- | -------------------------------- |
| `evaluatiaon.ml`    | Expression evaluator             |
| `miniml.ml`         | Reads strings and evaluates them |
| `mini_lex.mll`      | A lexical analyzer for MiniML    |
| `miniml_parse.mly`  | A parser for MiniML              |



[CS51]: https://cs51.io/