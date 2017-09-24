          ___           ___           ___                       ___           ___     
         /\  \         /\  \         /\__\          ___        /\__\         /\  \    
        /::\  \       /::\  \       /:/  /         /\  \      /::|  |       /::\  \   
       /:/\:\  \     /:/\:\  \     /:/  /          \:\  \    /:|:|  |      /:/\:\  \  
      /::\~\:\  \   /:/  \:\  \   /:/  /  ___      /::\__\  /:/|:|  |__   /::\~\:\  \ 
     /:/\:\ \:\__\ /:/__/ \:\__\ /:/__/  /\__\  __/:/\/__/ /:/ |:| /\__\ /:/\:\ \:\__\
     \/__\:\ \/__/ \:\  \ /:/  / \:\  \ /:/  / /\/:/  /    \/__|:|/:/  / \:\~\:\ \/__/
          \:\__\    \:\  /:/  /   \:\  /:/  /  \::/__/         |:/:/  /   \:\ \:\__\  
           \/__/     \:\/:/  /     \:\/:/  /    \:\__\         |::/  /     \:\ \/__/  
                      \::/  /       \::/  /      \/__/         /:/  /       \:\__\    
                       \/__/         \/__/                     \/__/         \/__/    




## Compile:
Make sure ocamlbuild is installed. Then just type `make`

## How to use:
By default `./fouine` is an interpretor.
To use it type `./fouine`. Several options are available:
- `-debug` to pretty print the instructions after they are inputted, or complementary informations when compiling.
- `-nocoloration` to deactivate the syntax coloration. It is activated by default.
- `-noinference` to deactivate type inference (activated by default)
- `-interm FILE` to save the compiled code in the file `FILE`
- `-o FILE` to save transformed code in a file
- `-R` to activate the transformation suppressing references
- `-E` to activate the cps transformation (expressions are made by continuations)
- `ER` to activate both transformations
- `-nobuildins` to deactivate the buildins
- `-noinference` to deactivate the inference
- `-machine (Z|S|J)` if you want to compile your fouine file. `Z|S|J` determines for which machine it will be compiled.
    It is important to note that the different machines don't support pattern matching and constructors !
    - `Z` is a ZINC machine
    - `S` is a secd machine
    - `J` is a joint interpretation / secd machine. It will interpret the program until "pure" expressions (only made of arithmetical expressions) is found. It then switch to a secd machine for this expression.
- a file can be passed to `./fouine`. In that case, this file will be executed. Otherwise `./fouine` will be launched under the repl mode


The script `test.sh` will test Fouine with the files found in the folder `tests/`

## Syntax: 

The syntax - and the functionnalities - are similar with Caml. Here is a summary:

- Basic mathematical operators : `+,-, /, *, =, <>, <, >, <=, >=, and, or, not`. 
   - Operators `+,-, /, *` have types `int -> int-> int`. 
   - `and, or, not` have types `bool-> bool-> bool` and `bool->bool` 
   - `=, <>, <, >, <=, >=` have types `'a->'a->int` 
   Depending on how the interpreter / compiler is launch, these operators are either buildins or not. With the option `-nobuildins`, or if it is compiled for a `ZINC` machine, then they aren't buildins. Otherwise they are : we can therefore change their behaviour by redefining `+`, `*`, ...
- Branching: `if condition then foo else bar`. `foo` and `bar` must have the same type. Expressions like `if cond then expr` works only if `expr` is of type `unit`
- Functions: `fun a-> fun b -> expr` is a two variables anonymous fonction
- Affectation and variables:
     - `let ident = exp  in expression` will affect to the identifier `ident` the value `expr`. `let ident a b c = expr in expression` is a shortcut for `let ident = fun a-> fun b-> fun c->expr in expression`. Expressions of the form `let ident = expr` are only accepted on the top level.
     - `let rec ident = expr` will behave almost identically as `let ident = expr`: `expr` is assigned to `ident`, but `ident` can be present in `expr`, thus allowing recursive functions.
- References. References are almost likes pointer. They are mutable. We can access to the value of a reference with the operator `!`, and modify the value of a reference with `:=` (type `ref 'a -> 'a -> unit`).

    ```ocaml
    let a = ref 6 in
    let _ = a := 8 in
    !a (* <- it is 8 *)
    ```

- Underscore (`_`). It matches everything. These instructions are valid:
    - `let _ = expr`
    - `let f x _ = x in f `
- Exceptions: 
    - An exception can be emitted with the instruction `raise n` where n is an integer.
    - An exception can be caught with a bloc of the form `try foo with E x -> bar`. If `x` is a constant, then `bar` is executed only if `foo` raised an exception having `x` has value. Otherwise, `bar` is executed if `foo` raised an exception
- array: integer fixed-length arrays can be created with the syntax `makeArray n` where `n` is the length. An element can be accessed with the syntax `array.(index)`, and affected with `array.(index) <- value`
- prInt: `prInt expr` will print `expr` and return the value `expr`. It has type `int -> int`
- Files. The command `open "file"` will open a fouine file and will load its code as a module (functions declared in this file will be accessible with the syntax `file.function`. If the file doesn't exists, or if it contains a parsing error, the loaded code will be `()`. Beware: paths are relatives to the interpreter files 
- Tuples: `(a, b, c)` will create a three dimensionnal tuple. You can match on the elements: `let x, y = 1, 2`
- Types and constructors
    - Declarations are like in Caml with the syntax: 
`type ('a, ..., 'b) type_name = | Constr1 of (type_arguments1) .... | Constrn of (type_argumentsn)`
    - Types are recursives: `let 'a test = None of 'a test`
    - Constructors aren't force to have arguments
- Pattern matching: expression like `let 0, (), (x, _), Constr y = ....` or `fun (x, Constr (a, b)) -> ...` are valid. You can explicitely match a value with the syntax `match expr with | pattern_1 -> expr1 | ... -> ... | pattern_n -> exprn`. If `expr` matches with `patterni`, then `expri` will be executed 
- `;;` are required at the end of an expression
- We can redefined a number of operators (infix or prefix). The syntax is the same than in caml: `let (@@) a b = ....`
- List: An empty list can be build with `[]`, two list can be concatenated with `@` and an element can be inserted to the front with `::`. They are compatible with pattern matching (their definition is simply `type 'a list = None | Elem of ('a * 'a list)`). They are not working with compilation.
- modules. A module can be defined as follow: `module Test : sig ... end = struct .. end;;`. Signatures can be also provided
 `module type TestSig = sig type t;; type t2 = int;; val f : int -> int -> int end;;
 module Test : TestSig = struct type t = int;; let f a b = a + b;; end;;`
 It is important to note that signatures only checks for the presence of the elements. They are not as powerfull as in OCaml.
- Type constraints. Type constraints are working if no `ref` are presents.
`let f x : int = x;; int -> int`
`let f (x : bool) = x;; bool -> bool`
`((fun x -> x) : int -> int)`
- Base types: `'a -> 'b`, `'a ref`, `int array`, `int`, `bool`


The constructors of our types have only an argument which is a tuple. From there, certains expressions which are not working in Caml are working in Fouine:

```ocaml
>>> type 'a ok = Machin of 'a;;
>>> let a = Machin 3;;
val a : int ok = Machin (3)
>>> let Machin b = a;;
val b : int = 3
```

## Code transformations
Two types transformations can be applied.
The first one will remove the references and simulate them using an array (transformation R)
The second one do a cps transformation of the code (transformation E). Recursive functions are transformed using an Y-combinator.
The two transformations can be applied at the same time (transformation ER). Typing errors can then appear because our fouine langage is converted into a subset of fouine very similar to lambda calculus. Therefore our typing system isn't powerfull enough to type these expressions. (but the same problem arise in Caml)



## Architecture:
- `inference.ml`: type inference
- `buildins.ml`: buildins functions definition (apport from basic mathematical operators)
- `inference_old.ml`: old type inference. Kept for archeleogical purposes
- `transformations.ml`: code transformations
- `prettyprint.ml`: fouine pretty printer
- `binop.ml`: binary operators functions
- `shared.ml`: buildins declarations and variables environments
- `types.ml`: type definitions and utilities around types
- `commons.ml`: file containing elements usefull everywhere in the code
- `errors.ml`: errors les erreurs
- `file.ml`: everything to deal with files
- `main.ml`: repl, main and loading files
- `interpret.ml`: interpreter
- `compilB.ml`: fouine to SECD machine bytecode compilation
- `secdB.ml`: to execute SECD bytecode
- `utils.ml`: display, debug and utilities functions for the SECD simulator
- `bruijn.ml`: De bruijn indices
- `dream.ml`: environment used for the secd and the bruijn indices
- `expr.ml`: declaration of the types used to define our ast
-  `parser.mly`, `lexer.mll`: parsing and lexing
- `bruijnZ.ml`, `compilZ.ml`, `secdZ.ml`: de bruijn indices, compilation and simulation for a ZINC machine
- `jit.ml`: mixed machine


