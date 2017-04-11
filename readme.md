

# Fouine 
## syntaxe: 
- opérateurs mathématiques simples : `+,-, /, *, =, <>, <, >, <=, >=, and, or, not`. 
   - Les opérateurs `+,-, /, *` sont de type `int -> int-> int`. 
   - `and, or, not` sont de type `bool-> bool-> bool` et `bool->bool` 
   - `=, <>, <, >, <=, >=` sont de type `'a->'a->int` 
- structure de controle: `if condition then foo else bar`. `foo` et `bar` doivent avoir le même type
- fonctions: `fun a-> fun b -> expr` est une fonction anonyme à deux arguments `a` et `b` évaluant l'expression `expr`
- Affectation et variables:
     - `let ident = exp  in expression` est un programme affectant `expr` à l'identifiant `ident` lors de l'exécution de expression. `let ident a b c = expr in expression` est un raccourci pour l'expression `let ident = fun a-> fun b-> fun c->expr in expression`.Les expressions de la forme `let ident = expr` sont uniquement autorisé dans le toplevel
     - `let rec ident = expr` in expression se comporte comme un `let ident = expr` à une exception près : `expr` est assigné à l'identifiant `ident` dès qu'il est vu. Cela permet de définir des fonctions récursives 
- References: les réferences à des valeurs de tous les 


repl compile -> pas de sauvegarde d'envirronment car n'a pas vraiment de sens
