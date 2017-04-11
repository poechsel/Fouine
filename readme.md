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
## syntaxe: 
- opérateurs mathématiques simples : `+,-, /, *, =, <>, <, >, <=, >=, and, or, not`. 
   - Les opérateurs `+,-, /, *` sont de type `int -> int-> int`. 
   - `and, or, not` sont de type `bool-> bool-> bool` et `bool->bool` 
   - `=, <>, <, >, <=, >=` sont de type `'a->'a->int` 
- structure de controle: `if condition then foo else bar`. `foo` et `bar` doivent avoir le même type. Les expressions du type `if cond then expr` fonctionnent également, mais `expr` doit être de type `unit`
- fonctions: `fun a-> fun b -> expr` est une fonction anonyme à deux arguments `a` et `b` évaluant l'expression `expr`
- Affectation et variables:
     - `let ident = exp  in expression` est un programme affectant `expr` à l'identifiant `ident` lors de l'exécution de expression. `let ident a b c = expr in expression` est un raccourci pour l'expression `let ident = fun a-> fun b-> fun c->expr in expression`.Les expressions de la forme `let ident = expr` sont uniquement autorisé dans le toplevel
     - `let rec ident = expr` in expression se comporte comme un `let ident = expr` à une exception près : `expr` est assigné à l'identifiant `ident` dès qu'il est vu. Cela permet de définir des fonctions récursives 
- References: les réferences à des valeurs de tous les types. On peut déferencer une valeur avec `!`, en créer une avec `ref`, et changer la valeur d'une avec `:=` (type `ref 'a -> 'a -> unit'`)
- Underscore (`_`): le underscore est implementée. Il s'agit d'un identifiant joker pouvant avoir n'importe quel valeur. Exemples: 
    - `let _ = expr`
    - `let f x _ = x in f `
- exceptions: 
    - on peut raise une exception avec `raise n` ou n est un entier
    - On peut recuperer des exceptions avec un bloc du type `try foo with E x -> bar`. Si `x` est une constante, `bar` est executé uniquement si `foo` léve une exception de numéro égale à la constante, sinon l'exception continue son chemin. Si `x` est un identifiant, `bar` est executé dés que `foo` lève une exception.
- array: On support les array d'entiers
- prInt: comme dans la spec


repl compile -> pas de sauvegarde d'envirronment car n'a pas vraiment de sens
