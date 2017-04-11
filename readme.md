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
- ouverture de fichier: la commande `open "fichier"` ouvre le fichier `fichier`. Si il n'existe pas, ou si il contient une erreur de parsing, le code chargé sera `()`
- les `;;` à la fin d'une expression sont requis


##options:
l'éxecutable Fouine dispose de 5 options:
- debug, pour afficher le pretty print d'un fichier / commande, et d'autres informations complémentaires lorsque l'on est en mode compilateur
- machine, pour passer en mode compilateur
- coloration, pour activer la coloration syntaxique dans les erreurs / le pretty print
- inference pour activer l'inférence de types
- interm pour sauvegarder le programme compilé dans un fichier

Sans nom de fichier, fouine passera en mode repl. Sinon il executera le contenu du fichier selon le mode choisi (par défaut, en mode interpreteur)


repl compile -> pas de sauvegarde d'envirronment car n'a pas vraiment de sens


##Architecture:
- inference.ml contient les fonctions responsables de l'inferences
- prettyprint.ml le print d'ast fouine
- main.ml la repl et les fonctions de chargement de fichiers
- interpret.ml l'interpretation
- compil.ml la compilation d'ast vers 'bytecode'
- secd.ml la machine à pile
- expr.ml les types principaux de l'ast et quelques fonctions de manipulations
- env.ml, errors.ml et binop.ml sont des fichiers contenant des fonctions utilitaires
- le parser et le lexer se trouvent dans parser.mly et lexer.mll respectivement


##Repartition des taches:
- Pierre
    - interpreteur
    - parseur / lexer
    - inference de types
    - main.ml (parsing des arguments, chargement de fichiers, repl...)
    - prettyprinting
- Guillaume
    - compilation de l'ast vers du 'bytecode'
    - machine secd
    - ebauche de machine zinc



##Implementation:
- L'interpretation se base lourdement sur les continuations: cela permet de faire aisément les exceptions, et puis au moins j'ai pu découvrir un truc
- L'inférence de type à été ajouté pour 3 raisons principales, malgré le fait que cela ne soit pas demandé:
    - Cela permet de faire une prépass unifié pour détecter les erreurs, commune à l'interpretation et à la compilation
    - Je n'avais jamais fait d'inférence et j'ai voulu apprendre à en faire
    - le but finale est de faire du nbe, mais celui-ci à besoin de connaitre le type de l'expression attendue pour fonctionner. L'inférence de type est donc une premiére étape vers le nbe
