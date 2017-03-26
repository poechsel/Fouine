https://esumii.github.io/min-caml/


Quand on tombe sur un let g = expr, on commence par parcourir expr (durant ce parcours, toutes references vers g va referer vers le dertnier g ajouté dans l'environement), puis on ajoute ce g a l'environement
Si on tombe sur un let rec g, on fait pareil MAIS en ajoutant g d'abord
