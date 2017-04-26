type 'a fix = Buildins_Fix of ('a fix -> 'a);;
let buildins_y t = let p (Buildins_Fix f) x = t (f (Buildins_Fix f)) x in p (Buildins_Fix p);;

let buildins_y_noinference t = let p f x = t (f f) x in p p;;
