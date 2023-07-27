import Lean

macro "corollary" name:ident args:bracketedBinder* ":" t:term ":=" body:term : command =>
  `(theorem $name $args* : $t := $body )
