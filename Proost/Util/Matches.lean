syntax term ".matches" ("|" term)+ : term

macro_rules 
  | `($te:term .matches | $pat) => 
    `(if let $pat := $te then true else false) 
  | `($te:term .matches | $pat $[| $rest]*) => 
    `(if let $pat := $te then true else $te .matches $[| $rest]*) 
