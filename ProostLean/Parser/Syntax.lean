declare_syntax_cat proost_level

syntax num : proost_level
syntax ident : proost_level
syntax proost_level "+" num : proost_level
syntax "max" proost_level (proost_level)+ : proost_level
syntax "imax" proost_level (proost_level)+ : proost_level


declare_syntax_cat constant
syntax ident (".{" (proost_level)+ "}")? : constant

declare_syntax_cat proost
syntax constant : proost
syntax "(" proost ")" : proost
syntax "(" proost ":" proost ")" : proost
syntax "fun" (ident* (":" proost)?),* "=>" proost : proost 
syntax "(" ident* ":" proost ")" "->" proost : proost
syntax proost "->" proost : proost
syntax proost proost : proost
syntax "Prop" : proost
syntax "Type" proost_level : proost
syntax "Sort" proost_level : proost