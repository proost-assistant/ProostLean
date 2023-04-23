structure CallOptions where
  debug : List String
  --todo add_more options (example : naive reduction vs nbe)

instance : Inhabited CallOptions where
  default := {debug := []}