import Lake
open Lake DSL

package proostLean {
  -- add package configuration options here
}

lean_lib ProostLean {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe proostLean {
  root := `Main
}
