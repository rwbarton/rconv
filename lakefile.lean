import Lake
open Lake DSL

package rconv {
  -- add package configuration options here
}

lean_lib Rconv {
  -- add library configuration options here
}

@[default_target]
lean_exe rconv {
  root := `Main
}
