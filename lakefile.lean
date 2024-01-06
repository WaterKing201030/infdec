import Lake
open Lake DSL

package «infdec» {
  -- add package configuration options here
}

lean_lib «Infdec» {
  -- add library configuration options here
}

@[default_target]
lean_exe «infdec» {
  root := `Main
}
