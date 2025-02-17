import Lake
open Lake DSL

package «llean» where
  -- add package configuration options here

lean_lib «Llean» where
  -- add library configuration options here

@[default_target]
lean_exe «llean» where
  root := `Main

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"
