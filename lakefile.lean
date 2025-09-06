import Lake
open Lake DSL

package «lambdacube» where
  -- add package configuration options here

lean_lib «LambdaCube» where
  -- add library configuration options here

@[default_target]
lean_exe «lambdacube» where
  root := `Main

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"
