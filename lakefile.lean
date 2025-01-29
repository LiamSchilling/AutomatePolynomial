import Lake
open Lake DSL

package «automate-polynomial» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «AutomatePolynomial» where
  -- add library configuration options here

@[default_target]
lean_exe «automate-polynomial» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
