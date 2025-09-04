import Lake
open Lake DSL

package «automate-polynomial» where
  -- add package configuration options here

require "leanprover-community" / "mathlib" @ "git#79e94a093aff4a60fb1b1f92d9681e407124c2ca"

lean_lib «AutomatePolynomial» where
  -- add library configuration options here

@[default_target]
lean_exe «automate-polynomial» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

require "PatrickMassot" / "checkdecls"
require "leanprover" / "doc-gen4" @ "git#58b48e75bd19f785927e06912dea610e5e48f1fa"
