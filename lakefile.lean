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

meta if get_config? env = some "dev" then
require "leanprover" / "doc-gen4"
