import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

package «NagataFactoriality» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «NagataFactoriality» where
