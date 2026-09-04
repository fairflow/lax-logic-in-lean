import Lake
open Lake DSL

require VersoBlueprint from git
  "https://github.com/leanprover/verso-blueprint"@"v4.31.0"

package LaxBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib LaxBlueprint where
