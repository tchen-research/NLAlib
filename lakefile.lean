import Lake
open Lake DSL

/-- NLAlib: a Lean 4 / Mathlib library of the foundations of randomized numerical linear algebra. -/
package «NLAlib» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib «NLAlib» where
