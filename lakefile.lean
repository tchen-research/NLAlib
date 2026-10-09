import Lake
open Lake DSL

/-- NLAlib: a Lean 4 / Mathlib library of the foundations of randomized numerical linear algebra. -/
package «NLAlib» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

/-- Matrix concentration inequalities, Tropp 2015 Ch. 3–8. Kept under its original module
and namespace so existing citations keep resolving; re-exported by `NLAlib.Concentration.Matrix`. -/
lean_lib «TroppMatrixConcentration» where

@[default_target]
lean_lib «NLAlib» where
