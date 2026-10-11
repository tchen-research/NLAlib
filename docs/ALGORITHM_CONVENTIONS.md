# Algorithms in NLAlib: factorizations, recursions, realisation theorems

Companion to `docs/KRYLOV_DEFINITIONS.md`. Scope: exact arithmetic only. Finite-precision
(rounding, backward stability) statements are **on hold** until their design is agreed; do not
introduce perturbed-relation hypotheses or rounding models.

## 1. The object is the factorization, the algorithm is a witness

Every classical algorithm is stated as three declarations:

1. **The factorization predicate** (what the output *is*): `IsLU A L U`, `IsPLU A P L U`,
   `IsCholesky A L`, `IsQR A Q R` (thin: `Q : Matrix m (Fin n) ℝ`, `HasOrthonormalCols Q`, `R` upper
   triangular), `IsFullQR`, `IsHessenbergForm A Q H`. These live in `NLAlib/Matrix/Factorizations/`
   (layer 0) with existence, uniqueness and the identities consumers use (`Qᵀ A = R`, `A⁺ = R⁻¹Qᵀ`).
2. **The algorithm as a total recursion** over an ordered index: `lu`, `cholesky`, `gramSchmidt`,
   `householderQR`, `cgRecurrence`, `lanczosRecurrence`. Total because Lean has `x / 0 = 0` and
   `√(negative) = 0`: a bad pivot produces junk, never an error. Recursions are over `Fin n`
   (leading pivot = `Fin.succ`/`Matrix.fromBlocks` splitting or `Fin.cons`); statements for a general
   `Fintype` index are obtained by `reindex` lemmas.
3. **The success predicate and the realisation theorem**: `CholeskySucceeds A : Prop` (every pivot
   positive along the recursion), `choleskySucceeds_iff_posDef`, `isCholesky_cholesky (h : CholeskySucceeds A)`.
   Consumers cite the predicate (`IsCholesky`), never the recursion. Breakdown theorems
   ("fails iff …") are exact-arithmetic statements and belong here.

Krylov methods follow the same shape with the predicate first (`IsCGIterate`, `LanczosDecomp`):
the recurrence (`cgRecurrence`, three-term Lanczos) is the witness and `isCGIterate_cgRecurrence`
the realisation theorem.

## 2. Conventions
- Names: recursion `fooBar` (lowerCamel), success predicate `FooSucceeds` (UpperCamel, Prop),
  factorization predicate `IsFoo`, realisation theorem `isFoo_fooBar`/`isFoo_of_fooSucceeds`,
  breakdown theorem `fooSucceeds_iff_…`.
- Triangularity: `Matrix.BlockTriangular` with `id` as the ordering, or a local `IsUpperTriangular`
  with a bridge lemma to Mathlib's; never a bespoke notion without the bridge.
- Permutations: `Matrix.PEquiv.toMatrix` / `Equiv.Perm` permutation matrices from Mathlib.
- One elimination step is a Schur complement: use `Matrix.fromBlocks` and Mathlib's block
  lemmas (`Matrix.PosDef.fromBlocks₁₁`, `det_fromBlocks₁₁`, `inv_fromBlocks…`).
- Real matrices, explicit constants, hypotheses explicit; eigenvalue algorithms are stated for
  symmetric `A` first.
- Atlas: predicate and existence/uniqueness share the factorization's id (`lu-decomposition`,
  `qr-decomposition`); the algorithm's success/realisation theorems have their own id
  (`lu-algorithm`, `cholesky-algorithm`, `householder-qr`, `gram-schmidt`, `cg-recurrence`,
  `lanczos-recurrence-algorithm`), so a consumer can cite the predicate without inheriting the
  algorithm's status.
- Cost (flops) is an atlas note, not a theorem (see KRYLOV_DEFINITIONS §3.10).

## 3. What not to formalise
Elimination loops as programs, determinant/inverse by LU for their own sake, operation counts,
and anything about rounding until the finite-precision design exists.
