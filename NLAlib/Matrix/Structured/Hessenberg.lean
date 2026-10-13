import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Real.Basic

/-!
# Hessenberg and tridiagonal shapes

Shape predicates on square matrices indexed by `Fin n`:

* `IsUpperHessenberg H` (`H i j = 0` for `j + 1 < i`), `IsTridiagonal T` (`T` and `Tᵀ` upper
  Hessenberg) and `IsUnreducedHessenberg H` (upper Hessenberg with no zero subdiagonal entry);
* closure lemmas: upper triangular ⇒ Hessenberg, Hessenberg × upper triangular and
  upper triangular × Hessenberg are Hessenberg, shifts `H ∓ μI` are Hessenberg
  (`IsUpperHessenberg.sub_smul_one`, `.add_smul_one`), symmetric Hessenberg ⇒ tridiagonal.

They are used by Givens QR (`NLAlib.Matrix.Factorizations.Givens`), Hessenberg reduction
(`NLAlib.Matrix.Factorizations.Hessenberg`) and the QR algorithm.
Sources: Golub–Van Loan 2013 [`gvl13`], §7.4, §8.3; Trefethen–Bau 1997 [`tb97`], Lect. 26.
Atlas: `givens-rotation-def`, `hessenberg-reduction`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {n : ℕ}

/-- `H` is **upper Hessenberg**: `H i j = 0` whenever `j + 1 < i` (zero below the first
subdiagonal). Golub–Van Loan 2013, §7.4; Trefethen–Bau 1997, Lect. 26.
atlas: givens-rotation-def -/
def IsUpperHessenberg (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, (j : ℕ) + 1 < i → H i j = 0

/-- `T` is **tridiagonal**: `T` and `Tᵀ` are upper Hessenberg (`T i j = 0` for `|i − j| > 1`).
Golub–Van Loan 2013, §8.3; Trefethen–Bau 1997, Lect. 26.
atlas: givens-rotation-def -/
def IsTridiagonal (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsUpperHessenberg T ∧ IsUpperHessenberg Tᵀ

/-- An upper triangular matrix is upper Hessenberg. -/
theorem isUpperHessenberg_of_isUpperTriangular {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : U.IsUpperTriangular) : IsUpperHessenberg U :=
  fun i j hij => hU (show j < i by rw [Fin.lt_def]; omega)

/-- **Hessenberg × upper triangular is Hessenberg.** Golub–Van Loan 2013, §7.4.2 (proof of
Hessenberg preservation). -/
theorem IsUpperHessenberg.mul_isUpperTriangular {H U : Matrix (Fin n) (Fin n) ℝ}
    (hH : IsUpperHessenberg H) (hU : U.IsUpperTriangular) : IsUpperHessenberg (H * U) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) + 1 < i
  · rw [hH i k hk, zero_mul]
  · rw [hU (show j < k by rw [Fin.lt_def]; omega), mul_zero]

/-- **Upper triangular × Hessenberg is Hessenberg.** Golub–Van Loan 2013, §7.4.2. -/
theorem IsUpperHessenberg.isUpperTriangular_mul {H U : Matrix (Fin n) (Fin n) ℝ}
    (hH : IsUpperHessenberg H) (hU : U.IsUpperTriangular) : IsUpperHessenberg (U * H) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) < i
  · rw [hU (Fin.lt_def.2 hk), zero_mul]
  · rw [hH k j (by omega), mul_zero]

/-- **A symmetric upper Hessenberg matrix is tridiagonal.** Golub–Van Loan 2013, §8.3.1;
Trefethen–Bau 1997, Lect. 26. -/
theorem IsUpperHessenberg.isTridiagonal_of_isSymm {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : IsUpperHessenberg H) (hS : H.IsSymm) : IsTridiagonal H :=
  ⟨hH, by rw [hS.eq]; exact hH⟩

/-- Subtracting a multiple of the identity keeps upper Hessenberg form. Helper for
`qr-algorithm-simultaneous-iteration`. -/
theorem IsUpperHessenberg.sub_smul_one {H : Matrix (Fin n) (Fin n) ℝ} (hH : IsUpperHessenberg H)
    (μ : ℝ) : IsUpperHessenberg (H - μ • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  intro i j hij
  have hne : i ≠ j := fun h => by subst h; omega
  simp [hH i j hij, Matrix.one_apply_ne hne]

/-- Adding a multiple of the identity keeps upper Hessenberg form. Helper for
`qr-algorithm-simultaneous-iteration`. -/
theorem IsUpperHessenberg.add_smul_one {H : Matrix (Fin n) (Fin n) ℝ} (hH : IsUpperHessenberg H)
    (μ : ℝ) : IsUpperHessenberg (H + μ • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  intro i j hij
  have hne : i ≠ j := fun h => by subst h; omega
  simp [hH i j hij, Matrix.one_apply_ne hne]

/-- `H` has **no zero subdiagonal entry** (`H (j+1) j ≠ 0`) and is upper Hessenberg.
Golub–Van Loan 2013, §7.4.3 ("unreduced"); Trefethen–Bau 1997, Lect. 26.
atlas: hessenberg-reduction -/
def IsUnreducedHessenberg (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsUpperHessenberg H ∧ ∀ i j : Fin n, (i : ℕ) = j + 1 → H i j ≠ 0

end NLAlib
