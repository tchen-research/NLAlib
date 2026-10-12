import NLAlib.Matrix.Structured.CirculantCharacterization
import NLAlib.Matrix.Structured.CauchyDeterminantFinite
/-!
# Complete structured-matrix contract

Ordinary Toeplitz/Hankel indexing, Cauchy's denominator-only determinant
formula, the Hilbert special case, and the cyclic-shift characterization
of circulants, including empty matrices.
-/

noncomputable section
open scoped Matrix BigOperators
namespace NLAlib

/-- The complete structured-matrix bundle with the source indexing
conventions, all Cauchy determinant factors, repeated-parameter allowance,
Hilbert specialization and positivity, and the exact circulant commutant
characterization. Horn–Johnson 2013, §§0.9.7, 0.9.8 and 0.9.12.
atlas: structured-matrices-def -/
theorem structured_matrices_properties (n : ℕ) :
    (∀ (t : ℤ → ℝ) (i j : Fin n),
      toeplitzMatrix t i j = t ((j.val : ℤ) - (i.val : ℤ))) ∧
    (∀ (h : ℕ → ℝ) (i j : Fin n), hankelMatrix h i j = h (i.val + j.val)) ∧
    (∀ (x y : Fin n → ℝ), (∀ i j, x i + y j ≠ 0) →
      (cauchyMatrix x y).det =
        (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j - x i)) *
          (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y j - y i)) /
            (∏ i : Fin n, ∏ j : Fin n, (x i + y j))) ∧
    (hilbertMatrix n = cauchyMatrix (fun i : Fin n => (i.val : ℝ) + 1)
      (fun j : Fin n => (j.val : ℝ))) ∧
    (0 < (hilbertMatrix n).det) ∧
    (∀ (k : ℕ) [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ),
      (∃ v : Fin k → ℝ, A = Matrix.circulant v) ↔
        (∃ t : ℤ → ℝ, A = toeplitzMatrix t) ∧
          A * cyclicShiftMatrix k = cyclicShiftMatrix k * A) ∧
    (∀ A : Matrix (Fin 0) (Fin 0) ℝ,
      (∃ t : ℤ → ℝ, A = toeplitzMatrix t) ∧
        (∃ v : Fin 0 → ℝ, A = Matrix.circulant v)) :=
  ⟨(by intros; rfl), (by intros; rfl), det_cauchyMatrix_eq_prod_differences,
    hilbertMatrix_eq_cauchyMatrix n, det_hilbertMatrix_pos n,
    (by intro k _ A; exact exists_circulant_iff_toeplitz_and_commute A),
    exists_toeplitz_circulant_of_empty⟩

end NLAlib
