import NLAlib.Matrix.Inequalities.PlaneRotationSpectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Decreasing rotations for the Schur–Horn minimum

An explicit positive plane rotation decreases squared diagonal error whenever
the residual-weighted spectral pair is strictly inverted. Source: Schur–Horn
variational rederivation, equation (6), supporting atlas `schur-horn`.
-/
noncomputable section
open scoped Matrix BigOperators
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared diagonal error changes by an exact quadratic expression when
two orthonormal eigenvectors have disjoint supports. Schur–Horn variational
rederivation, equation (6). -/
theorem sum_sq_diagonal_error_planeRotation_eq
    (A : Matrix n n ℝ) (hA : Aᵀ = A) (d u v : n → ℝ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0)
    (α β : ℝ) (hAu : A *ᵥ u = α • u) (hAv : A *ᵥ v = β • v)
    (hdisjoint : ∀ i, u i * v i = 0) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (∑ i, ((planeRotation u v c s * A * (planeRotation u v c s)ᵀ) i i - d i) ^ 2) -
      (∑ i, (A i i - d i) ^ 2) =
      2 * s ^ 2 * (β - α) * (∑ i, (A i i - d i) * (u i ^ 2 - v i ^ 2)) +
        s ^ 4 * (β - α) ^ 2 * (∑ i, (u i ^ 2 - v i ^ 2) ^ 2) := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [planeRotation_mul_mul_transpose_apply_diag_of_disjoint_eigenvectors
    A hA u v hu hv huv α β hAu hAv hdisjoint c s hcs]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem exists_pos_quadratic_neg {δ η K : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hK : 0 ≤ K) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ -2 * h * δ * η + h ^ 2 * δ ^ 2 * K < 0 := by
  let h : ℝ := min (1 / 2) (η / (δ * (K + 1)))
  have hden : 0 < δ * (K + 1) := mul_pos hδ (by linarith)
  have hh : 0 < h := lt_min (by norm_num) (div_pos hη hden)
  have hh1 : h ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hbudget : h * (δ * (K + 1)) ≤ η :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hhδ : 0 < h * δ := mul_pos hh hδ
  have hlin : h * δ * K ≤ η := by nlinarith
  have hquad : h ^ 2 * δ ^ 2 * K ≤ h * δ * η := by
    have h := mul_le_mul_of_nonneg_left hlin hhδ.le
    nlinarith
  refine ⟨h, hh, hh1, ?_⟩
  have hneg : 0 < h * δ * η := mul_pos hhδ hη
  nlinarith

/-- If residual-weighted unit eigenvectors have positive separation, their
eigenvalues cannot be strictly inverted at a global squared-diagonal-error
minimum. The contradiction uses an explicit finite decreasing rotation.
Schur–Horn variational rederivation, equation (6). -/
theorem eigenvalue_le_of_diagonal_error_min
    (A : Matrix n n ℝ) (hA : Aᵀ = A) (d u v : n → ℝ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0)
    (α β : ℝ) (hAu : A *ᵥ u = α • u) (hAv : A *ᵥ v = β • v)
    (hdisjoint : ∀ i, u i * v i = 0)
    (hη : 0 < ∑ i, (A i i - d i) * (u i ^ 2 - v i ^ 2))
    (hmin : ∀ R : Matrix n n ℝ, Rᵀ * R = 1 →
      (∑ i, (A i i - d i) ^ 2) ≤ ∑ i, ((R * A * Rᵀ) i i - d i) ^ 2) :
    α ≤ β := by
  by_contra hnot
  have hδ : 0 < α - β := sub_pos.mpr (lt_of_not_ge hnot)
  let η := ∑ i, (A i i - d i) * (u i ^ 2 - v i ^ 2)
  let K := ∑ i, (u i ^ 2 - v i ^ 2) ^ 2
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => sq_nonneg _
  obtain ⟨h, hh0, hh1, hneg⟩ := exists_pos_quadratic_neg hδ hη hK
  let c : ℝ := Real.sqrt (1 - h)
  let s : ℝ := Real.sqrt h
  have hc : c ^ 2 = 1 - h := Real.sq_sqrt (sub_nonneg.mpr hh1)
  have hs : s ^ 2 = h := Real.sq_sqrt hh0.le
  have hcs : c ^ 2 + s ^ 2 = 1 := by rw [hc, hs]; ring
  have horth := transpose_planeRotation_mul_self u v hu hv huv c s hcs
  have hbound := hmin (planeRotation u v c s) horth
  have hdiff := sum_sq_diagonal_error_planeRotation_eq
    A hA d u v hu hv huv α β hAu hAv hdisjoint c s hcs
  have hs4 : s ^ 4 = h ^ 2 := by nlinarith [sq_nonneg (s ^ 2 - h)]
  change _ = 2 * s ^ 2 * (β - α) * η + s ^ 4 * (β - α) ^ 2 * K at hdiff
  rw [hs, hs4] at hdiff
  have heq : 2 * h * (β - α) * η + h ^ 2 * (β - α) ^ 2 * K =
      -2 * h * (α - β) * η + h ^ 2 * (α - β) ^ 2 * K := by ring
  rw [heq] at hdiff
  linarith

end NLAlib
