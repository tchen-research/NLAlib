import NLAlib.Matrix.Functions.GeometricMean

/-!
# Square-root and Riccati identities for the geometric mean

Finite functional calculus and inverse-square-root cancellation prove
`(A # B) A⁻¹ (A # B) = B`, including singular `B`.
Tropp (2022), Definition 16.15 and the block characterization.
-/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The square root squares back to any PSD matrix, including singular inputs. -/
theorem cfc_sqrt_mul_self_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    cfc Real.sqrt A * cfc Real.sqrt A = A := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) := by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).continuousOn f
  rw [← cfc_mul _ _ A (hc _) (hc _)]
  calc
    cfc (fun x => Real.sqrt x * Real.sqrt x) A = cfc (fun x : ℝ => x) A := by
      apply cfc_congr
      intro x hx
      rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact Real.mul_self_sqrt (hA.eigenvalues_nonneg i)
    _ = A := cfc_id' ℝ A hA.isHermitian

/-- The ordinary inverse of a positive-definite matrix is the square of
its inverse square root. -/
theorem inv_eq_cfc_inv_sqrt_mul_self {A : Matrix n n 𝕜} (hA : A.PosDef) :
    A⁻¹ = cfc (fun x => (Real.sqrt x)⁻¹) A * cfc (fun x => (Real.sqrt x)⁻¹) A := by
  apply Matrix.inv_eq_right_inv
  calc
    _ = (cfc Real.sqrt A * cfc Real.sqrt A) *
        (cfc (fun x => (Real.sqrt x)⁻¹) A * cfc (fun x => (Real.sqrt x)⁻¹) A) := by
      rw [cfc_sqrt_mul_self hA]
    _ = cfc Real.sqrt A * (cfc Real.sqrt A * cfc (fun x => (Real.sqrt x)⁻¹) A) *
        cfc (fun x => (Real.sqrt x)⁻¹) A := by noncomm_ring
    _ = 1 := by rw [cfc_sqrt_mul_inv_sqrt hA, Matrix.mul_one, cfc_sqrt_mul_inv_sqrt hA]

/-- The positive-definite-first geometric mean solves the Riccati identity,
even when the second argument is singular. -/
theorem matrixGeometricMean_mul_inv_mul {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosSemidef) :
    matrixGeometricMean A B * A⁻¹ * matrixGeometricMean A B = B := by
  let S := cfc Real.sqrt A
  let R := cfc (fun x => (Real.sqrt x)⁻¹) A
  let C := R * B * R
  let T := cfc Real.sqrt C
  have hR : R.IsHermitian := cfc_predicate _ _
  have hC : C.PosSemidef := by
    simpa only [C, hR.eq] using hB.mul_mul_conjTranspose_same R
  have hTT : T * T = C := cfc_sqrt_mul_self_of_posSemidef hC
  have hSR : S * R = 1 := cfc_sqrt_mul_inv_sqrt hA
  have hRS : R * S = 1 := cfc_inv_sqrt_mul_sqrt hA
  have hi : A⁻¹ = R * R := inv_eq_cfc_inv_sqrt_mul_self hA
  change (S * T * S) * A⁻¹ * (S * T * S) = B
  calc
    _ = S * T * (S * R) * (R * S) * T * S := by rw [hi]; noncomm_ring
    _ = S * (T * T) * S := by rw [hSR, hRS]; noncomm_ring
    _ = (S * R) * B * (R * S) := by rw [hTT]; dsimp [C]; noncomm_ring
    _ = B := by rw [hSR, hRS, Matrix.one_mul, Matrix.mul_one]

end NLAlib
