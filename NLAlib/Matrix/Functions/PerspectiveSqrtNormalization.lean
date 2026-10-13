import NLAlib.Matrix.OperatorTheory.Basic
/-!
# Square root and inverse square root of a positive definite matrix

For positive definite `A : Matrix ι ι 𝕜` (`[RCLike 𝕜]`), `S = √A = cfc Real.sqrt A` and
`R = A^{-1/2} = cfc (fun x => (√x)⁻¹) A` are Hermitian (`cfc_predicate`), `S S = A`
(`cfc_sqrt_mul_self`) and `R S = S R = 1` (`cfc_inv_sqrt_mul_sqrt`, `cfc_sqrt_mul_inv_sqrt`).
These normalise the matrix perspective `matrixPerspective` (Tropp 2015, Def. 8.6.1 and the
proof of Thm 8.6.2). Atlas: `operator-monotone-convex` (step of Thm 8.6.2).
-/
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

section
variable {A : Matrix ι ι 𝕜} (hA : A.PosDef)
include hA

private lemma cfc_continuousOn (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) := by
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues]
  exact (Set.finite_range _).continuousOn f

private lemma spectrum_pos' {x : ℝ} (hx : x ∈ spectrum ℝ A) : 0 < x :=
  hA.isStrictlyPositive.spectrum_pos hx

/-- `√A √A = A` for positive definite `A`. Tropp 2015, Def. 8.6.1. -/
theorem cfc_sqrt_mul_self : cfc Real.sqrt A * cfc Real.sqrt A = A := by
  rw [← cfc_mul _ _ A (cfc_continuousOn hA _) (cfc_continuousOn hA _)]
  calc
    cfc (fun x => Real.sqrt x * Real.sqrt x) A = cfc (fun x : ℝ => x) A :=
      cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_pos' hA hx).le
    _ = A := cfc_id' ℝ A hA.isHermitian

/-- `A^{-1/2} √A = 1` for positive definite `A`. Tropp 2015, proof of Thm 8.6.2. -/
theorem cfc_inv_sqrt_mul_sqrt : cfc (fun x => (Real.sqrt x)⁻¹) A * cfc Real.sqrt A = 1 := by
  rw [← cfc_mul _ _ A (cfc_continuousOn hA _) (cfc_continuousOn hA _)]
  calc
    cfc (fun x => (Real.sqrt x)⁻¹ * Real.sqrt x) A = cfc (fun _ : ℝ => 1) A :=
      cfc_congr fun x hx => inv_mul_cancel₀ (Real.sqrt_pos.mpr (spectrum_pos' hA hx)).ne'
    _ = 1 := cfc_one ℝ A hA.isHermitian

/-- `√A A^{-1/2} = 1` for positive definite `A`. Tropp 2015, proof of Thm 8.6.2. -/
theorem cfc_sqrt_mul_inv_sqrt : cfc Real.sqrt A * cfc (fun x => (Real.sqrt x)⁻¹) A = 1 := by
  rw [← cfc_mul _ _ A (cfc_continuousOn hA _) (cfc_continuousOn hA _)]
  calc
    cfc (fun x => Real.sqrt x * (Real.sqrt x)⁻¹) A = cfc (fun _ : ℝ => 1) A :=
      cfc_congr fun x hx => mul_inv_cancel₀ (Real.sqrt_pos.mpr (spectrum_pos' hA hx)).ne'
    _ = 1 := cfc_one ℝ A hA.isHermitian

end

end NLAlib
