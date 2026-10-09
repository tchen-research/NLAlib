import NLAlib.Concentration.Matrix.Defs.Ch8Entropy

/-!
# Square-root and inverse-square-root identities for positive definite matrices

Lean name: `NLAlib.ch8_perspective_sqrt_normalization`.

Source: Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1, Definition 8.6.1 and proof of Theorem 8.6.2, printed pp. 134–135 (PDF pp. 140–141), positive-definite square-root normalization.
-/
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open NLAlib

theorem NLAlib.ch8_perspective_sqrt_normalization
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (hA : A.PosDef) :
    let S := ch8_matrixFunction Real.sqrt A
    let R := ch8_matrixFunction (fun x => (Real.sqrt x)⁻¹) A
    S.IsHermitian ∧ R.IsHermitian ∧ S * S = A ∧ R * S = 1 ∧ S * R = 1 := by
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) := by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).continuousOn f
  have hpos (x : ℝ) (hx : x ∈ spectrum ℝ A) : 0 < x :=
    hA.isStrictlyPositive.spectrum_pos hx
  dsimp only [ch8_matrixFunction]
  refine ⟨cfc_predicate _ A, cfc_predicate _ A, ?_, ?_, ?_⟩
  · rw [← cfc_mul _ _ A (hcont _) (hcont _)]
    calc
      cfc (fun x => Real.sqrt x * Real.sqrt x) A = cfc (fun x : ℝ => x) A :=
        cfc_congr fun x hx => Real.mul_self_sqrt (hpos x hx).le
      _ = A := cfc_id' ℝ A hA.isHermitian
  · rw [← cfc_mul _ _ A (hcont _) (hcont _)]
    calc
      cfc (fun x => (Real.sqrt x)⁻¹ * Real.sqrt x) A = cfc (fun _ : ℝ => 1) A :=
        cfc_congr fun x hx => inv_mul_cancel₀ (Real.sqrt_pos.mpr (hpos x hx)).ne'
      _ = 1 := cfc_one ℝ A hA.isHermitian
  · rw [← cfc_mul _ _ A (hcont _) (hcont _)]
    calc
      cfc (fun x => Real.sqrt x * (Real.sqrt x)⁻¹) A = cfc (fun _ : ℝ => 1) A :=
        cfc_congr fun x hx => mul_inv_cancel₀ (Real.sqrt_pos.mpr (hpos x hx)).ne'
      _ = 1 := cfc_one ℝ A hA.isHermitian


