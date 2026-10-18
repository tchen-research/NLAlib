import NLAlib.Matrix.Spectral.HermitianExtremaNorm
import NLAlib.Matrix.Spectral.CourantFischer
import NLAlib.Matrix.Functions.ExtremeEigenvalues

/-!
# Perturbation and continuity of the largest Hermitian eigenvalue

Weyl subadditivity gives the spectral norm perturbation bound and a continuous
Hermitian-part extension. Nonnegative scalar combinations give the expected
maximum decomposition used in Gaussian proxy comparison.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The largest eigenvalue is subadditive on Hermitian matrices of nonzero
finite dimension. -/
theorem lambdaMax_add_le [Nonempty n] (A B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    lambdaMax (A + B) ≤ lambdaMax A + lambdaMax B := by
  let z : Fin (Fintype.card n) := ⟨0, Fintype.card_pos⟩
  have h := hA.eigenvalues₀_add_le hB z z (by simpa only [z, zero_add] using Fintype.card_pos (α := n))
  rw [lambdaMax_eq_eigenvalues₀_zero (hA.add hB),
    lambdaMax_eq_eigenvalues₀_zero hA, lambdaMax_eq_eigenvalues₀_zero hB]
  simpa only [z, zero_add] using h

/-- Perturbing a Hermitian matrix changes its largest eigenvalue by at most
the spectral norm of the perturbation. -/
theorem abs_lambdaMax_sub_le_specNorm_sub [Nonempty n]
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    |lambdaMax A - lambdaMax B| ≤ specNorm (A - B) := by
  have h1 := lambdaMax_add_le B (A - B) hB (hA.sub hB)
  have h2 := lambdaMax_add_le A (B - A) hA (hB.sub hA)
  have hb1 := (hA.sub hB).lambdaMax_le_specNorm
  have hb2 := (hB.sub hA).lambdaMax_le_specNorm
  have he : specNorm (B - A) = specNorm (A - B) := by
    rw [← neg_sub A B, specNorm_neg]
  have hBA : B + (A - B) = A := by abel
  have hAB : A + (B - A) = B := by abel
  rw [hBA] at h1
  rw [hAB] at h2
  rw [he] at hb2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

open scoped Matrix.Norms.L2Operator in
/-- Projecting a matrix to its Hermitian part gives a continuous globally
defined maximum-eigenvalue observable. This supplies measurable extensions
for probability laws supported almost surely on Hermitian matrices. -/
theorem continuous_lambdaMax_selfAdjointPart [Nonempty n] :
    Continuous (fun A : Matrix n n ℂ =>
      lambdaMax (selfAdjointPart ℝ A : Matrix n n ℂ)) := by
  let f : selfAdjoint (Matrix n n ℂ) → ℝ := fun A => lambdaMax (A : Matrix n n ℂ)
  have hf : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro A B
    simp only [f, NNReal.coe_one, one_mul, dist_eq_norm]
    change |lambdaMax (A : Matrix n n ℂ) - lambdaMax (B : Matrix n n ℂ)| ≤
      ‖(A : Matrix n n ℂ) - (B : Matrix n n ℂ)‖
    simpa only [one_mul, specNorm_eq_norm] using
      abs_lambdaMax_sub_le_specNorm_sub (A : Matrix n n ℂ) (B : Matrix n n ℂ)
        A.property.isHermitian B.property.isHermitian
  have hp : Continuous (selfAdjointPart ℝ : Matrix n n ℂ → selfAdjoint (Matrix n n ℂ)) :=
    (selfAdjointPart ℝ).toContinuousLinearMap.continuous
  exact hf.continuous.comp hp

/-- Increasing the scale of a Hermitian perturbation separates the excess
scale from a fixed-offset maximum eigenvalue. -/
theorem lambdaMax_smul_add_smul_le [Nonempty n]
    (D Z : Matrix n n ℂ) (hD : D.IsHermitian) (hZ : Z.IsHermitian)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    lambdaMax (a • D + b • Z) ≤
      a * lambdaMax (D + Z) + (b - a) * lambdaMax Z := by
  have he : a • D + b • Z = a • (D + Z) + (b - a) • Z := by
    rw [smul_add, sub_smul]
    abel
  rw [he]
  calc
    _ ≤ lambdaMax (a • (D + Z)) + lambdaMax ((b - a) • Z) :=
      lambdaMax_add_le _ _ ((hD.add hZ).smul (IsSelfAdjoint.all a))
        (hZ.smul (IsSelfAdjoint.all (b - a)))
    _ = _ := by
      rw [lambdaMax_smul_of_nonneg _ ha,
        lambdaMax_smul_of_nonneg _ (sub_nonneg.mpr hab)]

end NLAlib
