import NLAlib.Matrix.Functions.GeometricMeanIdentities
import NLAlib.Matrix.Functions.LoewnerHeinz

/-!
# Maximal positive block completion

The geometric mean is the greatest Hermitian off-diagonal block of a
positive block matrix, including singular second arguments. The common
algebraic proof is instantiated with square-root monotonicity over both
real and complex matrices. Tropp (2022), Definition 16.15 and Theorem 12.16.
-/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- A Hermitian matrix is bounded above by the positive square root of its square. -/
theorem le_cfc_sqrt_sq {X : Matrix n n 𝕜} (hX : X.IsHermitian) :
    X ≤ cfc Real.sqrt (X ^ 2) := by
  calc
    X = cfc (fun x : ℝ => x) X := (cfc_id' ℝ X hX).symm
    _ ≤ cfc (fun x : ℝ => Real.sqrt (x ^ 2)) X := by
      exact cfc_mono (fun x _ => by
        rw [Real.sqrt_sq_eq_abs]
        exact le_abs_self x) (by fun_prop) (by fun_prop)
    _ = cfc Real.sqrt (X ^ 2) := cfc_comp_pow Real.sqrt 2 X (by fun_prop) hX

/-- The geometric mean attains a positive block completion. -/
theorem posSemidef_fromBlocks_matrixGeometricMean {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A (matrixGeometricMean A B) (matrixGeometricMean A B) B).PosSemidef := by
  let : Invertible A := hA.isUnit.invertible
  have hG := (posSemidef_matrixGeometricMean A B).isHermitian
  have h := Matrix.PosDef.fromBlocks₁₁ (matrixGeometricMean A B) B hA
  rw [hG.eq] at h
  apply h.mpr
  rw [matrixGeometricMean_mul_inv_mul hA hB, sub_self]
  exact Matrix.PosSemidef.zero

private theorem le_matrixGeometricMean_of_sqrt_mono
    (hmono : ∀ {C D : Matrix n n 𝕜}, C.PosSemidef → C ≤ D →
      cfc Real.sqrt C ≤ cfc Real.sqrt D)
    {A B X : Matrix n n 𝕜} (hA : A.PosDef)
    (hX : X.IsHermitian) (hblock : (Matrix.fromBlocks A X X B).PosSemidef) :
    X ≤ matrixGeometricMean A B := by
  let R := cfc (fun x => (Real.sqrt x)⁻¹) A
  let S := cfc Real.sqrt A
  let Y := R * X * R
  let C := R * B * R
  have hR : R.IsHermitian := cfc_predicate _ _
  have hS : S.IsHermitian := cfc_predicate _ _
  have hY : Y.IsHermitian := by
    dsimp [Y]
    simpa only [hR.eq] using Matrix.isHermitian_mul_mul_conjTranspose R hX
  have hRS : R * S = 1 := cfc_inv_sqrt_mul_sqrt hA
  have hSR : S * R = 1 := cfc_sqrt_mul_inv_sqrt hA
  have hi : A⁻¹ = R * R := inv_eq_cfc_inv_sqrt_mul_self hA
  let : Invertible A := hA.isUnit.invertible
  have hschur := (Matrix.PosDef.fromBlocks₁₁ X B hA).mp
    (by simpa only [hX.eq] using hblock)
  have hcong := hschur.mul_mul_conjTranspose_same R
  have heq : R * (B - X.conjTranspose * A⁻¹ * X) * R.conjTranspose = C - Y ^ 2 := by
    rw [hX.eq, hR.eq, hi]
    dsimp [C, Y]
    noncomm_ring
  rw [heq] at hcong
  have hYY : (Y ^ 2).PosSemidef := by
    simpa only [hY.eq, pow_two] using Matrix.posSemidef_conjTranspose_mul_self Y
  have hYC : Y ≤ cfc Real.sqrt C :=
    (le_cfc_sqrt_sq hY).trans (hmono hYY (Matrix.le_iff.mpr hcong))
  have hfinal := (Matrix.le_iff.mp hYC).mul_mul_conjTranspose_same S
  have heq' : S * (cfc Real.sqrt C - Y) * S.conjTranspose = matrixGeometricMean A B - X := by
    rw [hS.eq]
    change S * (cfc Real.sqrt C - R * X * R) * S =
      S * cfc Real.sqrt C * S - X
    calc
      _ = S * cfc Real.sqrt C * S - (S * R) * X * (R * S) := by noncomm_ring
      _ = _ := by rw [hSR, hRS, Matrix.one_mul, Matrix.mul_one]
  exact Matrix.le_iff.mpr (heq' ▸ hfinal)

/-- The geometric mean is the greatest Hermitian positive block completion
over real matrices, including a singular second argument.
atlas: matrix-geometric-mean-block-maximum (partial) -/
theorem matrixGeometricMean_block_maximum_real {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A (matrixGeometricMean A B) (matrixGeometricMean A B) B).PosSemidef ∧
      ∀ X : Matrix n n ℝ, X.IsHermitian → (Matrix.fromBlocks A X X B).PosSemidef →
        X ≤ matrixGeometricMean A B := by
  refine ⟨posSemidef_fromBlocks_matrixGeometricMean hA hB, fun X hX hblock => ?_⟩
  apply le_matrixGeometricMean_of_sqrt_mono (fun hC hCD => ?_) hA hX hblock
  rw [show Real.sqrt = (fun x : ℝ => x ^ ((1 : ℝ) / 2)) from funext Real.sqrt_eq_rpow]
  exact cfc_rpow_le_cfc_rpow hC hCD
    (r := (1 : ℝ) / 2) (by constructor <;> norm_num)

/-- The geometric mean is the greatest Hermitian positive block completion
over complex matrices, including a singular second argument.
atlas: matrix-geometric-mean-block-maximum (partial) -/
theorem matrixGeometricMean_block_maximum_complex {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A (matrixGeometricMean A B) (matrixGeometricMean A B) B).PosSemidef ∧
      ∀ X : Matrix n n ℂ, X.IsHermitian → (Matrix.fromBlocks A X X B).PosSemidef →
        X ≤ matrixGeometricMean A B := by
  refine ⟨posSemidef_fromBlocks_matrixGeometricMean hA hB, fun X hX hblock => ?_⟩
  apply le_matrixGeometricMean_of_sqrt_mono (fun {C D} hC hCD => ?_) hA hX hblock
  have hD : D.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (hC.nonneg.trans hCD)
  have h := CFC.sqrt_le_sqrt C D hCD
  simpa only [CFC.sqrt_eq_real_sqrt C hC.nonneg, CFC.sqrt_eq_real_sqrt D hD.nonneg,
    cfcₙ_eq_cfc (hf0 := Real.sqrt_zero)] using h

end NLAlib
