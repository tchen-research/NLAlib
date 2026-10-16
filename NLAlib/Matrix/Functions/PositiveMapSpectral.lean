import NLAlib.Matrix.Functions.SpectralProjectors
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Positive maps on a single spectral algebra

Positive images of finite spectral projectors give positive block sums.
This proves Kadison's inequality on Hermitian inputs using positivity of
the original map, without a complete-positivity assumption.
Tropp (2022), Theorem 12.17. Atlas: `positive-map-kadison`.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Scalar rank-one block coefficients preserve positivity of a matrix. -/
theorem posSemidef_scalar_gram_fromBlocks {B : Matrix m m ℂ}
    (hB : B.PosSemidef) (a b : ℂ) :
    (fromBlocks ((a * star a) • B) ((a * star b) • B)
      ((b * star a) • B) ((b * star b) • B)).PosSemidef := by
  have h := hB.mul_mul_conjTranspose_same
    (fromRows (a • (1 : Matrix m m ℂ)) (b • (1 : Matrix m m ℂ)))
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols] at h
  simpa only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    mul_comm] using h

omit [Fintype m] [DecidableEq m] in
/-- The image of each spectral projector under a positive map is positive. -/
theorem posSemidef_map_unitarySpectralProjector
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ)
    (U : unitary (Matrix n n ℂ)) (i : n) :
    (Φ (unitarySpectralProjector U i)).PosSemidef :=
  (Φ.map_nonneg (posSemidef_unitarySpectralProjector U i).nonneg).posSemidef

omit [Fintype m] [DecidableEq m] in
/-- Positive complex-linear maps preserve Hermitian matrices. -/
theorem isHermitian_map_of_positive (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : (Φ A).IsHermitian := by
  rw [sum_eigenvalue_smul_unitarySpectralProjector hA, map_sum]
  simp only [map_smul]
  apply isSelfAdjoint_sum
  intro i _
  exact (posSemidef_map_unitarySpectralProjector Φ _ i).isHermitian.smul
    (by simp [IsSelfAdjoint])

/-- Kadison's inequality for positive unital complex-linear maps, on
Hermitian inputs. Tropp (2022), Theorem 12.17. Positivity is sufficient;
the theorem does not assume complete positivity.
atlas: positive-map-kadison -/
theorem map_sq_le_of_positive_unital
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ) (hΦ : Φ 1 = 1)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : (Φ A) ^ 2 ≤ Φ (A ^ 2) := by
  let P := unitarySpectralProjector hA.eigenvectorUnitary
  let B : n → Matrix m m ℂ := fun i => Φ (P i)
  let ev : n → ℂ := fun i => hA.eigenvalues i
  have hB (i : n) : (B i).PosSemidef := posSemidef_map_unitarySpectralProjector Φ _ i
  have hsum : ∑ i, B i = 1 := by
    dsimp [B, P]
    rw [← map_sum, sum_unitarySpectralProjector, hΦ]
  have hfirst : ∑ i, ev i • B i = Φ A := by
    rw [sum_eigenvalue_smul_unitarySpectralProjector hA, map_sum]
    simp only [map_smul]
    rfl
  have hsecond : ∑ i, (ev i) ^ 2 • B i = Φ (A ^ 2) := by
    rw [pow_eq_sum_eigenvalue_pow_smul_unitarySpectralProjector hA 2, map_sum]
    simp only [map_smul]
    rfl
  have hblocks (i : n) :
      (fromBlocks (B i) (ev i • B i) (ev i • B i) (ev i ^ 2 • B i)).PosSemidef := by
    simpa [ev, pow_two] using posSemidef_scalar_gram_fromBlocks (hB i) 1 (ev i)
  have hH := Matrix.posSemidef_sum Finset.univ (fun i _ => hblocks i)
  have heq : (∑ i, fromBlocks (B i) (ev i • B i) (ev i • B i)
      (ev i ^ 2 • B i)) =
      fromBlocks (∑ i, B i) (∑ i, ev i • B i) (∑ i, ev i • B i)
        (∑ i, ev i ^ 2 • B i) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.sum_apply, fromBlocks]
  rw [heq, hsum, hfirst, hsecond] at hH
  let : Invertible (1 : Matrix m m ℂ) := invertibleOne
  have h := (Matrix.PosDef.fromBlocks₁₁ (Φ A) (Φ (A ^ 2))
    (Matrix.PosDef.one : (1 : Matrix m m ℂ).PosDef))
  rw [(isHermitian_map_of_positive Φ hA).eq] at h
  have hres := h.mp hH
  apply Matrix.le_iff.mpr
  simpa only [inv_one, Matrix.mul_one, ← pow_two] using hres

end NLAlib
