import NLAlib.Matrix.Functions.OperatorCapacitySpectral
import NLAlib.Matrix.Functions.GeometricMean

/-!
# One-step normalization of a positive-capacity Kraus map

Every normalized positive definite test matrix yields an actual invertible
congruence scaling of a positive-capacity Kraus map that is unital. The
determinant factor is the reciprocal of its objective value. Applied to
approximate minimizers, this supplies balanced scalings without assuming
that a capacity minimizer exists or using a scaling algorithm.

Source: the normalization in GGOW, arXiv:1511.03730v4, Lemma 3.9;
used here in the proof of tensor multiplicativity, Theorem 3.11.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-- A positive-capacity Kraus map sends every normalized positive definite
test matrix to a positive definite matrix. Its determinant is bounded below
by the positive capacity. -/
theorem posDef_krausMap_of_operatorCapacity_pos
    (A : ι → Matrix n n ℂ) (hcap : 0 < operatorCapacity (krausMap A))
    {X : Matrix n n ℂ} (hX : X.PosDef) (hdet : X.det = 1) :
    (krausMap A X).PosDef := by
  have hpos : 0 < (krausMap A X).det.re :=
    hcap.trans_le (operatorCapacity_le_det_apply (krausMap A) (krausMap_posSemidef A) hX hdet)
  apply (krausMap_posSemidef A X hX.posSemidef).posDef_iff_det_ne_zero.mpr
  intro hzero
  simp only [hzero, Complex.zero_re, lt_self_iff_false] at hpos

/-- Normalizing a positive-capacity Kraus family at an actual determinant-one
positive definite test matrix gives an invertible unital scaling. The product
of its squared determinant factors is exactly the reciprocal objective value.
Source: GGOW, arXiv:1511.03730v4, Lemma 3.9, normalization formula. -/
theorem exists_isUnit_unital_scaling_of_operatorCapacity_pos
    (A : ι → Matrix n n ℂ) (hcap : 0 < operatorCapacity (krausMap A))
    {X : Matrix n n ℂ} (hX : X.PosDef) (hdet : X.det = 1) :
    ∃ L R : Matrix n n ℂ, IsUnit L ∧ IsUnit R ∧
      krausMap (fun a => L * A a * R) 1 = 1 ∧
      Complex.normSq L.det * Complex.normSq R.det = ((krausMap A X).det.re)⁻¹ := by
  let Y := krausMap A X
  have hY : Y.PosDef := posDef_krausMap_of_operatorCapacity_pos A hcap hX hdet
  let R : Matrix n n ℂ := cfc Real.sqrt X
  let Rinv : Matrix n n ℂ := cfc (fun x => (Real.sqrt x)⁻¹) X
  let L : Matrix n n ℂ := cfc (fun x => (Real.sqrt x)⁻¹) Y
  let Linv : Matrix n n ℂ := cfc Real.sqrt Y
  have hR : IsUnit R :=
    ⟨⟨R, Rinv, cfc_sqrt_mul_inv_sqrt hX, cfc_inv_sqrt_mul_sqrt hX⟩, rfl⟩
  have hL : IsUnit L :=
    ⟨⟨L, Linv, cfc_inv_sqrt_mul_sqrt hY, cfc_sqrt_mul_inv_sqrt hY⟩, rfl⟩
  have hRH : R.IsHermitian := cfc_predicate _ _
  have hLH : L.IsHermitian := cfc_predicate _ _
  have hRX : R * 1 * Rᴴ = X := by
    rw [Matrix.mul_one, hRH.eq]
    exact cfc_sqrt_mul_self hX
  have hLY : L * Y * Lᴴ = 1 := by
    rw [hLH.eq]
    exact cfc_inv_sqrt_mul_self_mul_inv_sqrt hY
  have hRdet : (Complex.normSq R.det : ℂ) = X.det := by
    have h := congrArg Matrix.det hRX
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one, mul_one,
      Matrix.det_conjTranspose] at h
    rw [Complex.normSq_eq_conj_mul_self]
    simpa only [Complex.star_def, mul_comm] using h
  have hRdet1 : Complex.normSq R.det = 1 := by
    have h := congrArg Complex.re hRdet
    simpa only [hdet, Complex.ofReal_re, Complex.one_re] using h
  have hLdet : (Complex.normSq L.det : ℂ) * Y.det = 1 := by
    have h := congrArg Matrix.det hLY
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    rw [Complex.normSq_eq_conj_mul_self]
    simpa only [Complex.star_def, mul_comm, mul_left_comm, mul_assoc] using h
  have hLdetre : Complex.normSq L.det * Y.det.re = 1 := by
    have h := congrArg Complex.re hLdet
    simpa only [Complex.re_ofReal_mul, Complex.one_re] using h
  refine ⟨L, R, hL, hR, ?_, ?_⟩
  · rw [krausMap_mul_mul_apply, hRX]
    exact hLY
  · rw [hRdet1, mul_one]
    exact eq_inv_of_mul_eq_one_left hLdetre

end NLAlib
