/-
The Gram evaluation and embedded-identity witness proofs are adapted from the
Prove2me Gaussian Random Matrices series, solution
`Sol_GaussianMatrix_full_rank_ae`, previously in SecondMoment.lean.
-/
import NLAlib.ForMathlib.MeasureTheory.PolynomialZeroSets
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Lebesgue-null singular Gram matrices

The Gram determinants are nonzero polynomials in the matrix entries. Their zero
sets are null for Lebesgue measure in the standard flat entry coordinates, with
the row/column dimension hypotheses made explicit. This is the algebraic
null-set argument in HMT 2011, Proposition A.5 (`gaussian-full-rank-ae`);
Gaussian almost-sure rank is its distributional consumer.
-/

noncomputable section

open MeasureTheory

namespace Matrix

/-- Evaluating the entry polynomial Gram determinant gives the actual row Gram
determinant. HMT 2011, Proposition A.5, algebraic identity. -/
theorem eval_det_mvPolynomialX_mul_transpose (p m : ℕ) (G : Matrix (Fin p) (Fin m) ℝ) :
    MvPolynomial.eval (fun ab : Fin p × Fin m => G ab.1 ab.2)
      (mvPolynomialX (Fin p) (Fin m) ℝ * (mvPolynomialX (Fin p) (Fin m) ℝ)ᵀ).det
      = (G * Gᵀ).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
  have hX : (mvPolynomialX (Fin p) (Fin m) ℝ).map
      (MvPolynomial.eval fun ab : Fin p × Fin m => G ab.1 ab.2) = G := by
    ext i j
    simp
  rw [hX]

/-- Evaluating the entry polynomial column Gram determinant gives the actual
column Gram determinant. HMT 2011, Proposition A.5. -/
theorem eval_det_transpose_mvPolynomialX_mul (p m : ℕ) (G : Matrix (Fin p) (Fin m) ℝ) :
    MvPolynomial.eval (fun ab : Fin p × Fin m => G ab.1 ab.2)
      ((mvPolynomialX (Fin p) (Fin m) ℝ)ᵀ * mvPolynomialX (Fin p) (Fin m) ℝ).det
      = (Gᵀ * G).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
  have hX : (mvPolynomialX (Fin p) (Fin m) ℝ).map
      (MvPolynomial.eval fun ab : Fin p × Fin m => G ab.1 ab.2) = G := by
    ext i j
    simp
  rw [hX]

/-- In the wide case, the row Gram determinant is a nonzero polynomial in the
entries, witnessed by the embedded identity matrix. HMT 2011, Proposition A.5. -/
theorem det_mvPolynomialX_mul_transpose_ne_zero {k t : ℕ} (h : k ≤ t) :
    (mvPolynomialX (Fin k) (Fin t) ℝ * (mvPolynomialX (Fin k) (Fin t) ℝ)ᵀ).det ≠ 0 := by
  intro h0
  let G0 : Matrix (Fin k) (Fin t) ℝ := of fun i j => if j = Fin.castLE h i then 1 else 0
  have hE : G0 * G0ᵀ = 1 := by
    ext i l
    simp [G0, mul_apply, one_apply, Fin.castLE_inj, eq_comm]
  have he := eval_det_mvPolynomialX_mul_transpose k t G0
  rw [h0, map_zero, hE, det_one] at he
  exact zero_ne_one he

/-- In the tall case, the column Gram determinant is a nonzero polynomial in
the entries, witnessed by the embedded identity. HMT 2011, Proposition A.5. -/
theorem det_transpose_mvPolynomialX_mul_ne_zero {k t : ℕ} (h : t ≤ k) :
    ((mvPolynomialX (Fin k) (Fin t) ℝ)ᵀ * mvPolynomialX (Fin k) (Fin t) ℝ).det ≠ 0 := by
  intro h0
  let G0 : Matrix (Fin k) (Fin t) ℝ := of fun i j => if i = Fin.castLE h j then 1 else 0
  have hE : G0ᵀ * G0 = 1 := by
    ext i l
    simp [G0, mul_apply, one_apply, Fin.castLE_inj, eq_comm]
  have he := eval_det_transpose_mvPolynomialX_mul k t G0
  rw [h0, map_zero, hE, det_one] at he
  exact zero_ne_one he

/-- The singular row-Gram locus is Lebesgue-null in standard flat entry
coordinates for a wide matrix, including zero rows. HMT 2011, Proposition A.5.
atlas: gaussian-full-rank-ae (partial) -/
theorem volume_det_mul_transpose_eq_zero {k t : ℕ} (h : k ≤ t) :
    volume {x : Fin k × Fin t → ℝ |
      ((of fun i j => x (i, j)) * (of fun i j => x (i, j))ᵀ).det = 0} = 0 := by
  have hn := MvPolynomial.volume_eval_eq_zero _ (det_mvPolynomialX_mul_transpose_ne_zero h)
  convert hn using 1
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [← eval_det_mvPolynomialX_mul_transpose k t (of fun i j => x (i, j))]
  rfl

/-- The singular column-Gram locus is Lebesgue-null in standard flat entry
coordinates for a tall matrix, including zero columns. HMT 2011, Proposition A.5.
atlas: gaussian-full-rank-ae (partial) -/
theorem volume_det_transpose_mul_eq_zero {k t : ℕ} (h : t ≤ k) :
    volume {x : Fin k × Fin t → ℝ |
      ((of fun i j => x (i, j))ᵀ * (of fun i j => x (i, j))).det = 0} = 0 := by
  have hn := MvPolynomial.volume_eval_eq_zero _ (det_transpose_mvPolynomialX_mul_ne_zero h)
  convert hn using 1
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [← eval_det_transpose_mvPolynomialX_mul k t (of fun i j => x (i, j))]
  rfl

end Matrix
