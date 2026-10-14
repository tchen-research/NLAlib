import NLAlib.Krylov.Quadrature.ChristoffelNumbers
import NLAlib.Matrix.Functions.DiagonalCalculus
import NLAlib.Matrix.Subspaces.OrthogonalProducts
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.LinearAlgebra.Vandermonde

/-! # Finite discrete measures and diagonal matrix problems

An atomic positive measure is the spectral measure of its diagonal node matrix
and square-root weight vector. Distinct nodes and positive weights give full
Krylov grade by a weighted Vandermonde determinant. The identities include empty
matrices; first-coordinate formulas state positive dimension explicitly.
Source: Gautschi (2004), Theorem 1.9 and Sections 2.2.3.1--2.2.3.2.
Atlas: `discrete-measure-jacobi-matrix`.
-/

noncomputable section

open Matrix Polynomial MeasureTheory
open scoped Matrix Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A nonnegative finite atomic measure is the spectral measure of its diagonal
node matrix and square-root weight vector. Repeated nodes and zero weights are
allowed in this measure identity. Source: Gautschi (2004), Theorem 1.9.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem spectralMeasure_diagonal_sqrt_eq_sum_dirac (t w : n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    spectralMeasure (Matrix.isHermitian_diagonal t) (fun i => Real.sqrt (w i)) =
      ∑ i, ENNReal.ofReal (w i) • Measure.dirac (t i) := by
  let : IsFiniteMeasure (∑ i, ENNReal.ofReal (w i) • Measure.dirac (t i)) := ⟨by simp⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_spectralMeasure, cfc_diagonal,
    integral_finsetSum_measure fun i _ =>
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top]
  simp only [dotProduct, Matrix.mulVec_diagonal, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal (hw _), smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    Real.sqrt (w i) * (f (t i) * Real.sqrt (w i)) = Real.sqrt (w i) ^ 2 * f (t i) := by ring
    _ = w i * f (t i) := by rw [Real.sq_sqrt (hw i)]

/-- The grade of a diagonal matrix at a nonzero-coordinate vector is its full
dimension when the diagonal entries are distinct. The empty case is included.
Source: Gautschi (2004), Section 2.2.3.1, weighted Vandermonde construction.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem krylovGrade_diagonal_eq_card {N : ℕ} (t b : Fin N → ℝ)
    (ht : Function.Injective t) (hb : ∀ i, b i ≠ 0) :
    krylovGrade (Matrix.diagonal t) b = N := by
  let K : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal b * Matrix.vandermonde t
  have hK : K.det ≠ 0 := by
    change (Matrix.diagonal b * Matrix.vandermonde t).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hb i))
      (Matrix.det_vandermonde_ne_zero_iff.mpr ht)
  have hunit : IsUnit K := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hK)
  have hcols := Matrix.linearIndependent_cols_of_isUnit hunit
  have heq : K.col = fun j : Fin N => ((Matrix.diagonal t) ^ j.val) *ᵥ b := by
    ext j i
    simp [K, Matrix.col, diagonal_pow, Matrix.mulVec_diagonal,
      Matrix.vandermonde_apply, mul_comm]
  rw [heq] at hcols
  have hgrade := (linearIndependent_pow_mulVec_iff_le_krylovGrade
    (A := Matrix.diagonal t) (b := b)).mp hcols
  exact le_antisymm (by simpa using krylovGrade_le_card (Matrix.diagonal t) b) hgrade

/-- Positive atomic weights and distinct nodes give a diagonal spectral problem
whose grade equals the number of atoms. Source: Gautschi (2004), Section 2.2.3.1.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem krylovGrade_diagonal_sqrt_eq_card {N : ℕ} (t w : Fin N → ℝ)
    (ht : Function.Injective t) (hw : ∀ i, 0 < w i) :
    krylovGrade (Matrix.diagonal t) (fun i => Real.sqrt (w i)) = N :=
  krylovGrade_diagonal_eq_card t _ ht (fun i => (Real.sqrt_pos.mpr (hw i)).ne')

namespace LanczosDecomp

variable {t w : n → ℝ} {q : ℕ}

/-- For a diagonal spectral problem, each Lanczos column is the corresponding
polynomial evaluated at each node, multiplied by its square-root weight.
Source: Gautschi (2004), Section 2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem Q_apply_diagonal_sqrt_eq_eval_poly_mul
    (D : LanczosDecomp (Matrix.diagonal t) (fun i => Real.sqrt (w i)) q)
    (r : n) (j : Fin q) : D.Q r j = Real.sqrt (w r) * (D.poly j.val).eval (t r) := by
  have h := congrFun (D.vec_eq_aeval_poly j.val) r
  rw [D.vec_of_lt j.isLt, aeval_diagonal] at h
  simpa only [Matrix.col, Matrix.transpose_apply, Fin.eta,
    Matrix.mulVec_diagonal, Pi.mul_apply, mul_comm] using h

/-- At full dimension the polynomial evaluations obey dual orthogonality at the
atomic nodes. Source: Gautschi (2004), Section 2.2.3.2. Positivity is needed only
to divide by the atomic weights.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem sum_eval_poly_mul_eval_poly_eq_div_weight {N : ℕ} {t w : Fin N → ℝ}
    (D : LanczosDecomp (Matrix.diagonal t) (fun i => Real.sqrt (w i)) N)
    (hw : ∀ i, 0 < w i) (r s : Fin N) :
    (∑ j : Fin N, (D.poly j.val).eval (t r) * (D.poly j.val).eval (t s)) =
      (if r = s then 1 else 0) / w r := by
  have horth := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M r s)
    D.hasOrthonormalCols.mul_conjTranspose_self
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    Matrix.one_apply] at horth
  have hfactor : (Real.sqrt (w r) * Real.sqrt (w s)) *
      (∑ j : Fin N, (D.poly j.val).eval (t r) * (D.poly j.val).eval (t s)) =
        if r = s then 1 else 0 := by
    rw [← horth, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [D.Q_apply_diagonal_sqrt_eq_eval_poly_mul, D.Q_apply_diagonal_sqrt_eq_eval_poly_mul]
    ring
  by_cases hrs : r = s
  · subst s
    rw [← pow_two, Real.sq_sqrt (hw r).le, if_pos rfl] at hfactor
    rw [if_pos rfl]
    apply (eq_div_iff (hw r).ne').mpr
    nlinarith [hfactor]
  · rw [if_neg hrs] at hfactor ⊢
    rw [zero_div]
    exact (mul_eq_zero.mp hfactor).resolve_left
      (mul_ne_zero (Real.sqrt_pos.mpr (hw r)).ne' (Real.sqrt_pos.mpr (hw s)).ne')

end LanczosDecomp

namespace ArnoldiDecomp

variable {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- A positively oriented first Krylov vector gives the bordered starting-vector
identity. Source: Gautschi (2004), Section 2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem transpose_Q_mulVec_eq_single_of_pos (D : ArnoldiDecomp A b q) (hq : 0 < q)
    (h0 : 0 < D.Q.col ⟨0, hq⟩ ⬝ᵥ b) :
    D.Qᵀ *ᵥ b = Pi.single ⟨0, hq⟩ ‖WithLp.toLp 2 b‖ := by
  have hcpos : 0 < (D.Qᵀ *ᵥ b) ⟨0, hq⟩ := h0
  have hsq := D.sq_transpose_Q_mulVec_apply_zero hq
  rw [← norm_toLp_sq_eq_dotProduct_self] at hsq
  have heq : (D.Qᵀ *ᵥ b) ⟨0, hq⟩ = ‖WithLp.toLp 2 b‖ := by
    nlinarith [norm_nonneg (WithLp.toLp 2 b)]
  ext k
  by_cases hk : k = ⟨0, hq⟩
  · subst k
    simpa only [Pi.single_eq_same] using heq
  · rw [Pi.single_eq_of_ne hk, D.transpose_Q_mulVec_apply_eq_zero]
    have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext h)
    omega

end ArnoldiDecomp

/-- The canonical Arnoldi construction has the positively oriented bordered
starting-vector identity, including a complete discrete spectral problem.
Source: Gautschi (2004), Section 2.2.3.2.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem transpose_arnoldiMatrix_mulVec_eq_single
    (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ} (hq : 0 < q) (h : q ≤ krylovGrade A b) :
    (arnoldiMatrix A b q)ᵀ *ᵥ b = Pi.single ⟨0, hq⟩ ‖WithLp.toLp 2 b‖ := by
  apply (arnoldiDecomp A b q h).transpose_Q_mulVec_eq_single_of_pos hq
  exact arnoldiBasis_zero_dotProduct_pos A b (hq.trans_le h)

/-- The spectral measure of a Jacobi matrix and the mass-scaled first coordinate
vector is its Gauss atomic rule. This is a measure identity, not only polynomial
moment matching. Source: Gautschi (2004), Corollary to Theorem 3.1.
atlas: discrete-measure-jacobi-matrix (partial) -/
theorem spectralMeasure_T_first_eq_sum_dirac
    {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ} (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (hq : 0 < q) :
    spectralMeasure (D.isHermitian_T hA) (Pi.single ⟨0, hq⟩ ‖WithLp.toLp 2 b‖) =
      ∑ i : Fin q, ENNReal.ofReal ((b ⬝ᵥ b) *
        ((D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩) ^ 2) •
        Measure.dirac ((D.isHermitian_T hA).eigenvalues i) := by
  unfold spectralMeasure
  apply Finset.sum_congr rfl
  intro i _
  rw [dotProduct_single, mul_pow, norm_toLp_sq_eq_dotProduct_self]
  congr 2
  ring

end NLAlib
