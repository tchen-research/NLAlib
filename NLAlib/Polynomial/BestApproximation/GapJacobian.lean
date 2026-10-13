import NLAlib.Polynomial.BestApproximation.GapRank
import NLAlib.Polynomial.BestApproximation.InterpolationPeakDerivatives
import NLAlib.Polynomial.BestApproximation.NodeSimplex
import NLAlib.ForMathlib.Algebra.OrderedNodalProducts

/-!
# The actual node-to-peak Jacobian

The coordinate derivatives of the actual gap peaks factor into nonzero nodal row and column
scalings of the divided-derivative evaluation matrix. Every maximal minor is nonsingular.
Source: focused rederivations, `polyretry:peak-jacobian`.
-/

noncomputable section

open Polynomial Matrix Finset Set

namespace NLAlib

/-- The explicit actual peak Jacobian, using canonical nodal products and barycentric weights.
Source: focused rederivations, `polyretry:peak-jacobian`. -/
def interpolationGapJacobian (n : ℕ) (t : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin n) ℝ :=
  fun i j => (Lagrange.nodal univ (canonicalIntervalNodes n t)).eval (interpolationGapCriticalPoint n t i) *
    Lagrange.nodalWeight univ (canonicalIntervalNodes n t) j.castSucc.succ *
      (interpolationGapDividedDerivative n t i).eval (t j)

/-- The nodal row factor of the actual peak Jacobian is nonzero.
Source: the actual critical point lies strictly inside its own node gap. -/
theorem eval_nodal_interpolationGapCriticalPoint_ne_zero {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    (Lagrange.nodal univ (canonicalIntervalNodes n t)).eval (interpolationGapCriticalPoint n t i) ≠ 0 :=
  eval_nodal_in_gap_ne_zero ht i (interpolationGapCriticalPoint_spec hn ht i).1

/-- The explicit factored peak Jacobian equals the exact derivative of the nodal equations.
Source: the cardinal barycentric formula and critical-factor identity. -/
theorem interpolationGapJacobian_eq_nodal_derivative {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) (j : Fin n) :
    interpolationGapJacobian n t i j = -(interpolationGapPolynomial n t i).derivative.eval (t j) *
      (Lagrange.basis univ (canonicalIntervalNodes n t) j.castSucc.succ).eval
        (interpolationGapCriticalPoint n t i) := by
  let τ := interpolationGapCriticalPoint n t i
  have hnon : τ ≠ canonicalIntervalNodes n t j.castSucc.succ := by
    intro heq
    have hω := eval_nodal_interpolationGapCriticalPoint_ne_zero hn ht i
    rw [show interpolationGapCriticalPoint n t i = canonicalIntervalNodes n t j.castSucc.succ from heq,
      Lagrange.eval_nodal_at_node (mem_univ _)] at hω
    exact hω rfl
  rw [Lagrange.eval_basis_not_at_node (mem_univ _) hnon]
  have hf := congrArg (fun p : ℝ[X] => p.eval (t j)) (mul_interpolationGapDividedDerivative hn ht i)
  simp only [eval_mul, eval_sub, eval_X, eval_C] at hf
  rw [← hf, canonicalIntervalNodes_interior]
  dsimp [interpolationGapJacobian]
  change _ = -((t j - τ) * (interpolationGapDividedDerivative n t i).eval (t j)) *
    ((Lagrange.nodal univ (canonicalIntervalNodes n t)).eval τ *
      (Lagrange.nodalWeight univ (canonicalIntervalNodes n t) j.castSucc.succ * (τ - t j)⁻¹))
  have hneq : τ - t j ≠ 0 := sub_ne_zero.mpr (by simpa only [canonicalIntervalNodes_interior] using hnon)
  field_simp
  ring

/-- The explicit actual Jacobian rows are the Frechet derivatives of the actual gap peaks.
Source: the smooth implicit peak chart and exact nodal derivative. -/
theorem hasFDerivAt_interpolationGapPeak_jacobian {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (i : Fin (n + 1)) :
    HasFDerivAt (fun s => interpolationGapPeak n s i)
      (∑ j : Fin n, interpolationGapJacobian n t i j •
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) t := by
  simp_rw [interpolationGapJacobian_eq_nodal_derivative hn ht i]
  exact hasFDerivAt_interpolationGapPeak hn ht i

/-- Every actual peak-Jacobian maximal minor is nonsingular.
Source: nonzero diagonal scalings of the actual divided-derivative evaluation matrix.
atlas: lebesgue-constant-lower-bound (partial) -/
theorem det_interpolationGapJacobian_minor_ne_zero {n : ℕ} (hn : 0 < n) {t : Fin n → ℝ}
    (ht : t ∈ interiorNodeSimplex n) (k : Fin (n + 1)) :
    ((interpolationGapJacobian n t).submatrix k.succAbove id).det ≠ 0 := by
  let R : Fin n → ℝ := fun i =>
    (Lagrange.nodal univ (canonicalIntervalNodes n t)).eval (interpolationGapCriticalPoint n t (k.succAbove i))
  let Cw : Fin n → ℝ := fun j => Lagrange.nodalWeight univ (canonicalIntervalNodes n t) j.castSucc.succ
  let Q : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    (interpolationGapDividedDerivative n t (k.succAbove i)).eval (t j)
  have htinj : Function.Injective t := by
    intro i j hij
    apply Fin.ext
    have hnodes : canonicalIntervalNodes n t i.castSucc.succ = canonicalIntervalNodes n t j.castSucc.succ := by
      simpa only [canonicalIntervalNodes_interior] using hij
    have heq := ht.injective hnodes
    have hval := congrArg Fin.val heq
    simp only [Fin.val_succ, Fin.val_castSucc] at hval
    omega
  have hQ : Q.det ≠ 0 := det_gapDirection_eval_ne_zero hn ht k t htinj
  have hR : (∏ i, R i) ≠ 0 := prod_ne_zero_iff.mpr fun i hi =>
    eval_nodal_interpolationGapCriticalPoint_ne_zero hn ht _
  have hC : (∏ j, Cw j) ≠ 0 := prod_ne_zero_iff.mpr fun j hj =>
    Lagrange.nodalWeight_ne_zero ht.injective.injOn (mem_univ _)
  have hmatrix : (interpolationGapJacobian n t).submatrix k.succAbove id =
      Matrix.diagonal R * Q * Matrix.diagonal Cw := by
    ext i j
    simp only [submatrix_apply, id_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
    dsimp [interpolationGapJacobian, R, Q, Cw]
    ring
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  exact mul_ne_zero (mul_ne_zero hR hQ) hC

end NLAlib
