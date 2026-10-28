import NLAlib.Krylov.Solvers.GMRESCurveCompanion
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Greenbaum--Pták--Strakoš: any nonincreasing GMRES curve is possible

Every prescribed positive nonincreasing residual sequence and every prescribed
nonzero complex spectrum are realized by an explicit companion similarity.
The conclusion concerns the existing native complex GMRES minimizers and the
concrete pseudoinverse-based iterate; no residual polynomial or eigenvalue
realization is assumed.
Source: Greenbaum--Pták--Strakoš (1996), main theorem.
-/

noncomputable section
open scoped Matrix
open Polynomial Matrix Finset
namespace NLAlib

/-- Append a terminal zero to the finite positive prescribed curve. -/
def gmresCurveExtension {n : ℕ} (f : Fin n → ℝ) (j : ℕ) : ℝ :=
  if hj : j < n then f ⟨j,hj⟩ else 0

private theorem isUnit_of_charpoly_eq_product_nonzero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (ev : Fin n → ℂ) (hev : ∀ i, ev i ≠ 0)
    (hc : A.charpoly = ∏ i : Fin n, (X-C (ev i))) : IsUnit A := by
  apply (Matrix.isUnit_iff_isUnit_det A).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_eq_sign_charpoly_coeff,hc,coeff_zero_eq_eval_zero,eval_prod]
  apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simpa only [eval_sub,eval_X,eval_C,zero_sub] using neg_ne_zero.mpr (hev i)

/-- **Greenbaum--Pták--Strakoš.** Every positive nonincreasing finite curve and
every nonzero complex spectrum, with arbitrary multiplicities, occur together
for one invertible matrix. Every native GMRES minimizer from zero has the exact
prescribed residual norm. Stagnation and dimension one are included.
atlas: gmres-any-convergence-curve -/
theorem exists_matrix_gmres_any_convergence_curve {n : ℕ} (hn : 0 < n)
    (f : Fin n → ℝ) (hpos : ∀ i, 0 < f i) (hmono : Antitone f)
    (ev : Fin n → ℂ) (hev : ∀ i, ev i ≠ 0) :
    ∃ (A : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ),
      IsUnit A ∧ A.charpoly = ∏ i : Fin n, (X-C (ev i)) ∧
      ∀ (k : Fin n) (x : Fin n → ℂ), IsGMRESIterate A b 0 k.val x →
        ‖WithLp.toLp 2 (b-A *ᵥ x)‖ = f k := by
  let g := gmresCurveExtension f
  have hgn : g n = 0 := by simp [g,gmresCurveExtension]
  have hgp (j : ℕ) (hj : j < n) : 0 ≤ g j := by
    simpa only [g,gmresCurveExtension,dif_pos hj] using (hpos ⟨j,hj⟩).le
  have hgm (j : ℕ) (hj : j < n) : g (j+1) ≤ g j := by
    by_cases hnext : j+1 < n
    · simpa only [g,gmresCurveExtension,dif_pos hj,dif_pos hnext] using
        hmono (show (⟨j,hj⟩ : Fin n) ≤ ⟨j+1,hnext⟩ by exact_mod_cast Nat.le_succ j)
    · simp only [g,gmresCurveExtension,dif_pos hj,dif_neg hnext]
      exact (hpos ⟨j,hj⟩).le
  let b := gmresCurveVector g n
  have hb : b ⟨n-1,by omega⟩ ≠ 0 := by
    rw [show b ⟨n-1,by omega⟩ = (g (n-1) : ℂ) from
      gmresCurveVector_last hn g (hgp _ (by omega)) hgn]
    apply Complex.ofReal_ne_zero.mpr
    simpa only [g,gmresCurveExtension,dif_pos (show n-1<n by omega)] using
      (hpos (⟨n-1,by omega⟩ : Fin n)).ne'
  let A := gmresCurveMatrix hn b ev
  have hchar : A.charpoly = ∏ i : Fin n, (X-C (ev i)) :=
    charpoly_gmresCurveMatrix hn b hb ev
  refine ⟨A,b,isUnit_of_charpoly_eq_product_nonzero A ev hev hchar,hchar,?_⟩
  intro k x hx
  have hs := pow_succ_gmresCurveMatrix_mulVec hn b hb ev
  rw [hx.residual_eq_coordinate_tail k.isLt hs]
  have hnorm := norm_gmresCurveVector_tail g k.isLt hgp hgm hgn
  simpa only [b,g,gmresCurveExtension,dif_pos k.isLt] using hnorm

/-- The concrete native GMRES iterate realizes the entire requested convergence
curve, with exact prescribed complex characteristic polynomial.
atlas: gmres-any-convergence-curve -/
theorem exists_matrix_gmresIterate_any_convergence_curve {n : ℕ} (hn : 0 < n)
    (f : Fin n → ℝ) (hpos : ∀ i, 0 < f i) (hmono : Antitone f)
    (ev : Fin n → ℂ) (hev : ∀ i, ev i ≠ 0) :
    ∃ (A : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ),
      IsUnit A ∧ A.charpoly = ∏ i : Fin n, (X-C (ev i)) ∧
      ∀ k : Fin n, ‖WithLp.toLp 2 (b-A *ᵥ gmresIterate A b 0 k.val)‖ = f k := by
  obtain ⟨A,b,hA,hchar,hcurve⟩ := exists_matrix_gmres_any_convergence_curve hn f hpos hmono ev hev
  exact ⟨A,b,hA,hchar,fun k => hcurve k _ (isGMRESIterate_gmresIterate A b 0 k.val)⟩

end NLAlib
