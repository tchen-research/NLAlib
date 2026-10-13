import NLAlib.Matrix.Factorizations.GramColumnExchange
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import NLAlib.Matrix.Norms.Core

/-!
# The shared maximum-volume exchange budget

Summing the exact column exchanges preserves the interpolation and residual
terms together, giving the sharp `k(n-k)` budget required by strong RRQR.
Gu–Eisenstat 1996, Theorem 3.2; derivations §alg:rrqr.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- A maximum-volume selection bounds each interpolation entry and, jointly,
the interpolation Frobenius square plus the inverse-Gram trace times the
projResidual Frobenius square. The columns of `D` are perpendicular to `C` and
`C T + D` are the columns offered for exchange. Gu–Eisenstat 1996,
Theorem 3.2; derivations equations alg:swap and alg:rrqr-budget.
Supports `rank-revealing-qr`. -/
theorem frobSq_add_trace_inv_gram_mul_frobSq_le_of_maximum_volume
    {m p q : Type*} [Fintype m] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq p] [DecidableEq q]
    (C : Matrix m p ℝ) (T : Matrix p q ℝ) (D : Matrix m q ℝ)
    (hC : 0 < (Cᵀ * C).det) (hOrth : Cᵀ * D = 0)
    (hMax : ∀ i j, ((C.updateCol i ((C * T + D).col j))ᵀ *
      C.updateCol i ((C * T + D).col j)).det ≤ (Cᵀ * C).det) :
    (∀ i j, |T i j| ≤ 1) ∧
      frobSq T + (Cᵀ * C)⁻¹.trace * frobSq D ≤ (Fintype.card p : ℝ) * Fintype.card q := by
  have hUnit : IsUnit (Cᵀ * C).det := isUnit_iff_ne_zero.mpr hC.ne'
  have hPSD : (Cᵀ * C)⁻¹.PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self C).inv
  have hEntry (i : p) (j : q) :
      T i j ^ 2 + (∑ a, D a j ^ 2) * (Cᵀ * C)⁻¹ i i ≤ 1 := by
    have hd : Cᵀ *ᵥ D.col j = 0 := by
      have hh := congrArg (fun M : Matrix p q ℝ => M.col j) hOrth
      exact hh
    have hReplace : C *ᵥ T.col j + D.col j = (C * T + D).col j := rfl
    have hx := det_gram_updateCol_eq_det_mul C hUnit i (T.col j) (D.col j) hd
    rw [hReplace] at hx
    have hle := hMax i j
    rw [hx] at hle
    have he := (mul_le_mul_iff_right₀ hC).mp (show
        (Cᵀ * C).det * (T.col j i ^ 2 + (D.col j ⬝ᵥ D.col j) * (Cᵀ * C)⁻¹ i i) ≤
          (Cᵀ * C).det * 1 by simpa only [mul_one] using hle)
    simpa only [Matrix.col, Matrix.transpose_apply, dotProduct, pow_two] using he
  constructor
  · intro i j
    have hn : 0 ≤ (∑ a, D a j ^ 2) * (Cᵀ * C)⁻¹ i i :=
      mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hPSD.diag_nonneg
    have he := hEntry i j
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  · have hsum : (∑ i : p, ∑ j : q,
        (T i j ^ 2 + (∑ a : m, D a j ^ 2) * (Cᵀ * C)⁻¹ i i)) ≤
        ∑ _i : p, ∑ _j : q, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hEntry i j
    have hD : (∑ j : q, ∑ a : m, D a j ^ 2) = frobSq D := by
      rw [frobSq_eq_sum_sq, Finset.sum_comm]
    have hCalc : (∑ i : p, ∑ j : q,
        (T i j ^ 2 + (∑ a : m, D a j ^ 2) * (Cᵀ * C)⁻¹ i i)) =
        frobSq T + (Cᵀ * C)⁻¹.trace * frobSq D := by
      rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib), Finset.sum_add_distrib,
        ← frobSq_eq_sum_sq]
      congr 1
      simp only [← Finset.sum_mul, hD]
      rw [← Finset.mul_sum]
      exact mul_comm _ _
    rw [hCalc] at hsum
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hsum

end NLAlib
