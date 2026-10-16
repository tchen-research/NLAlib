import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # Rigidity of a complex weighted average on a norm boundary

If positive weights sum to one and the average attains a common norm bound,
every summand equals the average. The proof is the finite variance identity.
-/

noncomputable section
open Finset
open ComplexConjugate
namespace Complex
variable {ι : Type*} [Fintype ι]

/-- Finite complex variance decomposition for real weights of total mass one. -/
theorem sum_weight_normSq_sub_average (w : ι → ℝ) (z : ι → ℂ)
    (hw : ∑ i, w i = 1) :
    let a : ℂ := ∑ i, (w i : ℂ) * z i
    (∑ i, w i * Complex.normSq (z i - a)) =
      (∑ i, w i * Complex.normSq (z i)) - Complex.normSq a := by
  dsimp only
  let a : ℂ := ∑ i, (w i : ℂ) * z i
  have hcross : (∑ i, w i * (z i * conj a).re) = Complex.normSq a := by
    calc
      _ = (∑ i, (w i : ℂ) * (z i * conj a)).re := by
        simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      _ = (a * conj a).re := by
        simp only [a, Finset.sum_mul, mul_assoc]
      _ = _ := by rw [Complex.mul_conj, Complex.ofReal_re]
  change (∑ i, w i * Complex.normSq (z i - a)) = _
  simp only [Complex.normSq_sub, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  have hconst : (∑ i, w i * Complex.normSq a) = Complex.normSq a := by rw [← Finset.sum_mul, hw, one_mul]
  have htwo : (∑ i, w i * (2 * (z i * conj a).re)) = 2 * Complex.normSq a := by
    rw [← hcross, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hconst, htwo]
  ring

/-- A positive weighted average can attain a common norm bound only when
every input is that average. This includes one summand and a zero norm bound. -/
theorem eq_average_of_norm_average_eq_bound (w : ι → ℝ) (z : ι → ℂ)
    (hw : ∀ i, 0 < w i) (hws : ∑ i, w i = 1) {M : ℝ} (hM : 0 ≤ M)
    (hz : ∀ i, ‖z i‖ ≤ M) (ha : ‖∑ i, (w i : ℂ) * z i‖ = M) :
    ∀ j, z j = ∑ i, (w i : ℂ) * z i := by
  classical
  let a : ℂ := ∑ i, (w i : ℂ) * z i
  have hvar := sum_weight_normSq_sub_average w z hws
  have hbudget : (∑ i, w i * Complex.normSq (z i)) ≤ M ^ 2 := by
    calc
      _ ≤ ∑ i, w i * M ^ 2 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (by
          rw [Complex.normSq_eq_norm_sq]
          exact (sq_le_sq₀ (norm_nonneg _) hM).mpr (hz i)) (hw i).le
      _ = M ^ 2 := by rw [← Finset.sum_mul, hws, one_mul]
  have hsum : (∑ i, w i * Complex.normSq (z i - a)) ≤ 0 := by
    rw [hvar, Complex.normSq_eq_norm_sq, ha]
    linarith
  intro j
  have hsingle := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_nonneg (hw i).le (Complex.normSq_nonneg (z i - a))) (mem_univ j)
  have hzero : Complex.normSq (z j - a) = 0 := by
    have hnonneg := Complex.normSq_nonneg (z j - a)
    nlinarith [hw j]
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hzero)

end Complex
