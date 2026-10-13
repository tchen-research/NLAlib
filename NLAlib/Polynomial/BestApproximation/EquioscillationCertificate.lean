import NLAlib.Polynomial.BestApproximation.AlternationLowerBound

/-!
# Sufficient equioscillation certificates

The de la Vallée Poussin bound certifies optimality when the alternating sample errors
all have the full uniform-error magnitude. This file proves the certificate direction of
the Chebyshev alternation theorem, including zero error.
Source: Trefethen, ATAP, Theorem 10.1.
Atlas: `equioscillation` (sufficiency).
-/

noncomputable section

open Polynomial

namespace NLAlib

/-- Equal-magnitude alternating extrema certify a best degree-`n` polynomial.
Source: Trefethen, ATAP, Theorem 10.1, the sufficient direction. The sign is represented
by `|σ|=1`, equivalent to `σ∈{1,-1}`, and zero-error certificates are included.
atlas: equioscillation (partial) -/
theorem norm_sub_eq_minimaxError_of_equioscillation {s : Set ℝ} [CompactSpace s]
    {n : ℕ} (f : C(s, ℝ)) {p : ℝ[X]} (hp : p.degree ≤ n)
    {v : Fin (n + 2) → s} (hv : StrictMono (fun i => (v i : ℝ)))
    {σ : ℝ} (hσ : |σ| = 1)
    (hosc : ∀ i, f (v i) - p.eval (v i : ℝ) =
      σ * (-1) ^ (i : ℕ) * ‖f - p.toContinuousMapOn s‖) :
    ‖f - p.toContinuousMapOn s‖ = minimaxError n f := by
  have hupper := minimaxError_le_norm_sub f
    (mem_polynomialApproximationSpace_iff.mpr ⟨p, hp, rfl⟩)
  apply le_antisymm ?_ hupper
  by_cases hE : ‖f - p.toContinuousMapOn s‖ = 0
  · rw [hE]; exact minimaxError_nonneg n f
  · have hEpos : 0 < ‖f - p.toContinuousMapOn s‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hE)
    have habs : ∀ i, |f (v i) - p.eval (v i : ℝ)| = ‖f - p.toContinuousMapOn s‖ := by
      intro i
      rw [hosc, abs_mul, abs_mul, abs_pow, hσ]
      simp [abs_of_nonneg (norm_nonneg _)]
    apply le_minimaxError_of_alternation f hp hv ?_ (fun i => (habs i).ge)
    intro i
    have hnext : f (v i.succ) - p.eval (v i.succ : ℝ) =
        -(f (v i.castSucc) - p.eval (v i.castSucc : ℝ)) := by
      rw [hosc, hosc]
      simp only [Fin.val_succ, Fin.val_castSucc, pow_succ]
      ring
    have hne : f (v i.castSucc) - p.eval (v i.castSucc : ℝ) ≠ 0 := by
      intro hzero
      have := habs i.castSucc
      rw [hzero, abs_zero] at this
      linarith
    rw [hnext]
    nlinarith [sq_pos_of_ne_zero hne]

end NLAlib
