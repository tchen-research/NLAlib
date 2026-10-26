import NLAlib.Matrix.Spectral.RestrictedInvertibilityScalar
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Exact stable-rank lower-barrier parameters

The real parameter `ε` and natural floor are kept exact. The terminal barrier
is at least `(1-ε)²F/M`, while each selected nonzero eigenvalue remains strictly
above that barrier. Source: Spielman--Srivastava (2009), Theorem 2.
-/

noncomputable section

namespace NLAlib.RestrictedInvertibility

/-- The initial weighted potential is exactly its lower-barrier budget for
the stable-rank parameters. -/
theorem neg_div_initial_barrier_eq {F Λ M ε : ℝ}
    (hF : 0 < F) (hΛ : 0 < Λ) (hM : 0 < M) (_hε : 0 < ε) (hε1 : ε < 1) :
    -F / ((1 - ε) * F / M) = -M - Λ / ((1 - ε) * Λ / (ε * M)) := by
  have hne : 1 - ε ≠ 0 := ne_of_gt (sub_pos.mpr hε1)
  field_simp [ne_of_gt hF, ne_of_gt hΛ, ne_of_gt hM, ne_of_gt _hε, hne]
  ring

/-- The exact floor of the stable-rank budget fits strictly below the initial
barrier and leaves the asserted strict endpoint available. -/
theorem floor_mul_decrement_lt_and_terminal_barrier_le {F Λ M ε : ℝ}
    (hF : 0 < F) (hΛ : 0 < Λ) (hM : 0 < M) (hε : 0 < ε) (hε1 : ε < 1) :
    let b₀ := (1 - ε) * F / M
    let δ := (1 - ε) * Λ / (ε * M)
    let k := ⌊ε ^ 2 * F / Λ⌋₊
    (k : ℝ) * δ < b₀ ∧ (1 - ε) ^ 2 * F / M ≤ b₀ - (k : ℝ) * δ := by
  let b₀ := (1 - ε) * F / M
  let δ := (1 - ε) * Λ / (ε * M)
  let k := ⌊ε ^ 2 * F / Λ⌋₊
  have hb₀ : 0 < b₀ := by dsimp [b₀]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hk : (k : ℝ) ≤ ε ^ 2 * F / Λ := Nat.floor_le (by positivity)
  have hkb : (k : ℝ) * δ ≤ ε * b₀ := by
    calc
      _ ≤ (ε ^ 2 * F / Λ) * δ := mul_le_mul_of_nonneg_right hk hδ.le
      _ = ε * b₀ := by
        dsimp [δ, b₀]
        field_simp
  have heq : (1 - ε) ^ 2 * F / M = (1 - ε) * b₀ := by dsimp [b₀]; ring
  refine ⟨hkb.trans_lt ?_, ?_⟩
  · nlinarith
  · rw [heq]
    linarith

end NLAlib.RestrictedInvertibility
