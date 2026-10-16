import NLAlib.Polynomial.BestApproximation.OddMinimax
/-!+# Positive interval images of odd minimax updates

A linear competitor makes every positive-interval minimax error less than
one. Its image is therefore positive. Optimal scalar rescaling centers
the image at one, including singleton intervals.
-/
noncomputable section
open Polynomial Finset Set
namespace NLAlib

/-- The constant-plus-odd coefficient convention includes every linear update. -/
theorem oddScalarUpdate_single_zero (q : ℕ) (t x : ℝ) :
    oddScalarUpdate q (Pi.single 0 t) x = t * x := by
  unfold oddScalarUpdate
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0; simp [Pi.single_apply, hj0]
  · simp

/-- Scaling a positive interval to be centered at one has exact uniform
relative-width error. The estimate also holds for singleton intervals. -/
theorem abs_one_sub_two_div_mul_le {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hx : x ∈ Icc a b) :
    |1 - (2 / (a + b)) * x| ≤ (b - a) / (a + b) := by
  have hs : 0 < a + b := by linarith
  have hlo : 1 - (b - a) / (a + b) = (2 / (a + b)) * a := by field_simp; ring
  have hhi : 1 + (b - a) / (a + b) = (2 / (a + b)) * b := by field_simp; ring
  have hca : (2 / (a + b)) * a ≤ (2 / (a + b)) * x :=
    mul_le_mul_of_nonneg_left hx.1 (by positivity)
  have hcb : (2 / (a + b)) * x ≤ (2 / (a + b)) * b :=
    mul_le_mul_of_nonneg_left hx.2 (by positivity)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Every genuine positive-interval odd minimax error is less than one. -/
theorem IsOddMinimaxOn.error_lt_one {q : ℕ} {c : ℕ → ℝ} {a b : ℝ}
    (h : IsOddMinimaxOn q c a b) (ha : 0 < a) (hab : a ≤ b) :
    oddUniformError q c a b < 1 := by
  have hs : 0 < a + b := by linarith
  have hr : 0 ≤ (b - a) / (a + b) := div_nonneg (sub_nonneg.mpr hab) hs.le
  have he : oddUniformError q (Pi.single 0 (2 / (a + b))) a b ≤ (b - a) / (a + b) := by
    apply oddUniformError_le_of_forall hr
    intro x hx
    rw [oddScalarUpdate_single_zero]
    exact abs_one_sub_two_div_mul_le ha hab hx
  exact ((h _).trans he).trans_lt ((div_lt_one hs).mpr (by linarith))

/-- Actual minimum and maximum values of a continuous interval update. -/
theorem exists_oddScalarUpdate_interval_bounds (q : ℕ) (c : ℕ → ℝ) {a b : ℝ}
    (hab : a ≤ b) :
    ∃ m M : ℝ, (∀ x ∈ Icc a b, m ≤ oddScalarUpdate q c x ∧ oddScalarUpdate q c x ≤ M) ∧
      (∃ x ∈ Icc a b, oddScalarUpdate q c x = m) ∧
      (∃ x ∈ Icc a b, oddScalarUpdate q c x = M) := by
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
    (continuous_oddScalarUpdate q c).continuousOn
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab)
    (continuous_oddScalarUpdate q c).continuousOn
  exact ⟨oddScalarUpdate q c x, oddScalarUpdate q c y,
    fun z hz => ⟨hmin hz, hmax hz⟩, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩

/-- A genuine minimax interval image is positive, centered at one, and
its uniform error equals one minus its lower endpoint. No strict-length
assumption is needed; a singleton minimax image is exactly `{1}`. -/
theorem IsOddMinimaxOn.interval_image_normalized {q : ℕ} {c : ℕ → ℝ} {a b m M : ℝ}
    (h : IsOddMinimaxOn q c a b) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x ∈ Icc a b, m ≤ oddScalarUpdate q c x ∧ oddScalarUpdate q c x ≤ M)
    (hm : ∃ x ∈ Icc a b, oddScalarUpdate q c x = m)
    (hM : ∃ x ∈ Icc a b, oddScalarUpdate q c x = M) :
    0 < m ∧ m ≤ M ∧ m + M = 2 ∧ oddUniformError q c a b = 1 - m := by
  obtain ⟨xm, hxm, hxmval⟩ := hm
  obtain ⟨xM, hxM, hxMval⟩ := hM
  have hem : |1 - m| ≤ oddUniformError q c a b := by
    simpa only [hxmval] using abs_one_sub_oddScalarUpdate_le q c a b xm hxm
  have heM : |1 - M| ≤ oddUniformError q c a b := by
    simpa only [hxMval] using abs_one_sub_oddScalarUpdate_le q c a b xM hxM
  have hE := h.error_lt_one ha hab
  have hmpos : 0 < m := by have hh := (abs_le.mp hem).2; linarith
  have hmM : m ≤ M := by simpa only [hxmval] using (hbounds xm hxm).2
  have hs : 0 < m + M := by linarith
  have hscaled : oddUniformError q (fun j => (2 / (m + M)) * c j) a b ≤
      (M - m) / (m + M) := by
    apply oddUniformError_le_of_forall (div_nonneg (sub_nonneg.mpr hmM) hs.le)
    intro x hx
    rw [oddScalarUpdate_smul_coeff]
    exact abs_one_sub_two_div_mul_le hmpos hmM (hbounds x hx)
  have hratio : oddUniformError q c a b * (m + M) ≤ M - m :=
    (le_div_iff₀ hs).mp ((h _).trans hscaled)
  have hcenter : m + M = 2 := by
    rcases lt_trichotomy (m + M) 2 with hlt | heq | hgt
    · have hlo : 1 - m ≤ oddUniformError q c a b := (le_abs_self _).trans hem
      have hh := mul_le_mul_of_nonneg_right hlo hs.le
      nlinarith
    · exact heq
    · have hhi : M - 1 ≤ oddUniformError q c a b := by
        have hh := (neg_le_abs (1 - M)).trans heM
        linarith
      have hh := mul_le_mul_of_nonneg_right hhi hs.le
      have hMpos : 0 < M := hmpos.trans_le hmM
      nlinarith
  have hnorm : oddUniformError q c a b ≤ 1 - m := by
    apply oddUniformError_le_of_forall (by linarith)
    intro x hx
    obtain ⟨hlo, hhi⟩ := hbounds x hx
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact ⟨hmpos, hmM, hcenter, le_antisymm hnorm ((le_abs_self _).trans hem)⟩

end NLAlib
