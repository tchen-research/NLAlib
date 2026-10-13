import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cotangent monotonicity for sharp interpolation constants

The function `x cot x` decreases on the positive half quadrant. Consequently normalized
sine ratios increase, the scalar comparison underlying the exact Lobatto kernel maximum.
Source: focused polynomial-approximation rederivations, equation `eq:cotpair`.
-/

noncomputable section

open Real Set

namespace NLAlib

/-- The real cotangent has derivative `-1/sin²` away from sine zeros.
Source: the elementary quotient rule. -/
theorem hasDerivAt_cot {x : ℝ} (hx : sin x ≠ 0) :
    HasDerivAt Real.cot (-1 / (sin x) ^ 2) x := by
  have h := (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hx
  have heq : (-sin x * sin x - cos x * cos x) / sin x ^ 2 = -1 / sin x ^ 2 := by
    congr 1
    nlinarith [sin_sq_add_cos_sq x]
  exact (h.congr_deriv heq).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y => Real.cot_eq_cos_div_sin y))

/-- The derivative of `x cot x` in a nonsingular quadrant.
Source: the elementary product rule. -/
theorem hasDerivAt_mul_cot {x : ℝ} (hx : sin x ≠ 0) :
    HasDerivAt (fun t => t * Real.cot t) ((sin x * cos x - x) / (sin x) ^ 2) x := by
  have h := (hasDerivAt_id x).mul (hasDerivAt_cot hx)
  apply h.congr_deriv
  simp only [one_mul, id_eq, Real.cot_eq_cos_div_sin]
  field_simp
  ring

/-- `x cot x` decreases on the positive half quadrant, including its right endpoint.
Source: the sharp Lobatto-kernel comparison in equation `eq:cotpair`. -/
theorem antitoneOn_mul_cot : AntitoneOn (fun x => x * Real.cot x) (Ioc 0 (π / 2)) := by
  have hs : ∀ x ∈ Ioc (0 : ℝ) (π / 2), 0 < sin x := by
    intro x hx
    exact sin_pos_of_pos_of_lt_pi hx.1 (hx.2.trans_lt (by linarith [pi_pos]))
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 (π / 2))
    (fun x hx => (hasDerivAt_mul_cot (hs x hx).ne').continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_mul_cot (hs x (interior_subset hx)).ne').hasDerivWithinAt)
  intro x hx
  apply div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
  have hx' := interior_subset hx
  have hsc : sin x * cos x ≤ sin x := mul_le_of_le_one_right (hs x hx').le (cos_le_one x)
  have hsin : sin x ≤ x := Real.sin_le hx'.1.le
  linarith

/-- The ratio `sin(hs)/sin(ks)` increases in `s` when `0<h≤k≤π/2`.
Source: the scalar monotonicity argument in the sharp Lobatto-kernel comparison. -/
theorem monotoneOn_sin_mul_div_sin_mul {h k : ℝ} (hh : 0 < h) (hk : h ≤ k)
    (hkπ : k ≤ π / 2) :
    MonotoneOn (fun s => sin (h * s) / sin (k * s)) (Ioc 0 (1 / 2 : ℝ)) := by
  have hkpos : 0 < k := hh.trans_le hk
  have hargs : ∀ s ∈ Ioc (0 : ℝ) (1 / 2),
      h * s ∈ Ioc 0 (π / 2) ∧ k * s ∈ Ioc 0 (π / 2) := by
    intro s hs
    have hsone : s ≤ 1 := by linarith [hs.2]
    have hsh : h * s ≤ h := by nlinarith
    have hsk : k * s ≤ k := by nlinarith
    exact ⟨⟨mul_pos hh hs.1, hsh.trans (hk.trans hkπ)⟩,
      ⟨mul_pos hkpos hs.1, hsk.trans hkπ⟩⟩
  have hsine : ∀ s ∈ Ioc (0 : ℝ) (1 / 2), 0 < sin (h * s) ∧ 0 < sin (k * s) := by
    intro s hs
    obtain ⟨ha, hb⟩ := hargs s hs
    exact ⟨sin_pos_of_pos_of_lt_pi ha.1 (ha.2.trans_lt (by linarith [pi_pos])),
      sin_pos_of_pos_of_lt_pi hb.1 (hb.2.trans_lt (by linarith [pi_pos]))⟩
  let d := fun s =>
    (h * cos (h * s) * sin (k * s) - k * sin (h * s) * cos (k * s)) /
      (sin (k * s)) ^ 2
  have hderiv : ∀ s ∈ Ioc (0 : ℝ) (1 / 2),
      HasDerivAt (fun s => sin (h * s) / sin (k * s)) (d s) s := by
    intro s hs
    have hhder := (Real.hasDerivAt_sin (h * s)).comp s ((hasDerivAt_id s).const_mul h)
    have hkder := (Real.hasDerivAt_sin (k * s)).comp s ((hasDerivAt_id s).const_mul k)
    apply (hhder.div hkder (hsine s hs).2.ne').congr_deriv
    dsimp [d]
    ring
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 (1 / 2))
    (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hderiv s (interior_subset hs)).hasDerivWithinAt)
  intro s hs
  have hs' := interior_subset hs
  obtain ⟨ha, hb⟩ := hargs s hs'
  obtain ⟨haSin, hbSin⟩ := hsine s hs'
  have hanti := antitoneOn_mul_cot ha hb (mul_le_mul_of_nonneg_right hk hs'.1.le)
  simp only [Real.cot_eq_cos_div_sin, ← mul_div_assoc] at hanti
  rw [div_le_div_iff₀ hbSin haSin] at hanti
  have hnum : 0 ≤ h * cos (h * s) * sin (k * s) - k * sin (h * s) * cos (k * s) := by
    apply le_of_mul_le_mul_left (a := s) ?_ hs'.1
    nlinarith [hanti]
  exact div_nonneg hnum (sq_nonneg _)


/-- A normalized half-angle sine comparison, the quantitative core of the cotangent pairing.
Source: focused rederivations, equation `eq:cotpair`. -/
theorem sin_mul_sq_le_two_mul_sin_half_sq {h u s : ℝ} (hh : 0 < h)
    (hhπ : h ≤ π / 2) (hu : h / 2 ≤ u) (huπ : u ≤ π / 2)
    (hs : s ∈ Icc (0 : ℝ) (1 / 2)) :
    sin (h * s) ^ 2 ≤ 2 * sin (π * s / 2) ^ 2 * sin u ^ 2 := by
  by_cases hs0 : s = 0
  · simp [hs0]
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  have hsinhalf : 0 < sin (π / 4) := sin_pos_of_pos_of_lt_pi (by linarith [pi_pos])
    (by linarith [pi_pos])
  have hsinarg : 0 < sin (π / 2 * s) := sin_pos_of_pos_of_lt_pi
    (mul_pos (by linarith [pi_pos]) hspos) (by nlinarith [pi_pos, hs.2])
  have hm := monotoneOn_sin_mul_div_sin_mul hh hhπ le_rfl
    ⟨hspos, hs.2⟩ (by norm_num) hs.2
  have heq1 : h * (1 / 2 : ℝ) = h / 2 := by ring
  have heq2 : π / 2 * (1 / 2 : ℝ) = π / 4 := by ring
  dsimp only at hm
  rw [heq1, heq2, div_le_div_iff₀ hsinarg hsinhalf] at hm
  have hhs : 0 ≤ sin (h * s) := sin_nonneg_of_nonneg_of_le_pi
    (mul_nonneg hh.le hs.1) (by nlinarith [pi_pos, hs.2])
  have hhhalf : 0 ≤ sin (h / 2) := sin_nonneg_of_nonneg_of_le_pi
    (by linarith) (by linarith [pi_pos])
  have hsq := sq_le_sq₀ (mul_nonneg hhs hsinhalf.le)
    (mul_nonneg hhhalf hsinarg.le) |>.mpr hm
  have hhcmp : sin (h / 2) ≤ sin u := sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [pi_pos]) huπ hu
  have husin : 0 ≤ sin u := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
  have husq := sq_le_sq₀ hhhalf husin |>.mpr hhcmp
  have hhalfSq : sin (π / 4) ^ 2 = (1 / 2 : ℝ) := by
    rw [sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsq' : sin (h * s) ^ 2 / 2 ≤ sin (h / 2) ^ 2 * sin (π / 2 * s) ^ 2 := by
    simpa only [mul_pow, hhalfSq, mul_one_div] using hsq
  have harg : π / 2 * s = π * s / 2 := by ring
  rw [harg] at hsq'
  nlinarith [mul_le_mul_of_nonneg_right husq (sq_nonneg (sin (π * s / 2)))]

/-- The sine product identity used to pair cotangents about a midpoint.
Source: the elementary sine addition formulas. -/
theorem sin_add_mul_sin_sub (u v : ℝ) :
    sin (u + v) * sin (u - v) = sin u ^ 2 - sin v ^ 2 := by
  rw [sin_add, sin_sub]
  nlinarith [sin_sq_add_cos_sq u, sin_sq_add_cos_sq v,
    mul_nonneg (sq_nonneg (sin u)) (sq_nonneg (sin v))]

/-- Pairing equally spaced cotangents never exceeds the value at the central phase.
Source: focused rederivations, equation `eq:cotpair`. -/
theorem cos_mul_cot_pair_le {h u s : ℝ} (hh : 0 < h) (hhπ : h ≤ π / 2)
    (hu : h / 2 ≤ u) (huπ : u ≤ π / 2) (hs : s ∈ Ico (0 : ℝ) (1 / 2)) :
    cos (π * s) * (Real.cot (u + h * s) + Real.cot (u - h * s)) ≤ 2 * Real.cot u := by
  have hup : 0 < u + h * s := by nlinarith [hs.1]
  have hum : 0 < u - h * s := by nlinarith [hs.2]
  have hupπ : u + h * s < π := by nlinarith [hs.2, pi_pos]
  have humπ : u - h * s < π := by nlinarith [hs.1, pi_pos]
  have hp := sin_pos_of_pos_of_lt_pi hup hupπ
  have hm := sin_pos_of_pos_of_lt_pi hum humπ
  have husin : 0 < sin u := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hucos : 0 ≤ cos u := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], huπ⟩
  have hd : 0 < sin u ^ 2 - sin (h * s) ^ 2 := by
    rw [← sin_add_mul_sin_sub]
    exact mul_pos hp hm
  have hpair : Real.cot (u + h * s) + Real.cot (u - h * s) =
      (2 * sin u * cos u) / (sin u ^ 2 - sin (h * s) ^ 2) := by
    simp only [Real.cot_eq_cos_div_sin]
    rw [← sin_add_mul_sin_sub]
    field_simp
    rw [sin_add, sin_sub, cos_add, cos_sub]
    calc
      _ = 2 * sin u * cos u * (sin (h * s) ^ 2 + cos (h * s) ^ 2) := by ring
      _ = _ := by rw [sin_sq_add_cos_sq, mul_one]
  rw [hpair, Real.cot_eq_cos_div_sin, ← mul_div_assoc,
    ← mul_div_assoc, div_le_div_iff₀ hd husin]
  have hsin := sin_mul_sq_le_two_mul_sin_half_sq hh hhπ hu huπ ⟨hs.1, hs.2.le⟩
  have hcos : cos (π * s) = 1 - 2 * sin (π * s / 2) ^ 2 := by
    have h := cos_two_mul (π * s / 2)
    rw [show 2 * (π * s / 2) = π * s by ring] at h
    nlinarith [sin_sq_add_cos_sq (π * s / 2)]
  rw [hcos]
  have hbound := mul_le_mul_of_nonneg_left hsin (mul_nonneg (by positivity : (0 : ℝ) ≤ 2) hucos)
  nlinarith [hbound]



end NLAlib
