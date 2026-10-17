import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Separating finite upper-half-plane clusters by a circle

A circle tangent to the real axis can enclose any prescribed finite set of
upper-half-plane points. Upper hemicontinuity preserves the selection locally
for a finite spectrum disjoint from the real axis. Individual roots need not
be labelled or distinct.
-/

noncomputable section

open Complex Set Metric Filter
open scoped Topology

namespace Complex

/-- A circle tangent to the real axis lies entirely in the open upper
half-plane. The squared-norm criterion also gives an explicit enclosure test. -/
theorem dist_mul_I_lt_iff {z : ℂ} {r : ℝ} (hr : 0 < r) :
    dist z ((r : ℂ) * I) < r ↔ ‖z‖ ^ 2 < 2 * r * z.im := by
  have heq : dist z ((r : ℂ) * I) ^ 2 = ‖z‖ ^ 2 + r ^ 2 - 2 * r * z.im := by
    simp only [dist_eq_norm, Complex.sq_norm, normSq_apply, sub_re, sub_im,
      mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  constructor
  · intro h
    nlinarith [sq_nonneg (‖z‖), dist_nonneg (x := z) (y := (r : ℂ) * I)]
  · intro h
    nlinarith [dist_nonneg (x := z) (y := (r : ℂ) * I)]

/-- Every point of a circle tangent from above has positive imaginary part. -/
theorem im_pos_of_dist_mul_I_lt {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : dist z ((r : ℂ) * I) < r) : 0 < z.im := by
  have h := (dist_mul_I_lt_iff hr).mp hz
  nlinarith [sq_nonneg ‖z‖]

/-- One tangent circle selects exactly the upper-half-plane points of any
finite set. The real-axis points, if present, lie outside the open circle. -/
theorem exists_pos_dist_mul_I_lt_iff_im_pos (s : Finset ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ s, dist z ((r : ℂ) * I) < r ↔ 0 < z.im := by
  let f : ℂ → ℝ := fun z => ‖z‖ ^ 2 / (2 * |z.im|)
  let r := 1 + ∑ z ∈ s, f z
  have hf (z : ℂ) : 0 ≤ f z := div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))
  have hsum : 0 ≤ ∑ z ∈ s, f z := Finset.sum_nonneg (fun z _ => hf z)
  have hr : 0 < r := by dsimp [r]; linarith
  refine ⟨r, hr, fun z hz => ⟨im_pos_of_dist_mul_I_lt hr, fun hzim => ?_⟩⟩
  apply (dist_mul_I_lt_iff hr).mpr
  have hterm : f z ≤ ∑ z ∈ s, f z := Finset.single_le_sum (fun z _ => hf z) hz
  have hquot : ‖z‖ ^ 2 / (2 * z.im) < r := by
    have heq : f z = ‖z‖ ^ 2 / (2 * z.im) := by dsimp [f]; rw [abs_of_pos hzim]
    rw [heq] at hterm
    dsimp [r]
    linarith
  have h := (div_lt_iff₀ (by positivity : 0 < 2 * z.im)).mp hquot
  nlinarith

/-- An upper hemicontinuous finite cluster avoiding the real axis has one
locally valid circle selecting precisely its upper points. The same circle
also avoids every nearby cluster point, including repeated spectral roots. -/
theorem exists_tangent_circle_eventually_mem_iff_im_pos
    {α : Type*} [TopologicalSpace α] {F : α → Set ℂ} {a : α}
    (hF : UpperHemicontinuousAt F a) (hfin : (F a).Finite)
    (hreal : ∀ z ∈ F a, z.im ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ x in 𝓝 a, ∀ z ∈ F x,
      (dist z ((r : ℂ) * I) < r ↔ 0 < z.im) ∧ dist z ((r : ℂ) * I) ≠ r := by
  classical
  obtain ⟨r, hr, hsel⟩ := exists_pos_dist_mul_I_lt_iff_im_pos hfin.toFinset
  let U : Set ℂ := ball ((r : ℂ) * I) r ∪ {z : ℂ | z.im < 0}
  have hopen : IsOpen U := isOpen_ball.union (isOpen_lt continuous_im continuous_const)
  have hcover : F a ⊆ U := by
    intro z hz
    by_cases hpos : 0 < z.im
    · exact Or.inl ((hsel z (hfin.mem_toFinset.mpr hz)).mpr hpos)
    · exact Or.inr (lt_of_le_of_ne (le_of_not_gt hpos) (hreal z hz))
  have hnear : ∀ᶠ x in 𝓝 a, F x ⊆ U := by
    filter_upwards [hF U (hopen.mem_nhdsSet.mpr hcover)] with x hx
    exact subset_of_mem_nhdsSet hx
  refine ⟨r, hr, ?_⟩
  filter_upwards [hnear] with x hx z hz
  have hzU := hx hz
  refine ⟨⟨im_pos_of_dist_mul_I_lt hr, ?_⟩, ?_⟩
  · intro hpos
    rcases hzU with hball | hneg
    · exact hball
    · exact False.elim (not_lt_of_ge hpos.le hneg)
  · intro heq
    rcases hzU with hball | hneg
    · exact ne_of_lt hball heq
    · have him : |z.im - r| ≤ dist z ((r : ℂ) * I) := by
        simpa [dist_eq_norm] using abs_im_le_norm (z - (r : ℂ) * I)
      have habs' := neg_le_abs (z.im - r)
      rw [heq] at him
      change z.im < 0 at hneg
      linarith

end Complex
