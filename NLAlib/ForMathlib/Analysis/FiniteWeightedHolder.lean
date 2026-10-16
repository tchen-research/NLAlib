import Mathlib.Analysis.MeanInequalities

/-! # Finite weighted Hölder inequality

The weights need not sum to one and may vanish. This is ordinary finite
Hölder after distributing the weight between the two factors.
-/

noncomputable section
namespace NLAlib

/-- Finite weighted Hölder, with arbitrary nonnegative weights. -/
theorem sum_mul_mul_le_rpow_sum_mul_rpow {ι : Type*} (s : Finset ι)
    (w f g : ι → ℝ) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∑ i ∈ s, w i * f i * g i) ≤
      (∑ i ∈ s, w i * f i ^ p) ^ (1 / p) *
        (∑ i ∈ s, w i * g i ^ q) ^ (1 / q) := by
  have hp := hpq.pos
  have hq := hpq.symm.pos
  have hsum : 1 / p + 1 / q = 1 := by simpa only [one_div] using hpq.inv_add_inv_eq_one
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq
    (f := fun i => w i ^ (1 / p) * f i)
    (g := fun i => w i ^ (1 / q) * g i)
    (fun i hi => mul_nonneg (Real.rpow_nonneg (hw i hi) _) (hf i hi))
    (fun i hi => mul_nonneg (Real.rpow_nonneg (hw i hi) _) (hg i hi))
  have hleft (i : ι) (hi : i ∈ s) :
      (w i ^ (1 / p) * f i) * (w i ^ (1 / q) * g i) = w i * f i * g i := by
    calc
      _ = (w i ^ (1 / p) * w i ^ (1 / q)) * f i * g i := by ring
      _ = _ := by rw [← Real.rpow_add' (hw i hi) (by positivity), hsum, Real.rpow_one]
  have hpow (i : ι) (hi : i ∈ s) (r : ℝ) (hr : 0 < r) (a : ℝ) (ha : 0 ≤ a) :
      (w i ^ (1 / r) * a) ^ r = w i * a ^ r := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i hi) _) ha,
      ← Real.rpow_mul (hw i hi), one_div_mul_cancel hr.ne', Real.rpow_one]
  simpa only [Finset.sum_congr rfl hleft,
    Finset.sum_congr rfl (fun i hi => hpow i hi p hp (f i) (hf i hi)),
    Finset.sum_congr rfl (fun i hi => hpow i hi q hq (g i) (hg i hi))] using h

end NLAlib
