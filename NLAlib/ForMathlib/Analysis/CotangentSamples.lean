import NLAlib.ForMathlib.Analysis.CotangentPrefix

/-! # Finite sine-distance and cotangent sample identities

The elementary cosine-difference identity converts the actual root-grid
cardinal samples into finite cotangent prefixes.
-/
noncomputable section
open Real Set Finset
namespace NLAlib

/-- Cotangent is odd.
Source: the elementary sine and cosine negation identities. -/
theorem cot_neg (x : ℝ) : Real.cot (-x) = -Real.cot x := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, cos_neg, sin_neg, div_neg]

/-- The sine-over-cosine-difference kernel is a sum of two half-angle cotangents.
Source: focused reroutes, the identity preceding equation `polyretry:sample-C`. -/
theorem sin_div_cos_sub_eq_half_cot_add {θ φ : ℝ}
    (hm : sin ((θ - φ) / 2) ≠ 0) (hp : sin ((θ + φ) / 2) ≠ 0) :
    sin θ / (cos φ - cos θ) =
      (Real.cot ((θ - φ) / 2) + Real.cot ((θ + φ) / 2)) / 2 := by
  have hden : cos φ - cos θ = 2 * sin ((θ - φ) / 2) * sin ((θ + φ) / 2) := by
    rw [cos_sub_cos]
    have harg : (φ - θ) / 2 = -((θ - φ) / 2) := by ring
    rw [harg, sin_neg]
    have hadd : (φ + θ) / 2 = (θ + φ) / 2 := by ring
    rw [hadd]
    ring
  have hnum : sin θ = cos ((θ - φ) / 2) * sin ((θ + φ) / 2) +
      cos ((θ + φ) / 2) * sin ((θ - φ) / 2) := by
    nth_rw 1 [show θ = (θ - φ) / 2 + (θ + φ) / 2 by ring]
    rw [sin_add]
    ring
  rw [hden, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  have hfrac (a b c d s : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hs : s = c * b + d * a) :
      s / (2 * a * b) = (c / a + d / b) / 2 := by
    field_simp [ha, hb]
    linarith
  exact hfrac _ _ _ _ _ hm hp hnum

/-- Below a sampling extremum, the absolute sine-distance kernel has a cotangent
difference. Source: focused reroutes, finite root sample splitting. -/
theorem sin_div_abs_cos_sub_of_lt {θ φ : ℝ} (hθ : θ ∈ Ioo 0 π) (hφ : φ ∈ Ioo 0 π)
    (hlt : θ < φ) :
    sin θ / |cos φ - cos θ| =
      (Real.cot ((φ - θ) / 2) - Real.cot ((θ + φ) / 2)) / 2 := by
  have hcos : cos φ < cos θ := strictAntiOn_cos ⟨hθ.1.le, hθ.2.le⟩ ⟨hφ.1.le, hφ.2.le⟩ hlt
  have hp : sin ((θ + φ) / 2) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, hφ.1]) (by linarith [hθ.2, hφ.2])).ne'
  have hmpos : 0 < sin ((φ - θ) / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hφ.2, hθ.1, pi_pos])
  have hm : sin ((θ - φ) / 2) ≠ 0 := by
    rw [show (θ - φ) / 2 = -((φ - θ) / 2) by ring, sin_neg]
    exact neg_ne_zero.mpr hmpos.ne'
  rw [abs_of_neg (sub_neg.mpr hcos), div_neg, sin_div_cos_sub_eq_half_cot_add hm hp,
    show (θ - φ) / 2 = -((φ - θ) / 2) by ring, cot_neg]
  ring

/-- Above a sampling extremum, the absolute sine-distance kernel has a cotangent
sum. Source: focused reroutes, finite root sample splitting. -/
theorem sin_div_abs_cos_sub_of_gt {θ φ : ℝ} (hθ : θ ∈ Ioo 0 π) (hφ : φ ∈ Ioo 0 π)
    (hlt : φ < θ) :
    sin θ / |cos φ - cos θ| =
      (Real.cot ((θ - φ) / 2) + Real.cot ((θ + φ) / 2)) / 2 := by
  have hcos : cos θ < cos φ := strictAntiOn_cos ⟨hφ.1.le, hφ.2.le⟩ ⟨hθ.1.le, hθ.2.le⟩ hlt
  have hp : sin ((θ + φ) / 2) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, hφ.1]) (by linarith [hθ.2, hφ.2])).ne'
  have hm : sin ((θ - φ) / 2) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2, hφ.1, pi_pos])).ne'
  rw [abs_of_pos (sub_pos.mpr hcos), sin_div_cos_sub_eq_half_cot_add hm hp]

/-- The finite root-grid sine-distance sum is exactly its cotangent prefix sample.
Source: focused reroutes, equation `polyretry:sample-C`. -/
theorem sum_sin_div_abs_cos_sub_eq_rootCotangentSample {N k : ℕ}
    (hk0 : 0 < k) (hkN : k < N) :
    (1 / (N : ℝ)) * (∑ j ∈ range N,
      sin (((j : ℝ) + 1 / 2) * π / N) /
        |cos ((k : ℝ) * π / N) - cos (((j : ℝ) + 1 / 2) * π / N)|) =
          rootCotangentSample N k := by
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hkNR : (k : ℝ) < N := by exact_mod_cast hkN
  let f := fun j : ℕ => Real.cot (((j : ℝ) + 1 / 2) * π / (2 * N))
  let G := fun j : ℕ => sin (((j : ℝ) + 1 / 2) * π / N) /
    |cos ((k : ℝ) * π / N) - cos (((j : ℝ) + 1 / 2) * π / N)|
  have hφ : (k : ℝ) * π / N ∈ Ioo 0 π := by
    constructor
    · positivity
    · rw [div_lt_iff₀ hNR]
      nlinarith [pi_pos]
  have hθ (j : ℕ) (hj : j < N) : ((j : ℝ) + 1 / 2) * π / N ∈ Ioo 0 π := by
    have hjR : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
    constructor
    · positivity
    · rw [div_lt_iff₀ hNR]
      nlinarith [pi_pos]
  have hfirst (j : ℕ) (hj : j < k) : G j = (f (k - 1 - j) - f (k + j)) / 2 := by
    have hjR : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
    have hlt : ((j : ℝ) + 1 / 2) * π / N < (k : ℝ) * π / N := by
      rw [div_lt_div_iff_of_pos_right hNR]
      nlinarith [pi_pos]
    dsimp only [G]
    rw [sin_div_abs_cos_sub_of_lt (hθ j (hj.trans hkN)) hφ hlt]
    dsimp [f]
    congr 2
    · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring_nf
    · push_cast
      ring_nf
  have hsecond (j : ℕ) (hj : j < N - k) : G (k + j) = (f j + f (2 * k + j)) / 2 := by
    have hjN : k + j < N := by omega
    have hlt : (k : ℝ) * π / N < (((k + j : ℕ) : ℝ) + 1 / 2) * π / N := by
      rw [div_lt_div_iff_of_pos_right hNR]
      push_cast
      nlinarith [pi_pos, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    dsimp only [G]
    rw [sin_div_abs_cos_sub_of_gt (hθ _ hjN) hφ hlt]
    dsimp [f]
    congr 2 <;> push_cast <;> ring_nf
  have hA : (∑ j ∈ range k, G j) =
      (2 * rootCotangentPrefix N k - rootCotangentPrefix N (2 * k)) / 2 := by
    have heq : (∑ j ∈ range k, G j) = ∑ j ∈ range k, (f (k - 1 - j) - f (k + j)) / 2 :=
      sum_congr rfl (fun j hj => hfirst j (mem_range.mp hj))
    rw [heq]
    rw [← sum_div, sum_sub_distrib, sum_range_reflect]
    have hsplit := sum_range_add f k k
    change rootCotangentPrefix N (k + k) = rootCotangentPrefix N k + ∑ j ∈ range k, f (k + j) at hsplit
    rw [show k + k = 2 * k by omega] at hsplit
    change (rootCotangentPrefix N k - ∑ j ∈ range k, f (k + j)) / 2 = _
    congr 1
    linarith
  have hB : (∑ j ∈ range (N - k), G (k + j)) =
      (rootCotangentPrefix N (N - k) + rootCotangentPrefix N (N + k) - rootCotangentPrefix N (2 * k)) / 2 := by
    have heq : (∑ j ∈ range (N - k), G (k + j)) = ∑ j ∈ range (N - k), (f j + f (2 * k + j)) / 2 :=
      sum_congr rfl (fun j hj => hsecond j (mem_range.mp hj))
    rw [heq]
    rw [← sum_div, sum_add_distrib]
    have hsplit := sum_range_add f (2 * k) (N - k)
    change rootCotangentPrefix N (2 * k + (N - k)) = rootCotangentPrefix N (2 * k) +
      ∑ j ∈ range (N - k), f (2 * k + j) at hsplit
    rw [show 2 * k + (N - k) = N + k by omega] at hsplit
    change (rootCotangentPrefix N (N - k) + ∑ j ∈ range (N - k), f (2 * k + j)) / 2 = _
    congr 1
    linarith
  have href : rootCotangentPrefix N (N + k) = rootCotangentPrefix N (N - k) := by
    have h := rootCotangentPrefix_reflect hN (show N - k ≤ 2 * N by omega)
    rw [show 2 * N - (N - k) = N + k by omega] at h
    exact h
  change (1 / (N : ℝ)) * ∑ j ∈ range N, G j = _
  have hsplit : (∑ j ∈ range N, G j) = (∑ j ∈ range k, G j) + ∑ j ∈ range (N - k), G (k + j) := by
    simpa only [Nat.add_sub_of_le hkN.le] using sum_range_add G k (N - k)
  rw [hsplit, hA, hB, href]
  unfold rootCotangentSample
  ring

end NLAlib
