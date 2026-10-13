import NLAlib.Polynomial.BestApproximation.RootSamples
import NLAlib.ForMathlib.Analysis.CotangentSamples
import NLAlib.ForMathlib.Analysis.CotangentLogLower

/-! # Sharp lower witnesses in every Chebyshev-root gap

Finite cotangent prefix symmetry and convexity show that every extremum sample
exceeds the exact universal logarithmic constant. Each sample lies in its own
consecutive-root interval.
-/
noncomputable section
open Real Set Polynomial Polynomial.Chebyshev Finset
namespace NLAlib

/-- The actual Chebyshev-root extremum sample equals its finite cotangent prefix.
Source: focused reroutes, equation `polyretry:sample-C`. -/
theorem lebesgueFunction_chebyshevZero_eq_rootCotangentSample {N k : ℕ}
    (hk0 : 0 < k) (hkN : k < N) :
    lebesgueFunction (chebyshevZero N) (cos ((k : ℝ) * π / N)) = rootCotangentSample N k := by
  have hN : 0 < N := by omega
  rw [lebesgueFunction_chebyshevZero_cos_nat_mul_pi_div hN]
  have heq : (∑ j : Fin N, sin (((j : ℝ) + 1 / 2) * π / N) /
      |cos ((k : ℝ) * π / N) - cos (((j : ℝ) + 1 / 2) * π / N)|) =
      ∑ j ∈ range N, sin (((j : ℝ) + 1 / 2) * π / N) /
        |cos ((k : ℝ) * π / N) - cos (((j : ℝ) + 1 / 2) * π / N)| := by
    rw [sum_fin_eq_sum_range]
    apply sum_congr rfl
    intro j hj
    rw [dif_pos (mem_range.mp hj)]
  rw [heq]
  exact sum_sin_div_abs_cos_sub_eq_rootCotangentSample hk0 hkN

/-- Every interior Chebyshev-root extremum sample exceeds the sharp universal
logarithmic constant. Source: focused reroutes, equation `polyretry:all-intervals`. -/
theorem logarithmic_lower_lt_lebesgueFunction_chebyshevZero_sample {N k : ℕ}
    (hN : 2 ≤ N) (hk0 : 1 ≤ k) (hkN : k < N) :
    (2 / π) * (log (N : ℝ) + eulerMascheroniConstant + log (4 / π)) <
      lebesgueFunction (chebyshevZero N) (cos ((k : ℝ) * π / N)) := by
  have h := logarithmic_lower_lt_central_cotangent_sum hN
  rw [← rootCotangentSample_center_eq hN] at h
  rw [lebesgueFunction_chebyshevZero_eq_rootCotangentSample (show 0 < k by omega) hkN]
  exact h.trans_le (rootCotangentSample_center_le hN hk0 hkN)

/-- The `k`th sampling extremum lies strictly between its consecutive Chebyshev roots.
Source: the explicit cosine grid and strict cosine monotonicity. -/
theorem cos_nat_mul_pi_div_mem_chebyshevZero_gap {N k : ℕ} (hk0 : 1 ≤ k) (hkN : k < N) :
    cos ((k : ℝ) * π / N) ∈
      Ioo (chebyshevZero N ⟨k, hkN⟩) (chebyshevZero N ⟨k - 1, by omega⟩) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkNR : (k : ℝ) < N := by exact_mod_cast hkN
  have hφ : (k : ℝ) * π / N ∈ Icc 0 π := by
    constructor
    · positivity
    · rw [div_le_iff₀ hNR]
      nlinarith [pi_pos]
  have hθ := chebyshev_root_angle_mem_Ioo (⟨k, hkN⟩ : Fin N)
  have hprev := chebyshev_root_angle_mem_Ioo (⟨k - 1, by omega⟩ : Fin N)
  rw [chebyshevZero_eq_cos_half_index, chebyshevZero_eq_cos_half_index]
  constructor
  · apply strictAntiOn_cos hφ ⟨hθ.1.le, hθ.2.le⟩
    rw [div_lt_div_iff_of_pos_right hNR]
    dsimp only
    nlinarith [pi_pos]
  · apply strictAntiOn_cos ⟨hprev.1.le, hprev.2.le⟩ hφ
    rw [div_lt_div_iff_of_pos_right hNR]
    simp only [Nat.cast_sub hk0, Nat.cast_one]
    nlinarith [pi_pos]

/-- Each consecutive Chebyshev-root gap has a strict logarithmic lower witness.
Source: focused reroutes, equation `polyretry:all-intervals`. This finite certificate
is the reference-grid input to the arbitrary-node peak comparison. -/
theorem exists_mem_chebyshevZero_gap_logarithmic_lower_lt {N k : ℕ} (hN : 2 ≤ N)
    (hk0 : 1 ≤ k) (hkN : k < N) :
    ∃ x ∈ Ioo (chebyshevZero N ⟨k, hkN⟩) (chebyshevZero N ⟨k - 1, by omega⟩),
      (2 / π) * (log (N : ℝ) + eulerMascheroniConstant + log (4 / π)) <
        lebesgueFunction (chebyshevZero N) x := by
  exact ⟨cos ((k : ℝ) * π / N), cos_nat_mul_pi_div_mem_chebyshevZero_gap hk0 hkN,
    logarithmic_lower_lt_lebesgueFunction_chebyshevZero_sample hN hk0 hkN⟩

end NLAlib
