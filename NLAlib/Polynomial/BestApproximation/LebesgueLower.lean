import NLAlib.Polynomial.BestApproximation.PeakComparison
import NLAlib.Polynomial.BestApproximation.RootReferenceGrid
import NLAlib.Polynomial.BestApproximation.EquispacedLebesgue

/-!
# Sharp universal and equispaced Lebesgue lower bounds

The actual global peak comparison and finite Chebyshev-root reference witnesses
give the precise logarithmic constant for every ordered interpolation grid.
The equispaced result retains its strict exponential bound.
Source: Trefethen, ATAP, Theorem 15.2; focused reroutes.
-/

noncomputable section

open Set Finset Real

namespace NLAlib

/-- Every nontrivial canonical node grid exceeds the sharp universal logarithmic
constant. Source: Bernstein–Erdős peak comparison and the finite reference-grid
cotangent bounds in the focused reroutes. -/
theorem logarithmic_lower_lt_lebesgueConstant_canonical {n : ℕ} (hn : 0 < n)
    {u : Fin n → ℝ} (hu : u ∈ interiorNodeSimplex n) :
    (2 / π) * (log (n + 2 : ℕ) + eulerMascheroniConstant + log (4 / π)) <
      lebesgueConstant (Icc (-1 : ℝ) 1) (canonicalIntervalNodes n u) := by
  obtain ⟨t, ht, _, hcompare⟩ := exists_equal_interpolation_peaks_with_convex_combination hn
  obtain ⟨r, hr, hlower⟩ := exists_canonical_reference_grid_logarithmic_lower_lt_peaks n
  obtain ⟨w, hw, hs, heq⟩ := hcompare r hr
  have hpositive : 0 < ∑ i, w i := by rw [hs]; norm_num
  obtain ⟨i, hi, hwi⟩ := (sum_pos_iff_of_nonneg (fun i _ => hw i)).mp hpositive
  have href : (2 / π) * (log (n + 2 : ℕ) + eulerMascheroniConstant + log (4 / π)) <
      interpolationGapPeak n t 0 := by
    rw [heq]
    calc
      _ = ∑ i, w i * ((2 / π) * (log (n + 2 : ℕ) + eulerMascheroniConstant + log (4 / π))) := by
        rw [← sum_mul, hs, one_mul]
      _ < _ := sum_lt_sum
        (fun j _ => mul_le_mul_of_nonneg_left (hlower j).le (hw j))
        ⟨i, hi, mul_lt_mul_of_pos_left (hlower i) hwi⟩
  obtain ⟨a, ha, has, heu⟩ := hcompare u hu
  have hpeak : ∀ i, interpolationGapPeak n u i ≤
      lebesgueConstant (Icc (-1 : ℝ) 1) (canonicalIntervalNodes n u) := by
    intro i
    exact lebesgueConstant_subset_le _
      (Icc_subset_Icc (canonicalIntervalNodes_mem_Icc hu i.castSucc).1
        (canonicalIntervalNodes_mem_Icc hu i.succ).2)
  apply href.trans_le
  rw [heu]
  calc
    _ ≤ ∑ i, a i * lebesgueConstant (Icc (-1 : ℝ) 1) (canonicalIntervalNodes n u) :=
      sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpeak i) (ha i))
    _ = _ := by rw [← sum_mul, has, one_mul]

/-- Every ordered grid with at least two nodes exceeds the sharp universal
logarithmic constant. Source: ATAP Theorem 15.2 and the canonical node-hull reduction. -/
theorem logarithmic_lower_lt_lebesgueConstant_ordered_add_two {n : ℕ}
    (v : Fin (n + 2) → ℝ) (hv : StrictMono v) (hvI : ∀ j, v j ∈ Icc (-1 : ℝ) 1) :
    (2 / π) * (log (n + 2 : ℕ) + eulerMascheroniConstant + log (4 / π)) <
      lebesgueConstant (Icc (-1 : ℝ) 1) v := by
  by_cases hn : 0 < n
  · obtain ⟨t, ht, hnorm⟩ := exists_canonical_nodes_le_lebesgueConstant v hv hvI
    exact (logarithmic_lower_lt_lebesgueConstant_canonical hn ht).trans_le hnorm
  · have hn0 : n = 0 := by omega
    subst n
    have hone : 1 ≤ lebesgueConstant (Icc (-1 : ℝ) 1) v :=
      (one_le_lebesgueFunction v hv.injective 0).trans
        (lebesgueFunction_le_lebesgueConstant v (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1))
    exact logarithmic_interpolation_lower_two_lt_one.trans_le hone

/-- The sharp logarithmic lower bound for every ordered interpolation grid,
including a single node. Source: ATAP Theorem 15.2.
atlas: lebesgue-constant-lower-bound (partial) -/
theorem logarithmic_lower_lt_lebesgueConstant_ordered {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hv : StrictMono v) (hvI : ∀ j, v j ∈ Icc (-1 : ℝ) 1) :
    (2 / π) * (log (n + 1 : ℕ) + eulerMascheroniConstant + log (4 / π)) <
      lebesgueConstant (Icc (-1 : ℝ) 1) v := by
  cases n with
  | zero =>
    have hone : 1 ≤ lebesgueConstant (Icc (-1 : ℝ) 1) v :=
      (one_le_lebesgueFunction v hv.injective 0).trans
        (lebesgueFunction_le_lebesgueConstant v (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1))
    simpa using logarithmic_interpolation_lower_one_lt_one.trans_le hone
  | succ n => exact logarithmic_lower_lt_lebesgueConstant_ordered_add_two v hv hvI

/-- The universal sharp logarithmic bound and strict equispaced exponential
bound, with their exact constants. Source: Trefethen, ATAP, Theorem 15.2,
equations (15.7) and (15.9); focused reroutes.
atlas: lebesgue-constant-lower-bound -/
theorem lebesgueConstant_logarithmic_and_equispaced_lower_bounds :
    (∀ (n : ℕ) (v : Fin (n + 1) → ℝ), StrictMono v →
      (∀ j, v j ∈ Icc (-1 : ℝ) 1) →
      (2 / π) * (log (n + 1 : ℕ) + eulerMascheroniConstant + log (4 / π)) <
        lebesgueConstant (Icc (-1 : ℝ) 1) v) ∧
    (∀ n : ℕ, 0 < n →
      (2 : ℝ) ^ n / (4 * (n : ℝ) ^ 2) <
        lebesgueConstant (Icc (-1 : ℝ) 1) (fun j : Fin (n + 1) => -1 + 2 * (j : ℝ) / n)) :=
  ⟨fun _ v hv hvI => logarithmic_lower_lt_lebesgueConstant_ordered v hv hvI,
    fun _ hn => pow_two_div_four_mul_sq_lt_lebesgueConstant_equispaced hn⟩

end NLAlib
