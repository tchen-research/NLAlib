import NLAlib.Polynomial.BestApproximation.LobattoCardinals
import NLAlib.Polynomial.BestApproximation.LobattoKernelBound
import NLAlib.Polynomial.BestApproximation.InterpolationProjection

/-!
# The sharp logarithmic Lebesgue bound for Chebyshev interpolation

Interpolation at `cos(jπ/n)` has Lebesgue constant at most `1+(2/π)log(n+1)` and is
correspondingly near-best. Source: Trefethen, ATAP, Theorem 15.2; focused rederivations,
Theorem `thm:lobatto`.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Real Finset Set

namespace NLAlib

private theorem sum_range_endpoints {f : ℕ → ℝ} {n : ℕ} (hn : 0 < n) :
    (∑ j ∈ range (n + 1), f j) = f 0 + (∑ j ∈ range (n - 1), f (j + 1)) + f n := by
  rw [sum_range_succ]
  have hs : (∑ j ∈ range n, f j) = (∑ j ∈ range (n - 1), f (j + 1)) + f 0 := by
    simpa only [Nat.sub_add_cancel hn] using sum_range_succ' f (n - 1)
  rw [hs]
  ring

private theorem weighted_kernel_sum {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (∑ j ∈ range (n + 1), lobattoEndpointWeight n j *
      (|lobattoKernel n (t - j * π / n)| + |lobattoKernel n (t + j * π / n)|)) =
        lobattoKernelSum n t := by
  let f := fun j : ℕ => lobattoEndpointWeight n j *
    (|lobattoKernel n (t - j * π / n)| + |lobattoKernel n (t + j * π / n)|)
  have hf0 : f 0 = |lobattoKernel n t| := by dsimp [f, lobattoEndpointWeight]; simp; ring
  have hmidd : lobattoKernel n (t + π) = lobattoKernel n (t - π) := by
    have hp := lobattoKernel_periodic n (t - π)
    rw [show t - π + 2 * π = t + π by ring] at hp
    exact hp
  have hncast : (n : ℝ) ≠ 0 := by positivity
  have hfn : f n = |lobattoKernel n (t - π)| := by
    dsimp [f, lobattoEndpointWeight]
    simp only [or_true, ite_true, mul_div_cancel_left₀ π hncast, hmidd]
    ring
  have hfi : ∀ j ∈ range (n - 1), f (j + 1) =
      |lobattoKernel n (t - (j + 1 : ℕ) * π / n)| +
        |lobattoKernel n (t + (j + 1 : ℕ) * π / n)| := by
    intro j hj
    have hne : ¬(j + 1 = 0 ∨ j + 1 = n) := by have := mem_range.mp hj; omega
    dsimp only [f]
    rw [show lobattoEndpointWeight n (j + 1) = 1 from if_neg hne, one_mul]
  change (∑ j ∈ range (n + 1), f j) = _
  rw [sum_range_endpoints hn, hf0, hfn, sum_congr rfl hfi, sum_add_distrib,
    lobattoKernelSum_eq_paired hn]
  have hplus : (∑ j ∈ range n, |lobattoKernel n (t + j * π / n)|) =
      (∑ j ∈ range (n - 1), |lobattoKernel n (t + (j + 1 : ℕ) * π / n)|) + |lobattoKernel n t| := by
    simpa only [Nat.sub_add_cancel hn, Nat.cast_zero, zero_mul, zero_div, add_zero] using
      sum_range_succ' (fun j : ℕ => |lobattoKernel n (t + j * π / n)|) (n - 1)
  have hminus : (∑ j ∈ range n, |lobattoKernel n (t - (j + 1 : ℕ) * π / n)|) =
      (∑ j ∈ range (n - 1), |lobattoKernel n (t - (j + 1 : ℕ) * π / n)|) + |lobattoKernel n (t - π)| := by
    simpa only [Nat.sub_add_cancel hn, mul_div_cancel_left₀ π hncast] using
      sum_range_succ (fun j : ℕ => |lobattoKernel n (t - (j + 1 : ℕ) * π / n)|) (n - 1)
  rw [hplus, hminus]
  ring

/-- The canonical Chebyshev extrema, bundled in `[-1,1]` with finite indexing.
Source: Mathlib `Polynomial.Chebyshev.node`. -/
def chebyshevExtrema (n : ℕ) (j : Fin (n + 1)) : Icc (-1 : ℝ) 1 :=
  ⟨node n j, node_mem_Icc⟩

/-- Bundling the extrema does not change their injectivity.
Source: Mathlib `strictAntiOn_node`. -/
theorem injective_chebyshevExtrema (n : ℕ) : Function.Injective (chebyshevExtrema n) := by
  intro i j hij
  exact injective_chebyshev_extrema_fin n (congrArg Subtype.val hij)

/-- The Lobatto Lebesgue function is bounded by the translated finite angular kernel sum.
Source: the endpoint-half DCT cardinal expansion. -/
theorem lebesgueFunction_chebyshev_le_kernelSum {n : ℕ} (hn : 0 < n) (t : ℝ) :
    lebesgueFunction (fun j : Fin (n + 1) => node n j) (cos t) ≤ lobattoKernelSum n t := by
  unfold lebesgueFunction
  simp_rw [← lobattoCardinal_eq_basis_fin hn]
  rw [show (∑ j : Fin (n + 1), |(lobattoCardinal n j).eval (cos t)|) =
      ∑ j ∈ range (n + 1), |(lobattoCardinal n j).eval (cos t)| from
    Fin.sum_univ_eq_sum_range (fun j : ℕ => |(lobattoCardinal n j).eval (cos t)|) (n + 1)]
  have hpoint : ∀ j ∈ range (n + 1), |(lobattoCardinal n j).eval (cos t)| ≤
      lobattoEndpointWeight n j *
        (|lobattoKernel n (t - j * π / n)| + |lobattoKernel n (t + j * π / n)|) := by
    intro j hj
    rw [eval_lobattoCardinal_cos, abs_mul]
    have hw : 0 ≤ lobattoEndpointWeight n j := by unfold lobattoEndpointWeight; split_ifs <;> norm_num
    rw [abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hw
  exact (sum_le_sum hpoint).trans_eq (weighted_kernel_sum hn t)

/-- Interpolation at Chebyshev extrema has the sharp logarithmic pointwise Lebesgue bound.
Source: Trefethen, ATAP, Theorem 15.2; focused rederivations, Theorem `thm:lobatto`.
atlas: lebesgue-constant-chebyshev (partial) -/
theorem lebesgueFunction_chebyshev_le_log {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    lebesgueFunction (fun j : Fin (n + 1) => node n j) x ≤
      1 + (2 / π) * log ((n : ℝ) + 1) := by
  rw [← cos_arccos hx.1 hx.2]
  exact (lebesgueFunction_chebyshev_le_kernelSum hn (arccos x)).trans (lobattoKernelSum_le_log hn _)

/-- The Lebesgue constant of Chebyshev-extrema interpolation is at most `1+(2/π)log(n+1)`.
Source: Trefethen, ATAP, Theorem 15.2.
atlas: lebesgue-constant-chebyshev -/
theorem lebesgueConstant_chebyshev_le_log {n : ℕ} (hn : 0 < n) :
    lebesgueConstant (Icc (-1 : ℝ) 1) (fun j : Fin (n + 1) => node n j) ≤
      1 + (2 / π) * log ((n : ℝ) + 1) := by
  have hlog : 0 ≤ log ((n : ℝ) + 1) := log_nonneg (by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith)
  unfold lebesgueConstant
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖lebesgueFunction (fun j : Fin (n + 1) => node n j) (x : ℝ)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (lebesgueFunction_nonneg _ _)]
  exact lebesgueFunction_chebyshev_le_log hn x.property

/-- The Chebyshev-extrema interpolation operator has the sharp logarithmic norm bound.
Source: Trefethen, ATAP, Theorem 15.2.
atlas: lebesgue-constant-chebyshev -/
theorem norm_chebyshev_interpolationOperator_le_log {n : ℕ} (hn : 0 < n) :
    ‖interpolationOperator (chebyshevExtrema n)‖ ≤ 1 + (2 / π) * log ((n : ℝ) + 1) := by
  rw [norm_interpolationOperator_eq_lebesgueConstant _ (injective_chebyshevExtrema n)]
  exact lebesgueConstant_chebyshev_le_log hn

/-- Chebyshev interpolation is within `2+(2/π)log(n+1)` of best uniform degree-`n` approximation.
Source: Trefethen, ATAP, Theorem 15.2 with Theorem 15.1.
atlas: lebesgue-constant-chebyshev -/
theorem norm_sub_chebyshev_interpolation_le_minimaxError {n : ℕ} (hn : 0 < n)
    (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    ‖f - interpolationLinearMap (Icc (-1 : ℝ) 1) (chebyshevExtrema n) f‖ ≤
      (2 + (2 / π) * log ((n : ℝ) + 1)) * minimaxError n f := by
  have hnear := norm_sub_interpolationLinearMap_le_minimaxError (chebyshevExtrema n)
    (injective_chebyshevExtrema n) f
  simp only [Fintype.card_fin, Nat.add_sub_cancel] at hnear
  apply hnear.trans
  have hbound := lebesgueConstant_chebyshev_le_log hn
  have hB : 1 + lebesgueConstant (Icc (-1 : ℝ) 1) (fun i => (chebyshevExtrema n i : ℝ)) ≤
      2 + (2 / π) * log ((n : ℝ) + 1) := by
    change 1 + lebesgueConstant (Icc (-1 : ℝ) 1) (fun i : Fin (n + 1) => node n i) ≤ _
    linarith
  exact mul_le_mul_of_nonneg_right hB (minimaxError_nonneg n f)

end NLAlib
