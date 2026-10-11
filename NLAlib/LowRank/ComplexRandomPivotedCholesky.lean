import NLAlib.LowRank.ComplexCholeskyHistories
import NLAlib.LowRank.TraceDrift
import NLAlib.LowRank.TracePotential
import NLAlib.Matrix.ComplexTraceTail

/-!
# Expected relative trace error of complex randomly pivoted Cholesky

The actual finite adaptive pivot process supplies the PSD invariant, one-step
trace mean, sorted-tail energy bound, finite Jensen recursion, and scalar potential.
The source's relative optimal tail and additive tolerance are kept distinct.
Source: CETW (2025); manuscript `sa:rp-theorem`.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The exact Cholesky approximation after a finite adaptive pivot history.
Source: manuscript `sa:rp-update`, `Ahat_t = A - R_t`. -/
def complexRandomizedCholeskyApproximation (A : Matrix n n ℂ) (t : ℕ) (h : Fin t → n) :
    Matrix n n ℂ := A - complexCholeskyResidualHistory A t h

/-- The relative optimal trace tail is the spectral tail divided by the full trace.
Source: manuscript `sa:rp-theorem`, its relative parameter `eta`. -/
def complexRelativeSpectralTraceTail (A : Matrix n n ℂ) (hA : A.IsHermitian) (r : ℕ) : ℝ :=
  complexSpectralTraceTail A hA r / A.trace.re

/-- The actual adaptive expected trace obeys the source's nonlinear relative-tail
recursion. Source: manuscript `sa:rp-recursion`; CETW (2025).
All matrix and probability inequalities are derived from the input PSD matrix.
atlas: rpcholesky (partial) -/
theorem complexCholeskyExpectedTrace_succ_le_traceExcessDrift
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {r : ℕ} (hr : 1 ≤ r) (t : ℕ) :
    complexCholeskyExpectedTrace A (t + 1) ≤ complexCholeskyExpectedTrace A t -
      traceExcessDrift (complexSpectralTraceTail A hA.isHermitian r) (complexCholeskyExpectedTrace A t) / r := by
  let τ := complexSpectralTraceTail A hA.isHermitian r
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hstep : ∀ h : Fin t → n,
      (complexCholeskyResidualHistory A t h).trace.re -
        (complexCholeskyResidualHistory A t h * complexCholeskyResidualHistory A t h).trace.re /
          (complexCholeskyResidualHistory A t h).trace.re ≤
      (complexCholeskyResidualHistory A t h).trace.re -
        traceExcessDrift τ (complexCholeskyResidualHistory A t h).trace.re / r := by
    intro h
    let R := complexCholeskyResidualHistory A t h
    have hR := posSemidef_complexCholeskyResidualHistory hA t h
    have hAR := posSemidef_sub_complexCholeskyResidualHistory hA t h
    have he := complex_sq_max_trace_sub_spectralTraceTail_le_mul_trace_sq hA hR hAR r
    have hd : (max (R.trace.re - τ) 0) ^ 2 / r ≤ (R * R).trace.re :=
      (div_le_iff₀ hr0).mpr (by simpa only [mul_comm] using he)
    have htr : 0 ≤ R.trace.re := re_trace_nonneg_of_complex_posSemidef hR
    have hdiv : traceExcessDrift τ R.trace.re / r ≤ (R * R).trace.re / R.trace.re := by
      rw [traceExcessDrift, div_right_comm]
      exact div_le_div_of_nonneg_right hd htr
    exact sub_le_sub_left hdiv R.trace.re
  have he : complexCholeskyExpectedTrace A (t + 1) ≤
      ∑ h : Fin t → n, complexCholeskyHistoryWeight A t h *
        ((complexCholeskyResidualHistory A t h).trace.re -
          traceExcessDrift τ (complexCholeskyResidualHistory A t h).trace.re / r) := by
    rw [complexCholeskyExpectedTrace_succ_eq hA t]
    exact Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hstep h)
      (complexCholeskyHistoryWeight_nonneg hA t h)
  simp only [mul_sub, Finset.sum_sub_distrib, ← mul_div_assoc, ← Finset.sum_div] at he
  have hj := traceExcessDrift_sum_le_sum (complexCholeskyHistoryWeight A t)
    (fun h => (complexCholeskyResidualHistory A t h).trace.re)
    (complexCholeskyHistoryWeight_nonneg hA t)
    (fun h => re_trace_nonneg_of_complex_posSemidef (posSemidef_complexCholeskyResidualHistory hA t h))
    (sum_complexCholeskyHistoryWeight A t) (complexSpectralTraceTail_nonneg hA r)
  have hJ := div_le_div_of_nonneg_right hj hr0.le
  change complexCholeskyExpectedTrace A (t + 1) ≤ complexCholeskyExpectedTrace A t -
    (∑ h : Fin t → n, complexCholeskyHistoryWeight A t h * traceExcessDrift τ
      (complexCholeskyResidualHistory A t h).trace.re) / r at he
  change traceExcessDrift τ (complexCholeskyExpectedTrace A t) / r ≤ _ at hJ
  exact he.trans (sub_le_sub_left hJ _)

/-- The actual RPCholesky expected trace reaches the precise relative-error target
under the manuscript's logarithmic pivot budget. Source: manuscript `sa:rp-theorem`;
CETW (2025). This is the positive-tail complex-matrix branch, with all positive tolerances.
atlas: rpcholesky (partial) -/
theorem complexCholeskyExpectedTrace_le_mul_complexSpectralTraceTail
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {r k : ℕ} (hr : 1 ≤ r)
    (hτ : 0 < complexSpectralTraceTail A hA.isHermitian r) {ε : ℝ} (hε : 0 < ε)
    (hbudget : (r : ℝ) / ε + r * Real.log (A.trace.re / (ε * complexSpectralTraceTail A hA.isHermitian r)) ≤ k) :
    complexCholeskyExpectedTrace A k ≤ (1 + ε) * complexSpectralTraceTail A hA.isHermitian r := by
  apply le_mul_tail_of_traceExcessDrift_recursion (complexCholeskyExpectedTrace A)
    (complexCholeskyExpectedTrace_antitone hA) hτ (by exact_mod_cast (by omega : 0 < r)) hε
    (fun t => complexCholeskyExpectedTrace_succ_le_traceExcessDrift hA hr t) k
  simpa only [complexCholeskyExpectedTrace_zero] using hbudget

/-- The relative parameter is exactly `eta = tau_*/tr A`, with the source's budget
`r/epsilon + r log(1/(epsilon eta))`. Source: manuscript `sa:rp-theorem`; CETW (2025).
It is not interpreted as an additive error tolerance.
atlas: rpcholesky (partial) -/
theorem complexCholeskyExpectedTrace_le_of_complexRelativeSpectralTraceTail
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {r k : ℕ} (hr : 1 ≤ r)
    (hτ : 0 < complexSpectralTraceTail A hA.isHermitian r) {ε : ℝ} (hε : 0 < ε)
    (hbudget : (r : ℝ) / ε + r * Real.log (1 / (ε * complexRelativeSpectralTraceTail A hA.isHermitian r)) ≤ k) :
    complexCholeskyExpectedTrace A k ≤ (1 + ε) * complexSpectralTraceTail A hA.isHermitian r := by
  have htr : 0 < A.trace.re := hτ.trans_le (complexSpectralTraceTail_le_trace hA r)
  have he : 1 / (ε * complexRelativeSpectralTraceTail A hA.isHermitian r) =
      A.trace.re / (ε * complexSpectralTraceTail A hA.isHermitian r) := by
    unfold complexRelativeSpectralTraceTail
    field_simp
  apply complexCholeskyExpectedTrace_le_mul_complexSpectralTraceTail hA hr hτ hε
  simpa only [he] using hbudget

/-- An additive tolerance has its own scale-correct pivot budget, distinct from the
relative optimal tail parameter. Source: manuscript `sa:rp-theorem`, additive corollary.
atlas: rpcholesky (partial) -/
theorem complexCholeskyExpectedTrace_le_mul_complexSpectralTraceTail_add
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {r k : ℕ} (hr : 1 ≤ r)
    (hτ : 0 < complexSpectralTraceTail A hA.isHermitian r) {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h)
    (hbudget : (r : ℝ) * complexSpectralTraceTail A hA.isHermitian r /
        (ε * complexSpectralTraceTail A hA.isHermitian r + h) +
      r * Real.log (A.trace.re / (ε * complexSpectralTraceTail A hA.isHermitian r + h)) ≤ k) :
    complexCholeskyExpectedTrace A k ≤ (1 + ε) * complexSpectralTraceTail A hA.isHermitian r + h := by
  let τ := complexSpectralTraceTail A hA.isHermitian r
  have heps : 0 < ε + h / τ := add_pos hε (div_pos hh hτ)
  have hmul : (ε + h / τ) * τ = ε * τ + h := by
    rw [add_mul, div_mul_cancel₀ _ hτ.ne']
  have hdiv : (r : ℝ) / (ε + h / τ) = r * τ / (ε * τ + h) := by
    have hsum : 0 < ε * τ + h := add_pos (mul_pos hε hτ) hh
    apply (div_eq_div_iff heps.ne' hsum.ne').mpr
    rw [← hmul]
    ring
  have hB : (r : ℝ) / (ε + h / τ) + r * Real.log (A.trace.re / ((ε + h / τ) * τ)) ≤ k := by
    rw [hdiv, hmul]
    exact hbudget
  have hC := complexCholeskyExpectedTrace_le_mul_complexSpectralTraceTail hA hr hτ heps hB
  have hR : (1 + (ε + h / τ)) * τ = (1 + ε) * τ + h := by
    calc (1 + (ε + h / τ)) * τ = τ + (ε + h / τ) * τ := by ring
      _ = _ := by rw [hmul]; ring
  exact hC.trans_eq hR

omit [Nonempty n] in
/-- A zero optimal trace tail yields exact RPCholesky expected trace after at most
the target rank pivots, including a rank-zero input. Source: manuscript `sa:rp-theorem`.
atlas: rpcholesky (partial) -/
theorem complexCholeskyExpectedTrace_eq_zero_of_complexSpectralTraceTail_eq_zero
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {r k : ℕ}
    (ht : complexSpectralTraceTail A hA.isHermitian r = 0) (hk : r ≤ k) :
    complexCholeskyExpectedTrace A k = 0 :=
  complexCholeskyExpectedTrace_eq_zero_of_rank_le hA ((complex_rank_le_of_spectralTraceTail_eq_zero hA ht).trans hk)

omit [Nonempty n] [DecidableEq n] in
/-- The expected trace of the actual approximation error equals the expected residual
trace used in the bounds. Source: manuscript `sa:rp-update`, definition of `Ahat_t`. -/
theorem sum_complexCholeskyHistoryWeight_mul_trace_sub_approximation_eq
    (A : Matrix n n ℂ) (t : ℕ) :
    (∑ h : Fin t → n, complexCholeskyHistoryWeight A t h *
      (A - complexRandomizedCholeskyApproximation A t h).trace.re) = complexCholeskyExpectedTrace A t := by
  apply Finset.sum_congr rfl
  intro h _
  have he : A - complexRandomizedCholeskyApproximation A t h = complexCholeskyResidualHistory A t h := by
    unfold complexRandomizedCholeskyApproximation
    abel
  rw [he]

/-- The actual complex RPCholesky expectation obeys the retained relative-tail
budget and the exact zero-tail endpoint. The relative parameter is exactly
`eta = tail/re(tr A)`, and every positive tolerance is allowed. Source: manuscript
`sa:rp-theorem`; audit Part VII; CETW (2025), the eta-dependent branch of Theorem 5.1.
No eta-independent alternative from the full paper is asserted here.
atlas: rpcholesky -/
theorem complexCholeskyExpectedTrace_le_of_relative_budget_or_zero_tail
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {r k : ℕ} (hr : 1 ≤ r)
    {ε : ℝ} (hε : 0 < ε)
    (hbudget : (0 < complexSpectralTraceTail A hA.isHermitian r ∧
      (r : ℝ) / ε + r * Real.log
        (1 / (ε * complexRelativeSpectralTraceTail A hA.isHermitian r)) ≤ k) ∨
      (complexSpectralTraceTail A hA.isHermitian r = 0 ∧ r ≤ k)) :
    complexCholeskyExpectedTrace A k ≤ (1 + ε) * complexSpectralTraceTail A hA.isHermitian r := by
  rcases hbudget with ⟨hτ, hb⟩ | ⟨hτ, hk⟩
  · exact complexCholeskyExpectedTrace_le_of_complexRelativeSpectralTraceTail hA hr hτ hε hb
  · rw [complexCholeskyExpectedTrace_eq_zero_of_complexSpectralTraceTail_eq_zero hA hτ hk,
      hτ, mul_zero]

end NLAlib
