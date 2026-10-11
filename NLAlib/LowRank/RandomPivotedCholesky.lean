import NLAlib.LowRank.CholeskyHistories
import NLAlib.LowRank.TraceDrift
import NLAlib.LowRank.TracePotential
import NLAlib.Matrix.TraceTail

/-!
# Expected relative trace error of randomly pivoted Cholesky

The actual finite adaptive pivot process supplies the PSD invariant, one-step
trace mean, sorted-tail energy bound, finite Jensen recursion, and scalar potential.
The source's relative optimal tail and additive tolerance are kept distinct.
Source: CETW (2025); manuscript `sa:rp-theorem`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The exact Cholesky approximation after a finite adaptive pivot history.
Source: manuscript `sa:rp-update`, `Ahat_t = A - R_t`. -/
def randomizedCholeskyApproximation (A : Matrix n n ℝ) (t : ℕ) (h : Fin t → n) :
    Matrix n n ℝ := A - choleskyResidualHistory A t h

/-- The relative optimal trace tail is the spectral tail divided by the full trace.
Source: manuscript `sa:rp-theorem`, its relative parameter `eta`. -/
def relativeSpectralTraceTail (A : Matrix n n ℝ) (hA : A.IsHermitian) (r : ℕ) : ℝ :=
  spectralTraceTail A hA r / A.trace

/-- The actual adaptive expected trace obeys the source's nonlinear relative-tail
recursion. Source: manuscript `sa:rp-recursion`; CETW (2025).
All matrix and probability inequalities are derived from the input PSD matrix.
atlas: rpcholesky (partial) -/
theorem choleskyExpectedTrace_succ_le_traceExcessDrift
    {A : Matrix n n ℝ} (hA : A.PosSemidef) {r : ℕ} (hr : 1 ≤ r) (t : ℕ) :
    choleskyExpectedTrace A (t + 1) ≤ choleskyExpectedTrace A t -
      traceExcessDrift (spectralTraceTail A hA.isHermitian r) (choleskyExpectedTrace A t) / r := by
  let τ := spectralTraceTail A hA.isHermitian r
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hstep : ∀ h : Fin t → n,
      (choleskyResidualHistory A t h).trace -
        (choleskyResidualHistory A t h * choleskyResidualHistory A t h).trace /
          (choleskyResidualHistory A t h).trace ≤
      (choleskyResidualHistory A t h).trace -
        traceExcessDrift τ (choleskyResidualHistory A t h).trace / r := by
    intro h
    let R := choleskyResidualHistory A t h
    have hR := posSemidef_choleskyResidualHistory hA t h
    have hAR := posSemidef_sub_choleskyResidualHistory hA t h
    have he := sq_max_trace_sub_spectralTraceTail_le_mul_trace_sq hA hR hAR r
    have hd : (max (R.trace - τ) 0) ^ 2 / r ≤ (R * R).trace :=
      (div_le_iff₀ hr0).mpr (by simpa only [mul_comm] using he)
    have htr : 0 ≤ R.trace := Finset.sum_nonneg fun j _ => hR.diag_nonneg
    have hdiv : traceExcessDrift τ R.trace / r ≤ (R * R).trace / R.trace := by
      rw [traceExcessDrift, div_right_comm]
      exact div_le_div_of_nonneg_right hd htr
    exact sub_le_sub_left hdiv R.trace
  have he : choleskyExpectedTrace A (t + 1) ≤
      ∑ h : Fin t → n, choleskyHistoryWeight A t h *
        ((choleskyResidualHistory A t h).trace -
          traceExcessDrift τ (choleskyResidualHistory A t h).trace / r) := by
    rw [choleskyExpectedTrace_succ_eq hA t]
    exact Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hstep h)
      (choleskyHistoryWeight_nonneg hA t h)
  simp only [mul_sub, Finset.sum_sub_distrib, ← mul_div_assoc, ← Finset.sum_div] at he
  have hj := traceExcessDrift_sum_le_sum (choleskyHistoryWeight A t)
    (fun h => (choleskyResidualHistory A t h).trace)
    (choleskyHistoryWeight_nonneg hA t)
    (fun h => Finset.sum_nonneg fun j _ => (posSemidef_choleskyResidualHistory hA t h).diag_nonneg)
    (sum_choleskyHistoryWeight A t) (spectralTraceTail_nonneg hA r)
  have hJ := div_le_div_of_nonneg_right hj hr0.le
  change choleskyExpectedTrace A (t + 1) ≤ choleskyExpectedTrace A t -
    (∑ h : Fin t → n, choleskyHistoryWeight A t h * traceExcessDrift τ
      (choleskyResidualHistory A t h).trace) / r at he
  change traceExcessDrift τ (choleskyExpectedTrace A t) / r ≤ _ at hJ
  exact he.trans (sub_le_sub_left hJ _)

/-- The actual RPCholesky expected trace reaches the precise relative-error target
under the manuscript's logarithmic pivot budget. Source: manuscript `sa:rp-theorem`;
CETW (2025). This is the positive-tail real-matrix branch, with all positive tolerances.
atlas: rpcholesky (partial) -/
theorem choleskyExpectedTrace_le_mul_spectralTraceTail
    {A : Matrix n n ℝ} (hA : A.PosSemidef) {r k : ℕ} (hr : 1 ≤ r)
    (hτ : 0 < spectralTraceTail A hA.isHermitian r) {ε : ℝ} (hε : 0 < ε)
    (hbudget : (r : ℝ) / ε + r * Real.log (A.trace / (ε * spectralTraceTail A hA.isHermitian r)) ≤ k) :
    choleskyExpectedTrace A k ≤ (1 + ε) * spectralTraceTail A hA.isHermitian r := by
  apply le_mul_tail_of_traceExcessDrift_recursion (choleskyExpectedTrace A)
    (choleskyExpectedTrace_antitone hA) hτ (by exact_mod_cast (by omega : 0 < r)) hε
    (fun t => choleskyExpectedTrace_succ_le_traceExcessDrift hA hr t) k
  simpa only [choleskyExpectedTrace_zero] using hbudget

/-- The relative parameter is exactly `eta = tau_*/tr A`, with the source's budget
`r/epsilon + r log(1/(epsilon eta))`. Source: manuscript `sa:rp-theorem`; CETW (2025).
It is not interpreted as an additive error tolerance.
atlas: rpcholesky (partial) -/
theorem choleskyExpectedTrace_le_of_relativeSpectralTraceTail
    {A : Matrix n n ℝ} (hA : A.PosSemidef) {r k : ℕ} (hr : 1 ≤ r)
    (hτ : 0 < spectralTraceTail A hA.isHermitian r) {ε : ℝ} (hε : 0 < ε)
    (hbudget : (r : ℝ) / ε + r * Real.log (1 / (ε * relativeSpectralTraceTail A hA.isHermitian r)) ≤ k) :
    choleskyExpectedTrace A k ≤ (1 + ε) * spectralTraceTail A hA.isHermitian r := by
  have htr : 0 < A.trace := hτ.trans_le (spectralTraceTail_le_trace hA r)
  have he : 1 / (ε * relativeSpectralTraceTail A hA.isHermitian r) =
      A.trace / (ε * spectralTraceTail A hA.isHermitian r) := by
    unfold relativeSpectralTraceTail
    field_simp
  apply choleskyExpectedTrace_le_mul_spectralTraceTail hA hr hτ hε
  simpa only [he] using hbudget

/-- An additive tolerance has its own scale-correct pivot budget, distinct from the
relative optimal tail parameter. Source: manuscript `sa:rp-theorem`, additive corollary.
atlas: rpcholesky (partial) -/
theorem choleskyExpectedTrace_le_mul_spectralTraceTail_add
    {A : Matrix n n ℝ} (hA : A.PosSemidef) {r k : ℕ} (hr : 1 ≤ r)
    (hτ : 0 < spectralTraceTail A hA.isHermitian r) {ε h : ℝ} (hε : 0 < ε) (hh : 0 < h)
    (hbudget : (r : ℝ) * spectralTraceTail A hA.isHermitian r /
        (ε * spectralTraceTail A hA.isHermitian r + h) +
      r * Real.log (A.trace / (ε * spectralTraceTail A hA.isHermitian r + h)) ≤ k) :
    choleskyExpectedTrace A k ≤ (1 + ε) * spectralTraceTail A hA.isHermitian r + h := by
  let τ := spectralTraceTail A hA.isHermitian r
  have heps : 0 < ε + h / τ := add_pos hε (div_pos hh hτ)
  have hmul : (ε + h / τ) * τ = ε * τ + h := by
    rw [add_mul, div_mul_cancel₀ _ hτ.ne']
  have hdiv : (r : ℝ) / (ε + h / τ) = r * τ / (ε * τ + h) := by
    have hsum : 0 < ε * τ + h := add_pos (mul_pos hε hτ) hh
    apply (div_eq_div_iff heps.ne' hsum.ne').mpr
    rw [← hmul]
    ring
  have hB : (r : ℝ) / (ε + h / τ) + r * Real.log (A.trace / ((ε + h / τ) * τ)) ≤ k := by
    rw [hdiv, hmul]
    exact hbudget
  have hC := choleskyExpectedTrace_le_mul_spectralTraceTail hA hr hτ heps hB
  have hR : (1 + (ε + h / τ)) * τ = (1 + ε) * τ + h := by
    calc (1 + (ε + h / τ)) * τ = τ + (ε + h / τ) * τ := by ring
      _ = _ := by rw [hmul]; ring
  exact hC.trans_eq hR

omit [Nonempty n] in
/-- A zero optimal trace tail yields exact RPCholesky expected trace after at most
the target rank pivots, including a rank-zero input. Source: manuscript `sa:rp-theorem`.
atlas: rpcholesky (partial) -/
theorem choleskyExpectedTrace_eq_zero_of_spectralTraceTail_eq_zero
    {A : Matrix n n ℝ} (hA : A.PosSemidef) {r k : ℕ}
    (ht : spectralTraceTail A hA.isHermitian r = 0) (hk : r ≤ k) :
    choleskyExpectedTrace A k = 0 :=
  choleskyExpectedTrace_eq_zero_of_rank_le hA ((rank_le_of_spectralTraceTail_eq_zero hA ht).trans hk)

omit [Nonempty n] in
/-- The expected trace of the actual approximation error equals the expected residual
trace used in the bounds. Source: manuscript `sa:rp-update`, definition of `Ahat_t`. -/
theorem sum_choleskyHistoryWeight_mul_trace_sub_approximation_eq
    (A : Matrix n n ℝ) (t : ℕ) :
    (∑ h : Fin t → n, choleskyHistoryWeight A t h *
      (A - randomizedCholeskyApproximation A t h).trace) = choleskyExpectedTrace A t := by
  apply Finset.sum_congr rfl
  intro h _
  have he : A - randomizedCholeskyApproximation A t h = choleskyResidualHistory A t h := by
    unfold randomizedCholeskyApproximation
    abel
  rw [he]

end NLAlib
