/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.LowRank.Cholesky.HistoryDeterminant
import NLAlib.Matrix.Factorizations.EliminationTraceProduct
import NLAlib.Matrix.Spectral.PrincipalMinors
import Mathlib.MeasureTheory.Measure.Real
import NLAlib.ForMathlib.Combinatorics.ElementarySymmetricBounds

/-!
# Factorial trace tails for the actual RPCholesky process

The native adaptive history laws, chronological determinant telescope,
deterministic trace rank budget, and scalar subset counting give the
eta-independent tail. The nonstrict event requires positive optimal tail;
the strict event includes the zero-tail exact-termination endpoint.
Source: Epperly (2026), Theorem 1.2, with the corrected zero-tail endpoint
in the supplied `determinantal.tex`; atlas `rpcholesky-factorial-trace-tail`.
-/

noncomputable section
open MeasureTheory
open scoped Matrix ComplexOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
  [MeasurableSpace n] [MeasurableSingletonClass n]

/-- The eta-independent factorial RPCholesky trace-tail bound,
`min(1, k!/(k-r)! * (1+ε)^(-(k-r)))`. -/
def choleskyFactorialTraceTail (r k : ℕ) (ε : ℝ) : ℝ :=
  min 1 ((k.factorial : ℝ) / ((k - r).factorial * (1 + ε) ^ (k - r)))

private theorem measureReal_trace_ge_le_factorial_elementary_div
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) {k r : ℕ} (hrk : r ≤ k)
    (μ : Measure (Fin k → n)) [IsProbabilityMeasure μ]
    (hMass : ∀ h : Fin k → n,
      μ.real {h} * choleskyHistoryTraceProduct A h = RCLike.re (A.submatrix h h).det)
    (hτ : 0 < spectralTraceTail A hA.isHermitian r) {c : ℝ} (hc : 0 < c) :
    μ.real {h | c ≤ RCLike.re (eliminationListResidual A (List.ofFn h)).trace} ≤
      ((k.factorial : ℝ) *
        ∑ S ∈ (Finset.univ : Finset (Fin (Fintype.card n))).powersetCard k,
          ∏ i ∈ S, hA.isHermitian.eigenvalues₀ i) /
        ((∏ j : Fin r, spectralTraceTail A hA.isHermitian j) * c ^ (k - r)) := by
  classical
  let D := (∏ j : Fin r, spectralTraceTail A hA.isHermitian j) * c ^ (k - r)
  have hD : 0 < D := mul_pos
    (Finset.prod_pos fun j _ => hτ.trans_le (spectralTraceTail_antitone hA (by omega)))
    (pow_pos hc _)
  let E : Finset (Fin k → n) := Finset.univ.filter
    fun h => c ≤ RCLike.re (eliminationListResidual A (List.ofFn h)).trace
  have hSet : (E : Set (Fin k → n)) =
      {h | c ≤ RCLike.re (eliminationListResidual A (List.ofFn h)).trace} := by
    ext h
    simp [E]
  rw [← hSet, ← sum_measureReal_singleton]
  calc
    (∑ h ∈ E, μ.real {h}) ≤ ∑ h ∈ E, RCLike.re (A.submatrix h h).det / D := by
      apply Finset.sum_le_sum
      intro h hh
      have hLower : D ≤ choleskyHistoryTraceProduct A h := by
        simpa only [D, choleskyHistoryTraceProduct, List.length_ofFn] using
          prod_spectralTraceTail_mul_pow_le_eliminationTraceProduct hA (List.ofFn h)
            (by simpa only [List.length_ofFn] using hrk) hc.le (Finset.mem_filter.mp hh).2
      apply (le_div_iff₀ hD).mpr
      calc
        μ.real {h} * D ≤ μ.real {h} * choleskyHistoryTraceProduct A h :=
          mul_le_mul_of_nonneg_left hLower measureReal_nonneg
        _ = _ := hMass h
    _ = (∑ h ∈ E, RCLike.re (A.submatrix h h).det) / D := by rw [Finset.sum_div]
    _ ≤ (∑ h : Fin k → n, RCLike.re (A.submatrix h h).det) / D := by
      apply div_le_div_of_nonneg_right _ hD.le
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
      intro h _ _
      exact (RCLike.nonneg_iff.mp (hA.submatrix h).det_nonneg).1
    _ = _ := by rw [sum_re_det_submatrix_eq_factorial_mul_sum_prod_eigenvalues₀ hA.isHermitian]

private theorem measureReal_trace_ge_le_factorialTraceTail
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) {k r : ℕ} (hrk : r ≤ k)
    (μ : Measure (Fin k → n)) [IsProbabilityMeasure μ]
    (hMass : ∀ h : Fin k → n,
      μ.real {h} * choleskyHistoryTraceProduct A h = RCLike.re (A.submatrix h h).det)
    (hτ : 0 < spectralTraceTail A hA.isHermitian r) {ε : ℝ} (hε : 0 < ε) :
    μ.real {h | (1 + ε) * spectralTraceTail A hA.isHermitian r ≤
      RCLike.re (eliminationListResidual A (List.ofFn h)).trace} ≤
        choleskyFactorialTraceTail r k ε := by
  let τ := spectralTraceTail A hA.isHermitian r
  let T := ∏ j : Fin r, spectralTraceTail A hA.isHermitian j
  let E := ∑ S ∈ (Finset.univ : Finset (Fin (Fintype.card n))).powersetCard k,
    ∏ i ∈ S, hA.isHermitian.eigenvalues₀ i
  have hT : 0 < T := Finset.prod_pos fun j _ =>
    hτ.trans_le (spectralTraceTail_antitone hA (by omega))
  have hOne : 0 < 1 + ε := by linarith
  have hc : 0 < (1 + ε) * τ := mul_pos hOne hτ
  have hDen : 0 < T * ((1 + ε) * τ) ^ (k - r) := mul_pos hT (pow_pos hc _)
  have hFac : 0 < ((k - r).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k - r)
  have hFinalDen : 0 < ((k - r).factorial : ℝ) * (1 + ε) ^ (k - r) :=
    mul_pos hFac (pow_pos hOne _)
  have hScalar : ((k - r).factorial : ℝ) * E ≤ T * τ ^ (k - r) := by
    simpa only [E, T, τ, spectralTraceTail] using
      factorial_mul_sum_powersetCard_prod_le_prod_sum_tail_mul_pow
        hA.isHermitian.eigenvalues₀ (eigenvalues₀_nonneg_of_posSemidef hA) hrk
  have hRatio : ((k.factorial : ℝ) * E) / (T * ((1 + ε) * τ) ^ (k - r)) ≤
      (k.factorial : ℝ) / ((k - r).factorial * (1 + ε) ^ (k - r)) := by
    apply (div_le_div_iff₀ hDen hFinalDen).mpr
    calc
      ((k.factorial : ℝ) * E) * ((k - r).factorial * (1 + ε) ^ (k - r)) =
          ((k.factorial : ℝ) * (1 + ε) ^ (k - r)) * ((k - r).factorial * E) := by ring
      _ ≤ ((k.factorial : ℝ) * (1 + ε) ^ (k - r)) * (T * τ ^ (k - r)) :=
        mul_le_mul_of_nonneg_left hScalar (by positivity)
      _ = (k.factorial : ℝ) * (T * ((1 + ε) * τ) ^ (k - r)) := by rw [mul_pow]; ring
  apply le_min measureReal_le_one
  exact (measureReal_trace_ge_le_factorial_elementary_div hA hrk μ hMass hτ hc).trans hRatio

/-- Nonstrict factorial trace tail for the actual real adaptive RPCholesky law.
Positive optimal tail is required at this endpoint.
atlas: rpcholesky-factorial-trace-tail (partial)-/
theorem measureReal_trace_choleskyHistoryLaw_ge_le_factorialTraceTail [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) {k r : ℕ} (hrk : r ≤ k)
    (hτ : 0 < spectralTraceTail A hA.isHermitian r) {ε : ℝ} (hε : 0 < ε) :
    (choleskyHistoryLaw A hA k).real
      {h | (1 + ε) * spectralTraceTail A hA.isHermitian r ≤ (partialCholeskyResidual A h).trace} ≤
        choleskyFactorialTraceTail r k ε := by
  have hh := measureReal_trace_ge_le_factorialTraceTail hA hrk (choleskyHistoryLaw A hA k)
    (fun h => by simpa only [RCLike.re_to_real] using
      choleskyHistoryLaw_singleton_mul_traceProduct_eq_det A hA k h) hτ hε
  simpa only [eliminationListResidual_ofFn_eq_partialCholeskyResidual, RCLike.re_to_real] using hh

/-- Nonstrict factorial trace tail for the actual complex adaptive law.
The same positive-tail qualification is retained.
atlas: rpcholesky-factorial-trace-tail (partial)-/
theorem measureReal_trace_complexCholeskyHistoryLaw_ge_le_factorialTraceTail [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {k r : ℕ} (hrk : r ≤ k)
    (hτ : 0 < spectralTraceTail A hA.isHermitian r) {ε : ℝ} (hε : 0 < ε) :
    (complexCholeskyHistoryLaw A hA k).real
      {h | (1 + ε) * spectralTraceTail A hA.isHermitian r ≤
        (complexCholeskyResidualHistory A k h).trace.re} ≤ choleskyFactorialTraceTail r k ε := by
  have hh := measureReal_trace_ge_le_factorialTraceTail hA hrk (complexCholeskyHistoryLaw A hA k)
    (fun h => complexCholeskyHistoryLaw_singleton_mul_traceProduct_eq_re_det A hA k h) hτ hε
  simpa only [eliminationListResidual_ofFn_eq_complexCholeskyResidualHistory,
    RCLike.re_to_complex] using hh

/-- With zero optimal tail, the actual real adaptive process terminates almost
surely by every time `k≥r`. This is the endpoint needed for the strict tail.
atlas: rpcholesky-factorial-trace-tail (partial) -/
theorem ae_partialCholeskyResidual_eq_zero_of_spectralTraceTail_eq_zero [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) {k r : ℕ} (hrk : r ≤ k)
    (hτ : spectralTraceTail A hA.isHermitian r = 0) :
    ∀ᵐ h ∂choleskyHistoryLaw A hA k, partialCholeskyResidual A h = 0 := by
  apply ae_iff_of_countable.mpr
  intro h hh
  have hw : choleskyHistoryWeight A k h ≠ 0 := by
    rw [← choleskyHistoryLaw_singleton A hA k h]
    exact (measureReal_ne_zero_iff (by finiteness)).mpr hh
  exact partialCholeskyResidual_eq_zero_of_rank_le hA
    ((rank_le_of_spectralTraceTail_eq_zero hA hτ).trans hrk) h
    ((choleskyHistoryWeight_nonneg hA k h).lt_of_ne (Ne.symm hw))

/-- The same zero-tail exact termination holds for the actual complex law.
atlas: rpcholesky-factorial-trace-tail (partial) -/
theorem ae_complexCholeskyResidualHistory_eq_zero_of_spectralTraceTail_eq_zero [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {k r : ℕ} (hrk : r ≤ k)
    (hτ : spectralTraceTail A hA.isHermitian r = 0) :
    ∀ᵐ h ∂complexCholeskyHistoryLaw A hA k, complexCholeskyResidualHistory A k h = 0 := by
  apply ae_iff_of_countable.mpr
  intro h hh
  have hw : complexCholeskyHistoryWeight A k h ≠ 0 := by
    rw [← complexCholeskyHistoryLaw_singleton A hA k h]
    exact (measureReal_ne_zero_iff (by finiteness)).mpr hh
  exact complexCholeskyResidualHistory_eq_zero_of_rank_le hA
    ((rank_le_of_spectralTraceTail_eq_zero hA hτ).trans hrk) h
    ((complexCholeskyHistoryWeight_nonneg hA k h).lt_of_ne (Ne.symm hw))

/-- Strict factorial trace tail for every PSD real input, including a zero
optimal tail and exact rank termination. This is the corrected all-PSD statement.
atlas: rpcholesky-factorial-trace-tail (partial)-/
theorem measureReal_trace_choleskyHistoryLaw_gt_le_factorialTraceTail [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) {k r : ℕ} (hrk : r ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    (choleskyHistoryLaw A hA k).real
      {h | (1 + ε) * spectralTraceTail A hA.isHermitian r < (partialCholeskyResidual A h).trace} ≤
        choleskyFactorialTraceTail r k ε := by
  by_cases hτ : spectralTraceTail A hA.isHermitian r = 0
  · have hz := ae_partialCholeskyResidual_eq_zero_of_spectralTraceTail_eq_zero hA hrk hτ
    have hm : (choleskyHistoryLaw A hA k).real
        {h | (1 + ε) * spectralTraceTail A hA.isHermitian r < (partialCholeskyResidual A h).trace} = 0 := by
      apply (measureReal_eq_zero_iff (by finiteness)).mpr
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hz] with h hh
      simp [hh, hτ]
    rw [hm]
    apply le_min zero_le_one
    apply div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _))
  · have hSub : {h : Fin k → n | (1 + ε) * spectralTraceTail A hA.isHermitian r <
          (partialCholeskyResidual A h).trace} ⊆
        {h : Fin k → n | (1 + ε) * spectralTraceTail A hA.isHermitian r ≤
          (partialCholeskyResidual A h).trace} := by
      intro h hh
      exact (show (1 + ε) * spectralTraceTail A hA.isHermitian r <
        (partialCholeskyResidual A h).trace from hh).le
    exact (measureReal_mono hSub).trans
      (measureReal_trace_choleskyHistoryLaw_ge_le_factorialTraceTail hA hrk
        ((spectralTraceTail_nonneg hA r).lt_of_ne (Ne.symm hτ)) hε)

/-- Strict factorial trace tail for every PSD complex input, including zero tail.
atlas: rpcholesky-factorial-trace-tail (partial)-/
theorem measureReal_trace_complexCholeskyHistoryLaw_gt_le_factorialTraceTail [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {k r : ℕ} (hrk : r ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    (complexCholeskyHistoryLaw A hA k).real
      {h | (1 + ε) * spectralTraceTail A hA.isHermitian r <
        (complexCholeskyResidualHistory A k h).trace.re} ≤ choleskyFactorialTraceTail r k ε := by
  by_cases hτ : spectralTraceTail A hA.isHermitian r = 0
  · have hz := ae_complexCholeskyResidualHistory_eq_zero_of_spectralTraceTail_eq_zero hA hrk hτ
    have hm : (complexCholeskyHistoryLaw A hA k).real
        {h | (1 + ε) * spectralTraceTail A hA.isHermitian r <
          (complexCholeskyResidualHistory A k h).trace.re} = 0 := by
      apply (measureReal_eq_zero_iff (by finiteness)).mpr
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hz] with h hh
      simp [hh, hτ]
    rw [hm]
    apply le_min zero_le_one
    apply div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _))
  · have hSub : {h : Fin k → n | (1 + ε) * spectralTraceTail A hA.isHermitian r <
          (complexCholeskyResidualHistory A k h).trace.re} ⊆
        {h : Fin k → n | (1 + ε) * spectralTraceTail A hA.isHermitian r ≤
          (complexCholeskyResidualHistory A k h).trace.re} := by
      intro h hh
      exact (show (1 + ε) * spectralTraceTail A hA.isHermitian r <
        (complexCholeskyResidualHistory A k h).trace.re from hh).le
    exact (measureReal_mono hSub).trans
      (measureReal_trace_complexCholeskyHistoryLaw_ge_le_factorialTraceTail hA hrk
        ((spectralTraceTail_nonneg hA r).lt_of_ne (Ne.symm hτ)) hε)

/-- Strict factorial trace tail transported to any real-valued history sample
having the actual adaptive law.
atlas: rpcholesky-factorial-trace-tail (partial)-/
theorem measureReal_trace_choleskyHistoryLaw_gt_le_factorialTraceTail_of_hasLaw [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) {k r : ℕ} (hrk : r ≤ k)
    {ε : ℝ} (hε : 0 < ε) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {H : Ω → Fin k → n}
    (hH : ProbabilityTheory.HasLaw H (choleskyHistoryLaw A hA k) μ) :
    μ.real {ω | (1 + ε) * spectralTraceTail A hA.isHermitian r <
      (partialCholeskyResidual A (H ω)).trace} ≤ choleskyFactorialTraceTail r k ε := by
  rw [hH.measureReal_eq (p := fun h : Fin k → n =>
    (1 + ε) * spectralTraceTail A hA.isHermitian r < (partialCholeskyResidual A h).trace)
    (Set.toFinite _).measurableSet]
  exact measureReal_trace_choleskyHistoryLaw_gt_le_factorialTraceTail hA hrk hε

/-- Strict factorial trace tail transported to any complex adaptive history sample.
atlas: rpcholesky-factorial-trace-tail (partial)-/
theorem measureReal_trace_complexCholeskyHistoryLaw_gt_le_factorialTraceTail_of_hasLaw [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {k r : ℕ} (hrk : r ≤ k)
    {ε : ℝ} (hε : 0 < ε) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {H : Ω → Fin k → n}
    (hH : ProbabilityTheory.HasLaw H (complexCholeskyHistoryLaw A hA k) μ) :
    μ.real {ω | (1 + ε) * spectralTraceTail A hA.isHermitian r <
      (complexCholeskyResidualHistory A k (H ω)).trace.re} ≤ choleskyFactorialTraceTail r k ε := by
  rw [hH.measureReal_eq (p := fun h : Fin k → n =>
    (1 + ε) * spectralTraceTail A hA.isHermitian r < (complexCholeskyResidualHistory A k h).trace.re)
    (Set.toFinite _).measurableSet]
  exact measureReal_trace_complexCholeskyHistoryLaw_gt_le_factorialTraceTail hA hrk hε

end NLAlib
