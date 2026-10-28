import NLAlib.Estimation.Reconstruction.ChebyshevQueryProgram
import NLAlib.Krylov.QueryModel.Recovery

/-!
# Decreasing-probe spectral recovery with the exact dimension cap

Choose between the shared recurrence and coordinate-vector recovery before the
matrix oracle is supplied. The latter returns the exact empirical spectral law
using `card n` products, with its eigensolver treated as free postprocessing.
Source: MMRS Section 5, Theorem 19 and the full-recovery query cap.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

private def totalHermitianSpectralLaw (A : Matrix n n ℝ) : Measure ℝ :=
  if h : A.IsHermitian then empiricalSpectralLaw h else 0

private theorem totalHermitianSpectralLaw_eq {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    totalHermitianSpectralLaw A = empiricalSpectralLaw hA := dif_pos hA

/-- The smaller of the two matrix-independent query budgets chooses between
the shared-probe recurrence and exact coordinate-vector recovery. -/
def cappedChebyshevDensityAlg (k : ℕ) (hk : 1 ≤ k) (S δ : ℝ)
    (G : Matrix n (Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) ℝ) :
    MatvecAlg ℝ n (Measure ℝ) :=
  if chebyshevQueryCount (chebyshevProbeBudget (Fintype.card n) k δ) k ≤ Fintype.card n then
    ⟨_, chebyshevDensityProgram k hk S δ G⟩
  else ⟨_, matrixRecoveryProgram.map totalHermitianSpectralLaw⟩

/-- The implementation pays exactly the minimum of its active-prefix sum and
the dimension, independently of the matrix and of the random probes.
atlas: chebyshev-spectral-density-query (partial) -/
theorem cost_cappedChebyshevDensityAlg (k : ℕ) (hk : 1 ≤ k) (S δ : ℝ)
    (G : Matrix n (Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) ℝ) :
    (cappedChebyshevDensityAlg k hk S δ G).cost =
      min (chebyshevQueryCount (chebyshevProbeBudget (Fintype.card n) k δ) k) (Fintype.card n) := by
  by_cases h : chebyshevQueryCount (chebyshevProbeBudget (Fintype.card n) k δ) k ≤ Fintype.card n
  · simp only [cappedChebyshevDensityAlg, if_pos h, MatvecAlg.cost, min_eq_left h]
  · simp only [cappedChebyshevDensityAlg, if_neg h, MatvecAlg.cost, min_eq_right (le_of_not_ge h)]

/-- The capped query count has the exact source dependence, with a universal
constant and all integer-rounding terms retained.
atlas: chebyshev-spectral-density-query (partial) -/
theorem cost_cappedChebyshevDensityAlg_le (k : ℕ) (hk : 1 ≤ k) (S δ : ℝ)
    (G : Matrix n (Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) ℝ) :
    ((cappedChebyshevDensityAlg k hk S δ G).cost : ℝ) ≤
      min (Fintype.card n : ℝ)
        (2 * k + chebyshevProbeConstant * k ^ 2 * (1 + Real.log k) ^ 2 *
          Real.log ((k : ℝ) / δ) ^ 2 / Fintype.card n) := by
  rw [cost_cappedChebyshevDensityAlg]
  apply le_min
  · exact_mod_cast min_le_right _ _
  · apply (Nat.cast_le.mpr (min_le_left _ _)).trans
    rw [chebyshevQueryCount_eq_sum, Nat.cast_sum]
    exact sum_chebyshevProbeCount_budget_le hk δ

/-- On every symmetric input, the output is the original empirical spectral law
in the full-recovery branch and the prescribed grid law in the recurrence branch. -/
theorem run_cappedChebyshevDensityAlg {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (k : ℕ) (hk : 1 ≤ k) (S δ : ℝ)
    (G : Matrix n (Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) ℝ) :
    (cappedChebyshevDensityAlg k hk S δ G).run A =
      if chebyshevQueryCount (chebyshevProbeBudget (Fintype.card n) k δ) k ≤ Fintype.card n then
        (chebyshevSpectralDensityEstimate (S⁻¹ • A) k hk δ G).map (fun x => S * x)
      else empiricalSpectralLaw hA := by
  by_cases h : chebyshevQueryCount (chebyshevProbeBudget (Fintype.card n) k δ) k ≤ Fintype.card n
  · have he : cappedChebyshevDensityAlg k hk S δ G =
        ⟨_, chebyshevDensityProgram k hk S δ G⟩ := if_pos h
    rw [if_pos h]
    exact (congrArg (fun alg : MatvecAlg ℝ n (Measure ℝ) => alg.run A) he).trans
      (run_chebyshevDensityProgram A k hk S δ G)
  · have he : cappedChebyshevDensityAlg k hk S δ G =
        ⟨_, matrixRecoveryProgram.map totalHermitianSpectralLaw⟩ := if_neg h
    rw [if_neg h]
    apply (congrArg (fun alg : MatvecAlg ℝ n (Measure ℝ) => alg.run A) he).trans
    simp only [MatvecAlg.run, QueryProgram.run_map,
      run_matrixRecoveryProgram, totalHermitianSpectralLaw_eq hA]

/-- Both branches return actual probability measures, for every probe array.
atlas: chebyshev-spectral-density-query (partial) -/
theorem isProbabilityMeasure_run_cappedChebyshevDensityAlg [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (k : ℕ) (hk : 1 ≤ k) (S δ : ℝ)
    (G : Matrix n (Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) ℝ) :
    IsProbabilityMeasure ((cappedChebyshevDensityAlg k hk S δ G).run A) := by
  rw [run_cappedChebyshevDensityAlg hA]
  split_ifs
  · unfold chebyshevSpectralDensityEstimate
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  · infer_instance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The matrix-independent capped algorithm obeys the native spectral-law
error guarantee under the actual shared Rademacher probe law.
atlas: chebyshev-spectral-density-query (partial) -/
theorem measureReal_wassersteinEDistOne_cappedChebyshevDensityAlg_gt_le
    [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {S : ℝ} (hS : 0 < S) (hbound : specNorm A ≤ S)
    {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {G : Ω → Matrix n (Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) ℝ}
    (hG : HasLaw (fun ω (e : n × Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) =>
      G ω e.1 e.2)
      (rademacherVector (n × Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1))) μ) :
    μ.real {ω | ENNReal.ofReal ((38 + Real.pi / 2) * S / k) <
      wassersteinEDistOne (empiricalSpectralLaw hA)
        ((cappedChebyshevDensityAlg k (by omega) S δ (G ω)).run A)} ≤ δ := by
  simp_rw [run_cappedChebyshevDensityAlg hA]
  split_ifs
  · exact measureReal_wassersteinEDistOne_empiricalSpectralLaw_scaled_gt_le hA hS hbound hk hδ hδ1 hG
  · simpa only [wassersteinEDistOne_self, not_lt_zero, Set.ofPred_false, measureReal_empty]
      using hδ.le

/-- The exact prescribed rounded degree is at least two in the source accuracy range. -/
theorem two_le_spectralDensity_degree {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    2 ≤ ⌈(38 + Real.pi / 2) / ε⌉₊ := by
  have h : (2 : ℝ) ≤ (38 + Real.pi / 2) / ε := by
    apply (le_div_iff₀ hε).mpr
    nlinarith [Real.pi_pos]
  exact_mod_cast h.trans (Nat.le_ceil _)

/-- The source's rounded accuracy choice gives error `epsilon * S` for the
actual capped oracle algorithm.
atlas: chebyshev-spectral-density-query (partial) -/
theorem measureReal_wassersteinEDistOne_cappedChebyshevDensityAlg_epsilon_gt_le
    [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {S : ℝ} (hS : 0 < S) (hbound : specNorm A ≤ S)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {G : Ω → Matrix n
      (Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n)
        ⌈(38 + Real.pi / 2) / ε⌉₊ δ) 1)) ℝ}
    (hG : HasLaw (fun ω (e : n × Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n)
        ⌈(38 + Real.pi / 2) / ε⌉₊ δ) 1)) => G ω e.1 e.2)
      (rademacherVector (n × Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n)
        ⌈(38 + Real.pi / 2) / ε⌉₊ δ) 1))) μ) :
    μ.real {ω | ENNReal.ofReal (ε * S) < wassersteinEDistOne (empiricalSpectralLaw hA)
      ((cappedChebyshevDensityAlg ⌈(38 + Real.pi / 2) / ε⌉₊
        (by have := two_le_spectralDensity_degree hε hε1; omega) S δ (G ω)).run A)} ≤ δ := by
  apply (measureReal_mono ?_ (measure_ne_top _ _)).trans
    (measureReal_wassersteinEDistOne_cappedChebyshevDensityAlg_gt_le
      hA hS hbound (two_le_spectralDensity_degree hε hε1) hδ hδ1 hG)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  apply lt_of_le_of_lt _ hω
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_right (spectralDensity_constant_div_ceil_le hε) hS.le
  simpa only [div_mul_eq_mul_div] using h

end NLAlib
