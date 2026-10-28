import NLAlib.Estimation.Reconstruction.ChebyshevMomentTail
import NLAlib.Estimation.Reconstruction.EmpiricalSpectralLaw
import NLAlib.ForMathlib.MeasureTheory.WassersteinMap

/-!
# Spectral-law recovery from shared Rademacher moments

The output is the actual simplex law on the prescribed Chebyshev grid.
An exact residual-norm minimizer exists by compactness; its use is free
postprocessing in the matrix-vector query model, not a claim about numerical
optimization time. The probability estimates allow all moments to share probes.
Source: Musco--Musco--Rosenblatt--Singh, Section 5, Theorem 19.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Polynomial
open scoped Matrix
namespace NLAlib

private def restrictChebyshevMoments (k : ℕ) (mhat : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j ∈ Finset.Icc 1 k then mhat j else 0

private theorem weightedChebyshevError_restrict_right (k : ℕ) (a mhat : ℕ → ℝ) :
    weightedChebyshevError k a (restrictChebyshevMoments k mhat) =
      weightedChebyshevError k a mhat := by
  simp only [weightedChebyshevError_eq_sqrt_sum]
  congr 1
  exact Finset.sum_congr rfl fun j hj => by simp [restrictChebyshevMoments, hj]

private def chooseChebyshevWeights (k : ℕ) (hk : 1 ≤ k) (mhat : ℕ → ℝ) :
    stdSimplex ℝ (Fin ⌈(k : ℝ) ^ (3 / 2 : ℝ)⌉₊) := by
  let h := exists_minimizer_weightedChebyshevError_gridMoments
    (g := ⌈(k : ℝ) ^ (3 / 2 : ℝ)⌉₊)
    k
    (Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos
      (Nat.cast_pos.mpr (show 0 < k by omega)) _)) mhat
  exact ⟨h.choose, h.choose_spec.1⟩

/-- Select a simplex minimizer using only the finitely many observed degrees. -/
def chebyshevRegressionWeights (k : ℕ) (hk : 1 ≤ k) (mhat : ℕ → ℝ) :
    stdSimplex ℝ (Fin ⌈(k : ℝ) ^ (3 / 2 : ℝ)⌉₊) :=
  chooseChebyshevWeights k hk (restrictChebyshevMoments k mhat)

/-- The selected weights attain the minimum residual norm over the entire simplex. -/
theorem chebyshevRegressionWeights_minimizes (k : ℕ) (hk : 1 ≤ k) (mhat : ℕ → ℝ)
    (a : stdSimplex ℝ (Fin ⌈(k : ℝ) ^ (3 / 2 : ℝ)⌉₊)) :
    weightedChebyshevError k (chebyshevGridMoments (chebyshevRegressionWeights k hk mhat).val) mhat ≤
      weightedChebyshevError k (chebyshevGridMoments a.val) mhat := by
  rw [← weightedChebyshevError_restrict_right k _ mhat,
    ← weightedChebyshevError_restrict_right k (chebyshevGridMoments a.val) mhat]
  exact (exists_minimizer_weightedChebyshevError_gridMoments
    (g := ⌈(k : ℝ) ^ (3 / 2 : ℝ)⌉₊)
    k
    (Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos
      (Nat.cast_pos.mpr (show 0 < k by omega)) _))
      (restrictChebyshevMoments k mhat)).choose_spec.2 a.val a.property

/-- Recovery depends only on the finitely many estimated positive moments. -/
theorem chebyshevRegressionWeights_congr (k : ℕ) (hk : 1 ≤ k) {a b : ℕ → ℝ}
    (h : ∀ j ∈ Finset.Icc 1 k, a j = b j) :
    chebyshevRegressionWeights k hk a = chebyshevRegressionWeights k hk b := by
  have he : restrictChebyshevMoments k a = restrictChebyshevMoments k b := by
    funext j
    by_cases hj : j ∈ Finset.Icc 1 k
    · simp [restrictChebyshevMoments, hj, h j hj]
    · simp [restrictChebyshevMoments, hj]
  unfold chebyshevRegressionWeights
  rw [he]

/-- Recover a probability law from the actual shared-probe moment estimates. -/
def chebyshevSpectralDensityEstimate {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (k : ℕ) (hk : 1 ≤ k) (δ : ℝ)
    (G : Matrix n (Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) ℝ) :
    Measure ℝ :=
  chebyshevGridLaw (chebyshevRegressionWeights k hk
    (chebyshevTraceMomentEstimate A (chebyshevProbeBudget (Fintype.card n) k δ)
      (chebyshevProbeBudget_nonneg _ _ _) G))

variable {n Ω : Type*} [Fintype n] [DecidableEq n] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual reconstructed spectral probability law has error
`(38 + pi/2)/k` with failure probability at most `delta`.
atlas: chebyshev-spectral-density-query (partial) -/
theorem measureReal_wassersteinEDistOne_empiricalSpectralLaw_gt_le
    [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsHermitian) (hbound : specNorm A ≤ 1)
    {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {G : Ω → Matrix n (Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) ℝ}
    (hG : HasLaw (fun ω (e : n × Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) =>
      G ω e.1 e.2)
      (rademacherVector (n × Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1))) μ) :
    μ.real {ω | ENNReal.ofReal ((38 + Real.pi / 2) / k) <
      wassersteinEDistOne (empiricalSpectralLaw hA)
        (chebyshevSpectralDensityEstimate A k (by omega) δ (G ω))} ≤ δ := by
  apply (measureReal_mono (s₂ := {ω | 1 / (k : ℝ) < weightedChebyshevError k
      (chebyshevTraceMomentEstimate A (chebyshevProbeBudget (Fintype.card n) k δ)
        (chebyshevProbeBudget_nonneg _ _ _) (G ω))
      (fun j => (aeval A (Chebyshev.T ℝ (j : ℤ))).trace / Fintype.card n)})
    ?_ (measure_ne_top _ _)).trans
    (measureReal_weightedChebyshevError_traceMomentEstimate_gt_le hA hbound hk hδ hδ1 hG)
  intro ω hω
  by_contra hbad
  simp only [Set.mem_ofPred_eq] at hbad hω
  have hn := le_of_not_gt hbad
  have hm : (fun j : ℕ => (aeval A (Chebyshev.T ℝ (j : ℤ))).trace / Fintype.card n) =
      chebyshevMoments (empiricalSpectralLaw hA) :=
    funext fun j => (chebyshevMoments_empiricalSpectralLaw hA j).symm
  rw [hm] at hn
  have hw := wassersteinEDistOne_gridLaw_le_of_ceil_rpow_three_div_two
    (empiricalSpectralLaw hA) (ae_mem_Icc_empiricalSpectralLaw hA hbound) (by omega)
    _ hn (chebyshevRegressionWeights k (by omega) _) (η := 0)
    (fun a => (chebyshevRegressionWeights_minimizes k (by omega) _ a).trans_eq (by simp))
  have hc : (36 + Real.pi / 2) / (k : ℝ) + 2 * (1 / k) + 0 =
      (38 + Real.pi / 2) / k := by ring
  rw [hc] at hw
  exact (not_lt_of_ge hw) hω

open scoped Matrix.Norms.L2Operator in
/-- Positive scaling transfers the recovered normalized law back to the
original matrix, with the source's exact constant.
atlas: chebyshev-spectral-density-query (partial) -/
theorem measureReal_wassersteinEDistOne_empiricalSpectralLaw_scaled_gt_le
    [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {S : ℝ} (hS : 0 < S) (hbound : specNorm A ≤ S)
    {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {G : Ω → Matrix n (Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) ℝ}
    (hG : HasLaw (fun ω (e : n × Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1)) =>
      G ω e.1 e.2)
      (rademacherVector (n × Fin (chebyshevProbeCount (chebyshevProbeBudget (Fintype.card n) k δ) 1))) μ) :
    μ.real {ω | ENNReal.ofReal ((38 + Real.pi / 2) * S / k) <
      wassersteinEDistOne (empiricalSpectralLaw hA)
        ((chebyshevSpectralDensityEstimate (S⁻¹ • A) k (by omega) δ (G ω)).map
          (fun x => S * x))} ≤ δ := by
  let B := S⁻¹ • A
  have hB : B.IsHermitian := hA.smul (by simp [IsSelfAdjoint])
  have hnorm : specNorm B ≤ 1 := by
    dsimp [B]
    rw [specNorm_eq_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hS.le)]
    calc
      _ ≤ S⁻¹ * S := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hS.le)
      _ = 1 := inv_mul_cancel₀ hS.ne'
  have hlaw : (empiricalSpectralLaw hB).map (fun x => S * x) = empiricalSpectralLaw hA := by
    have hh := empiricalSpectralLaw_smul hB S
    simpa only [B, smul_smul, mul_inv_cancel₀ hS.ne', one_smul] using hh.symm
  apply (measureReal_mono (s₂ := {ω | ENNReal.ofReal ((38 + Real.pi / 2) / k) <
      wassersteinEDistOne (empiricalSpectralLaw hB)
        (chebyshevSpectralDensityEstimate B k (by omega) δ (G ω))})
    ?_ (measure_ne_top _ _)).trans
    (measureReal_wassersteinEDistOne_empiricalSpectralLaw_gt_le hB hnorm hk hδ hδ1 hG)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hn
  have hw := wassersteinEDistOne_map_mul_le (empiricalSpectralLaw hB)
    (chebyshevSpectralDensityEstimate B k (by omega) δ (G ω)) hS
  rw [hlaw] at hw
  have hw' := hw.trans (mul_le_mul_right (le_of_not_gt hn) (ENNReal.ofReal S))
  rw [← ENNReal.ofReal_mul hS.le] at hw'
  have he : S * ((38 + Real.pi / 2) / (k : ℝ)) = (38 + Real.pi / 2) * S / k := by ring
  rw [he] at hw'
  exact (not_lt_of_ge hw') hω

/-- The prescribed degree reaches an arbitrary requested relative scale. -/
theorem spectralDensity_constant_div_ceil_le {ε : ℝ} (hε : 0 < ε) :
    (38 + Real.pi / 2) / (⌈(38 + Real.pi / 2) / ε⌉₊ : ℝ) ≤ ε := by
  have hc : (0 : ℝ) < 38 + Real.pi / 2 := by positivity
  have hceil : 0 < ⌈(38 + Real.pi / 2) / ε⌉₊ :=
    Nat.one_le_ceil_iff.mpr (div_pos hc hε)
  apply (div_le_iff₀ (Nat.cast_pos.mpr hceil)).2
  have := Nat.le_ceil ((38 + Real.pi / 2) / ε)
  exact (div_le_iff₀ hε).mp this |>.trans_eq (mul_comm _ _)

end NLAlib
