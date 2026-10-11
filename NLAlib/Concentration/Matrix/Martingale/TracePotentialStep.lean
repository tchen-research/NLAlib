import NLAlib.Concentration.Matrix.Laplace.ConditionalLiebPredictable

/-!
# The actual conditional trace-potential decrease

Predictable-offset conditional Lieb and the derived one-sided conditional cumulant
bound give the step needed for the matrix Freedman supermartingale.
-/

noncomputable section
set_option maxHeartbeats 600000

open MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

/-- The actual trace-exponential potential decreases conditionally after one centered
Hermitian increment. Its variance update is the actual conditional second moment.
The predictable previous sum has only an upper spectral bound and the previous variance
is PSD; no conditional-mgf or supermartingale conclusion is assumed.
Source: Tropp 2011, Freedman's inequality; operator rederivations Section 3.3.
atlas: matrix-freedman (partial) -/
theorem condExp_traceExp_variance_update_le
    {Ω n : Type*} {m mΩ : MeasurableSpace Ω} [Fintype n] [DecidableEq n] [Nonempty n]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {X Y W : Ω → Matrix n n ℂ} (hXMeas : Measurable X)
    (hYMeas : Measurable[m] Y) (hWMeas : Measurable[m] W)
    (hX : Integrable X μ) (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    (hXHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (hYHerm : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    (hW : ∀ᵐ ω ∂μ, (W ω).PosSemidef) (hMean : μ[X | m] =ᵐ[μ] 0)
    {L θ b : ℝ} (hθ : 0 < θ) (hθL : θ * L < 3)
    (hXBound : ∀ᵐ ω ∂μ, X ω ≤ algebraMap ℝ (Matrix n n ℂ) L)
    (hYBound : ∀ᵐ ω ∂μ, Y ω ≤ algebraMap ℝ (Matrix n n ℂ) b) :
    μ[(fun ω => traceExp (θ • (Y ω + X ω) -
      ((θ ^ 2 / 2) / (1 - θ * L / 3)) • (W ω + μ[(fun ω => X ω ^ 2) | m] ω))) | m] ≤ᵐ[μ]
      fun ω => traceExp (θ • Y ω - ((θ ^ 2 / 2) / (1 - θ * L / 3)) • W ω) := by
  let g : ℝ := (θ ^ 2 / 2) / (1 - θ * L / 3)
  let V : Ω → Matrix n n ℂ := μ[(fun ω => X ω ^ 2) | m]
  let M : Ω → Matrix n n ℂ := μ[(fun ω => matrixExp (θ • X ω)) | m]
  let H : Ω → Matrix n n ℂ := fun ω => θ • Y ω - g • (W ω + V ω)
  have hg : 0 ≤ g := by
    dsimp [g]
    apply div_nonneg (by positivity)
    linarith
  have hcgf := ae_condExp_matrixExp_one_le_and_condExp_sq_posSemidef_and_matrixLog_le
    hm hX hX2 hXHerm hMean hθ hθL hXBound
  have hV : ∀ᵐ ω ∂μ, (V ω).PosSemidef := hcgf.mono fun ω hω => hω.2.1
  have hM : ∀ᵐ ω ∂μ, (M ω).PosDef := by
    filter_upwards [hcgf] with ω hω
    have hp := (Matrix.PosDef.one : (1 : Matrix n n ℂ).PosDef).add_posSemidef
      (Matrix.le_iff.mp hω.1)
    have heq : 1 + (M ω - 1) = M ω := by abel
    rw [heq] at hp
    exact hp
  have hVMeas : Measurable[m] V := stronglyMeasurable_condExp.measurable
  have hHMeas : Measurable[m] H :=
    (hYMeas.const_smul θ).sub ((hWMeas.add hVMeas).const_smul g)
  have hHHerm : ∀ᵐ ω ∂μ, (H ω).IsHermitian := by
    filter_upwards [hYHerm, hW, hV] with ω hYω hWω hVω
    exact (hYω.smul (IsSelfAdjoint.all _)).sub
      ((hWω.isHermitian.add hVω.isHermitian).smul (IsSelfAdjoint.all _))
  have hscale : ∀ (A : Matrix n n ℂ) (c : ℝ), A ≤ algebraMap ℝ (Matrix n n ℂ) c →
      θ • A ≤ algebraMap ℝ (Matrix n n ℂ) (θ * c) := by
    intro A c hAc
    apply Matrix.le_iff.mpr
    simpa only [smul_sub, Algebra.algebraMap_eq_smul_one, smul_smul] using
      (Matrix.le_iff.mp hAc).smul hθ.le
  have hHBound : ∀ᵐ ω ∂μ, H ω ≤ algebraMap ℝ (Matrix n n ℂ) (θ * b) := by
    filter_upwards [hYBound, hW, hV] with ω hYω hWω hVω
    have hcomp : (0 : Matrix n n ℂ) ≤ g • (W ω + V ω) := ((hWω.add hVω).smul hg).nonneg
    exact (sub_le_self _ hcomp).trans (hscale _ _ hYω)
  have hZBound : ∀ᵐ ω ∂μ, θ • X ω ≤ algebraMap ℝ (Matrix n n ℂ) (θ * L) :=
    hXBound.mono fun ω hω => hscale _ _ hω
  have hLieb := condExp_traceExp_add_le_traceExp_add_matrixLog_of_predictable hm
    hHMeas (hXMeas.const_smul θ) hHHerm
    (hXHerm.mono fun ω hω => by
      change (θ • X ω).IsHermitian
      exact hω.smul (IsSelfAdjoint.all θ)) hHBound hZBound hM
  simp only [Pi.smul_apply] at hLieb
  have hfun : (fun ω => traceExp (H ω + θ • X ω)) =
      (fun ω => traceExp (θ • (Y ω + X ω) - g • (W ω + V ω))) := by
    funext ω
    congr 1
    dsimp [H]
    simp only [smul_add]
    abel
  have hCEEq := condExp_congr_ae (m := m) (μ := μ)
    (Filter.Eventually.of_forall (fun ω => congrFun hfun ω))
  filter_upwards [hLieb, hCEEq, hcgf, hHHerm, hV] with ω hLω hCEω hcgfω hHω hVω
  rw [hCEω] at hLω
  refine hLω.trans ?_
  have hlog : (matrixLog (M ω)).IsHermitian := cfc_predicate Real.log (M ω)
  have hgv : (g • V ω).IsHermitian := hVω.isHermitian.smul (IsSelfAdjoint.all _)
  have hlogLe : matrixLog (M ω) ≤ g • V ω := hcgfω.2.2
  have hcomp := add_le_add (le_refl (H ω)) hlogLe
  have htrace := traceExp_le_traceExp_finite _ _ (hHω.add hlog) (hHω.add hgv) hcomp
  have heq : H ω + g • V ω = θ • Y ω - g • W ω := by
    dsimp [H]
    rw [smul_add]
    abel
  rw [heq] at htrace
  exact htrace

end NLAlib
