import NLAlib.Matrix.SimpleEigenvalueImplicitBranch
import NLAlib.ForMathlib.Analysis.ImplicitFunction

/-!
# Continuity of the scalar eigenvalue branch on a neighborhood

Local uniqueness identifies the scalar branch with the continuous inverse
from the implicit function theorem throughout a neighborhood.
Source: Horn–Johnson (2013), Theorem 6.3.12.
-/

noncomputable section
open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The locally unique scalar Schur branch is continuous throughout a
neighborhood and has the expected derivative at zero. Source:
Horn–Johnson (2013), Theorem 6.3.12. -/
theorem exists_continuous_simpleEigenvalueSchurFunction_branch (μ a : ℂ)
    (B F : Matrix n n ℂ) (b c : n → ℂ) (hμ : μ ∉ spectrum ℂ B) :
    ∃ ψ : ℂ → ℂ, ψ 0 = 0 ∧ ContinuousAt ψ 0 ∧ HasDerivAt ψ a 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), ContinuousAt ψ t) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), simpleEigenvalueSchurFunction μ a B F b c (t, ψ t) = 0) ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
        simpleEigenvalueSchurFunction μ a B F b c p = 0 ↔ ψ p.1 = p.2) := by
  obtain ⟨ψ, hψ₀, hψcont, hψderiv, hψeq, hψunique⟩ :=
    exists_simpleEigenvalueSchurFunction_branch μ a B F b c hμ
  let D : (ℂ × ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.snd ℂ ℂ ℂ - a • ContinuousLinearMap.fst ℂ ℂ ℂ
  have hf : HasStrictFDerivAt (simpleEigenvalueSchurFunction μ a B F b c) D 0 :=
    hasStrictFDerivAt_simpleEigenvalueSchurFunction μ a B F b c hμ
  have hD₂ : D ∘L ContinuousLinearMap.inr ℂ ℂ ℂ = ContinuousLinearMap.id ℂ ℂ := by
    apply ContinuousLinearMap.ext
    intro z
    change z - a * 0 = z
    ring
  have hif : (D ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    rw [hD₂]
    exact ⟨ContinuousLinearEquiv.refl ℂ ℂ, rfl⟩
  let g := hf.implicitFunctionOfProdDomain hif
  have hgcont : ∀ᶠ t in 𝓝 (0 : ℂ), ContinuousAt g t :=
    eventually_continuousAt_implicitFunctionOfProdDomain hf hif
  have hgraph : Tendsto (fun t : ℂ => (t, ψ t)) (𝓝 0) (𝓝 (0 : ℂ × ℂ)) := by
    change Tendsto (fun t : ℂ => (t, ψ t)) (𝓝 0) (𝓝 ((0 : ℂ), 0))
    simpa only [hψ₀, id_eq] using (continuousAt_id.prodMk hψcont).tendsto
  have hgψ : g =ᶠ[𝓝 (0 : ℂ)] ψ := by
    filter_upwards [hψeq,
      hgraph.eventually (hf.eventually_apply_eq_iff_implicitFunctionOfProdDomain hif)] with t ht hu
    apply hu.mp
    simpa [simpleEigenvalueSchurFunction] using ht
  refine ⟨ψ, hψ₀, hψcont, hψderiv, ?_, hψeq, hψunique⟩
  filter_upwards [hgcont, hgψ.eventually_nhds] with t hcont heq
  have heq' : g =ᶠ[𝓝 t] ψ := heq
  exact hcont.congr_of_eventuallyEq heq'.symm

end NLAlib
