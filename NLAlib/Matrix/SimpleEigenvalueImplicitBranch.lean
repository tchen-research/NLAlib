import NLAlib.Matrix.SimpleEigenvalueSchurFunction

/-!
# A local differentiable branch of the scalar Schur equation

The partial shift derivative is the identity, so the product-domain implicit
function theorem supplies a locally unique branch with derivative equal to
the leading perturbation entry. Source: Horn–Johnson (2013), Theorem 6.3.12;
operator re-derivation §gen:simple-branch.
-/

noncomputable section
open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The separated scalar Schur equation has a locally unique continuous
differentiable shift branch with derivative equal to its leading perturbation
entry. Source: Horn–Johnson (2013), Theorem 6.3.12; the parameter may be complex,
which is stronger than the real-parameter conclusion of the source. -/
theorem exists_simpleEigenvalueSchurFunction_branch (μ a : ℂ)
    (B F : Matrix n n ℂ) (b c : n → ℂ) (hμ : μ ∉ spectrum ℂ B) :
    ∃ ψ : ℂ → ℂ, ψ 0 = 0 ∧ ContinuousAt ψ 0 ∧ HasDerivAt ψ a 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), simpleEigenvalueSchurFunction μ a B F b c (t, ψ t) = 0) ∧
      (∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
        simpleEigenvalueSchurFunction μ a B F b c p = 0 ↔ ψ p.1 = p.2) := by
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
  let ψ : ℂ → ℂ := hf.implicitFunctionOfProdDomain hif
  have hevent := hf.eventually_apply_eq_iff_implicitFunctionOfProdDomain hif
  have hψ₀ : ψ 0 = 0 := hevent.self_of_nhds.mp rfl
  have hderiv : -(D ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).inverse ∘L
      (D ∘L ContinuousLinearMap.inl ℂ ℂ ℂ) = a • ContinuousLinearMap.id ℂ ℂ := by
    rw [hD₂, ContinuousLinearMap.inverse_id]
    apply ContinuousLinearMap.ext
    intro z
    change -(0 - a * z) = a * z
    ring
  have hψstrict := hf.hasStrictFDerivAt_implicitFunctionOfProdDomain hif
  have hψderiv : HasDerivAt ψ a 0 := by
    have h := hψstrict.hasFDerivAt.hasDerivAt
    rw [hderiv] at h
    simpa using h
  have hf₀ : simpleEigenvalueSchurFunction μ a B F b c (0 : ℂ × ℂ) = 0 := by
    simp only [simpleEigenvalueSchurFunction, Prod.fst_zero, Prod.snd_zero,
      zero_mul, sub_zero, zero_pow (by decide : 2 ≠ 0)]
  refine ⟨ψ, hψ₀, hψderiv.continuousAt, hψderiv, ?_, ?_⟩
  · have h := hf.eventually_apply_implicitFunctionOfProdDomain hif
    rw [hf₀] at h
    convert! h using 1
  · simpa only [hf₀] using hevent

end NLAlib
