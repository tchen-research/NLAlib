import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Entrywise finite matrix integrability

For finite real or complex matrices, Bochner integrability in the spectral
norm is equivalent to scalar integrability of every entry. Entry evaluation
commutes with the actual matrix integral.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

namespace Matrix

variable {Ω m n 𝕜 : Type*} [MeasurableSpace Ω] [Fintype m] [Fintype n]
  [DecidableEq n] [RCLike 𝕜] {μ : Measure Ω}

open scoped Matrix.Norms.L2Operator in
private local instance : NormedSpace ℝ (Matrix m n 𝕜) where
  toModule := inferInstance
  norm_smul_le := by
    intro r A
    have he : r • A = (r : 𝕜) • A := by
      ext i j
      simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    rw [he]
    simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using norm_smul_le (r : 𝕜) A

open scoped Matrix.Norms.L2Operator in
/-- A finite matrix function is integrable exactly when every entry is
integrable. The choice of the spectral norm does not add an entrywise bound. -/
theorem integrable_iff_entries {f : Ω → Matrix m n 𝕜} :
    Integrable f μ ↔ ∀ i j, Integrable (fun ω => f ω i j) μ := by
  let L : (m → n → 𝕜) ≃L[𝕜] Matrix m n 𝕜 :=
    (Matrix.ofLinearEquiv 𝕜).toContinuousLinearEquiv
  have h := L.integrable_comp_iff (φ := fun ω => fun i j => f ω i j) (μ := μ)
  have heq : (fun ω => L (fun i j => f ω i j)) = f := by
    funext ω
    ext i j
    rfl
  rw [heq] at h
  simpa only [integrable_pi_iff] using h

open scoped Matrix.Norms.L2Operator in
/-- A finite matrix function lies in a given `Lp` space exactly when every
entry does, for every finite or infinite exponent. -/
theorem memLp_iff_entries {f : Ω → Matrix m n 𝕜} {p : ℝ≥0∞} :
    MemLp f p μ ↔ ∀ i j, MemLp (fun ω => f ω i j) p μ := by
  let L : (m → n → 𝕜) ≃L[𝕜] Matrix m n 𝕜 :=
    (Matrix.ofLinearEquiv 𝕜).toContinuousLinearEquiv
  constructor
  · intro hf
    have h := L.symm.toContinuousLinearMap.comp_memLp' hf
    change MemLp (fun ω => fun i j => f ω i j) p μ at h
    exact fun i j => (h.eval i).eval j
  · intro hf
    have h : MemLp (fun ω => fun i j => f ω i j) p μ :=
      MemLp.of_eval (fun i => MemLp.of_eval (hf i))
    have hi := L.toContinuousLinearMap.comp_memLp' h
    have heq : (L.toContinuousLinearMap ∘ fun ω => fun i j => f ω i j) = f := by
      funext ω
      ext i j
      rfl
    rw [heq] at hi
    exact hi

open scoped Matrix.Norms.L2Operator in
/-- Each scalar entry of an actual finite matrix integral is the integral
of that entry. -/
theorem integral_apply {f : Ω → Matrix m n 𝕜} (hf : Integrable f μ) (i : m) (j : n) :
    (∫ ω, f ω ∂μ) i j = ∫ ω, f ω i j ∂μ := by
  let L : Matrix m n 𝕜 →L[𝕜] 𝕜 := (Matrix.entryLinearMap 𝕜 𝕜 i j).toContinuousLinearMap
  exact (L.integral_comp_comm hf).symm

end Matrix
