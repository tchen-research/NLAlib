import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Finite measures on compact real sets are determined by their moments

The actual integration functionals factor through the native continuous-map
inclusion into `L¹`. Polynomial equality extends to all continuous functions
by native Stone--Weierstrass, then finite Borel measure extensionality applies.
No moment determinacy hypothesis is assumed.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped Classical Polynomial

namespace MeasureTheory.Measure

variable {K : Set ℝ} [CompactSpace K]

private def continuousIntegral (μ : Measure K) [IsFiniteMeasure μ] : C(K, ℝ) →L[ℝ] ℝ :=
  (L1.integralCLM' ℝ).comp (ContinuousMap.toLp 1 μ ℝ)

private theorem continuousIntegral_apply (μ : Measure K) [IsFiniteMeasure μ]
    (f : C(K, ℝ)) : continuousIntegral μ f = ∫ x, f x ∂μ := by
  change L1.integralCLM' ℝ (ContinuousMap.toLp 1 μ ℝ f) = _
  rw [← L1.integral_eq' ℝ, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) μ f)

/-- Two finite Borel measures on the same compact real set are equal if all
their ordinary scalar moments agree. Empty compact sets are included. -/
theorem eq_of_integral_pow_eq_of_compact {μ ν : Measure K}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmom : ∀ n : ℕ, ∫ x, (x : ℝ) ^ n ∂μ = ∫ x, (x : ℝ) ^ n ∂ν) : μ = ν := by
  let Iμ := continuousIntegral μ
  let Iν := continuousIntegral ν
  have hpoly (P : ℝ[X]) :
      Iμ (Polynomial.toContinuousMapOnAlgHom K P) =
        Iν (Polynomial.toContinuousMapOnAlgHom K P) := by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
    | monomial n a =>
      have heq : Polynomial.toContinuousMapOnAlgHom K (Polynomial.monomial n a) =
          a • (Polynomial.toContinuousMapOnAlgHom K (Polynomial.X ^ n)) := by
        ext x
        simp
      rw [heq, map_smul, map_smul]
      congr 1
      simpa only [Iμ, Iν, continuousIntegral_apply,
        Polynomial.toContinuousMapOnAlgHom_apply, Polynomial.toContinuousMapOn_apply,
        Polynomial.toContinuousMap_apply, Polynomial.eval_pow, Polynomial.eval_X] using hmom n
  have hcont (f : C(K, ℝ)) : Iμ f = Iν f := by
    have hclosed : IsClosed {g : C(K, ℝ) | Iμ g = Iν g} :=
      isClosed_eq Iμ.continuous Iν.continuous
    have hsub : (polynomialFunctions K : Set C(K, ℝ)) ⊆
        {g : C(K, ℝ) | Iμ g = Iν g} := by
      rw [polynomialFunctions_coe]
      rintro _ ⟨P, rfl⟩
      exact hpoly P
    apply closure_minimal hsub hclosed
    change f ∈ (polynomialFunctions K).topologicalClosure
    rw [polynomialFunctions.topologicalClosure]
    trivial
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  simpa only [Iμ, Iν, continuousIntegral_apply,
    BoundedContinuousFunction.coe_toContinuousMap] using hcont f.toContinuousMap

end MeasureTheory.Measure

namespace MeasureTheory.Measure

/-- Compactly supported finite real measures are determined by their actual
ordinary moments. The common compact support may be empty. -/
theorem eq_of_integral_pow_eq_of_ae_mem_isCompact {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {K : Set ℝ} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ, x ∈ K) (hν : ∀ᵐ x ∂ν, x ∈ K)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) : μ = ν := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heq : μ.comap (Subtype.val : K → ℝ) = ν.comap (Subtype.val : K → ℝ) := by
    apply eq_of_integral_pow_eq_of_compact
    intro n
    rw [integral_subtype_comap (μ := μ) hK.measurableSet (fun x : ℝ => x ^ n),
      integral_subtype_comap (μ := ν) hK.measurableSet (fun x : ℝ => x ^ n),
      restrict_eq_self_of_ae_mem hμ, restrict_eq_self_of_ae_mem hν]
    exact hmom n
  have h := congrArg (fun ρ : Measure K => ρ.map Subtype.val) heq
  simpa only [map_comap_subtype_coe hK.measurableSet,
    restrict_eq_self_of_ae_mem hμ, restrict_eq_self_of_ae_mem hν] using h

end MeasureTheory.Measure
