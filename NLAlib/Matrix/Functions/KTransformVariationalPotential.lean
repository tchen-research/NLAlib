import NLAlib.Matrix.Functions.KTransformCompactStieltjesLaw
import NLAlib.Matrix.Functions.KTransformTraceBoundary
import NLAlib.Matrix.Functions.KTransformPotentialMinimum
import NLAlib.Matrix.Functions.KTransformPotentialNormalization

/-! # The attained variational logarithmic potential of the block-Wishart law

The actual native K branch constructs its compact probability trace law.
Its genuine lower-gap inverse has the exact Stieltjes derivative and the
normalization at negative infinity, hence its potential is the actual
logarithmic potential. Convexity of the actual stable K-image proves
global minimization over the original strict Frobenius-stable domain.

Source: Montanari--Saeed (2026), Theorem 2, using Theorem 3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- The actual stable inverse potential equals the logarithmic potential
of its characterized compact trace law throughout the true lower gap.
The exact derivative and normalization at negative infinity are proved
from the native equation and compact sample law.
Source: Montanari--Saeed (2026), Theorem 2, equation (45).
atlas: block-wishart-log-potential (partial) -/
theorem matrixKStableInverse_potential_eq_logarithmicPotential
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) (F : ℂ → M)
    (hFa : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hF : ∀ z : ℂ, 0 < z.im → (imaginaryPart (F z) : M).PosDef ∧
      matrixKTransform ν α (F z) = z • 1)
    (μ : FiniteMeasure ℝ) (hmass : μ.mass = 1)
    (hcompact : IsCompact (μ : Measure ℝ).support)
    (hμ : ∀ z : ℂ, 0 < z.im → normalizedTrace (α • F z) =
      ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂(μ : Measure ℝ))
    (u : ℝ) (hu : u < sInf (μ : Measure ℝ).support) :
    matrixKPotential ν α u (matrixKStableInverse ν α ((u : ℂ) • 1)) /
      (Fintype.card n : ℝ) = logarithmicPotential (μ : Measure ℝ) u := by
  have : IsProbabilityMeasure (μ : Measure ℝ) := ⟨by
    rw [← FiniteMeasure.ennreal_mass, hmass]; rfl⟩
  let a := sInf (μ : Measure ℝ).support
  have ha : ∀ t ∈ (μ : Measure ℝ).support, a ≤ t := fun t ht => csInf_le hcompact.bddBelow ht
  let S : ℝ → M := fun v => matrixKStableInverse ν α ((v : ℂ) • 1)
  have hsol (v : ℝ) (hv : v < a) : S v ∈ matrixKStableDomain ν α ∧
      matrixKTransform ν α (S v) = (v : ℂ) • 1 := by
    obtain ⟨Q, hQ, hKQ⟩ := exists_stable_matrixKTransform_scalar_solution_below_trace_support
      ν hν α hα F hFa hF μ hmass hcompact hμ v (fun t ht => lt_of_lt_of_le hv (ha t ht))
    exact matrixKStableInverse_mem_and_transform_eq ν α ⟨Q, hQ, hKQ⟩
  have hn := tendsto_matrixKPotential_scalar_solution_sub_log ν hν α hα S
    ((eventually_lt_atBot a).mono fun v hv => hsol v hv)
  have hd (v : ℝ) (hv : v < a) :=
    hasDerivAt_matrixKStableInverse_potential_below_trace_support
      ν hν α hα F hFa hF μ hmass hcompact hμ v (fun t ht => lt_of_lt_of_le hv (ha t ht))
  exact eqOn_logarithmicPotential_of_hasDerivAt_of_tendsto (μ : Measure ℝ) hcompact a ha
    (fun v => matrixKPotential ν α v (S v) / Fintype.card n) hd hn hu

/-- Every compact Hermitian probability sample law constructs its native
analytic K branch and compact probability trace law. Below the actual
lower support edge the true logarithmic potential is the attained minimum
of the source finite-matrix potential over the original strict stable
domain. The minimizing matrix solves K(S)=uI, and every sample determinant
appearing in its logarithm is genuinely positive, including indefinite
and singular samples. No law, branch, normalization, potential identity
or minimization conclusion is supplied as a premise.
Source: Montanari--Saeed (2026), Theorem 2 and its proof, using Theorem 3.
atlas: block-wishart-log-potential -/
theorem exists_matrixKTransform_law_variational_logarithmicPotential
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0 < α) :
    ∃ F : ℂ → M, AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → (imaginaryPart (F z) : M).PosDef ∧
        matrixKTransform ν α (F z) = z • 1) ∧
      ∃ μ : FiniteMeasure ℝ, μ.mass = 1 ∧ IsCompact (μ : Measure ℝ).support ∧
        (∀ z : ℂ, 0 < z.im → normalizedTrace (α • F z) =
          ∫ t : ℝ, ((t : ℂ) - z)⁻¹ ∂(μ : Measure ℝ)) ∧
        ∀ u < sInf (μ : Measure ℝ).support, ∃ S : M,
          S ∈ matrixKStableDomain ν α ∧ matrixKTransform ν α S = (u : ℂ) • 1 ∧
          logarithmicPotential (μ : Measure ℝ) u = matrixKPotential ν α u S / Fintype.card n ∧
          (∀ Q ∈ matrixKStableDomain ν α, matrixKPotential ν α u S ≤ matrixKPotential ν α u Q) ∧
          ∀ T ∈ ν.support, 0 < (1 + T.val * S).det := by
  obtain ⟨F, hFa, hF, μ, hμ, _huniq⟩ :=
    exists_analytic_matrixKTransform_compact_stieltjes_probability_measure ν hν α hα
  refine ⟨F, hFa, hF, μ, hμ.1, hμ.2.1, hμ.2.2, ?_⟩
  intro u hu
  obtain ⟨S, hS, hKS⟩ := exists_stable_matrixKTransform_scalar_solution_below_trace_support
    ν hν α hα F hFa hF μ hμ.1 hμ.2.1 hμ.2.2 u
      (fun t ht => lt_of_lt_of_le hu (csInf_le hμ.2.1.bddBelow ht))
  refine ⟨S, hS, hKS, ?_, ?_, ?_⟩
  · have he := matrixKStableInverse_potential_eq_logarithmicPotential ν hν α hα
      F hFa hF μ hμ.1 hμ.2.1 hμ.2.2 u hu
    rw [← hKS, matrixKStableInverse_matrixKTransform ν hν α hα S hS] at he
    exact he.symm
  · exact fun Q hQ => matrixKPotential_le_of_stable_scalar_solution ν hν α hα u S hS hKS Q hQ
  · exact fun T hT => det_one_add_mul_pos_of_matrixK_admissible S T.val hS.1 (hS.2.1 T hT)

end NLAlib
