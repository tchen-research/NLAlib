import NLAlib.Polynomial.FunctionApproximation.ChebyshevTensor

/-!
# Compactness and integration on the Chebyshev cube

These finite-dimensional support facts allow arbitrary laws on the closed
cube, including atoms on its boundary, to use continuous-observable estimates.
-/

noncomputable section

open Set MeasureTheory

namespace NLAlib

/-- The actual closed Chebyshev cube is compact in its Euclidean metric. -/
theorem isCompact_chebyshevCube {ι : Type*} [Fintype ι] :
    IsCompact (chebyshevCube ι) := by
  have hc : IsCompact (Set.univ.pi (fun _ : ι => Icc (-1 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  convert hc.image (PiLp.continuous_toLp 2 _) using 1
  ext x
  constructor
  · intro hx
    exact ⟨WithLp.ofLp x, fun i _ => hx i, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    exact fun i => hy i (Set.mem_univ i)

/-- Every continuous-on-cube observable is integrable for any finite law
supported on the cube. -/
theorem integrable_of_ae_mem_chebyshevCube_of_continuousOn
    {ι : Type*} [Fintype ι] (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ chebyshevCube ι) {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ContinuousOn f (chebyshevCube ι)) : Integrable f μ := by
  have hi := hf.integrableOn_compact (μ := μ) isCompact_chebyshevCube
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at hi

end NLAlib
