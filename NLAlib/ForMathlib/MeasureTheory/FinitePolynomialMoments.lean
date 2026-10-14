import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.Algebra.Polynomial

/-! # Polynomial moments determine finite-carrier measures

Finite Lagrange interpolation turns each bounded continuous test into a polynomial
with the same values on the carrier. All polynomial moment identities therefore
determine the whole measure, without an infinite moment-determinacy assumption.
-/

noncomputable section
open MeasureTheory Polynomial Finset

namespace MeasureTheory

/-- Two finite real measures concentrated on a finite set are equal if all polynomial
integrals agree. The finite carrier need not be minimal or have positive-mass atoms. -/
theorem measure_eq_of_integral_eval_eq_of_finite_carrier {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (s : Finset ℝ)
    (hμ : ∀ᵐ x ∂μ, x ∈ s) (hν : ∀ᵐ x ∂ν, x ∈ s)
    (h : ∀ p : ℝ[X], (∫ x, p.eval x ∂μ) = ∫ x, p.eval x ∂ν) : μ = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let p := Lagrange.interpolate s id f
  have hp (x : ℝ) (hx : x ∈ s) : p.eval x = f x := by
    exact Lagrange.eval_interpolate_at_node f (fun _ _ _ _ h => h) hx
  calc
    (∫ x, f x ∂μ) = ∫ x, p.eval x ∂μ := integral_congr_ae (by
      filter_upwards [hμ] with x hx
      exact (hp x hx).symm)
    _ = ∫ x, p.eval x ∂ν := h p
    _ = ∫ x, f x ∂ν := integral_congr_ae (by
      filter_upwards [hν] with x hx
      exact hp x hx)

end MeasureTheory
