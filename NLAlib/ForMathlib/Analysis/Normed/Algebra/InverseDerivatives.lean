import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# Ordered all-order derivatives of inversion and resolvents

The geometric power series gives actual native iterated Fréchet derivatives
as finite sums of ordered insertion words. All orders, including zero, are
included. Only the base point needs to be invertible; no global analyticity
or invertibility of perturbed arguments is assumed.
-/

noncomputable section
set_option autoImplicit false
open scoped Ring

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
  [NormedRing A] [NormedAlgebra 𝕜 A]

private def inverseSubSeries (R : A) : FormalMultilinearSeries 𝕜 A A :=
  ((ContinuousLinearMap.mul 𝕜 A).flip R).compFormalMultilinearSeries
    ((formalMultilinearSeries_geometric 𝕜 A).compContinuousLinearMap
      (ContinuousLinearMap.mul 𝕜 A R))

private theorem inverseSubSeries_apply (R : A) {k : ℕ} (H : Fin k → A) :
    inverseSubSeries (𝕜 := 𝕜) R k H =
      (List.ofFn (fun i => R * H i)).prod * R := rfl

private theorem inverse_sub_eq_inverse_one_sub_mul {b : A} (hb : IsUnit b) (x : A) :
    (b - x)⁻¹ʳ = (1 - b⁻¹ʳ * x)⁻¹ʳ * b⁻¹ʳ := by
  have hf : b - x = b * (1 - b⁻¹ʳ * x) := by
    rw [mul_sub, mul_one, ← mul_assoc, Ring.mul_inverse_cancel b hb, one_mul]
  rw [hf, Ring.inverse_mul (Or.inl hb)]

private theorem hasFPowerSeriesOnBall_inverse_sub [HasSummableGeomSeries A]
    {b : A} (hb : IsUnit b) :
    HasFPowerSeriesOnBall (fun x : A => (b - x)⁻¹ʳ)
      (inverseSubSeries (𝕜 := 𝕜) b⁻¹ʳ) 0
      (1 / ‖ContinuousLinearMap.mul 𝕜 A b⁻¹ʳ‖ₑ) := by
  let L : A →L[𝕜] A := ContinuousLinearMap.mul 𝕜 A b⁻¹ʳ
  have hg : HasFPowerSeriesOnBall (fun x : A => (1 - x)⁻¹ʳ)
      (formalMultilinearSeries_geometric 𝕜 A) (L 0) 1 := by
    simpa only [map_zero] using hasFPowerSeriesOnBall_inverse_one_sub 𝕜 A
  have hc : HasFPowerSeriesOnBall ((fun x : A => (1 - x)⁻¹ʳ) ∘ L)
      ((formalMultilinearSeries_geometric 𝕜 A).compContinuousLinearMap L)
      (0 : A) (1 / ‖L‖ₑ) := hg.compContinuousLinearMap
  have hp := ((ContinuousLinearMap.mul 𝕜 A).flip b⁻¹ʳ).comp_hasFPowerSeriesOnBall
    hc
  apply hp.congr
  intro x _
  exact (inverse_sub_eq_inverse_one_sub_mul hb x).symm

/-- The native iterated Fréchet derivative of inversion with a negative
perturbation is the sum over all ordered insertion permutations. The base
shift is an actual unit, and no global smoothness premise is imposed.
Source: the Banach-algebra geometric series; used in Brailovskaya–van Handel,
arXiv:2201.05142v3, Lemma 6.9. -/
theorem iteratedFDeriv_ringInverse_sub_apply [CompleteSpace A]
    {b : A} (hb : IsUnit b) {k : ℕ} (H : Fin k → A) :
    iteratedFDeriv 𝕜 k (fun x : A => (b - x)⁻¹ʳ) 0 H =
      ∑ σ : Equiv.Perm (Fin k),
        (List.ofFn (fun i => b⁻¹ʳ * H (σ i))).prod * b⁻¹ʳ := by
  rw [(hasFPowerSeriesOnBall_inverse_sub (𝕜 := 𝕜) hb).iteratedFDeriv_eq_sum_of_completeSpace]
  simp only [inverseSubSeries_apply]

/-- Every native resolvent derivative is the finite ordered insertion sum.
Only membership of the base scalar in the actual resolvent set is required.
The formula also includes derivative order zero and trivial algebras.
Source: geometric-series differentiation, as in Brailovskaya–van Handel,
arXiv:2201.05142v3, Lemma 6.9. -/
theorem iteratedFDeriv_resolvent_apply [CompleteSpace A]
    {a : A} {ζ : 𝕜} (hζ : ζ ∈ resolventSet 𝕜 a) {k : ℕ} (H : Fin k → A) :
    iteratedFDeriv 𝕜 k (fun x : A => resolvent x ζ) a H =
      ∑ σ : Equiv.Perm (Fin k),
        (List.ofFn (fun i => resolvent a ζ * H (σ i))).prod * resolvent a ζ := by
  have hb : IsUnit (algebraMap 𝕜 A ζ - a) := hζ
  have hp := (hasFPowerSeriesOnBall_inverse_sub (𝕜 := 𝕜) hb).comp_sub a
  have heq : (fun x : A => ((algebraMap 𝕜 A ζ - a) - (x - a))⁻¹ʳ) =
      (fun x : A => resolvent x ζ) := by
    funext x
    unfold resolvent
    congr 1
    abel
  simp only [zero_add, heq] at hp
  rw [hp.iteratedFDeriv_eq_sum_of_completeSpace]
  simp only [inverseSubSeries_apply, resolvent]
