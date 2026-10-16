import NLAlib.Matrix.Norms.Core
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Rational functional calculus on a complex normal matrix

Only the denominator is required to be nonzero on the spectrum. This is the
finite-dimensional normal-matrix interface needed for rational displacement.
-/

noncomputable section
open Polynomial
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A polynomial without zeros on a normal matrix's spectrum evaluates to an
invertible matrix. -/
theorem isUnit_aeval_of_normal (A : Matrix n n ℂ) (hA : A * Aᴴ = Aᴴ * A)
    (q : ℂ[X]) (hq : ∀ z ∈ spectrum ℂ A, q.eval z ≠ 0) : IsUnit (aeval A q) := by
  let : IsStarNormal A := ⟨hA.symm⟩
  rw [← cfc_polynomial q A]
  exact (isUnit_cfc_iff _ _ q.continuous.continuousOn).mpr hq

/-- Rational matrix evaluation agrees with the actual continuous functional
calculus, with total inverse used only where its denominator is invertible. -/
theorem cfc_inv_polynomial_mul_polynomial (A : Matrix n n ℂ)
    (hA : A * Aᴴ = Aᴴ * A) (p q : ℂ[X])
    (hq : ∀ z ∈ spectrum ℂ A, q.eval z ≠ 0) :
    cfc (fun z => (q.eval z)⁻¹ * p.eval z) A = (aeval A q)⁻¹ * aeval A p := by
  let : IsStarNormal A := ⟨hA.symm⟩
  have hcq : ContinuousOn (fun z => (q.eval z)⁻¹) (spectrum ℂ A) :=
    q.continuous.continuousOn.inv₀ hq
  rw [cfc_mul _ _ A hcq p.continuous.continuousOn, cfc_inv q.eval A hq,
    cfc_polynomial q A, cfc_polynomial p A, ← Matrix.nonsing_inv_eq_ringInverse]

/-- Spectral bounds on the scalar rational function bound the actual normal
matrix rational function. Source: user derivations, rational displacement.
atlas: displacement-singular-value-decay (partial), adi-sylvester-rational-error (partial) -/
theorem specNorm_inv_aeval_mul_aeval_le (A : Matrix n n ℂ)
    (hA : A * Aᴴ = Aᴴ * A) (p q : ℂ[X])
    (hq : ∀ z ∈ spectrum ℂ A, q.eval z ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ z ∈ spectrum ℂ A, ‖p.eval z / q.eval z‖ ≤ c) :
    specNorm ((aeval A q)⁻¹ * aeval A p) ≤ c := by
  let : IsStarNormal A := ⟨hA.symm⟩
  rw [← cfc_inv_polynomial_mul_polynomial A hA p q hq, specNorm_eq_norm]
  apply norm_cfc_le hc
  intro z hz
  simpa [div_eq_mul_inv, mul_comm] using hbound z hz

/-- The equivalent right-inverse ordering of rational matrix evaluation. -/
theorem specNorm_aeval_mul_inv_aeval_le (A : Matrix n n ℂ)
    (hA : A * Aᴴ = Aᴴ * A) (p q : ℂ[X])
    (hq : ∀ z ∈ spectrum ℂ A, q.eval z ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ z ∈ spectrum ℂ A, ‖p.eval z / q.eval z‖ ≤ c) :
    specNorm (aeval A p * (aeval A q)⁻¹) ≤ c := by
  let : IsStarNormal A := ⟨hA.symm⟩
  have hcalc : cfc (fun z => p.eval z / q.eval z) A = aeval A p * (aeval A q)⁻¹ := by
    rw [cfc_map_div p.eval q.eval A hq, cfc_polynomial p A, cfc_polynomial q A,
      ← Matrix.nonsing_inv_eq_ringInverse]
  rw [← hcalc, specNorm_eq_norm]
  exact norm_cfc_le hc hbound

end NLAlib
