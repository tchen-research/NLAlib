import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-! # Inverse bounds from imaginary-part coercivity

If the imaginary part of an operator's quadratic form is bounded below by
`η` times squared length, every negative right inverse has norm at most
`η⁻¹`. This generic Hilbert-space estimate supplies the basic matrix Dyson
bound without a diagonalization or normality assumption.
-/

noncomputable section

namespace ContinuousLinearMap

/-- Imaginary-part coercivity bounds a negative right inverse. In particular
this applies to the operator form of a matrix Dyson equation.
Source: Ajanki--Erdős--Krüger, Proposition 2.1, proof of equation (4.1). -/
theorem norm_le_inv_of_im_inner_coercive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T M : E →L[ℂ] E) {η : ℝ} (hη : 0 < η)
    (hTM : ∀ x, T (M x) = -x)
    (hcoercive : ∀ x, η * ‖x‖ ^ 2 ≤ (inner ℂ x (T x)).im) :
    ‖M‖ ≤ η⁻¹ := by
  apply opNorm_le_bound _ (inv_nonneg.mpr hη.le)
  intro x
  have hbound : η * ‖M x‖ ^ 2 ≤ ‖M x‖ * ‖x‖ := by
    calc
      _ ≤ (inner ℂ (M x) (T (M x))).im := hcoercive (M x)
      _ ≤ ‖inner ℂ (M x) (T (M x))‖ := Complex.im_le_norm _
      _ = ‖inner ℂ (M x) (-x)‖ := by rw [hTM]
      _ ≤ ‖M x‖ * ‖-x‖ := norm_inner_le_norm _ _
      _ = _ := by rw [norm_neg]
  by_cases hzero : ‖M x‖ = 0
  · rw [hzero]
    positivity
  have hpos : 0 < ‖M x‖ := (norm_nonneg _).lt_of_ne' hzero
  have hmul : η * ‖M x‖ ≤ ‖x‖ := by nlinarith
  exact (le_inv_mul_iff₀ hη).mpr hmul

end ContinuousLinearMap
