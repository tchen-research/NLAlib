import NLAlib.Probability.Gaussian.Moments.Hermite
import NLAlib.Matrix.Structured.HermiteIndices
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Finite Gaussian Hermite expansion isometry

A finite normalized Hermite expansion has exactly its coefficient Euclidean
norm as its Gaussian squared-integral norm. This is a finite sum identity,
with all pairwise integrability proved before interchanging sums and integrals.
Supports `gaussian-series-partial-transpose-norm`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Finset
namespace NLAlib
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

/-- The actual polynomial represented by a finite vector in the normalized
total-degree occupation basis. -/
def hermiteExpansion (z : HermiteIndex ι p → ℂ) (x : ι → ℝ) : ℂ :=
  ∑ a, z a * (productHermite a.val x : ℂ)

/-- Finite Hermite expansion commutes with finite sums of coefficient vectors. -/
theorem hermiteExpansion_sum {κ : Type*} [Fintype κ]
    (z : κ → HermiteIndex ι p → ℂ) (x : ι → ℝ) :
    hermiteExpansion (fun a => ∑ k, z k a) x = ∑ k, hermiteExpansion (z k) x := by
  simp only [hermiteExpansion, Finset.sum_mul]
  exact Finset.sum_comm

/-- A complex constant factors out of a finite Hermite expansion. -/
theorem hermiteExpansion_const_mul (c : ℂ) (z : HermiteIndex ι p → ℂ) (x : ι → ℝ) :
    hermiteExpansion (fun a => c * z a) x = c * hermiteExpansion z x := by
  simp only [hermiteExpansion, Finset.mul_sum, mul_assoc]

private theorem expansion_pairing (z w : HermiteIndex ι p → ℂ) (x : ι → ℝ) :
    star (hermiteExpansion z x) * hermiteExpansion w x =
      ∑ a, ∑ b, (star (z a) * w b) *
        ((productHermite a.val x * productHermite b.val x : ℝ) : ℂ) := by
  simp only [hermiteExpansion, map_sum, map_mul, Complex.star_def,
    Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum, Complex.ofReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Pairings of finite complex Hermite expansions are Gaussian integrable. -/
theorem integrable_hermiteExpansion_pairing (z w : HermiteIndex ι p → ℂ) :
    Integrable (fun x => star (hermiteExpansion z x) * hermiteExpansion w x)
      (gaussianVector ι) := by
  simp_rw [expansion_pairing]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    ((integrable_productHermite_mul a.val b.val).ofReal).const_mul _

/-- The Gaussian integral pairing is the ordinary finite coefficient pairing. -/
theorem integral_hermiteExpansion_pairing (z w : HermiteIndex ι p → ℂ) :
    (∫ x, star (hermiteExpansion z x) * hermiteExpansion w x ∂gaussianVector ι) =
      ∑ a, star (z a) * w a := by
  simp_rw [expansion_pairing]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
    ((integrable_productHermite_mul a.val b.val).ofReal).const_mul _))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ =>
    ((integrable_productHermite_mul a.val b.val).ofReal).const_mul _)]
  simp only [integral_const_mul, integral_complex_ofReal, integral_productHermite_mul]
  have he (b : HermiteIndex ι p) : a.val = b.val ↔ a = b := Subtype.ext_iff.symm
  simp_rw [he]
  simp [apply_ite, eq_comm]

private theorem re_star_mul_self (z : ℂ) : RCLike.re (star z * z) = ‖z‖ ^ 2 := by
  change (star z * z).re = _
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The actual Gaussian squared norm of a finite Hermite polynomial equals
the finite squared Euclidean norm of its complex coefficient vector. -/
theorem integral_norm_sq_hermiteExpansion (z : HermiteIndex ι p → ℂ) :
    (∫ x, ‖hermiteExpansion z x‖ ^ 2 ∂gaussianVector ι) = ∑ a, ‖z a‖ ^ 2 := by
  have hh := congrArg RCLike.re (integral_hermiteExpansion_pairing z z)
  rw [← integral_re (integrable_hermiteExpansion_pairing z z)] at hh
  simpa only [map_sum, re_star_mul_self] using hh

/-- The squared norm of a finite complex Hermite expansion is integrable. -/
theorem integrable_norm_sq_hermiteExpansion (z : HermiteIndex ι p → ℂ) :
    Integrable (fun x => ‖hermiteExpansion z x‖ ^ 2) (gaussianVector ι) := by
  simpa only [re_star_mul_self] using (integrable_hermiteExpansion_pairing z z).re

end NLAlib
