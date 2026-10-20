import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteArcCovariance
import NLAlib.Matrix.Functions.MixedResolventArcSplit

/-! # Actual finite-N covariance gradients are genuine crossing words

The native derivative formula and exact positive-arc reindexing identify
the Gaussian covariance contraction with the literal alternating coefficient
crossing functional, retaining the true dimension-normalized trace.
Source: arXiv:2108.06312v2, Lemma 6.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix Kronecker
namespace NLAlib
variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]
local notation "K" => GaussianFreeFiniteCoordinate ι n
local notation "E" => K → ℝ
local notation "M" => Matrix (d × n) (d × n) ℂ

open scoped Matrix.Norms.L2Operator in
/-- A genuine native mixed arc's single-coordinate derivative is the exact
finite sum of two positive native arcs with the actual coefficient between
them. No direction commutation or derivative identity is assumed. -/
theorem fderiv_gaussianFreeFiniteMixedArc_single_eq_sum_split
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b : ℕ) (x : E) (k : K) :
    fderiv ℝ (gaussianFreeFiniteMixedArc (n := n) A₀ A q ζ a b) x (Pi.single k 1) =
      ∑ j : Fin (a + b),
        gaussianFreeFiniteMixedArc A₀ A q ζ
          (mixedResolventSplitLeft a b j).1 (mixedResolventSplitLeft a b j).2 x *
        gaussianFreeFiniteCoefficient A q k *
        gaussianFreeFiniteMixedArc A₀ A q ζ
          (mixedResolventSplitRight a b j).1 (mixedResolventSplitRight a b j).2 x := by
  have hh : (∑ l : K, (Pi.single k (1 : ℝ) : E) l • gaussianFreeFiniteCoefficient A q l) =
      gaussianFreeFiniteCoefficient A q k := by simp
  have hd := fderiv_gaussianFreeFiniteMixedArc_apply (n := n)
    A₀ hA₀ A hA q ζ hζ a b x (Pi.single k 1 : E)
  simp only [hh] at hd
  refine hd.trans ?_
  simpa only [gaussianFreeFiniteMixedArc] using
    mixed_power_insertion_sum_eq_sum_split
      (resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ)
      (resolvent (gaussianFreeFiniteInterpolation A₀ A q x) (star ζ))
      (gaussianFreeFiniteCoefficient A q k) a b

open scoped Matrix.Norms.L2Operator in
/-- The actual coordinate-gradient contraction of two native mixed arcs is
the finite four-arc coefficient crossing. The outer family is arbitrary;
the inner family is exactly the true interpolation coefficient family.
Source: arXiv:2108.06312v2, Lemma 6.3.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem sum_nativeMixedArc_gradient_sandwich_eq_crossing
    {κ : Type*} [Fintype κ] [DecidableEq κ] (C : κ → M)
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im ≠ 0) (a b c e : ℕ) (x y : E) :
    (∑ k : K, ∑ i : κ, normalizedSandwichTraceBilinear (C i)
      (fderiv ℝ (gaussianFreeFiniteMixedArc A₀ A q ζ a b) x (Pi.single k 1))
      (fderiv ℝ (gaussianFreeFiniteMixedArc A₀ A q ζ c e) y (Pi.single k 1))) =
      (Fintype.card (d × n) : ℂ)⁻¹ * ∑ l : Fin (a + b), ∑ m : Fin (c + e),
        coefficientCrossingTraceMultilinear C (gaussianFreeFiniteCoefficient A q)
          ![gaussianFreeFiniteMixedArc A₀ A q ζ (mixedResolventSplitLeft a b l).1 (mixedResolventSplitLeft a b l).2 x,
            gaussianFreeFiniteMixedArc A₀ A q ζ (mixedResolventSplitRight a b l).1 (mixedResolventSplitRight a b l).2 x,
            gaussianFreeFiniteMixedArc A₀ A q ζ (mixedResolventSplitLeft c e m).1 (mixedResolventSplitLeft c e m).2 y,
            gaussianFreeFiniteMixedArc A₀ A q ζ (mixedResolventSplitRight c e m).1 (mixedResolventSplitRight c e m).2 y] := by
  simp only [fderiv_gaussianFreeFiniteMixedArc_single_eq_sum_split A₀ hA₀ A hA q ζ hζ,
    normalizedSandwichTraceBilinear_apply]
  rw [Finset.sum_comm]
  exact sum_normalizedTrace_sandwich_sums_eq_inv_card_mul_sum_crossing C
    (gaussianFreeFiniteCoefficient A q) _ _ _ _

end NLAlib
