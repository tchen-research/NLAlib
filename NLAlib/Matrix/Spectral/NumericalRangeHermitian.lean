import NLAlib.Matrix.Spectral.NumericalRangeNormal
import NLAlib.Matrix.Spectral.Core
import NLAlib.Matrix.Inequalities.AccretiveKernels
import Mathlib.Topology.Order.Monotone

/-!
# Real projections of the numerical range

Taking real parts of quadratic forms gives the Hermitian part. Its normal
numerical range is a finite spectral convex hull, hence its extreme eigenvalue
interval. Positive dimension is explicit because the empty numerical range
cannot project onto a nonempty closed interval.
Source: Horn–Johnson (1991), Chapter 1. Atlas: `field-of-values-def`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem convexHull_real_finite_eq_Icc {s : Set ℝ}
    (hs : s.Finite) (hne : s.Nonempty) : convexHull ℝ s = Set.Icc (sInf s) (sSup s) := by
  have hlo := hs.isClosed.csInf_mem hne hs.bddBelow
  have hhi := hs.isClosed.csSup_mem hne hs.bddAbove
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_Icc _ _)
    intro x hx
    exact ⟨csInf_le hs.bddBelow hx, le_csSup hs.bddAbove hx⟩
  · have hle : sInf s ≤ sSup s := csInf_le hs.bddBelow hhi
    rw [← segment_eq_Icc hle, ← convexHull_pair]
    apply convexHull_mono
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hlo
    · simpa only [Set.mem_singleton_iff] using hx ▸ hhi

omit [DecidableEq n] in
/-- The real projection of a matrix's numerical range agrees with that of its
Hermitian part; the statement also includes the empty numerical range. -/
theorem re_image_numericalRange_eq_selfAdjointPart (A : Matrix n n ℂ) :
    Complex.re '' numericalRange A =
      Complex.re '' numericalRange (selfAdjointPart ℝ A : Matrix n n ℂ) := by
  ext r
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨quadForm (selfAdjointPart ℝ A : Matrix n n ℂ) x, ⟨x, hx, rfl⟩, ?_⟩
    rw [quadForm_selfAdjointPart, Complex.ofReal_re]
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨quadForm A x, ⟨x, hx, rfl⟩, ?_⟩
    rw [quadForm_selfAdjointPart, Complex.ofReal_re]

/-- In positive dimension the real projection of the numerical range is the
closed interval between the extreme eigenvalues of the Hermitian part.
Source: Horn–Johnson (1991), Chapter 1.
atlas: field-of-values-def (partial) -/
theorem re_image_numericalRange_eq_Icc [Nonempty n] (A : Matrix n n ℂ) :
    Complex.re '' numericalRange A =
      Set.Icc (lambdaMin (selfAdjointPart ℝ A : Matrix n n ℂ))
        (lambdaMax (selfAdjointPart ℝ A : Matrix n n ℂ)) := by
  let H : Matrix n n ℂ := selfAdjointPart ℝ A
  have hH : H.IsHermitian := by
    change (selfAdjointPart ℝ A : Matrix n n ℂ)ᴴ = _
    exact (selfAdjointPart ℝ A).property
  have hnormal : H * Hᴴ = Hᴴ * H := by rw [hH.eq]
  rw [re_image_numericalRange_eq_selfAdjointPart]
  change Complex.re '' numericalRange H = _
  rw [numericalRange_eq_convexHull_spectrum_of_normal H hnormal]
  have himage := Complex.reCLM.toLinearMap.image_convexHull (spectrum ℂ H)
  change Complex.re '' convexHull ℝ (spectrum ℂ H) =
    convexHull ℝ (Complex.re '' spectrum ℂ H) at himage
  rw [himage, hH.spectrum_eq_image_range, Set.image_image]
  have hcomp : (fun x : ℝ => (RCLike.ofReal x : ℂ).re) ''
      Set.range hH.eigenvalues = Set.range hH.eigenvalues := by
    ext x
    simp
  change convexHull ℝ ((fun x : ℝ => (RCLike.ofReal x : ℂ).re) ''
    Set.range hH.eigenvalues) = _
  rw [hcomp]
  rw [convexHull_real_finite_eq_Icc (Set.finite_range _) (Set.range_nonempty _)]
  change Set.Icc (sInf (Set.range hH.eigenvalues)) (sSup (Set.range hH.eigenvalues)) =
    Set.Icc (lambdaMin H) (lambdaMax H)
  rw [lambdaMin, lambdaMax, hH.spectrum_real_eq_range_eigenvalues]

end NLAlib
