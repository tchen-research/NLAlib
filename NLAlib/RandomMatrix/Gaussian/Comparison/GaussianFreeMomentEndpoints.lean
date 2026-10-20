import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteMomentPath
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeDiagonalEndpoint
import NLAlib.Probability.Transforms.ResolventMixedMoments

/-! # The true diagonal endpoint of expected Gaussian Gram moments -/

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

private theorem mixed_constant_resolventWord_prod
    {v : Type*} [Fintype v] [DecidableEq v]
    (Y : Matrix v v ℂ) (ζ : ℂ) (p : ℕ) :
    (List.ofFn (fun j : Fin (p + p) => resolvent Y
      ((Fin.append (fun _ : Fin p => ζ) (fun _ : Fin p => star ζ)) j))).prod =
        resolvent Y ζ ^ p * resolvent Y (star ζ) ^ p := by
  have he : (fun j : Fin (p + p) => resolvent Y
      ((Fin.append (fun _ : Fin p => ζ) (fun _ : Fin p => star ζ)) j)) =
      Fin.append (fun _ : Fin p => resolvent Y ζ)
        (fun _ : Fin p => resolvent Y (star ζ)) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
  rw [he, List.ofFn_fin_append, List.prod_append]
  simp only [List.ofFn_const, List.prod_replicate]

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The genuine q=1 finite-ensemble Gram moment equals the actual original Gaussian matrix Gram moment, including moment order zero and empty matrix dimension.
Source: arXiv:2108.06312v2, Theorem 6.2 interpolation endpoint.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem integral_gaussianFreeFinite_resolventEvenMoment_one [Nonempty n]
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (p : ℕ) :
    (∫ x : E, resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A 1 x) ζ p
      ∂gaussianVector K) =
    ∫ x : ι → ℝ, resolventEvenMoment (A₀ + ∑ i, x i • A i) ζ p
      ∂gaussianVector ι := by
  let w : Fin (p + p) → ℂ := Fin.append (fun _ : Fin p => ζ) (fun _ : Fin p => star ζ)
  have hw : ∀ j, (w j).im ≠ 0 := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [w, Fin.append_left] using hζ
    · simpa only [w, Fin.append_right, Complex.star_def, Complex.conj_im] using neg_ne_zero.mpr hζ
  have he := integral_normalizedTrace_gaussianFreeFiniteResolventWord_one
    (n := n) A₀ hA₀ A hA w hw
  simp only [gaussianFreeFiniteResolventWord, w, mixed_constant_resolventWord_prod] at he
  have hm : Measurable (fun x : ι → ℝ => A₀ + ∑ i, x i • A i) := by fun_prop
  have hg := integral_resolventEvenMoment_eq_re_mixed_pow (gaussianVector ι)
    (fun x : ι → ℝ => A₀ + ∑ i, x i • A i) hm.aemeasurable
    (Filter.Eventually.of_forall fun x => hA₀.add (isHermitian_sum_smul_real A hA x)) hζ p
  rw [integral_gaussianFreeFinite_resolventEvenMoment_eq_re A₀ hA₀ A hA 1 ζ hζ p, hg]
  simpa only [gaussianFreeFiniteMixedArc] using congrArg Complex.re he

end NLAlib
