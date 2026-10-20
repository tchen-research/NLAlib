import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteResolventStein
import NLAlib.RandomMatrix.Gaussian.Basic.GUECovarianceAction
import NLAlib.Matrix.Structured.NormalizedPartialTrace

/-! # The actual finite-N Gaussian resolvent Dyson identity

Coordinate Gaussian integration by parts and the true GUE covariance action
produce the genuine expectation equation. Its fluctuation covariance will
be estimated separately by the native normalized partial-trace gradient.
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
local notation "M" => Matrix (d×n) (d×n) ℂ

open scoped Matrix.Norms.L2Operator in
/-- The genuine affine Gaussian model's expected shifted resolvent equals
its identity plus the actual integrated covariance sandwich. This exact
native equation assumes no model or moment comparison interface. -/
theorem shifted_integral_gaussianFreeFiniteResolvent
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im≠0) :
    (ζ • (1 : M)-A₀⊗ₖ(1 : Matrix n n ℂ))*
      (∫ x : E, resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ ∂gaussianVector K) =
      1+∫ x : E,
        (∑ k, gaussianFreeFiniteCoefficient A q k*
          resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ*
          gaussianFreeFiniteCoefficient A q k)*
            resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ ∂gaussianVector K := by
  let R : E → M := fun x => resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ
  let C := gaussianFreeFiniteCoefficient (n := n) A q
  let Z := ζ • (1 : M)-A₀⊗ₖ(1 : Matrix n n ℂ)
  let μ := gaussianVector K
  have hReq : R=gaussianFreeFiniteResolventWord A₀ A q (fun _ : Fin 1 => ζ) := by
    funext x
    simp [R,gaussianFreeFiniteResolventWord]
  have hRc : Continuous R := by
    rw [hReq]
    exact (contDiff_gaussianFreeFiniteResolventWord A₀ hA₀ A hA q _ (fun _ => hζ)
      (r := 0)).continuous
  have hR (x : E) : ‖R x‖≤|ζ.im|⁻¹ :=
    (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x).specNorm_resolvent_le hζ
  have hi : Integrable R μ :=
    Integrable.of_bound hRc.aestronglyMeasurable _ (Filter.Eventually.of_forall hR)
  have hxi (k : K) : Integrable (fun x : E => x k • R x) μ :=
    ((memLp_two_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector k)).integrable one_le_two).smul_bdd _ hRc.aestronglyMeasurable (Filter.Eventually.of_forall hR)
  have hci (k : K) : Integrable (fun x : E => R x*C k*R x) μ := by
    refine Integrable.of_bound ((hRc.mul_const _).mul hRc).aestronglyMeasurable
      (|ζ.im|⁻¹^2*‖C k‖) (Filter.Eventually.of_forall fun x => ?_)
    calc
      _ ≤ (‖R x‖*‖C k‖)*‖R x‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (|ζ.im|⁻¹*‖C k‖)*|ζ.im|⁻¹ := by gcongr <;> exact hR x
      _ = _ := by ring
  have hpoint (x : E) : Z*R x=1+∑ k : K, C k*(x k • R x) := by
    have hu := (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x).isUnit_smul_one_sub_of_im_ne_zero hζ
    have hinv : (ζ • (1 : M)-gaussianFreeFiniteInterpolation A₀ A q x)*R x=1 := by
      simpa only [R,resolvent,Algebra.algebraMap_eq_smul_one] using
        Ring.mul_inverse_cancel (ζ • (1 : M)-gaussianFreeFiniteInterpolation A₀ A q x) hu
    calc
      _ = (ζ • (1 : M)-gaussianFreeFiniteInterpolation A₀ A q x)*R x+
          (∑ k, x k • C k)*R x := by
        dsimp only [Z,C,gaussianFreeFiniteInterpolation]
        noncomm_ring
      _ = _ := by
        rw [hinv,Finset.sum_mul]
        simp only [smul_mul_assoc,mul_smul_comm]
  let P : M →L[ℂ] M := ContinuousLinearMap.mul ℂ M Z
  change Z*(∫ x, R x ∂μ)=_
  calc
    _ = ∫ x, Z*R x ∂μ := (P.integral_comp_comm hi).symm
    _ = ∫ x, (1 : M)+∑ k : K, C k*(x k • R x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = 1+∑ k : K, C k*(∫ x, x k • R x ∂μ) := by
      rw [integral_add (integrable_const _) (integrable_finsetSum _ fun k _ =>
        (hxi k).const_mul (C k)),integral_const,probReal_univ,one_smul,integral_finsetSum]
      · congr 1
        apply Finset.sum_congr rfl
        intro k _
        exact (ContinuousLinearMap.mul ℂ M (C k)).integral_comp_comm (hxi k)
      · intro k _
        exact (hxi k).const_mul _
    _ = 1+∑ k : K, C k*(∫ x, R x*C k*R x ∂μ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_coordinate_smul_gaussianFreeFiniteResolvent A₀ hA₀ A hA q ζ hζ k]
    _ = 1+∫ x, ∑ k : K, C k*(R x*C k*R x) ∂μ := by
      rw [integral_finsetSum]
      · congr 1
        apply Finset.sum_congr rfl
        intro k _
        exact ((ContinuousLinearMap.mul ℂ M (C k)).integral_comp_comm (hci k)).symm
      · intro k _
        exact (hci k).const_mul _
    _ = _ := by
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      simp only [R,C,Matrix.mul_assoc]

end NLAlib
