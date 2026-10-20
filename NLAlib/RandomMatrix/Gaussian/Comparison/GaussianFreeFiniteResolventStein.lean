import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteResolventWords
import NLAlib.Probability.Gaussian.Calculus.CoordinateSteinBanach

/-! # Actual coordinate Stein identity for native finite-N resolvents

The nonreal resolvent is differentiable and bounded on the entire true
real coordinate space. Its unbounded coordinate product is integrable
under the genuine Gaussian law, so Stein yields the actual single-insertion
integral without supplied regularity or covariance equations.
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

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The actual coordinate derivative of the genuine affine finite-N
resolvent is the literal native single-insertion sandwich. -/
theorem fderiv_gaussianFreeFiniteResolvent_apply
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im≠0) (x h : E) :
    fderiv ℝ (fun y : E => resolvent (gaussianFreeFiniteInterpolation A₀ A q y) ζ) x h =
      resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ*
        (∑ k, h k • gaussianFreeFiniteCoefficient A q k)*
        resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ := by
  let L := gaussianFreeFiniteSeriesCLM (n := n) A q
  let T := gaussianFreeFiniteInterpolation A₀ A q x
  have hT : T.IsHermitian := gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x
  have heq : gaussianFreeFiniteInterpolation A₀ A q =
      fun y : E => A₀⊗ₖ(1 : Matrix n n ℂ)+L y := by
    funext y
    simp [gaussianFreeFiniteInterpolation,L]
  have hL : HasFDerivAt (gaussianFreeFiniteInterpolation A₀ A q) L x := by
    rw [heq]
    exact L.hasFDerivAt.const_add _
  have hR := (hasFDerivAt_resolvent_of_isHermitian ζ T hT hζ).restrictScalars ℝ
  have hc := hR.comp x hL
  change HasFDerivAt (fun y : E => resolvent (gaussianFreeFiniteInterpolation A₀ A q y) ζ) _ x at hc
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_restrictScalars',
    rationalBlockMap_apply,rationalBlockDifference_resolvent,L,
    gaussianFreeFiniteSeriesCLM_apply,T]

open scoped Matrix.Norms.L2Operator in
/-- Stein's coordinate identity for the actual native finite-N resolvent.
The Gaussian law, inverse domain, differentiability and all integrability
conditions are derived; only Hermitian coefficients and a nonreal shift
are required. Empty coordinates and matrix dimensions are allowed.
Source: arXiv:2108.06312v2, Gaussian integration by parts in Sections 5--6. -/
theorem integral_coordinate_smul_gaussianFreeFiniteResolvent
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (q : ℝ) (ζ : ℂ) (hζ : ζ.im≠0) (k : K) :
    (∫ x : E, x k • resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ
      ∂gaussianVector K) =
      ∫ x : E, resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ*
        gaussianFreeFiniteCoefficient A q k*
        resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ ∂gaussianVector K := by
  let R : E → M := fun x => resolvent (gaussianFreeFiniteInterpolation A₀ A q x) ζ
  have hReq : R=gaussianFreeFiniteResolventWord A₀ A q (fun _ : Fin 1 => ζ) := by
    funext x
    simp [R,gaussianFreeFiniteResolventWord]
  have hRc : ContDiff ℝ ⊤ R := by
    rw [hReq]
    exact contDiff_gaussianFreeFiniteResolventWord A₀ hA₀ A hA q _ (fun _ => hζ)
  have hR (x : E) : ‖R x‖≤|ζ.im|⁻¹ :=
    (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA q x).specNorm_resolvent_le hζ
  have hi : Integrable R (gaussianVector K) :=
    Integrable.of_bound hRc.continuous.aestronglyMeasurable _ (Filter.Eventually.of_forall hR)
  have hx : Integrable (fun x : E => x k) (gaussianVector K) :=
    (memLp_two_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector k)).integrable one_le_two
  have hxi : Integrable (fun x : E => x k • R x) (gaussianVector K) :=
    hx.smul_bdd _ hRc.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hR)
  have hd (x : E) : fderiv ℝ R x (Pi.single k 1)=
      R x*gaussianFreeFiniteCoefficient A q k*R x := by
    rw [fderiv_gaussianFreeFiniteResolvent_apply A₀ hA₀ A hA q ζ hζ]
    simp [R]
  have hdi : Integrable (fun x : E => fderiv ℝ R x (Pi.single k 1)) (gaussianVector K) := by
    refine Integrable.of_bound
      (((hRc.fderiv_right (m := ⊤) (by simp)).continuous.clm_apply continuous_const).aestronglyMeasurable)
      (|ζ.im|⁻¹^2*‖gaussianFreeFiniteCoefficient A q k‖) ?_
    apply Filter.Eventually.of_forall
    intro x
    rw [hd]
    calc
      _ ≤ (‖R x‖*‖gaussianFreeFiniteCoefficient A q k‖)*‖R x‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (|ζ.im|⁻¹*‖gaussianFreeFiniteCoefficient A q k‖)*|ζ.im|⁻¹ := by gcongr <;> exact hR x
      _ = _ := by ring
  have hs := integral_coordinate_smul_eq_integral_fderiv_gaussian R
    (hRc.differentiable (by simp)) k hi hxi hdi
  simpa only [hd] using hs

end NLAlib
