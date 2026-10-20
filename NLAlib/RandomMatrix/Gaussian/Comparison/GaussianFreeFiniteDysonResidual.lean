import NLAlib.Matrix.Norms.EntryBounds
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteDysonResolvent
import NLAlib.Matrix.Functions.CoefficientSandwichSum
import NLAlib.Matrix.Norms.LinearCovarianceExpectation
import NLAlib.ForMathlib.MeasureTheory.BilinearCentering

/-! # Genuine finite-N Dyson covariance error

The exact native Gaussian equation and actual normalized partial-trace
Poincare estimate yield an N⁻² residual. Every mean, covariance product and
spectral norm is taken in the true model; no asymptotic endpoint is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]
local notation "K" => GaussianFreeFiniteCoordinate ι n
local notation "E" => K → ℝ
local notation "M" => Matrix (d×n) (d×n) ℂ
local notation "C" => Matrix d d ℂ

open scoped Matrix.Norms.L2Operator in
private def residualEntryCLM (a b : d) : C →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => T a b
      map_add' := by intro T U; rfl
      map_smul' := by intro c T; rfl }

open scoped Matrix.Norms.L2Operator in
/-- The genuine finite-N expected GUE resolvent has a Dyson residual of
order N⁻², uniformly in the deterministic mean and the real part of the
nonreal spectral parameter. The dimension factor is internal to endpoint
identification; the actual original coefficient entry covariance is kept.
Source: native Gaussian integration by parts and Poincare, arXiv:2108.06312v2.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem specNorm_gaussianFreeFiniteDysonResolvent_residual_le [Nonempty n]
    (A₀ : C) (hA₀ : A₀.IsHermitian)
    (A : ι → C) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im≠0) :
    let m := gaussianFreeFiniteDysonResolvent (n := n) A₀ A ζ
    let S := coefficientSandwichSum A
    specNorm ((ζ • (1 : C)-A₀-S m)*m-1) ≤
      (Fintype.card d : ℝ)^2*‖S‖*
        (specNorm (coefficientCovariance A)/(Fintype.card n : ℝ)^2*|ζ.im|⁻¹^4) := by
  dsimp only
  let m := gaussianFreeFiniteDysonResolvent (n := n) A₀ A ζ
  let S := coefficientSandwichSum A
  let R : E → M := fun x => resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) ζ
  let Q : E → C := fun x => normalizedPartialTrace (R x)
  let D : E → C := fun x => Q x-m
  let V := specNorm (coefficientCovariance A)/(Fintype.card n : ℝ)^2*|ζ.im|⁻¹^4
  have hReq : R=gaussianFreeFiniteResolventWord A₀ A 0 (fun _ : Fin 1 => ζ) := by
    funext x
    simp [R,gaussianFreeFiniteResolventWord]
  have hRcont : Continuous R := by
    rw [hReq]
    exact (contDiff_gaussianFreeFiniteResolventWord A₀ hA₀ A hA 0 _ (fun _ => hζ) (r := 0)).continuous
  have hRi : Integrable R (gaussianVector K) := by
    rw [hReq]
    exact integrable_gaussianFreeFiniteResolventWord A₀ hA₀ A hA 0 _ (fun _ => hζ)
  have hQcont : Continuous Q := (normalizedPartialTraceCLM (d := d) (n := n)).continuous.comp hRcont
  have hQ (x : E) : ‖Q x‖≤|ζ.im|⁻¹ :=
    (specNorm_normalizedPartialTrace_le _).trans
      ((gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA 0 x).specNorm_resolvent_le hζ)
  have hQi : Integrable Q (gaussianVector K) :=
    Integrable.of_bound hQcont.aestronglyMeasurable _ (Filter.Eventually.of_forall hQ)
  have hm : ‖m‖≤|ζ.im|⁻¹ := specNorm_gaussianFreeFiniteDysonResolvent_le (n := n) A₀ hA₀ A hA ζ hζ
  have hmean : (∫ x, Q x ∂gaussianVector K)=m :=
    (normalizedPartialTraceCLM (d := d) (n := n)).integral_comp_comm hRi
  have hDcont : Continuous D := hQcont.sub continuous_const
  have hD (x : E) : ‖D x‖≤2*|ζ.im|⁻¹ :=
    (norm_sub_le _ _).trans (by linarith [hQ x,hm])
  have hDi (a b : d) : Integrable (fun x : E => ‖D x a b‖^2) (gaussianVector K) := by
    have hc : Continuous (fun x : E => ‖D x a b‖^2) :=
      ((residualEntryCLM a b).continuous.comp hDcont).norm.pow 2
    refine Integrable.of_bound hc.aestronglyMeasurable ((2*|ζ.im|⁻¹)^2) ?_
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((norm_apply_le_specNorm (D x) a b).trans (hD x)) 2
  have hV (a b : d) : (∫ x : E, ‖D x a b‖^2 ∂gaussianVector K)≤V := by
    simpa only [D,Q,m,gaussianFreeFinitePartialTraceResolventEntry,Matrix.sub_apply] using
      integral_norm_partialTraceResolventEntry_sub_dyson_sq_le (n := n) A₀ hA₀ A hA ζ hζ a b
  let B : C →L[ℂ] C →L[ℂ] C := (ContinuousLinearMap.mul ℂ C).bilinearComp
    S (ContinuousLinearMap.id ℂ C)
  have hB (T U : C) : B T U=S T*U := rfl
  have hBcont : Continuous (fun x : E => B (Q x) (Q x)) :=
    (B.continuous.comp hQcont).clm_apply hQcont
  have hBbound (x : E) : ‖B (Q x) (Q x)‖≤‖S‖*|ζ.im|⁻¹^2 := by
    rw [hB]
    calc
      _ ≤ ‖S (Q x)‖*‖Q x‖ := norm_mul_le _ _
      _ ≤ (‖S‖*‖Q x‖)*‖Q x‖ := mul_le_mul_of_nonneg_right (S.le_opNorm _) (norm_nonneg _)
      _ ≤ (‖S‖*|ζ.im|⁻¹)*|ζ.im|⁻¹ := by gcongr <;> exact hQ x
      _ = _ := by ring
  have hBi : Integrable (fun x => B (Q x) (Q x)) (gaussianVector K) :=
    Integrable.of_bound hBcont.aestronglyMeasurable _ (Filter.Eventually.of_forall hBbound)
  have hcov := B.integral_bilinear_sub_integral Q hQi hBi
  rw [hmean] at hcov
  simp only [hB] at hcov
  change (∫ x, S (D x)*D x ∂gaussianVector K)=
    (∫ x, S (Q x)*Q x ∂gaussianVector K)-S m*m at hcov
  have hraw := gaussianFreeFiniteDysonResolvent_raw_dyson (n := n) A₀ hA₀ A hA ζ hζ
  change (ζ • (1 : C)-A₀)*m-(∫ x, (∑ i, A i*Q x*A i)*Q x ∂gaussianVector K)=1 at hraw
  simp_rw [← coefficientSandwichSum_apply_of_isHermitian A hA] at hraw
  have hres : (ζ • (1 : C)-A₀-S m)*m-1=
      ∫ x, S (D x)*D x ∂gaussianVector K := by
    rw [hcov,sub_mul,sub_eq_iff_eq_add.mp hraw]
    abel
  rw [hres]
  exact specNorm_integral_linearMap_mul_le_card_sq_mul_entry_second_moment S D
    hDcont.aestronglyMeasurable hDi V hV

end NLAlib
