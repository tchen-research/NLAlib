import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFinitePartialTraceGradient
import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteDysonIdentity
import NLAlib.RandomMatrix.Gaussian.Basic.GUECovarianceAction

/-! # The actual finite-N expected GUE Dyson resolvent

The coefficient-side function is defined by the genuine normalized partial
trace of the existing ensemble resolvent expectation. Its height bound and
entrywise centered variance retain the true N-dependent normalization.
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
/-- The actual coefficient-side normalized GUE resolvent expectation.
The mean matrix is arbitrary and the ensemble is the native finite-N model. -/
def gaussianFreeFiniteDysonResolvent
    (A₀ : Matrix d d ℂ) (A : ι → Matrix d d ℂ) (ζ : ℂ) : Matrix d d ℂ :=
  normalizedPartialTrace (∫ x : E,
    resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) ζ ∂gaussianVector K)

open scoped Matrix.Norms.L2Operator in
private def matrixEntryCLM (a b : d) : Matrix d d ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => T a b
      map_add' := by intro T U; rfl
      map_smul' := by intro c T; rfl }

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
private theorem integrable_finite_gue_resolvent
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im≠0) :
    Integrable (fun x : E => resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) ζ)
      (gaussianVector K) := by
  have heq : (fun x : E => resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) ζ)=
      gaussianFreeFiniteResolventWord A₀ A 0 (fun _ : Fin 1 => ζ) := by
    funext x
    simp [gaussianFreeFiniteResolventWord]
  rw [heq]
  exact integrable_gaussianFreeFiniteResolventWord A₀ hA₀ A hA 0 _ (fun _ => hζ)

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- Each entry of the genuine finite-N Dyson function is exactly the scalar
expectation of the actual normalized partial-trace resolvent entry. -/
theorem gaussianFreeFiniteDysonResolvent_apply
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im≠0) (a b : d) :
    gaussianFreeFiniteDysonResolvent (n := n) A₀ A ζ a b=
      ∫ x : E, gaussianFreeFinitePartialTraceResolventEntry A₀ A 0 ζ a b x
        ∂gaussianVector K := by
  let P := (matrixEntryCLM a b).comp (normalizedPartialTraceCLM (d := d) (n := n))
  have he := P.integral_comp_comm (integrable_finite_gue_resolvent (n := n) A₀ hA₀ A hA ζ hζ)
  exact he.symm

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The actual finite-N expected normalized partial trace has the exact
reciprocal-height spectral norm bound, uniformly in its mean and dimension. -/
theorem specNorm_gaussianFreeFiniteDysonResolvent_le
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im≠0) :
    specNorm (gaussianFreeFiniteDysonResolvent (n := n) A₀ A ζ)≤|ζ.im|⁻¹ := by
  apply (specNorm_normalizedPartialTrace_le (d := d) (n := n)
    (∫ x : E, resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) ζ ∂gaussianVector K)).trans
  change ‖∫ x : E, resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) ζ
    ∂gaussianVector K‖≤_
  have hi := integrable_finite_gue_resolvent (n := n) A₀ hA₀ A hA ζ hζ
  calc
    _ ≤ ∫ x : E, ‖resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) ζ‖
        ∂gaussianVector K := norm_integral_le_integral_norm _
    _ ≤ ∫ _x : E, |ζ.im|⁻¹ ∂gaussianVector K := integral_mono hi.norm (integrable_const _)
      (fun x => (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA 0 x).specNorm_resolvent_le hζ)
    _ = _ := by simp

open scoped Matrix.Norms.L2Operator in
/-- Centering a native normalized GUE partial-trace entry at the actual
finite-N Dyson function gives its true N⁻² variance estimate. No limiting
Dyson solution or assumed covariance-error interface is used.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem integral_norm_partialTraceResolventEntry_sub_dyson_sq_le
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im≠0) (a b : d) :
    (∫ x : E, ‖gaussianFreeFinitePartialTraceResolventEntry A₀ A 0 ζ a b x-
      gaussianFreeFiniteDysonResolvent (n := n) A₀ A ζ a b‖^2 ∂gaussianVector K) ≤
      specNorm (coefficientCovariance A)/(Fintype.card n : ℝ)^2*|ζ.im|⁻¹^4 := by
  rw [gaussianFreeFiniteDysonResolvent_apply A₀ hA₀ A hA ζ hζ]
  exact integral_norm_partialTraceResolventEntry_sub_integral_sq_le A₀ hA₀ A hA ζ hζ a b


omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
private theorem partialTrace_finite_gue_covariance_integrand
    (A : ι → Matrix d d ℂ) (T : M) :
    normalizedPartialTrace ((∑ k : K, gaussianFreeFiniteCoefficient A 0 k*T*
      gaussianFreeFiniteCoefficient A 0 k)*T)=
      (∑ i, A i*normalizedPartialTrace T*A i)*normalizedPartialTrace T := by
  have he : (∑ k : K, gaussianFreeFiniteCoefficient A 0 k*T*
      gaussianFreeFiniteCoefficient A 0 k)=
      ∑ i, (A i*normalizedPartialTrace T*A i)⊗ₖ(1 : Matrix n n ℂ) := by
    simp only [Fintype.sum_sum_type,gaussianFreeFiniteCoefficient,Real.sqrt_zero,
      zero_smul,zero_mul,mul_zero,sub_zero,Real.sqrt_one,one_smul,
      Finset.sum_const_zero,zero_add]
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => sum_kronecker_gueCoefficientMatrix_sandwich (A i) T
  rw [he,Finset.sum_mul]
  change normalizedPartialTraceCLM (∑ i, ((A i*normalizedPartialTrace T*A i)⊗ₖ(1 : Matrix n n ℂ))*T)=_
  rw [map_sum]
  simp only [normalizedPartialTraceCLM_apply,normalizedPartialTrace_kronecker_one_mul,
    Finset.sum_mul]

open scoped Matrix.Norms.L2Operator in
/-- The actual normalized finite-N GUE expectation satisfies its exact
coefficient-side Dyson equation before covariance factorization. Every
Gaussian integration-by-parts and covariance term is derived from the
existing native ensemble, with arbitrary Hermitian deterministic mean.
Source: arXiv:2108.06312v2, Section 6.1.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem gaussianFreeFiniteDysonResolvent_raw_dyson [Nonempty n]
    (A₀ : Matrix d d ℂ) (hA₀ : A₀.IsHermitian)
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ζ : ℂ) (hζ : ζ.im≠0) :
    (ζ • (1 : Matrix d d ℂ)-A₀)*gaussianFreeFiniteDysonResolvent (n := n) A₀ A ζ-
      (∫ x : E,
        (∑ i, A i*normalizedPartialTrace (resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) ζ)*A i)*
          normalizedPartialTrace (resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) ζ)
        ∂gaussianVector K) = 1 := by
  let R : E → M := fun x => resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) ζ
  let C := gaussianFreeFiniteCoefficient (n := n) A 0
  let F : E → M := fun x => (∑ k : K, C k*R x*C k)*R x
  let P := normalizedPartialTraceCLM (d := d) (n := n)
  have hRcont : Continuous R := by
    have heq : R=gaussianFreeFiniteResolventWord A₀ A 0 (fun _ : Fin 1 => ζ) := by
      funext x
      simp [R,gaussianFreeFiniteResolventWord]
    rw [heq]
    exact (contDiff_gaussianFreeFiniteResolventWord A₀ hA₀ A hA 0 _ (fun _ => hζ)
      (r := 0)).continuous
  have hR (x : E) : ‖R x‖≤|ζ.im|⁻¹ :=
    (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA 0 x).specNorm_resolvent_le hζ
  have hFcont : Continuous F :=
    (continuous_finsetSum _ (fun k _ => (continuous_const.mul hRcont).mul continuous_const)).mul hRcont
  have hFbound (x : E) : ‖F x‖≤(∑ k : K, ‖C k‖^2)*|ζ.im|⁻¹^2 := by
    dsimp only [F]
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ k : K, ‖C k*R x*C k*R x‖ := norm_sum_le _ _
      _ ≤ ∑ k : K, ‖C k‖^2*|ζ.im|⁻¹^2 := by
        apply Finset.sum_le_sum
        intro k _
        calc
          _ ≤ ((‖C k‖*‖R x‖)*‖C k‖)*‖R x‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
              ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
                (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))
          _ ≤ ((‖C k‖*|ζ.im|⁻¹)*‖C k‖)*|ζ.im|⁻¹ := by gcongr <;> exact hR x
          _ = _ := by ring
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hFi : Integrable F (gaussianVector K) :=
    Integrable.of_bound hFcont.aestronglyMeasurable _ (Filter.Eventually.of_forall hFbound)
  have hone : P (1 : M)=(1 : Matrix d d ℂ) := by
    rw [show (1 : M)=(1 : Matrix d d ℂ)⊗ₖ(1 : Matrix n n ℂ) by exact Matrix.one_kronecker_one.symm]
    exact normalizedPartialTrace_kronecker_one _
  have hZ : ζ • (1 : M)-A₀⊗ₖ(1 : Matrix n n ℂ)=
      (ζ • (1 : Matrix d d ℂ)-A₀)⊗ₖ(1 : Matrix n n ℂ) := by
    ext ⟨a,r⟩ ⟨b,s⟩
    by_cases hab : a=b <;> by_cases hrs : r=s <;>
      simp [Matrix.kroneckerMap_apply,hab,hrs,Matrix.smul_apply,smul_eq_mul]
  have hh := congrArg P (shifted_integral_gaussianFreeFiniteResolvent A₀ hA₀ A hA 0 ζ hζ)
  change P ((ζ • (1 : M)-A₀⊗ₖ(1 : Matrix n n ℂ))*(∫ x : E, R x ∂gaussianVector K))=
    P (1+∫ x : E, F x ∂gaussianVector K) at hh
  rw [map_add,hone,← P.integral_comp_comm hFi] at hh
  change normalizedPartialTrace ((ζ • (1 : M)-A₀⊗ₖ(1 : Matrix n n ℂ))*
    (∫ x : E, R x ∂gaussianVector K))=1+∫ x : E, normalizedPartialTrace (F x) ∂gaussianVector K at hh
  rw [hZ,normalizedPartialTrace_kronecker_one_mul] at hh
  simp only [F,C,partialTrace_finite_gue_covariance_integrand] at hh
  change (ζ • (1 : Matrix d d ℂ)-A₀)*gaussianFreeFiniteDysonResolvent (n := n) A₀ A ζ=
    1+_ at hh
  rw [hh,add_sub_cancel_right]

end NLAlib
