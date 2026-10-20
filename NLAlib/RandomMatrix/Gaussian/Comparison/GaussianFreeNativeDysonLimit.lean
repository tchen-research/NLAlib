import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeFiniteDysonResidual
import NLAlib.Probability.Free.WordNativeDysonStability
import NLAlib.ForMathlib.Analysis.Complex.HalfPlaneConvergence
import NLAlib.ForMathlib.MeasureTheory.ResolventPowerConvergence
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Actual Gaussian resolvent means converge to the concrete free model

The genuine finite-ensemble Dyson residual gives a uniform high-horizontal-line
bound with the true inverse-square ensemble scaling. Complex three-lines
propagation then identifies the concrete vacuum-compressed resolvent as the
locally uniform limit throughout the upper half-plane. Differentiating the
actual Bochner means proves the same convergence for every positive power.
These are native prerequisites for the endpoint step in Theorem 6.2 of
Bandeira--Boedihardjo--van Handel, arXiv:2108.06312v2.
The full two-sided spectral comparison is not asserted by this module.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical Matrix Topology
namespace NLAlib
variable {ι n d : Type*} [Fintype ι] [Fintype n] [Fintype d]
  [DecidableEq ι] [DecidableEq n] [DecidableEq d]
local notation "C" => Matrix d d ℂ

open scoped Matrix.Norms.L2Operator in
theorem specNorm_gaussianFreeFiniteDysonResolvent_sub_wordNative_le [Nonempty n]
    (A₀ : C) (hA₀ : A₀.IsHermitian) (A : ι → C) (hA : ∀ i, (A i).IsHermitian)
    {z : ℂ} (hz : 0<z.im)
    (hlarge : 2*(Fintype.card d : ℝ)*‖coefficientSandwichSum A‖≤z.im^2) :
    specNorm (gaussianFreeFiniteDysonResolvent (n := n) A₀ A z-
      wordNativeDysonResolvent A₀ A z) ≤
      (2*(Fintype.card d : ℝ)^3*‖coefficientSandwichSum A‖*
        specNorm (coefficientCovariance A))/(Fintype.card n : ℝ)^2*z.im⁻¹^5 := by
  have hne : z.im≠0 := ne_of_gt hz
  have hm := specNorm_gaussianFreeFiniteDysonResolvent_le (n := n) A₀ hA₀ A hA z hne
  have hc : ((Fintype.card d : ℝ)*|z.im|⁻¹)*‖coefficientSandwichSum A‖*
      specNorm (gaussianFreeFiniteDysonResolvent (n := n) A₀ A z)≤1/2 := by
    calc
      _ ≤ ((Fintype.card d : ℝ)*|z.im|⁻¹)*‖coefficientSandwichSum A‖*|z.im|⁻¹ :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = ((Fintype.card d : ℝ)*‖coefficientSandwichSum A‖)/(z.im^2) := by
        rw [abs_of_pos hz]
        simp only [div_eq_mul_inv,pow_two]
        ring
      _ ≤ 1/2 := by
        apply (div_le_iff₀ (sq_pos_of_pos hz)).mpr
        nlinarith
  have hr := specNorm_gaussianFreeFiniteDysonResolvent_residual_le (n := n) A₀ hA₀ A hA z hne
  have hs := specNorm_sub_wordNativeDysonResolvent_le_residual hA₀ hA hne
    (gaussianFreeFiniteDysonResolvent (n := n) A₀ A z) hc
  dsimp only at hr
  calc
    _ ≤ 2*((Fintype.card d : ℝ)*|z.im|⁻¹)*
        ((Fintype.card d : ℝ)^2*‖coefficientSandwichSum A‖*
          (specNorm (coefficientCovariance A)/(Fintype.card n : ℝ)^2*|z.im|⁻¹^4)) :=
      hs.trans (mul_le_mul_of_nonneg_left hr (by positivity))
    _ = _ := by
      rw [abs_of_pos hz]
      simp only [div_eq_mul_inv]
      ring

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The genuine Gaussian expected partial-trace resolvent is holomorphic on the upper half-plane. -/
theorem differentiableOn_gaussianFreeFiniteDysonResolvent
    (A₀ : C) (hA₀ : A₀.IsHermitian) (A : ι → C) (hA : ∀ i, (A i).IsHermitian) :
    DifferentiableOn ℂ (gaussianFreeFiniteDysonResolvent (n := n) A₀ A)
      {z : ℂ | 0<z.im} := by
  let X : (GaussianFreeFiniteCoordinate ι n → ℝ) →
      selfAdjoint (Matrix (d×n) (d×n) ℂ) := fun x =>
    ⟨gaussianFreeFiniteInterpolation A₀ A 0 x,
      gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA 0 x⟩
  have hXm : AEStronglyMeasurable X (gaussianVector (GaussianFreeFiniteCoordinate ι n)) := by
    apply Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp
    change AEStronglyMeasurable (gaussianFreeFiniteInterpolation A₀ A 0) _
    apply Continuous.aestronglyMeasurable
    unfold gaussianFreeFiniteInterpolation
    fun_prop
  have hh := differentiableOn_resolventPowerMean X hXm
    (normalizedPartialTraceCLM (d := d) (n := n)) 1
  unfold resolventPowerMean at hh
  unfold gaussianFreeFiniteDysonResolvent
  simpa only [pow_one,normalizedPartialTraceCLM_apply,X,gaussianFreeFiniteDysonResolvent] using hh

open scoped Matrix.Norms.L2Operator in
/-- The difference of the actual finite Gaussian mean and the concrete free resolvent tends locally uniformly to zero on the upper half-plane. -/
theorem tendstoLocallyUniformlyOn_gaussianFreeFiniteDysonResolvent_sub_wordNative_zero
    (A₀ : C) (hA₀ : A₀.IsHermitian) (A : ι → C) (hA : ∀ i, (A i).IsHermitian) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun z : ℂ => gaussianFreeFiniteDysonResolvent (n := Fin (N+1)) A₀ A z-
        wordNativeDysonResolvent A₀ A z)
      (fun _ => 0) atTop {z : ℂ | 0<z.im} := by
  let d₀ : ℝ := Fintype.card d
  let s : ℝ := ‖coefficientSandwichSum A‖
  let v : ℝ := specNorm (coefficientCovariance A)
  let u₀ : ℝ := 1+2*d₀*s
  let F : ℕ → ℂ → C := fun N z =>
    gaussianFreeFiniteDysonResolvent (n := Fin (N+1)) A₀ A z-wordNativeDysonResolvent A₀ A z
  have hd₀ : 0≤d₀ := Nat.cast_nonneg _
  have hs : 0≤s := norm_nonneg _
  have hv : 0≤v := specNorm_nonneg _
  apply Complex.tendstoLocallyUniformlyOn_zero_of_upper_boundary_error
    F atTop (d₀+1) u₀ (by positivity)
  · intro N
    exact (differentiableOn_gaussianFreeFiniteDysonResolvent (n := Fin (N+1)) A₀ hA₀ A hA).sub
      ((differentiableOn_wordNativeDysonResolvent hA₀ hA).mono fun z hz => ne_of_gt hz)
  · intro N z hz
    have hm := specNorm_gaussianFreeFiniteDysonResolvent_le (n := Fin (N+1)) A₀ hA₀ A hA z (ne_of_gt hz)
    have hf := specNorm_wordNativeDysonResolvent_le hA₀ hA (ne_of_gt hz)
    change specNorm (_-_)≤_
    calc
      _ ≤ specNorm (gaussianFreeFiniteDysonResolvent (n := Fin (N+1)) A₀ A z)+
          specNorm (wordNativeDysonResolvent A₀ A z) := norm_sub_le _ _
      _ ≤ |z.im|⁻¹+d₀*|z.im|⁻¹ := add_le_add hm hf
      _ = (d₀+1)/z.im := by rw [abs_of_pos hz]; simp only [div_eq_mul_inv]; ring
  · intro u hu
    have hu1 : 1≤u := by dsimp [u₀] at hu; nlinarith
    have hupos : 0<u := zero_lt_one.trans_le hu1
    have hlarge : 2*d₀*s≤u^2 := by dsimp [u₀] at hu; nlinarith
    let ε : ℕ → ℝ := fun N => (2*d₀^3*s*v)/((N : ℝ)+1)^2*u⁻¹^5
    have hε0 (N : ℕ) : 0≤ε N := by dsimp [ε]; positivity
    have hε : Tendsto ε atTop (𝓝 0) := by
      have hi : Tendsto (fun N : ℕ => 1/((N : ℝ)+1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hh := ((hi.pow 2).const_mul (2*d₀^3*s*v)).mul_const (u⁻¹^5)
      simpa only [ε,div_pow,one_pow,div_eq_mul_inv,mul_zero,zero_mul,one_mul,inv_pow,
        zero_pow (by decide : 2≠0)] using hh
    refine ⟨ε,hε0,hε,?_⟩
    intro N z hz
    have hzpos : 0<z.im := hz.symm ▸ hupos
    have hh := specNorm_gaussianFreeFiniteDysonResolvent_sub_wordNative_le
      (n := Fin (N+1)) A₀ hA₀ A hA hzpos (by simpa only [hz] using hlarge)
    simpa only [F,ε,d₀,s,v,Fintype.card_fin,Nat.cast_add,Nat.cast_one,hz,specNorm_eq_norm] using hh

open scoped Matrix.Norms.L2Operator in
/-- The actual Gaussian resolvent expectation converges locally uniformly to the actual vacuum-compressed free resolvent. Source Theorem 6.2 endpoint;
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem tendstoLocallyUniformlyOn_gaussianFreeFiniteDysonResolvent
    (A₀ : C) (hA₀ : A₀.IsHermitian) (A : ι → C) (hA : ∀ i, (A i).IsHermitian) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => gaussianFreeFiniteDysonResolvent (n := Fin (N+1)) A₀ A)
      (wordNativeDysonResolvent A₀ A) atTop {z : ℂ | 0<z.im} := by
  have hc : TendstoLocallyUniformlyOn
      (fun _ : ℕ => wordNativeDysonResolvent A₀ A)
      (wordNativeDysonResolvent A₀ A) atTop {z : ℂ | 0<z.im} := by
    intro U hU z hz
    refine ⟨Set.univ, Filter.univ_mem, Filter.Eventually.of_forall fun N w hw => ?_⟩
    exact refl_mem_uniformity hU
  have hh := (tendstoLocallyUniformlyOn_gaussianFreeFiniteDysonResolvent_sub_wordNative_zero
    A₀ hA₀ A hA).add hc
  simpa only [Pi.add_def, sub_add_cancel, zero_add] using hh

open scoped Matrix.Norms.L2Operator in
/-- Every genuine positive-power Gaussian resolvent mean converges locally uniformly to the corresponding vacuum compression of the concrete free resolvent power. Source Theorem 6.2 endpoint;
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem tendstoLocallyUniformlyOn_gaussianFreeFinite_resolventPowerMean
    (A₀ : C) (hA₀ : A₀.IsHermitian) (A : ι → C) (hA : ∀ i, (A i).IsHermitian)
    (k : ℕ) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun z : ℂ => normalizedPartialTrace
        (∫ x : (GaussianFreeFiniteCoordinate ι (Fin (N+1)) → ℝ),
          resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) z^(k+1)
            ∂gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1)))))
      (fun z : ℂ => wordMatrixVacuumCompression
        (resolvent (wordNativeMatrixLinearCombination A₀ A) z^(k+1)))
      atTop {z : ℂ | 0<z.im} := by
  let X := fun (N : ℕ) (x : GaussianFreeFiniteCoordinate ι (Fin (N+1)) → ℝ) =>
    (⟨gaussianFreeFiniteInterpolation A₀ A 0 x,
      gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA 0 x⟩ :
        selfAdjoint (Matrix (d×Fin (N+1)) (d×Fin (N+1)) ℂ))
  have hXm (N : ℕ) : AEStronglyMeasurable (X N)
      (gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1)))) := by
    apply Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp
    change AEStronglyMeasurable (gaussianFreeFiniteInterpolation A₀ A 0) _
    apply Continuous.aestronglyMeasurable
    unfold gaussianFreeFiniteInterpolation
    fun_prop
  have hf := tendstoLocallyUniformlyOn_gaussianFreeFiniteDysonResolvent A₀ hA₀ A hA
  have hh := tendstoLocallyUniformlyOn_resolventPowerMean_of_first
    (fun N : ℕ => gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1)))) X hXm
    (fun N => normalizedPartialTraceCLM (d := d) (n := Fin (N+1)))
    (⟨wordNativeMatrixLinearCombination A₀ A,
      isSelfAdjoint_wordNativeMatrixLinearCombination hA₀ hA⟩)
    (wordMatrixVacuumCompressionCLM (D := d) (ι := ι)) atTop (by
      unfold resolventPowerMean gaussianFreeFiniteDysonResolvent wordNativeDysonResolvent at *
      simp only [X,pow_one,normalizedPartialTraceCLM_apply]
      change TendstoLocallyUniformlyOn
        (fun N : ℕ => fun z : ℂ => normalizedPartialTrace
          (∫ x, resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) z
            ∂gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1)))))
        (fun z : ℂ => wordMatrixVacuumCompression
          (resolvent (wordNativeMatrixLinearCombination A₀ A) z)) atTop {z : ℂ | 0<z.im}
      exact hf) k
  unfold resolventPowerMean at hh
  change TendstoLocallyUniformlyOn
    (fun N : ℕ => fun z : ℂ => normalizedPartialTrace
      (∫ x, resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) z^(k+1)
        ∂gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1)))))
    (fun z : ℂ => wordMatrixVacuumCompression
      (resolvent (wordNativeMatrixLinearCombination A₀ A) z^(k+1))) atTop {z : ℂ | 0<z.im} at hh
  exact hh

end NLAlib
