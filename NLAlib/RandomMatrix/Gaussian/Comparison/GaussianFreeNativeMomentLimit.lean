import NLAlib.RandomMatrix.Gaussian.Comparison.GaussianFreeNativeDysonLimit
import NLAlib.ForMathlib.MeasureTheory.ResolventMixedMeanConvergence
import NLAlib.ForMathlib.MeasureTheory.MatrixIntegral
import NLAlib.Probability.Free.WordMatrixVacuum
import NLAlib.Matrix.Functions.ResolventMoments

/-!
# Actual Gaussian mixed resolvent moments converge to the concrete free model

Schwarz reflection of the genuine Bochner means gives both nonreal
half-planes. The true two-parameter resolvent recursion then identifies
all mixed means with positive total degree. Actual normalized traces and
real Gram moments therefore converge with their exact dimension factors.
This proves the free endpoint input to Theorem 6.2 of
Bandeira--Boedihardjo--van Handel, arXiv:2108.06312v2.
It is a prerequisite for atlas gaussian-free-spectrum-two-sided, rather
than the full two-sided comparison.
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

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- The actual Gaussian partial-trace power mean respects adjoint reflection at every spectral parameter, including the total-inverse convention. -/
theorem gaussianFreeFinite_resolventPowerMean_star
    (A₀ : C) (hA₀ : A₀.IsHermitian) (A : ι → C) (hA : ∀ i, (A i).IsHermitian)
    (k : ℕ) (z : ℂ) :
    normalizedPartialTrace
      (∫ x : GaussianFreeFiniteCoordinate ι n → ℝ,
        resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) (star z)^k
          ∂gaussianVector (GaussianFreeFiniteCoordinate ι n))=
      (normalizedPartialTrace
        (∫ x : GaussianFreeFiniteCoordinate ι n → ℝ,
          resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) z^k
            ∂gaussianVector (GaussianFreeFiniteCoordinate ι n)))ᴴ := by
  rw [← normalizedPartialTrace_conjTranspose,← Matrix.integral_conjTranspose]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [Matrix.conjTranspose_pow]
  have hr := star_resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) z
  rw [show star (gaussianFreeFiniteInterpolation A₀ A 0 x)=
    gaussianFreeFiniteInterpolation A₀ A 0 x from
      (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA 0 x).eq] at hr
  exact congrArg (fun T => T^k) hr.symm

open scoped Matrix.Norms.L2Operator in
/-- Every actual positive-power Gaussian resolvent mean converges to the actual compressed free resolvent power at every nonreal parameter. -/
theorem tendsto_gaussianFreeFinite_resolventPowerMean
    (A₀ : C) (hA₀ : A₀.IsHermitian) (A : ι → C) (hA : ∀ i, (A i).IsHermitian)
    {z : ℂ} (hz : z.im≠0) (k : ℕ) :
    Tendsto
      (fun N : ℕ => normalizedPartialTrace
        (∫ x : GaussianFreeFiniteCoordinate ι (Fin (N+1)) → ℝ,
          resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) z^(k+1)
            ∂gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1)))))
      atTop (𝓝 (wordMatrixVacuumCompression
        (resolvent (wordNativeMatrixLinearCombination A₀ A) z^(k+1)))) := by
  rcases lt_or_gt_of_ne hz with hzneg|hzpos
  · have hstar : 0<(star z).im := by simpa only [Complex.star_def,Complex.conj_im] using neg_pos.mpr hzneg
    have ht := ((tendstoLocallyUniformlyOn_gaussianFreeFinite_resolventPowerMean
      A₀ hA₀ A hA k).tendsto_at hstar).star
    simp only [Matrix.star_eq_conjTranspose,
      ← gaussianFreeFinite_resolventPowerMean_star A₀ hA₀ A hA (k+1) (star z),star_star] at ht
    have hr := star_resolvent (wordNativeMatrixLinearCombination A₀ A) (star z)
    rw [(isSelfAdjoint_wordNativeMatrixLinearCombination hA₀ hA).star_eq,star_star] at hr
    rw [← wordMatrixVacuumCompression_star,star_pow,hr] at ht
    exact ht
  · exact (tendstoLocallyUniformlyOn_gaussianFreeFinite_resolventPowerMean A₀ hA₀ A hA k).tendsto_at hzpos

open scoped Matrix.Norms.L2Operator in
/-- Genuine mixed resolvent means at two distinct nonreal parameters converge to the corresponding actual vacuum compression. -/
theorem tendsto_gaussianFreeFinite_resolventMixedMean
    (A₀ : C) (hA₀ : A₀.IsHermitian) (A : ι → C) (hA : ∀ i, (A i).IsHermitian)
    {z w : ℂ} (hz : z.im≠0) (hw : w.im≠0) (hzw : z≠w)
    (p q : ℕ) (hpq : 0<p+q) :
    Tendsto
      (fun N : ℕ => normalizedPartialTrace
        (∫ x : GaussianFreeFiniteCoordinate ι (Fin (N+1)) → ℝ,
          resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) z^p*
            resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) w^q
            ∂gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1)))))
      atTop (𝓝 (wordMatrixVacuumCompression
        (resolvent (wordNativeMatrixLinearCombination A₀ A) z^p*
          resolvent (wordNativeMatrixLinearCombination A₀ A) w^q))) := by
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
  have hzlim (k : ℕ) : Tendsto
      (fun N => resolventPowerMean
        (gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1))))
        (X N) (normalizedPartialTraceCLM (d := d) (n := Fin (N+1))) (k+1) z)
      atTop (𝓝 (wordMatrixVacuumCompressionCLM
        (resolvent (wordNativeMatrixLinearCombination A₀ A) z^(k+1)))) := by
    unfold resolventPowerMean
    exact tendsto_gaussianFreeFinite_resolventPowerMean A₀ hA₀ A hA hz k
  have hwlim (k : ℕ) : Tendsto
      (fun N => resolventPowerMean
        (gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1))))
        (X N) (normalizedPartialTraceCLM (d := d) (n := Fin (N+1))) (k+1) w)
      atTop (𝓝 (wordMatrixVacuumCompressionCLM
        (resolvent (wordNativeMatrixLinearCombination A₀ A) w^(k+1)))) := by
    unfold resolventPowerMean
    exact tendsto_gaussianFreeFinite_resolventPowerMean A₀ hA₀ A hA hw k
  have hh := tendsto_resolventMixedMean_of_powers
    (fun N => gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1)))) X hXm
    (fun N => normalizedPartialTraceCLM (d := d) (n := Fin (N+1)))
    (⟨wordNativeMatrixLinearCombination A₀ A,isSelfAdjoint_wordNativeMatrixLinearCombination hA₀ hA⟩)
    (wordMatrixVacuumCompressionCLM (D := d) (ι := ι)) atTop hz hw hzw hzlim hwlim p q hpq
  unfold resolventMixedMean at hh
  exact hh

open scoped Matrix.Norms.L2Operator in
/-- The true Gaussian expected normalized mixed trace converges to the actual normalized matrix vacuum of the concrete free resolvent word. Source Theorem 6.2 endpoint;
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem tendsto_integral_normalizedTrace_gaussianFreeFinite_resolvent_mixed_powers
    (A₀ : C) (hA₀ : A₀.IsHermitian) (A : ι → C) (hA : ∀ i, (A i).IsHermitian)
    {z w : ℂ} (hz : z.im≠0) (hw : w.im≠0) (hzw : z≠w)
    (p q : ℕ) (hpq : 0<p+q) :
    Tendsto
      (fun N : ℕ => ∫ x : GaussianFreeFiniteCoordinate ι (Fin (N+1)) → ℝ,
          normalizedTrace (resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) z^p*
            resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) w^q)
            ∂gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1))))
      atTop (𝓝 (wordMatrixVacuumExpectation
        (resolvent (wordNativeMatrixLinearCombination A₀ A) z^p*
          resolvent (wordNativeMatrixLinearCombination A₀ A) w^q))) := by
  let L : C →L[ℂ] ℂ := normalizedTraceLinearMap.toContinuousLinearMap
  have ht := L.continuous.continuousAt.tendsto.comp
    (tendsto_gaussianFreeFinite_resolventMixedMean A₀ hA₀ A hA hz hw hzw p q hpq)
  have he (N : ℕ) : L (normalizedPartialTrace
      (∫ x : GaussianFreeFiniteCoordinate ι (Fin (N+1)) → ℝ,
        resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) z^p*
          resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) w^q
          ∂gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1)))))=
      ∫ x : GaussianFreeFiniteCoordinate ι (Fin (N+1)) → ℝ,
        normalizedTrace (resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) z^p*
          resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) w^q)
          ∂gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1))) := by
    change normalizedTrace (normalizedPartialTrace _) = _
    rw [normalizedTrace_normalizedPartialTrace]
    have hi := integrable_resolvent_selfAdjoint_mixed_powers
      (μ := gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1))))
      (fun x : GaussianFreeFiniteCoordinate ι (Fin (N+1)) → ℝ =>
        (⟨gaussianFreeFiniteInterpolation A₀ A 0 x,
          gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA 0 x⟩ :
            selfAdjoint (Matrix (d×Fin (N+1)) (d×Fin (N+1)) ℂ)))
      (by
        apply Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp
        apply Continuous.aestronglyMeasurable
        change Continuous (gaussianFreeFiniteInterpolation A₀ A 0)
        unfold gaussianFreeFiniteInterpolation
        fun_prop) hz hw p q
    exact ((normalizedTraceLinearMap (n := d×Fin (N+1)) (𝕜 := ℂ)).toContinuousLinearMap.integral_comp_comm hi).symm
  dsimp only [Function.comp_def] at ht
  simp_rw [he] at ht
  exact ht

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
private theorem integrable_gaussianFreeFinite_mixedTrace
    (A₀ : C) (hA₀ : A₀.IsHermitian) (A : ι → C) (hA : ∀ i, (A i).IsHermitian)
    {z w : ℂ} (hz : z.im≠0) (hw : w.im≠0) (p q : ℕ) :
    Integrable (fun x : GaussianFreeFiniteCoordinate ι n → ℝ =>
      normalizedTrace (resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) z^p*
        resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) w^q))
      (gaussianVector (GaussianFreeFiniteCoordinate ι n)) := by
  let X : (GaussianFreeFiniteCoordinate ι n → ℝ) →
      selfAdjoint (Matrix (d×n) (d×n) ℂ) := fun x =>
    ⟨gaussianFreeFiniteInterpolation A₀ A 0 x,
      gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA 0 x⟩
  have hXm : AEStronglyMeasurable X (gaussianVector (GaussianFreeFiniteCoordinate ι n)) := by
    apply Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp
    apply Continuous.aestronglyMeasurable
    change Continuous (gaussianFreeFiniteInterpolation A₀ A 0)
    unfold gaussianFreeFiniteInterpolation
    fun_prop
  have hi := integrable_resolvent_selfAdjoint_mixed_powers X hXm hz hw p q
  exact (normalizedTraceLinearMap (n := d×n) (𝕜 := ℂ)).toContinuousLinearMap.integrable_comp hi

open scoped Matrix.Norms.L2Operator in
/-- The genuine expected even Gram resolvent moment converges to the actual free Gram moment, with its native normalization. Source Theorem 6.2 endpoint;
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem tendsto_integral_gaussianFreeFinite_resolventEvenMoment
    (A₀ : C) (hA₀ : A₀.IsHermitian) (A : ι → C) (hA : ∀ i, (A i).IsHermitian)
    {z : ℂ} (hz : z.im≠0) (p : ℕ) (hp : 0<p) :
    Tendsto
      (fun N : ℕ => ∫ x : GaussianFreeFiniteCoordinate ι (Fin (N+1)) → ℝ,
        resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A 0 x) z p
          ∂gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1))))
      atTop (𝓝 ((wordMatrixVacuumExpectation
        ((star (resolvent (wordNativeMatrixLinearCombination A₀ A) z)*
          resolvent (wordNativeMatrixLinearCombination A₀ A) z)^p)).re)) := by
  have hstar : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have hzw : z≠star z := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.star_def,Complex.conj_im] at hi
    exact hz (by linarith)
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_integral_normalizedTrace_gaussianFreeFinite_resolvent_mixed_powers
      A₀ hA₀ A hA hz hstar hzw p p (by omega))
  have he (N : ℕ) :
      (∫ x : GaussianFreeFiniteCoordinate ι (Fin (N+1)) → ℝ,
        normalizedTrace (resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) z^p*
          resolvent (gaussianFreeFiniteInterpolation A₀ A 0 x) (star z)^p)
          ∂gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1)))).re=
      ∫ x : GaussianFreeFiniteCoordinate ι (Fin (N+1)) → ℝ,
        resolventEvenMoment (gaussianFreeFiniteInterpolation A₀ A 0 x) z p
          ∂gaussianVector (GaussianFreeFiniteCoordinate ι (Fin (N+1))) := by
    have hi := (integral_re (integrable_gaussianFreeFinite_mixedTrace
      (n := Fin (N+1)) A₀ hA₀ A hA hz hstar p p)).symm
    simp only [RCLike.re_eq_complex_re] at hi
    rw [hi]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    exact (resolventEvenMoment_eq_re_normalizedTrace_mul_pow
      (gaussianFreeFiniteInterpolation_isHermitian A₀ hA₀ A hA 0 x) z p).symm
  dsimp only [Function.comp_def] at ht
  simp_rw [he] at ht
  have hr := star_resolvent (wordNativeMatrixLinearCombination A₀ A) z
  rw [(isSelfAdjoint_wordNativeMatrixLinearCombination hA₀ hA).star_eq] at hr
  have heq : (star (resolvent (wordNativeMatrixLinearCombination A₀ A) z)*
      resolvent (wordNativeMatrixLinearCombination A₀ A) z)^p=
      resolvent (wordNativeMatrixLinearCombination A₀ A) z^p*
        resolvent (wordNativeMatrixLinearCombination A₀ A) (star z)^p := by
    rw [hr,(commute_resolvent (wordNativeMatrixLinearCombination A₀ A) (star z) z).mul_pow]
    exact ((commute_resolvent (wordNativeMatrixLinearCombination A₀ A) (star z) z).pow_pow p p).eq
  rwa [heq]

end NLAlib
