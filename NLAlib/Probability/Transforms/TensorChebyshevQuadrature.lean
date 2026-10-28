import NLAlib.Polynomial.FunctionApproximation.GaussChebyshevQuadrature
import NLAlib.Probability.Transforms.ChebyshevKernelMeasure
import NLAlib.Probability.Transforms.TensorChebyshevMomentWasserstein

/-!
# Positive tensor Gauss-Chebyshev discretization

Sample the actual positive Jackson density on the `(M+1)`-point root grid in
each coordinate. Exact product quadrature retains all first `M` tensor moments.
-/

noncomputable section
open Real MeasureTheory Finset Set Polynomial.Chebyshev
open scoped NNReal ENNReal
namespace NLAlib
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual root-grid point in Euclidean coordinate space. -/
def tensorGaussChebyshevNode (L : ℕ) (σ : ι → Fin L) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => chebyshevZero L (σ i))

/-- Equal tensor-product Gauss weights applied to an actual scalar function. -/
def tensorGaussChebyshevRule (L : ℕ) (f : (ι → ℝ) → ℝ) : ℝ :=
  (π/L)^Fintype.card ι * ∑ σ : ι → Fin L,f (WithLp.ofLp (tensorGaussChebyshevNode L σ))

omit [DecidableEq ι] in
/-- Every tensor root-grid point belongs to the exact approximation cube. -/
theorem tensorGaussChebyshevNode_mem (L : ℕ) (σ : ι → Fin L) :
    tensorGaussChebyshevNode L σ ∈ chebyshevCube ι :=
  fun i => chebyshevZero_mem_Icc L (σ i)

private theorem tensorGaussChebyshevRule_prod (L : ℕ) (f : ι → ℝ → ℝ) :
    tensorGaussChebyshevRule L (fun x => ∏ i,f i (x i)) =
      ∏ i,gaussChebyshevRule L (f i) := by
  simp only [gaussChebyshevRule,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  rw [Fintype.prod_sum]
  rfl

private theorem tensorGaussChebyshevRule_sum {κ : Type*} (s : Finset κ)
    (f : κ → (ι → ℝ) → ℝ) (L : ℕ) :
    tensorGaussChebyshevRule L (fun x => ∑ a ∈ s,f a x) =
      ∑ a ∈ s,tensorGaussChebyshevRule L (f a) := by
  unfold tensorGaussChebyshevRule
  rw [Finset.sum_comm,Finset.mul_sum]

private theorem tensorGaussChebyshevRule_const_mul (L : ℕ) (c : ℝ) (f : (ι → ℝ) → ℝ) :
    tensorGaussChebyshevRule L (fun x => c*f x) = c*tensorGaussChebyshevRule L f := by
  unfold tensorGaussChebyshevRule
  rw [← Finset.mul_sum]
  ring

omit [DecidableEq ι] in
private theorem integral_tensorNormalizedChebyshev_mul (α β : ι → ℕ) :
    (∫ x,tensorNormalizedChebyshev α x*tensorNormalizedChebyshev β x
      ∂Measure.pi (fun _ : ι => measureT)) = if α=β then 1 else 0 := by
  simp only [tensorNormalizedChebyshev,← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (fun i x => normalizedChebyshev (α i) x*normalizedChebyshev (β i) x)]
  simp only [integral_normalizedChebyshev_mul]
  by_cases he : α=β
  · subst β;simp
  · rw [if_neg he]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp he
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Discrete tensor orthonormality is inherited from the proven scalar rule. -/
theorem tensorGaussChebyshevRule_normalized_mul {L : ℕ} (hL : 0<L)
    (α β : ι → ℕ) (hα : ∀ i,α i<L) (hβ : ∀ i,β i<L) :
    tensorGaussChebyshevRule L (fun x => tensorNormalizedChebyshev α x*tensorNormalizedChebyshev β x) =
      if α=β then 1 else 0 := by
  simp only [tensorNormalizedChebyshev,← Finset.prod_mul_distrib]
  rw [tensorGaussChebyshevRule_prod L (fun i x => normalizedChebyshev (α i) x*normalizedChebyshev (β i) x)]
  simp_rw [gaussChebyshevRule_normalized_mul hL (hα _) (hβ _)]
  by_cases he : α=β
  · subst β;simp
  · rw [if_neg he]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp he
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

omit [DecidableEq ι] in
/-- The averaged Jackson density is nonnegative at every point in the cube. -/
theorem tensorChebyshevSmoothedDensity_nonneg
    (μ : Measure (chebyshevCube ι)) (M : ℕ) {x : ι → ℝ}
    (hx : ∀ i,x i ∈ Icc (-1 : ℝ) 1) :
    0 ≤ tensorChebyshevSmoothedDensity μ M x := by
  apply integral_nonneg
  intro r
  exact tensorChebyshevJacksonKernel_nonneg M hx r.property

/-- Exact quadrature of density times every retained normalized tensor mode. -/
theorem tensorGaussChebyshevRule_density_mul_eq_integral
    (μ : Measure (chebyshevCube ι)) [IsProbabilityMeasure μ] (M : ℕ)
    (β : ι → ℕ) (hβ : ∀ i,β i≤M) :
    tensorGaussChebyshevRule (M+1) (fun x =>
      tensorChebyshevSmoothedDensity μ M x*tensorNormalizedChebyshev β x) =
      ∫ x,tensorChebyshevSmoothedDensity μ M x*tensorNormalizedChebyshev β x
        ∂Measure.pi (fun _ : ι => measureT) := by
  simp_rw [tensorChebyshevSmoothedDensity_eq_sum,Finset.sum_mul]
  rw [tensorGaussChebyshevRule_sum,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro α hα
    have hα' i : α i<M+1 := mem_range.mp (Fintype.mem_piFinset.mp hα i)
    have hβ' i : β i<M+1 := Nat.lt_succ_of_le (hβ i)
    simp_rw [show ∀ x : ι → ℝ,tensorChebyshevJacksonDamping M α*tensorNormalizedChebyshev α x*
      tensorChebyshevMoment μ α*tensorNormalizedChebyshev β x =
      (tensorChebyshevJacksonDamping M α*tensorChebyshevMoment μ α)*
        (tensorNormalizedChebyshev α x*tensorNormalizedChebyshev β x) from fun x => by ring]
    rw [tensorGaussChebyshevRule_const_mul,integral_const_mul,
      tensorGaussChebyshevRule_normalized_mul (by omega) α β hα' hβ',
      integral_tensorNormalizedChebyshev_mul]
  · intro α _
    apply integrable_pi_measureT_of_continuous
    fun_prop

/-- The actual finite density is continuous, including outside the cube. -/
@[fun_prop] theorem continuous_tensorChebyshevSmoothedDensity
    (μ : Measure (chebyshevCube ι)) [IsProbabilityMeasure μ] (M : ℕ) :
    Continuous (tensorChebyshevSmoothedDensity μ M) := by
  have he : tensorChebyshevSmoothedDensity μ M = fun x =>
      ∑ α ∈ Fintype.piFinset (fun _ : ι => range (M+1)),
        tensorChebyshevJacksonDamping M α*tensorNormalizedChebyshev α x*tensorChebyshevMoment μ α :=
    funext (tensorChebyshevSmoothedDensity_eq_sum μ M)
  rw [he]
  fun_prop

/-- Integrating a continuous observable under the actual smoothed law is
integration against its native density on the coordinate product measure. -/
theorem integral_tensorChebyshevSmoothedLaw_eq_density
    (μ : Measure (chebyshevCube ι)) [IsProbabilityMeasure μ] (M : ℕ)
    (f : EuclideanSpace ℝ ι → ℝ) (hf : Continuous f) :
    (∫ x,f x ∂tensorChebyshevSmoothedLaw μ M) =
      ∫ x,tensorChebyshevSmoothedDensity μ M x*f (WithLp.toLp 2 x)
        ∂Measure.pi (fun _ : ι => measureT) := by
  rw [tensorChebyshevSmoothedLaw_eq_map_withDensity,integral_map
    (PiLp.continuous_toLp 2 _).measurable.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_tensorChebyshevSmoothedDensity μ M).measurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_mem_chebyshevCube (ι := ι)] with x hx
  rw [ENNReal.toReal_ofReal (tensorChebyshevSmoothedDensity_nonneg μ M hx)]
  rfl

/-- The positive density has unit mass against the coordinate product measure. -/
theorem integral_tensorChebyshevSmoothedDensity
    (μ : Measure (chebyshevCube ι)) [IsProbabilityMeasure μ] (M : ℕ) :
    (∫ x,tensorChebyshevSmoothedDensity μ M x ∂Measure.pi (fun _ : ι => measureT)) = 1 := by
  have he := integral_tensorChebyshevSmoothedLaw_eq_density μ M (fun _ => 1) continuous_const
  simpa using he.symm

/-- The positive sampled density has exactly unit total quadrature weight. -/
theorem tensorGaussChebyshevRule_density_eq_one
    (μ : Measure (chebyshevCube ι)) [IsProbabilityMeasure μ] (M : ℕ) :
    tensorGaussChebyshevRule (M+1) (tensorChebyshevSmoothedDensity μ M) = 1 := by
  let c : ℝ := (1/sqrt π)^Fintype.card ι
  have hc : 0<c := by dsimp [c];positivity
  have hzero (x : ι → ℝ) : tensorNormalizedChebyshev (0 : ι → ℕ) x = c := by
    simp [tensorNormalizedChebyshev,c]
  have he := tensorGaussChebyshevRule_density_mul_eq_integral μ M (0 : ι → ℕ) (by simp)
  simp_rw [hzero,show ∀ x : ι → ℝ,tensorChebyshevSmoothedDensity μ M x*c =
    c*tensorChebyshevSmoothedDensity μ M x from fun x => mul_comm _ _] at he
  rw [tensorGaussChebyshevRule_const_mul,integral_const_mul,integral_tensorChebyshevSmoothedDensity] at he
  nlinarith

/-- The actual nonnegative quadrature weight at one tensor root-grid point. -/
def tensorChebyshevQuadratureWeight (μ : Measure (chebyshevCube ι)) (M : ℕ)
    (σ : ι → Fin (M+1)) : ℝ≥0 :=
  (((π/(M+1))^Fintype.card ι)*tensorChebyshevSmoothedDensity μ M
    (WithLp.ofLp (tensorGaussChebyshevNode (M+1) σ))).toNNReal

omit [DecidableEq ι] in
/-- The nonnegative weight is the literal density sample times its Gauss weight. -/
theorem coe_tensorChebyshevQuadratureWeight (μ : Measure (chebyshevCube ι)) (M : ℕ)
    (σ : ι → Fin (M+1)) :
    (tensorChebyshevQuadratureWeight μ M σ : ℝ) =
      (π/(M+1))^Fintype.card ι * tensorChebyshevSmoothedDensity μ M
        (WithLp.ofLp (tensorGaussChebyshevNode (M+1) σ)) := by
  apply Real.coe_toNNReal _
  exact mul_nonneg (by positivity)
    (tensorChebyshevSmoothedDensity_nonneg μ M (tensorGaussChebyshevNode_mem (M+1) σ))

/-- The sampled positive Jackson density, as an actual finite Euclidean law. -/
def tensorChebyshevQuadratureLaw (μ : Measure (chebyshevCube ι)) (M : ℕ) :
    Measure (EuclideanSpace ℝ ι) :=
  ∑ σ : ι → Fin (M+1),tensorChebyshevQuadratureWeight μ M σ •
    Measure.dirac (tensorGaussChebyshevNode (M+1) σ)

instance tensorChebyshevQuadratureLaw_isFiniteMeasure (μ : Measure (chebyshevCube ι)) (M : ℕ) :
    IsFiniteMeasure (tensorChebyshevQuadratureLaw μ M) := by
  unfold tensorChebyshevQuadratureLaw
  infer_instance

/-- The native quadrature law is an actual probability law. -/
instance tensorChebyshevQuadratureLaw_isProbabilityMeasure
    (μ : Measure (chebyshevCube ι)) [IsProbabilityMeasure μ] (M : ℕ) :
    IsProbabilityMeasure (tensorChebyshevQuadratureLaw μ M) := by
  have hsum : (∑ σ : ι → Fin (M+1),tensorChebyshevQuadratureWeight μ M σ : ℝ≥0) = 1 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_sum,coe_tensorChebyshevQuadratureWeight,NNReal.coe_one]
    rw [← Finset.mul_sum]
    simpa only [tensorGaussChebyshevRule,Nat.cast_add,Nat.cast_one] using
      tensorGaussChebyshevRule_density_eq_one μ M
  constructor
  simp only [tensorChebyshevQuadratureLaw,Measure.coe_finsetSum,Finset.sum_apply,
    Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),ENNReal.smul_def,
    smul_eq_mul,mul_one]
  exact_mod_cast hsum

/-- Actual finite-law integration is exactly the stated sampled-density rule. -/
theorem integral_tensorChebyshevQuadratureLaw (μ : Measure (chebyshevCube ι)) (M : ℕ)
    (f : EuclideanSpace ℝ ι → ℝ) :
    (∫ x,f x ∂tensorChebyshevQuadratureLaw μ M) =
      tensorGaussChebyshevRule (M+1) (fun x => tensorChebyshevSmoothedDensity μ M x*f (WithLp.toLp 2 x)) := by
  rw [tensorChebyshevQuadratureLaw,integral_finsetSum_measure (fun σ _ =>
    (integrable_dirac (by simp)).smul_measure_nnreal)]
  simp only [integral_smul_nnreal_measure,integral_dirac,NNReal.smul_def,
    coe_tensorChebyshevQuadratureWeight,smul_eq_mul,tensorGaussChebyshevRule,
    WithLp.toLp_ofLp,Nat.cast_add,Nat.cast_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-- Every first-`M` normalized tensor moment exactly matches the smoothed law. -/
theorem integral_tensorChebyshevQuadratureLaw_normalized_eq
    (μ : Measure (chebyshevCube ι)) [IsProbabilityMeasure μ] (M : ℕ)
    (β : ι → ℕ) (hβ : ∀ i,β i≤M) :
    (∫ x,tensorNormalizedChebyshev β (WithLp.ofLp x) ∂tensorChebyshevQuadratureLaw μ M) =
      ∫ x,tensorNormalizedChebyshev β (WithLp.ofLp x) ∂tensorChebyshevSmoothedLaw μ M := by
  rw [integral_tensorChebyshevQuadratureLaw,integral_tensorChebyshevSmoothedLaw_eq_density
    μ M (fun x => tensorNormalizedChebyshev β (WithLp.ofLp x))
      ((continuous_tensorNormalizedChebyshev β).comp (PiLp.continuous_ofLp 2 _))]
  simpa only [WithLp.ofLp_toLp] using tensorGaussChebyshevRule_density_mul_eq_integral μ M β hβ

/-- The quadrature law is supported on the exact approximation cube. -/
theorem ae_mem_chebyshevCube_tensorChebyshevQuadratureLaw
    (μ : Measure (chebyshevCube ι)) (M : ℕ) :
    ∀ᵐ x ∂tensorChebyshevQuadratureLaw μ M,x ∈ chebyshevCube ι := by
  rw [tensorChebyshevQuadratureLaw,ae_finsetSum_measure_iff]
  intro σ _
  apply Measure.ae_smul_measure
  exact (ae_dirac_iff isCompact_chebyshevCube.isClosed.measurableSet).mpr
    (tensorGaussChebyshevNode_mem _ _)

omit [DecidableEq ι] in
/-- The genuine continuous smoothed law is supported on the same cube. -/
private theorem ae_mem_chebyshevCube_tensorChebyshevSmoothedLaw
    (μ : Measure (chebyshevCube ι)) [IsProbabilityMeasure μ] (M : ℕ) :
    ∀ᵐ x ∂tensorChebyshevSmoothedLaw μ M,x ∈ chebyshevCube ι := by
  rw [tensorChebyshevSmoothedLaw_eq_map_withDensity,ae_map_iff
    (PiLp.continuous_toLp 2 _).measurable.aemeasurable
    (p := fun x : EuclideanSpace ℝ ι => x ∈ chebyshevCube ι)
      isCompact_chebyshevCube.isClosed.measurableSet]
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_mem_chebyshevCube (ι := ι))

/-- In two dimensions, positive quadrature adds at most `24/M` genuine W1 error. -/
theorem wassersteinEDistOne_tensorChebyshevQuadratureLaw_le
    (μ : Measure (chebyshevCube (Fin 2))) [IsProbabilityMeasure μ] {M : ℕ} (hM : 1≤M) :
    wassersteinEDistOne (tensorChebyshevQuadratureLaw μ M) (tensorChebyshevSmoothedLaw μ M) ≤
      ENNReal.ofReal (24/(M : ℝ)) := by
  have hzero : tensorChebyshevMomentError (tensorChebyshevQuadratureLaw μ M)
      (tensorChebyshevSmoothedLaw μ M) M = 0 := by
    unfold tensorChebyshevMomentError
    have he : ∀ β ∈ tensorChebyshevMomentIndices 2 M,
        tensorChebyshevMomentDiscrepancy (tensorChebyshevQuadratureLaw μ M)
          (tensorChebyshevSmoothedLaw μ M) β = 0 := by
      intro β hβ
      rw [tensorChebyshevMomentDiscrepancy,integral_tensorChebyshevQuadratureLaw_normalized_eq μ M β]
      · exact sub_self _
      · intro i
        have h := mem_range.mp (Fintype.mem_piFinset.mp (Finset.mem_erase.mp hβ).2 i)
        omega
    have hs : (∑ β ∈ tensorChebyshevMomentIndices 2 M,
        (tensorChebyshevMomentDiscrepancy (tensorChebyshevQuadratureLaw μ M)
          (tensorChebyshevSmoothedLaw μ M) β / sqrt (tensorChebyshevIndexNormSq β))^2) = 0 := by
      apply Finset.sum_eq_zero
      intro β hβ
      rw [he β hβ]
      simp
    rw [hs,sqrt_zero]
  have h := wassersteinEDistOne_le_tensorChebyshevMomentError
    (tensorChebyshevQuadratureLaw μ M) (tensorChebyshevSmoothedLaw μ M)
    (ae_mem_chebyshevCube_tensorChebyshevQuadratureLaw μ M)
    (ae_mem_chebyshevCube_tensorChebyshevSmoothedLaw μ M) hM
  norm_num only [hzero,mul_zero,add_zero,Nat.cast_ofNat,show (12 : ℝ)*2=24 by norm_num] at h
  exact h

/-- A concrete carrier with at most `(M+1)^d` atoms supports the quadrature law. -/
theorem exists_finite_support_tensorChebyshevQuadratureLaw
    (μ : Measure (chebyshevCube ι)) (M : ℕ) :
    ∃ s : Finset (EuclideanSpace ℝ ι),s.card ≤ (M+1)^Fintype.card ι ∧
      tensorChebyshevQuadratureLaw μ M (s : Set (EuclideanSpace ℝ ι))ᶜ = 0 := by
  classical
  let s := (Finset.univ : Finset (ι → Fin (M+1))).image (tensorGaussChebyshevNode (M+1))
  refine ⟨s,?_,?_⟩
  · apply Finset.card_image_le.trans
    simp
  · rw [measure_eq_zero_iff_ae_notMem,tensorChebyshevQuadratureLaw,ae_finsetSum_measure_iff]
    intro σ _
    apply Measure.ae_smul_measure
    have hh : ∀ᵐ x ∂Measure.dirac (tensorGaussChebyshevNode (M+1) σ),
        x ∈ (s : Set (EuclideanSpace ℝ ι)) := by
      apply (ae_dirac_iff (p := fun x : EuclideanSpace ℝ ι => x ∈ (s : Set (EuclideanSpace ℝ ι)))
        s.finite_toSet.measurableSet).mpr
      simp [s]
    filter_upwards [hh] with x hx
    exact fun he => he hx

end NLAlib
