import NLAlib.Polynomial.FunctionApproximation.JacksonTensorApproximation
import NLAlib.Polynomial.FunctionApproximation.ChebyshevCube
import NLAlib.ForMathlib.Probability.KernelDensity
import NLAlib.ForMathlib.MeasureTheory.WassersteinOne

/-! # Actual probability laws from positive tensor Chebyshev kernels

The displayed finite Jackson kernel defines a Markov transition from the
closed Euclidean cube. Mixing against any input probability measure gives an
actual positive probability law, including for atomic input measures. Its
density is the finite polynomial determined by the mixed normalized moments.

Source: Musco--Musco--Shah--Urschel--West, arXiv:2605.31430v2, Theorem 2.5.
Atlas `tensor-chebyshev-kernel-measure`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Polynomial.Chebyshev
open scoped ENNReal

namespace NLAlib

variable {ι : Type*} [Fintype ι]

private theorem measurable_tensorChebyshevJacksonKernel_input (M : ℕ) :
    Measurable (fun p : (chebyshevCube ι) × (ι → ℝ) =>
      tensorChebyshevJacksonKernel M p.2 (WithLp.ofLp p.1.val)) := by
  apply Continuous.measurable
  exact (continuous_tensorChebyshevJacksonKernel M).comp'
    (continuous_snd.prodMk
      ((PiLp.continuous_ofLp 2 _).comp (continuous_subtype_val.comp continuous_fst)))

/-- The actual positive tensor kernel as a Markov transition on coordinate
vectors; its output reference measure is the product Chebyshev measure. -/
def tensorChebyshevSmoothingKernel (M : ℕ) : Kernel (chebyshevCube ι) (ι → ℝ) :=
  (Kernel.const (chebyshevCube ι) (Measure.pi (fun _ : ι => measureT))).withDensity
    (fun r x => ENNReal.ofReal (tensorChebyshevJacksonKernel M x (WithLp.ofLp r.val)))

instance isMarkovKernel_tensorChebyshevSmoothingKernel (M : ℕ) :
    IsMarkovKernel (tensorChebyshevSmoothingKernel (ι := ι) M) := by
  apply Kernel.isMarkovKernel_const_withDensity_of_integral_eq_one
    (Measure.pi (fun _ : ι => measureT)) (measurable_tensorChebyshevJacksonKernel_input M)
  · intro r
    exact integrable_pi_measureT_of_continuous (by fun_prop)
  · intro r
    filter_upwards [ae_mem_chebyshevCube (ι := ι)] with x hx
    exact tensorChebyshevJacksonKernel_nonneg M hx r.property
  · intro r
    exact integral_tensorChebyshevJacksonKernel M (WithLp.ofLp r.val)

/-- The output law in the Euclidean transport space, constructed from the
actual Markov transition and input law. -/
def tensorChebyshevSmoothedLaw (μ : Measure (chebyshevCube ι)) (M : ℕ) :
    Measure (EuclideanSpace ℝ ι) :=
  ((tensorChebyshevSmoothingKernel M) ∘ₘ μ).map (WithLp.toLp 2)

instance isProbabilityMeasure_tensorChebyshevSmoothedLaw
    (μ : Measure (chebyshevCube ι)) [IsProbabilityMeasure μ] (M : ℕ) :
    IsProbabilityMeasure (tensorChebyshevSmoothedLaw μ M) := by
  exact Measure.isProbabilityMeasure_map (PiLp.continuous_toLp 2 _).measurable.aemeasurable

/-- The actual averaged density against the coordinate product Chebyshev
measure. Its finite moment expansion is established separately. -/
def tensorChebyshevSmoothedDensity (μ : Measure (chebyshevCube ι)) (M : ℕ)
    (x : ι → ℝ) : ℝ :=
  ∫ r, tensorChebyshevJacksonKernel M x (WithLp.ofLp r.val) ∂μ

/-- Every input law gives the stated averaged density. Positivity is only
needed on the reference measure's support, where the kernel is nonnegative. -/
theorem comp_tensorChebyshevSmoothingKernel_eq_withDensity
    (μ : Measure (chebyshevCube ι)) [IsProbabilityMeasure μ] (M : ℕ) :
    (tensorChebyshevSmoothingKernel M) ∘ₘ μ =
      (Measure.pi (fun _ : ι => measureT)).withDensity
        (fun x => ENNReal.ofReal (tensorChebyshevSmoothedDensity μ M x)) := by
  rw [tensorChebyshevSmoothingKernel, Kernel.comp_const_withDensity μ _
    (measurable_tensorChebyshevJacksonKernel_input M).ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [ae_mem_chebyshevCube (ι := ι)] with x hx
  have : CompactSpace (chebyshevCube ι) := isCompact_iff_compactSpace.mp isCompact_chebyshevCube
  have hc : Continuous (fun r : chebyshevCube ι =>
      tensorChebyshevJacksonKernel M x (WithLp.ofLp r.val)) :=
    (continuous_tensorChebyshevJacksonKernel M).comp'
      (continuous_const.prodMk ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val))
  have hi : Integrable (fun r : chebyshevCube ι =>
      tensorChebyshevJacksonKernel M x (WithLp.ofLp r.val)) μ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp : 0 ≤ᵐ[μ] (fun r : chebyshevCube ι =>
      tensorChebyshevJacksonKernel M x (WithLp.ofLp r.val)) :=
    ae_of_all _ (fun r => tensorChebyshevJacksonKernel_nonneg M hx r.property)
  exact (ofReal_integral_eq_lintegral_ofReal hi hp).symm

/-- The mixed normalized Chebyshev moments of the actual cube input law. -/
def tensorChebyshevMoment (μ : Measure (chebyshevCube ι)) (α : ι → ℕ) : ℝ :=
  ∫ r, tensorNormalizedChebyshev α (WithLp.ofLp r.val) ∂μ

/-- The density is precisely a finite polynomial in the coordinates, with
coefficients determined by the input law's finite mixed moments.
Source: Musco--Musco--Shah--Urschel--West, Theorem 2.5.
atlas: tensor-chebyshev-kernel-measure (partial) -/
theorem tensorChebyshevSmoothedDensity_eq_sum [DecidableEq ι]
    (μ : Measure (chebyshevCube ι)) [IsProbabilityMeasure μ] (M : ℕ) (x : ι → ℝ) :
    tensorChebyshevSmoothedDensity μ M x =
      ∑ α ∈ Fintype.piFinset (fun _ : ι => Finset.range (M + 1)),
        tensorChebyshevJacksonDamping M α * tensorNormalizedChebyshev α x *
          tensorChebyshevMoment μ α := by
  have : CompactSpace (chebyshevCube ι) := isCompact_iff_compactSpace.mp isCompact_chebyshevCube
  unfold tensorChebyshevSmoothedDensity
  simp_rw [tensorChebyshevJacksonKernel_eq_sum]
  rw [integral_finsetSum (f := fun (α : ι → ℕ) (r : chebyshevCube ι) =>
    tensorChebyshevJacksonDamping M α * tensorNormalizedChebyshev α x *
      tensorNormalizedChebyshev α (WithLp.ofLp r.val)) _ (fun α _ => ?_)]
  · simp_rw [integral_const_mul]
    rfl
  · apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold tensorNormalizedChebyshev normalizedChebyshev
    fun_prop

/-- Each transition has the required Euclidean first displacement. This is
an actual expectation under the constructed Markov law. -/
theorem lintegral_edist_tensorChebyshevSmoothingKernel_le {M : ℕ} (hM : 1 ≤ M)
    (r : chebyshevCube ι) :
    (∫⁻ x, edist r.val (WithLp.toLp 2 x) ∂tensorChebyshevSmoothingKernel M r) ≤
      ENNReal.ofReal (6 * Fintype.card ι / M) := by
  have hm : Measurable (fun x : ι → ℝ => edist r.val (WithLp.toLp 2 x)) :=
    (continuous_const.edist (PiLp.continuous_toLp 2 _)).measurable
  rw [tensorChebyshevSmoothingKernel, Kernel.lintegral_withDensity _
    (measurable_tensorChebyshevJacksonKernel_input M).ennreal_ofReal r hm]
  simp only [Kernel.const_apply]
  have he (x : ι → ℝ) : edist r.val (WithLp.toLp 2 x) =
      ENNReal.ofReal ‖WithLp.toLp 2 x - r.val‖ := by
    rw [edist_comm, edist_dist, dist_eq_norm]
  simp_rw [he, ← ENNReal.ofReal_mul' (norm_nonneg _)]
  have hi : Integrable (fun x : ι → ℝ =>
      tensorChebyshevJacksonKernel M x (WithLp.ofLp r.val) * ‖WithLp.toLp 2 x - r.val‖)
      (Measure.pi (fun _ => measureT)) := integrable_pi_measureT_of_continuous (by fun_prop)
  have hp : 0 ≤ᵐ[Measure.pi (fun _ : ι => measureT)] (fun x =>
      tensorChebyshevJacksonKernel M x (WithLp.ofLp r.val) * ‖WithLp.toLp 2 x - r.val‖) := by
    filter_upwards [ae_mem_chebyshevCube (ι := ι)] with x hx
    exact mul_nonneg (tensorChebyshevJacksonKernel_nonneg M hx r.property) (norm_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hp]
  apply ENNReal.ofReal_le_ofReal
  apply le_trans _ (integral_tensorChebyshevJacksonKernel_mul_sum_abs_sub_le hM r.property)
  apply integral_mono_ae hi (integrable_pi_measureT_of_continuous (by fun_prop))
  filter_upwards [ae_mem_chebyshevCube (ι := ι)] with x hx
  apply mul_le_mul_of_nonneg_left _ (tensorChebyshevJacksonKernel_nonneg M hx r.property)
  exact euclidean_norm_le_sum_abs (WithLp.toLp 2 x - r.val)

/-- The constructed joint input-transition law, pushed to Euclidean space,
is an explicit coupling. Its cost proves the sharp stated smoothing bound.
Source: Musco--Musco--Shah--Urschel--West, Theorem 2.5.
atlas: tensor-chebyshev-kernel-measure (partial) -/
theorem wassersteinEDistOne_tensorChebyshevSmoothedLaw_le
    (μ : Measure (chebyshevCube ι)) [IsProbabilityMeasure μ] {M : ℕ} (hM : 1 ≤ M) :
    wassersteinEDistOne (μ.map Subtype.val) (tensorChebyshevSmoothedLaw μ M) ≤
      ENNReal.ofReal (6 * Fintype.card ι / M) := by
  let κ := tensorChebyshevSmoothingKernel (ι := ι) M
  have hπ := (Measure.isCoupling_compProd μ κ).map measurable_subtype_coe
    (PiLp.continuous_toLp 2 _).measurable
  apply (wassersteinEDistOne_le_lintegral hπ).trans
  rw [lintegral_map (g := fun p : (chebyshevCube ι) × (ι → ℝ) =>
    (p.1.val, WithLp.toLp 2 p.2)) (measurable_fst.edist measurable_snd) (by fun_prop)]
  rw [Measure.lintegral_compProd (by fun_prop)]
  apply (lintegral_mono (fun r => lintegral_edist_tensorChebyshevSmoothingKernel_le hM r)).trans_eq
  simp

/-- The actual output law has the averaged kernel density, transported to
the Euclidean coordinate space.
Source: Musco--Musco--Shah--Urschel--West, Theorem 2.5.
atlas: tensor-chebyshev-kernel-measure (partial) -/
theorem tensorChebyshevSmoothedLaw_eq_map_withDensity
    (μ : Measure (chebyshevCube ι)) [IsProbabilityMeasure μ] (M : ℕ) :
    tensorChebyshevSmoothedLaw μ M =
      ((Measure.pi (fun _ : ι => measureT)).withDensity
        (fun x => ENNReal.ofReal (tensorChebyshevSmoothedDensity μ M x))).map (WithLp.toLp 2) := by
  rw [tensorChebyshevSmoothedLaw, comp_tensorChebyshevSmoothingKernel_eq_withDensity]

/-- The constructed smoothing is an actual probability law with the claimed
density and Euclidean transport bound.
Source: Musco--Musco--Shah--Urschel--West, Theorem 2.5.
atlas: tensor-chebyshev-kernel-measure (partial) -/
theorem tensorChebyshevSmoothedLaw_probability_density_wasserstein
    (μ : Measure (chebyshevCube ι)) [IsProbabilityMeasure μ] {M : ℕ} (hM : 1 ≤ M) :
    IsProbabilityMeasure (tensorChebyshevSmoothedLaw μ M) ∧
      tensorChebyshevSmoothedLaw μ M =
        ((Measure.pi (fun _ : ι => measureT)).withDensity
          (fun x => ENNReal.ofReal (tensorChebyshevSmoothedDensity μ M x))).map (WithLp.toLp 2) ∧
      wassersteinEDistOne (μ.map Subtype.val) (tensorChebyshevSmoothedLaw μ M) ≤
        ENNReal.ofReal (6 * Fintype.card ι / M) :=
  ⟨inferInstance, tensorChebyshevSmoothedLaw_eq_map_withDensity μ M,
    wassersteinEDistOne_tensorChebyshevSmoothedLaw_le μ hM⟩

end NLAlib
