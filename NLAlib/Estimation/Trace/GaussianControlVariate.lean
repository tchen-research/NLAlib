import NLAlib.Estimation.Trace.GaussianProbeMoments
import NLAlib.ForMathlib.Probability.IndependentKernel

/-!
# Independent Gaussian control variates

The control matrix may be random and unbounded. A finite expected squared
Frobenius residual suffices for square integrability of the estimator. Independence
then gives both conditional unbiasedness and the exact averaged residual variance.

Source: Chen--Halikias--Musco--Persson, Hutch#, Section 2, equation (7) and Fact 2.1;
Meyer--Musco--Musco--Woodruff, Hutch++, Section 3. The arbitrary independent-control
reformulation is the one in the supplied Estimation derivations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ]

/-- The independent-probe control-variate estimator `tr B + tr_κ(M - B)`. -/
def gaussianControlVariateEstimate (M B : Matrix n n ℝ) (G : Matrix n κ ℝ) : ℝ :=
  B.trace + hutchinsonEstimate (M - B) G

omit [DecidableEq n] [DecidableEq κ] in
/-- Centering a control variate leaves the centered residual probe average. -/
theorem gaussianControlVariateEstimate_sub_trace (M B : Matrix n n ℝ)
    (G : Matrix n κ ℝ) :
    gaussianControlVariateEstimate M B G - M.trace =
      hutchinsonEstimate (M - B) G - (M - B).trace := by
  simp only [gaussianControlVariateEstimate, Matrix.trace_sub]
  ring

omit [DecidableEq n] [DecidableEq κ] in
private theorem measurable_controlVariate (M : Matrix n n ℝ) :
    Measurable (fun p : Matrix n n ℝ × Matrix n κ ℝ =>
      gaussianControlVariateEstimate M p.1 p.2) := by
  simp only [gaussianControlVariateEstimate, hutchinsonEstimate, quadForm_eq_sum,
    Matrix.trace, Matrix.diag, star_trivial, Matrix.sub_apply]
  fun_prop

private theorem integral_controlVariate_fixed [Nonempty κ] (M B : Matrix n n ℝ) :
    ∫ G, gaussianControlVariateEstimate M B G ∂gaussianMatrix n κ = M.trace := by
  have hG : HasLaw (id : Matrix n κ ℝ → _) (gaussianMatrix n κ) (gaussianMatrix n κ) :=
    ⟨aemeasurable_id, Measure.map_id⟩
  have hi := (memLp_two_hutchinsonEstimate_of_hasLaw_gaussianMatrix (M - B) hG).integrable
    (by norm_num)
  simp only [id_eq] at hi
  have hmean := integral_hutchinsonEstimate_of_hasLaw_gaussianMatrix (M - B) hG
  simp only [id_eq] at hmean
  rw [show (fun G => gaussianControlVariateEstimate M B G) =
    (fun G => B.trace + hutchinsonEstimate (M - B) G) from rfl,
    integral_add (integrable_const _) hi,
    integral_const, probReal_univ, one_smul,
    hmean, Matrix.trace_sub]
  ring

private theorem controlVariate_product_moments [Nonempty κ]
    {ν : Measure (Matrix n n ℝ)} [IsProbabilityMeasure ν]
    {M : Matrix n n ℝ} (hM : M.IsHermitian)
    (hB : ∀ᵐ B ∂ν, B.IsHermitian)
    (hres : Integrable (fun B => frobSq (M - B)) ν) :
    MemLp (fun p : Matrix n n ℝ × Matrix n κ ℝ =>
      gaussianControlVariateEstimate M p.1 p.2) 2 (ν.prod (gaussianMatrix n κ)) ∧
    (∫ p, gaussianControlVariateEstimate M p.1 p.2 ∂ν.prod (gaussianMatrix n κ)) =
      M.trace ∧
    (∫ p, (gaussianControlVariateEstimate M p.1 p.2 - M.trace) ^ 2
      ∂ν.prod (gaussianMatrix n κ)) =
      2 / Fintype.card κ * ∫ B, frobSq (M - B) ∂ν := by
  let e : Matrix n n ℝ × Matrix n κ ℝ → ℝ := fun p =>
    gaussianControlVariateEstimate M p.1 p.2 - M.trace
  have he : Measurable e := (measurable_controlVariate M).sub_const _
  have hG : HasLaw (id : Matrix n κ ℝ → _) (gaussianMatrix n κ) (gaussianMatrix n κ) :=
    ⟨aemeasurable_id, Measure.map_id⟩
  have hfiber (B : Matrix n n ℝ) : MemLp (fun G => e (B, G)) 2 (gaussianMatrix n κ) := by
    have hi := (memLp_two_hutchinsonEstimate_of_hasLaw_gaussianMatrix (M - B) hG).sub
      (memLp_const (M - B).trace)
    change MemLp (fun G => hutchinsonEstimate (M - B) G - (M - B).trace) 2
      (gaussianMatrix n κ) at hi
    simpa only [e, gaussianControlVariateEstimate_sub_trace] using hi
  have hsecond : ∀ᵐ B ∂ν, ∫ G, e (B, G) ^ 2 ∂gaussianMatrix n κ =
      2 / Fintype.card κ * frobSq (M - B) := by
    filter_upwards [hB] with B hB
    simpa only [e, gaussianControlVariateEstimate_sub_trace, id_eq] using
      (integral_sq_hutchinsonEstimate_sub_trace_of_hasLaw_gaussianMatrix (hM.sub hB) hG).trans
        (by ring)
  have he2 : Integrable (fun p => e p ^ 2) (ν.prod (gaussianMatrix n κ)) := by
    apply (integrable_prod_iff (he.pow_const 2).aestronglyMeasurable).2
    refine ⟨ae_of_all _ fun B => (hfiber B).integrable_sq, ?_⟩
    have hi := hres.const_mul (2 / Fintype.card κ)
    apply hi.congr
    filter_upwards [hsecond] with B hB
    simpa only [Real.norm_eq_abs, abs_sq] using hB.symm
  have heLp : MemLp e 2 (ν.prod (gaussianMatrix n κ)) :=
    (memLp_two_iff_integrable_sq he.aestronglyMeasurable).2 he2
  have hFLp : MemLp (fun p : Matrix n n ℝ × Matrix n κ ℝ =>
      gaussianControlVariateEstimate M p.1 p.2) 2 (ν.prod (gaussianMatrix n κ)) := by
    have hi := heLp.add (memLp_const M.trace)
    change MemLp (fun p => e p + M.trace) 2 (ν.prod (gaussianMatrix n κ)) at hi
    simpa only [e, sub_add_cancel] using hi
  refine ⟨hFLp, ?_, ?_⟩
  · rw [integral_prod _ (hFLp.integrable (by norm_num))]
    simp_rw [integral_controlVariate_fixed]
    simp
  · change ∫ p, e p ^ 2 ∂ν.prod (gaussianMatrix n κ) = _
    rw [integral_prod _ he2, integral_congr_ae hsecond, integral_const_mul]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A random symmetric control, independent of a nonempty Gaussian probe matrix,
gives a square-integrable unbiased estimator. Its variance is exactly the expected
squared Frobenius residual times `2 / card κ`, and its conditional mean given the
control is the trace. The only size assumption on the control is that residual moment.
Source: Hutch#, Section 2, equation (7) and Fact 2.1, by Gaussian quadratic-form moments.
atlas: independent-control-variate-variance -/
theorem gaussianControlVariateEstimate_moments_of_indepFun [Nonempty κ]
    {M : Matrix n n ℝ} (hM : M.IsHermitian)
    {B : Ω → Matrix n n ℝ} {G : Ω → Matrix n κ ℝ}
    (hBm : Measurable B) (hB : ∀ᵐ ω ∂μ, (B ω).IsHermitian)
    (hG : HasLaw G (gaussianMatrix n κ) μ) (hind : IndepFun B G μ)
    (hres : Integrable (fun ω => frobSq (M - B ω)) μ) :
    MemLp (fun ω => gaussianControlVariateEstimate M (B ω) (G ω)) 2 μ ∧
    (∫ ω, gaussianControlVariateEstimate M (B ω) (G ω) ∂μ) = M.trace ∧
    Var[fun ω => gaussianControlVariateEstimate M (B ω) (G ω); μ] =
      2 / Fintype.card κ * ∫ ω, frobSq (M - B ω) ∂μ ∧
    μ[fun ω => gaussianControlVariateEstimate M (B ω) (G ω) |
      MeasurableSpace.comap B inferInstance] =ᵐ[μ] fun _ => M.trace := by
  have hBL : HasLaw B (μ.map B) μ := ⟨hBm.aemeasurable, rfl⟩
  have hBG := hind.hasLaw_prod hBL hG
  have : IsProbabilityMeasure (μ.map B) := Measure.isProbabilityMeasure_map hBm.aemeasurable
  have hsymm : MeasurableSet {T : Matrix n n ℝ | T.IsHermitian} := by
    have he : {T : Matrix n n ℝ | T.IsHermitian} =
        ⋂ i : n, ⋂ j : n, {T : Matrix n n ℝ | T j i = T i j} := by
      ext T
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Matrix.IsHermitian.ext_iff, star_trivial]
    rw [he]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_eq_fun (Matrix.measurable_entry (α := ℝ) j i)
        (Matrix.measurable_entry (α := ℝ) i j)
  have hB' := (ae_map_iff hBm.aemeasurable hsymm).2 hB
  have hmres : Measurable (fun T : Matrix n n ℝ => frobSq (M - T)) := by
    simp only [frobSq_eq_sum_sq, Matrix.sub_apply]
    fun_prop
  have hres' : Integrable (fun T => frobSq (M - T)) (μ.map B) :=
    (integrable_map_measure hmres.aestronglyMeasurable hBm.aemeasurable).2 hres
  obtain ⟨hLp, hmean, hsecond⟩ := controlVariate_product_moments (κ := κ) hM hB' hres'
  have hLp' : MemLp (fun ω => gaussianControlVariateEstimate M (B ω) (G ω)) 2 μ := by
    have h := hLp
    rw [← hBG.map_eq] at h
    exact h.comp_of_map hBG.aemeasurable
  have hmean' : (∫ ω, gaussianControlVariateEstimate M (B ω) (G ω) ∂μ) = M.trace :=
    (hBG.integral_comp hLp.aestronglyMeasurable).trans hmean
  refine ⟨hLp', hmean', ?_, ?_⟩
  · rw [variance_eq_integral hLp'.aemeasurable, hmean']
    have hm := ((measurable_controlVariate (κ := κ) M).sub_const M.trace).pow_const 2
    rw [show (∫ ω, (gaussianControlVariateEstimate M (B ω) (G ω) - M.trace) ^ 2 ∂μ) =
      ∫ p, (gaussianControlVariateEstimate M p.1 p.2 - M.trace) ^ 2
        ∂((μ.map B).prod (gaussianMatrix n κ)) from hBG.integral_comp hm.aestronglyMeasurable,
      hsecond]
    congr 1
    exact (hBL.integral_comp hmres.aestronglyMeasurable).symm
  · exact hind.condExp_comp_eq_const hBm hG (hLp.integrable (by norm_num))
      (ae_of_all _ fun T => integral_controlVariate_fixed M T)

end NLAlib
