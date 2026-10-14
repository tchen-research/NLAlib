import NLAlib.Estimation.Trace.Unbiased
import NLAlib.Matrix.Norms.DeflatedTraceBounds

/-!
# Integrability and independent leave-one-out trace estimation

The uniform orthogonal-frame bound in the supplied derivations (T2) removes the
product-law integrability hypothesis from independent deflation. Independence of a held-out
probe from the remaining probes follows from independence of disjoint finite subfamilies.
These are the remaining expectation bridges for `hutchpp-unbiased` and `xtrace-unbiased`.
-/

noncomputable section
open scoped Matrix
open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {n r κ : Type*} [Fintype n] [Fintype r] [Fintype κ]
  [DecidableEq n] [DecidableEq r]

omit [DecidableEq r] in
/-- The compressed trace plus residual quadratic form is a measurable function of its
frame and probe. This uses ordinary finite matrix operations, without choosing a basis. -/
theorem measurable_trace_compression_add_quadForm_residual (A : Matrix n n ℝ) :
    Measurable (fun p : Matrix n r ℝ × (n → ℝ) =>
      (p.1ᵀ * A * p.1).trace +
        quadForm ((1 - p.1 * p.1ᵀ) * A * (1 - p.1 * p.1ᵀ)) p.2) := by
  simp only [Matrix.trace, quadForm_eq_sum, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.sub_apply, Matrix.one_apply]
  fun_prop

variable {α : Type*} [MeasurableSpace α]
  {ν : Measure α} [IsProbabilityMeasure ν] {η : Measure (n → ℝ)} [IsProbabilityMeasure η]

/-- A measurable orthonormal frame and a probe with finite squared Euclidean norm give an
integrable deflated scalar trace kernel on the product measure. The frame distribution has
no moment assumptions. Source: supplied operator derivations, (T2), helper for
`hutchpp-unbiased` and `xtrace-unbiased`. -/
theorem integrable_trace_compression_add_quadForm_residual_prod
    (A : Matrix n n ℝ) {Q : α → Matrix n r ℝ} (hQm : Measurable Q)
    (hQ : ∀ᵐ s ∂ν, HasOrthonormalCols (Q s))
    (hw : Integrable (fun w : n → ℝ => ‖WithLp.toLp 2 w‖ ^ 2) η) :
    Integrable (fun p : α × (n → ℝ) => ((Q p.1)ᵀ * A * Q p.1).trace +
      quadForm ((1 - Q p.1 * (Q p.1)ᵀ) * A * (1 - Q p.1 * (Q p.1)ᵀ)) p.2) (ν.prod η) := by
  have hm := (measurable_trace_compression_add_quadForm_residual A).comp
    ((hQm.comp measurable_fst).prodMk measurable_snd)
  refine (((integrable_const (Fintype.card n : ℝ)).add (hw.comp_snd ν)).const_mul
    (specNorm A)).mono' hm.aestronglyMeasurable ?_
  filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hQ] with p hp
  simpa only [Real.norm_eq_abs, Pi.add_apply] using
    abs_trace_compression_add_quadForm_residual_le A hp p.2

/-- A measurable almost-surely orthonormal deflation frame and probes with finite second
moments give an integrable multi-probe trace estimate on their product law. Independence
between the probe columns is not needed. Helper for `hutchpp-unbiased`. -/
theorem integrable_deflatedTraceEstimate_prod [Nonempty κ]
    {η : Measure (Matrix n κ ℝ)} [IsProbabilityMeasure η]
    (A : Matrix n n ℝ) {Q : α → Matrix n r ℝ} (hQm : Measurable Q)
    (hQ : ∀ᵐ s ∂ν, HasOrthonormalCols (Q s))
    (hcol : ∀ k, Integrable (fun Z : Matrix n κ ℝ =>
      ‖WithLp.toLp 2 (fun j => Z j k)‖ ^ 2) η) :
    Integrable (fun p : α × Matrix n κ ℝ => deflatedTraceEstimate A (Q p.1) p.2)
      (ν.prod η) := by
  have hterm (k : κ) : Integrable (fun p : α × Matrix n κ ℝ =>
      ((Q p.1)ᵀ * A * Q p.1).trace +
        quadForm ((1 - Q p.1 * (Q p.1)ᵀ) * A * (1 - Q p.1 * (Q p.1)ᵀ))
          (fun j => p.2 j k)) (ν.prod η) := by
    have hm := (measurable_trace_compression_add_quadForm_residual A).comp
      ((hQm.comp measurable_fst).prodMk (measurable_pi_lambda _ fun j =>
        (Matrix.measurable_entry j k).comp measurable_snd))
    refine (((integrable_const (Fintype.card n : ℝ)).add
      ((hcol k).comp_snd ν)).const_mul (specNorm A)).mono'
      hm.aestronglyMeasurable ?_
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hQ] with p hp
    simpa only [Real.norm_eq_abs, Pi.add_apply] using
      abs_trace_compression_add_quadForm_residual_le A hp (fun j => p.2 j k)
  have heq (p : α × Matrix n κ ℝ) : deflatedTraceEstimate A (Q p.1) p.2 =
      (∑ k, (((Q p.1)ᵀ * A * Q p.1).trace +
        quadForm ((1 - Q p.1 * (Q p.1)ᵀ) * A * (1 - Q p.1 * (Q p.1)ᵀ))
          (fun j => p.2 j k))) / Fintype.card κ := by
    have hc : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [deflatedTraceEstimate, hutchinsonEstimate, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  simp_rw [heq]
  exact (integrable_finsetSum _ fun k _ => hterm k).div_const _

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Isotropic second moments force integrability of the squared Euclidean probe norm.
Only coordinate almost-everywhere measurability is needed. -/
theorem integrable_norm_toLp_sq_of_second_moments {w : Ω → n → ℝ}
    (hw : AEMeasurable w μ)
    (hsecond : ∀ i j, ∫ ω, w ω i * w ω j ∂μ = if i = j then 1 else 0) :
    Integrable (fun ω => ‖WithLp.toLp 2 (w ω)‖ ^ 2) μ := by
  have h := integrable_quadForm_of_second_moments (1 : Matrix n n ℝ)
    (z := w) (fun i => (measurable_pi_apply i).comp_aemeasurable hw) hsecond
  simpa only [norm_toLp_sq_eq_dotProduct_self, quadForm, star_trivial,
    Matrix.one_mulVec] using h

/-- Independent random measurable orthonormal deflation with isotropic probes is unbiased,
with no product-law integrability assumption. The proof derives it from uniform domination.
Source: Meyer–Musco–Musco–Woodruff (2021), §3; supplied operator derivations, (T1)–(T3).
The frame is supplied, and this does not assert measurability of an arbitrary choice of
sketch-image basis.
atlas: hutchpp-unbiased -/
theorem integral_deflatedTraceEstimate_comp_eq_trace_of_measurable
    [Nonempty κ] (A : Matrix n n ℝ) {Q : α → Matrix n r ℝ}
    (hQm : Measurable Q) (hQ : ∀ s, HasOrthonormalCols (Q s))
    {S : Ω → α} {G : Ω → Matrix n κ ℝ} (hS : AEMeasurable S μ)
    (hG : AEMeasurable G μ) (hind : IndepFun S G μ)
    (hsecond : ∀ k i j, ∫ ω, G ω i k * G ω j k ∂μ = if i = j then 1 else 0) :
    ∫ ω, deflatedTraceEstimate A (Q (S ω)) (G ω) ∂μ = A.trace := by
  have : IsProbabilityMeasure (μ.map S) := Measure.isProbabilityMeasure_map hS
  have : IsProbabilityMeasure (μ.map G) := Measure.isProbabilityMeasure_map hG
  apply integral_deflatedTraceEstimate_comp_eq_trace A hQ hS hG hind hsecond
  have hcol (k : κ) : Integrable (fun Z : Matrix n κ ℝ =>
      ‖WithLp.toLp 2 (fun j => Z j k)‖ ^ 2) (μ.map G) := by
    have hm : Measurable (fun Z : Matrix n κ ℝ => ‖WithLp.toLp 2 (fun j => Z j k)‖ ^ 2) := by
      fun_prop
    apply (integrable_map_measure hm.aestronglyMeasurable hG).2
    exact integrable_norm_toLp_sq_of_second_moments
      (aemeasurable_pi_lambda _ fun i => (Matrix.measurable_entry i k).comp_aemeasurable hG)
      (hsecond k)
  exact integrable_deflatedTraceEstimate_prod A hQm (Filter.Eventually.of_forall hQ) hcol

/-- Independent deflation remains unbiased when orthonormality holds only almost surely.
Measurability and isotropic second moments derive the required product-law integrability.
Source: supplied operator derivations, (T1)–(T3); Meyer–Musco–Musco–Woodruff (2021), §3.
No regular conditional distribution or standard Borel assumption on the sample space is used.
atlas: hutchpp-unbiased -/
theorem integral_deflatedTraceEstimate_comp_eq_trace_of_ae_hasOrthonormalCols
    [Nonempty κ] (A : Matrix n n ℝ) {Q : α → Matrix n r ℝ}
    (hQm : Measurable Q) {S : Ω → α} {G : Ω → Matrix n κ ℝ}
    (hS : AEMeasurable S μ) (hG : AEMeasurable G μ) (hind : IndepFun S G μ)
    (hQ : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q (S ω)))
    (hsecond : ∀ k i j, ∫ ω, G ω i k * G ω j k ∂μ = if i = j then 1 else 0) :
    ∫ ω, deflatedTraceEstimate A (Q (S ω)) (G ω) ∂μ = A.trace := by
  have : IsProbabilityMeasure (μ.map S) := Measure.isProbabilityMeasure_map hS
  have : IsProbabilityMeasure (μ.map G) := Measure.isProbabilityMeasure_map hG
  have hset : MeasurableSet {s | HasOrthonormalCols (Q s)} := by
    have heq : {s | HasOrthonormalCols (Q s)} =
        ⋂ i, ⋂ j, {s | ((Q s)ᴴ * Q s) i j = (1 : Matrix r r ℝ) i j} := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h i j
        exact congrFun (congrFun h.conjTranspose_mul_self i) j
      · intro h
        exact Matrix.ext h
    rw [heq]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_eq_fun ((Matrix.measurable_entry i j).comp
      ((Matrix.measurable_conjTranspose.comp hQm).matrix_mul hQm)) measurable_const
  have hQo : ∀ᵐ s ∂μ.map S, HasOrthonormalCols (Q s) := (ae_map_iff hS hset).2 hQ
  have hcol (k : κ) : Integrable (fun Z : Matrix n κ ℝ =>
      ‖WithLp.toLp 2 (fun j => Z j k)‖ ^ 2) (μ.map G) := by
    have hm : Measurable (fun Z : Matrix n κ ℝ => ‖WithLp.toLp 2 (fun j => Z j k)‖ ^ 2) := by
      fun_prop
    apply (integrable_map_measure hm.aestronglyMeasurable hG).2
    exact integrable_norm_toLp_sq_of_second_moments
      (aemeasurable_pi_lambda _ fun i => (Matrix.measurable_entry i k).comp_aemeasurable hG)
      (hsecond k)
  have hint := integrable_deflatedTraceEstimate_prod A hQm hQo hcol
  rw [integral_of_indepFun (g := fun s Z => deflatedTraceEstimate A (Q s) Z) hS hG hind hint]
  have hfixed : ∀ᵐ s ∂μ.map S,
      ∫ Z, deflatedTraceEstimate A (Q s) Z ∂μ.map G = A.trace := by
    filter_upwards [hQo, hint.prod_right_ae] with s hs hi
    rw [integral_map hG hi.aestronglyMeasurable]
    exact integral_deflatedTraceEstimate_eq_trace A hs
      (fun i k => (Matrix.measurable_entry i k).comp_aemeasurable hG) hsecond
  rw [integral_congr_ae hfixed, integral_const, probReal_univ, one_smul]

omit [Fintype n] [DecidableEq n] [IsProbabilityMeasure μ] in
/-- A column of an independent probe family is independent of the matrix formed by all
the other columns. Identical distribution and exchangeability are unnecessary.
This is the disjoint-subfamily bridge used for `xtrace-unbiased`. -/
theorem indepFun_leaveOneOutSketch_col [DecidableEq κ]
    {W : Ω → Matrix n κ ℝ} (hW : ∀ i, AEMeasurable (fun ω j => W ω j i) μ)
    (hind : iIndepFun (fun i ω j => W ω j i) μ) (i : κ) :
    IndepFun (fun ω => leaveOneOutSketch (W ω) i) (fun ω j => W ω j i) μ := by
  let s := Finset.univ.erase i
  let t : Finset κ := {i}
  have hdis : Disjoint s t := by simp [s, t]
  have hi := hind.indepFun_finset₀ s t hdis hW
  let f : (s → (n → ℝ)) → Matrix n {j : κ // j ≠ i} ℝ :=
    fun x k j => x ⟨j.1, by simp [s, j.2]⟩ k
  let g : (t → (n → ℝ)) → (n → ℝ) := fun x => x ⟨i, by simp [t]⟩
  have hf : Measurable f := by
    apply Matrix.measurable_iff_entries.mpr
    intro k j
    exact (measurable_pi_apply k).comp (measurable_pi_apply _)
  have hg : Measurable g := measurable_pi_apply _
  convert hi.comp hf hg using 1 <;> rfl

/-- Independent isotropic probes with measurable orthonormal corrections depending only
on the remaining columns give an unbiased leave-one-out average. Uniform domination
derives integrability, and disjoint-subfamily independence derives each held-out independence.
Source: Epperly–Tropp–Webber (2024), §2.1; supplied operator derivations, (T1)–(T3).
The probes may have different distributions; the result does not need identical distribution.
atlas: xtrace-unbiased -/
theorem integral_leaveOneOutDeflatedTraceEstimate_eq_trace_of_iIndepFun
    [Nonempty κ] [DecidableEq κ] (A : Matrix n n ℝ)
    {W : Ω → Matrix n κ ℝ} (hW : ∀ i, AEMeasurable (fun ω j => W ω j i) μ)
    (hind : iIndepFun (fun i ω j => W ω j i) μ)
    {Qf : ∀ i, Matrix n {j : κ // j ≠ i} ℝ → Matrix n r ℝ}
    (hQm : ∀ i, Measurable (Qf i))
    (hQ : ∀ i, ∀ᵐ ω ∂μ, HasOrthonormalCols (Qf i (leaveOneOutSketch (W ω) i)))
    (hsecond : ∀ i j j', ∫ ω, W ω j i * W ω j' i ∂μ = if j = j' then 1 else 0) :
    ∫ ω, leaveOneOutDeflatedTraceEstimate A
      (fun i => Qf i (leaveOneOutSketch (W ω) i)) (W ω) ∂μ = A.trace := by
  let S : ∀ i, Ω → Matrix n {j : κ // j ≠ i} ℝ :=
    fun i ω => leaveOneOutSketch (W ω) i
  have hS (i : κ) : AEMeasurable (S i) μ := by
    apply aemeasurable_pi_lambda
    intro j
    apply aemeasurable_pi_lambda
    intro k
    exact (measurable_pi_apply j).comp_aemeasurable (hW k.1)
  let D : κ → Ω → ℝ := fun i ω => ((Qf i (S i ω))ᵀ * A * Qf i (S i ω)).trace +
    quadForm ((1 - Qf i (S i ω) * (Qf i (S i ω))ᵀ) * A *
      (1 - Qf i (S i ω) * (Qf i (S i ω))ᵀ)) (fun j => W ω j i)
  have hDI (i : κ) : Integrable (D i) μ := by
    have hm := (measurable_trace_compression_add_quadForm_residual A).comp_aemeasurable
      (((hQm i).comp_aemeasurable (hS i)).prodMk (hW i))
    refine (((integrable_const (Fintype.card n : ℝ)).add
      (integrable_norm_toLp_sq_of_second_moments (hW i) (hsecond i))).const_mul
      (specNorm A)).mono' hm.aestronglyMeasurable ?_
    filter_upwards [hQ i] with ω hω
    simpa only [Real.norm_eq_abs, Pi.add_apply] using
      abs_trace_compression_add_quadForm_residual_le A hω (fun j => W ω j i)
  have hDE (i : κ) : ∫ ω, D i ω ∂μ = A.trace := by
    have hr : Measurable (Matrix.replicateCol Unit : (n → ℝ) → Matrix n Unit ℝ) := by
      apply Matrix.measurable_iff_entries.mpr
      intro j k
      exact measurable_pi_apply j
    have hi := (indepFun_leaveOneOutSketch_col hW hind i).comp measurable_id hr
    have h := integral_deflatedTraceEstimate_comp_eq_trace_of_ae_hasOrthonormalCols
      (κ := Unit) A (hQm i) (hS i) (hr.comp_aemeasurable (hW i)) hi (hQ i)
      (fun _ j k => hsecond i j k)
    simpa [D, deflatedTraceEstimate, hutchinsonEstimate] using h
  change ∫ ω, (∑ i, D i ω) / Fintype.card κ ∂μ = A.trace
  rw [integral_div, integral_finsetSum _ fun i _ => hDI i]
  simp only [hDE, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

end NLAlib
