import NLAlib.Solvers.Nystrom.RoundedExpectation

/-!
# Constant-probability Nyström PCG convergence

At the FTU effective-dimension width the actual finite condition number is at
most 56 with probability greater than one half. A native residual event, also
of probability greater than one half, gives the PCG energy estimate with the
universal rate `(sqrt 56-1)/(sqrt 56+1)` for all right-hand sides and initial
vectors at once.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder
namespace NLAlib

/-- Universal PCG convergence factor associated with condition number 56. -/
def nystromPCGRate : ℝ := (Real.sqrt 56-1)/(Real.sqrt 56+1)

open scoped Matrix.Norms.L2Operator in
/-- At the original rounded width, the actual FTU condition number is at
most 56 with probability strictly greater than one half.
atlas: nystrom-pcg (partial) -/
theorem measureReal_conditionNumber_nystrom_rounded_le_56_gt_half
    {Ωs : Type*} [MeasurableSpace Ωs] {ν : Measure Ωs}
    {n : ℕ} [Nonempty (Fin n)] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {μ : ℝ} (hμ : 0 < μ)
    (Ω : Ωs → Matrix (Fin n) (Fin (nystromSketchWidth A μ)) ℝ)
    (hΩ : HasLaw Ω (gaussianMatrix (Fin n) (Fin (nystromSketchWidth A μ))) ν) :
    1/2 < ν.real {ω | (conditionNumber (nystromPreconditionedMatrix A
      (nystrom A (Ω ω)) (nystromFloor A (Ω ω)) μ)).toReal ≤ 56} := by
  have := hΩ.isProbabilityMeasure
  let f := fun ω => (conditionNumber (nystromPreconditionedMatrix A
    (nystrom A (Ω ω)) (nystromFloor A (Ω ω)) μ)).toReal
  obtain ⟨hi,hb⟩ := integrable_and_integral_conditionNumber_nystrom_rounded_lt_28 hA hμ Ω hΩ
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => (ENNReal.toReal_nonneg : 0 ≤ f ω)) hi 56
  have hbad : ν.real {ω | 56 < f ω} < 1/2 := by
    have hsub : {ω | 56 < f ω} ⊆ {ω | 56 ≤ f ω} := by
      intro ω h
      exact (show 56 < f ω from h).le
    have hh := measureReal_mono (μ := ν) hsub
    change ∫ ω, f ω ∂ν < 28 at hb
    change 56 * ν.real {ω | 56 ≤ f ω} ≤ ∫ ω, f ω ∂ν at hm
    linarith
  have hnull : NullMeasurableSet {ω | f ω ≤ 56} ν :=
    hi.aestronglyMeasurable.aemeasurable.nullMeasurableSet_preimage measurableSet_Iic
  have hc := measureReal_add_measureReal_compl₀ (μ := ν) hnull
  rw [probReal_univ] at hc
  have he : {ω | f ω ≤ 56}ᶜ = {ω | 56 < f ω} := by ext ω; simp
  rw [he] at hc
  change 1/2 < ν.real {ω | f ω ≤ 56}
  linarith

open scoped Matrix.Norms.L2Operator in
/-- A residual of at most `54 μ` gives a universal native PCG energy bound
for the original FTU floor preconditioner at the rounded sketch width.
atlas: nystrom-pcg (partial) -/
theorem quadForm_sub_le_of_isPCGIterate_nystrom_rounded
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {μ : ℝ} (hμ : 0 < μ)
    (Ω : Matrix (Fin n) (Fin (nystromSketchWidth A μ)) ℝ)
    (hE : specNorm (A-nystrom A Ω) ≤ 54*μ)
    {c x₀ xs x : Fin n → ℝ} (hxs : (A+μ•1)*ᵥxs=c) {q : ℕ}
    (hx : IsPCGIterate (A+μ•1)
      (nystromPreconditioner (nystrom A Ω) (nystromFloor A Ω) μ) c x₀ q x) :
    quadForm (A+μ•1) (x-xs) ≤ (2*nystromPCGRate^q)^2 * quadForm (A+μ•1) (x₀-xs) := by
  have hB := posSemidef_nystrom hA Ω
  have hBA := Matrix.le_iff.mpr (posSemidef_sub_nystrom hA Ω)
  have ha : 0 ≤ nystromFloor A Ω := singularValues_nonneg _ _
  have hf := nystromFloor_le_regularization_of_effectiveDimension hA hμ
    (nystromEffectiveDimension_le_nystromSketchHead A hμ) Ω
  have hP := nystromPreconditioner_posDef hB ha hμ
  have hs := nystromPreconditioner_sandwich hB hBA ha hμ
  have hbound : nystromFloor A Ω+μ+specNorm (A-nystrom A Ω) ≤ 56*μ := by
    calc
      _ ≤ μ+μ+54*μ := add_le_add (add_le_add hf (le_refl μ)) hE
      _ = 56*μ := by ring
  have hu : A+μ•1 ≤ (56*μ) • nystromPreconditioner (nystrom A Ω) (nystromFloor A Ω) μ :=
    hs.2.trans (smul_le_smul_of_nonneg_right hbound hP.posSemidef.nonneg)
  have hr : (Real.sqrt (56*μ)-Real.sqrt μ)/(Real.sqrt (56*μ)+Real.sqrt μ) = nystromPCGRate := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 56)]
    unfold nystromPCGRate
    have hp := Real.sqrt_pos.mpr hμ
    have h56 := Real.sqrt_nonneg (56:ℝ)
    field_simp
  have hh := quadForm_sub_le_of_isPCGIterate hP hμ (by linarith : μ≤56*μ) hs.1 hu hxs hx
  rwa [hr] at hh

open scoped Matrix.Norms.L2Operator in
/-- The universal native PCG rate holds on one measurable residual event of
probability greater than one half, uniformly over right-hand sides and starts.
atlas: nystrom-pcg (partial) -/
theorem measureReal_nystrom_rounded_residual_le_gt_half
    {Ωs : Type*} [MeasurableSpace Ωs] {ν : Measure Ωs}
    {n : ℕ} [Nonempty (Fin n)] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {μ : ℝ} (hμ : 0 < μ)
    (Ω : Ωs → Matrix (Fin n) (Fin (nystromSketchWidth A μ)) ℝ)
    (hΩ : HasLaw Ω (gaussianMatrix (Fin n) (Fin (nystromSketchWidth A μ))) ν) :
    1/2 < ν.real {ω | specNorm (A-nystrom A (Ω ω)) ≤ 54*μ} := by
  have := hΩ.isProbabilityMeasure
  let f := fun ω => specNorm (A-nystrom A (Ω ω))
  obtain ⟨hi,hb⟩ := integrable_and_integral_specNorm_sub_nystrom_rounded_le hA hμ Ω hΩ
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => specNorm_nonneg (A-nystrom A (Ω ω))) hi (54*μ)
  have hbad : ν.real {ω | 54*μ < f ω} < 1/2 := by
    have hsub : {ω | 54*μ < f ω} ⊆ {ω | 54*μ ≤ f ω} := by
      intro ω h
      exact (show 54*μ < f ω from h).le
    have hh := measureReal_mono (μ := ν) hsub
    have he := Real.exp_one_lt_three
    have he0 := Real.exp_pos (1:ℝ)
    have hconst : 6+2*Real.exp 1^2 < 27 := by nlinarith
    have hb' : ∫ ω, f ω ∂ν < 27*μ := lt_of_le_of_lt hb (mul_lt_mul_of_pos_right hconst hμ)
    have hm' : 54*μ*ν.real {ω | 54*μ ≤ f ω} < 27*μ := lt_of_le_of_lt hm hb'
    have hgood : ν.real {ω | 54*μ ≤ f ω} < 1/2 := by
      by_contra h
      have hn := le_of_not_gt h
      have hlow : 27*μ ≤ 54*μ*ν.real {ω | 54*μ ≤ f ω} := by
        calc
          _ = (54*μ)*(1/2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)
      exact not_lt_of_ge hlow hm'
    exact hh.trans_lt hgood
  have hnull : NullMeasurableSet {ω | f ω ≤ 54*μ} ν :=
    hi.aestronglyMeasurable.aemeasurable.nullMeasurableSet_preimage measurableSet_Iic
  have hc := measureReal_add_measureReal_compl₀ (μ := ν) hnull
  rw [probReal_univ] at hc
  have he : {ω | f ω ≤ 54*μ}ᶜ = {ω | 54*μ < f ω} := by ext ω; simp
  rw [he] at hc
  change 1/2 < ν.real {ω | f ω ≤ 54*μ}
  linarith

end NLAlib
