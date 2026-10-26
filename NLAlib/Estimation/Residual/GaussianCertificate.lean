import NLAlib.Matrix.Norms.Net
import NLAlib.Probability.Gaussian.Basic.StandardVector
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic

/-!
# Gaussian residual certificates

The exact scalar small-ball constant and a norming linear functional reduce a
rectangular residual certificate to independent one-dimensional Gaussian events.

Source: Halko--Martinsson--Tropp (2011), Lemma 4.1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Matrix

namespace NLAlib

/-- The exact density-maximum small-ball estimate for a standard real Gaussian. -/
private theorem gaussianReal_abs_le_le_sqrt_two_div_pi (t : ℝ) :
    gaussianReal 0 1 {x : ℝ | |x| ≤ t} ≤ ENNReal.ofReal (Real.sqrt (2 / Real.pi) * t) := by
  have hp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hc : Real.sqrt (2 / Real.pi) * Real.sqrt (2 * Real.pi) = 2 := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 / Real.pi)]
    have he : (2 / Real.pi) * (2 * Real.pi) = 4 := by field_simp; ring
    rw [he]
    convert Real.sqrt_sq_eq_abs (2 : ℝ) using 1 <;> norm_num
  have hpdf (x : ℝ) : gaussianPDFReal 0 1 x ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])) (inv_nonneg.mpr hp.le)).trans
      (by rw [mul_one])
  have hset : {x : ℝ | |x| ≤ t} = Icc (-t) t := by ext x; simp [abs_le]
  rw [hset, gaussianReal_apply 0 (by norm_num : (1 : NNReal) ≠ 0)]
  calc
    (∫⁻ x in Icc (-t) t, gaussianPDF 0 1 x) ≤
        ∫⁻ _ in Icc (-t) t, ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ :=
      lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpdf x)
    _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * (2 * t)) := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hp.le)]
      congr 2
      ring
    _ = _ := by
      congr 1
      apply (mul_right_cancel₀ hp.ne')
      calc
        (Real.sqrt (2 * Real.pi))⁻¹ * (2 * t) * Real.sqrt (2 * Real.pi) = 2 * t := by
          field_simp
        _ = (Real.sqrt (2 / Real.pi) * Real.sqrt (2 * Real.pi)) * t := by rw [hc]
        _ = _ := by ring

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A nonzero rectangular matrix has a unit input functional dominated by its
output norm after multiplication by the spectral norm. -/
private theorem exists_unit_dotProduct_le_mulVec_norm [Nonempty m]
    (A : Matrix m n ℝ) (hA : specNorm A ≠ 0) :
    ∃ v : n → ℝ, ‖WithLp.toLp 2 v‖ = 1 ∧
      ∀ x, specNorm A * |v ⬝ᵥ x| ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖ := by
  have hpos : 0 < specNorm A := lt_of_le_of_ne (specNorm_nonneg A) (Ne.symm hA)
  have hGram : (A * Aᵀ).IsHermitian := by
    simpa using Matrix.isHermitian_conjTranspose_mul_self Aᵀ
  obtain ⟨u, hu, hq⟩ := exists_unit_abs_quadForm_eq_specNorm hGram
  let w : n → ℝ := Aᵀ *ᵥ u
  have hw : ‖WithLp.toLp 2 w‖ = specNorm A := by
    have hquad : quadForm (A * Aᵀ) u = w ⬝ᵥ w := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
        star_trivial] using quadForm_conjTranspose_mul_self Aᵀ u
    have hnorm : ‖WithLp.toLp 2 w‖ ^ 2 = w ⬝ᵥ w := norm_toLp_sq_eq_dotProduct_self w
    rw [hquad, abs_of_nonneg (dotProduct_self_nonneg w)] at hq
    have hgramnorm : specNorm (A * Aᵀ) = specNorm A ^ 2 := by
      simpa using specNorm_mul_conjTranspose_self A
    rw [hgramnorm] at hq
    nlinarith [norm_nonneg (WithLp.toLp 2 w)]
  let v : n → ℝ := (specNorm A)⁻¹ • w
  have hv : ‖WithLp.toLp 2 v‖ = 1 := by
    simp only [v, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hpos), hw, inv_mul_cancel₀ hA]
  refine ⟨v, hv, fun x => ?_⟩
  have hd : specNorm A * (v ⬝ᵥ x) = u ⬝ᵥ (A *ᵥ x) := by
    simp only [v, smul_dotProduct, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hA, one_mul]
    simp only [w, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have hcs := abs_real_inner_le_norm (WithLp.toLp 2 u : EuclideanSpace ℝ m)
    (WithLp.toLp 2 (A *ᵥ x))
  have hi : inner ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ m) (WithLp.toLp 2 (A *ᵥ x)) =
      u ⬝ᵥ (A *ᵥ x) := by simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [hi, hu, one_mul, ← hd, abs_mul, abs_of_pos hpos] at hcs
  exact hcs

variable {κ Ω : Type*} [Fintype κ] [Nonempty κ]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The largest Euclidean residual norm among a nonempty finite family of probes. -/
def gaussianResidualMaximum (A : Matrix m n ℝ) (g : κ → n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => ‖WithLp.toLp 2 (A *ᵥ g j)‖)

omit [DecidableEq m] [DecidableEq n] in
private theorem le_gaussianResidualMaximum (A : Matrix m n ℝ) (g : κ → n → ℝ) (j : κ) :
    ‖WithLp.toLp 2 (A *ᵥ g j)‖ ≤ gaussianResidualMaximum A g := by
  unfold gaussianResidualMaximum
  exact Finset.le_sup' (fun j => ‖WithLp.toLp 2 (A *ᵥ g j)‖) (Finset.mem_univ j)

omit [DecidableEq m] [DecidableEq n] in
private theorem gaussianResidualMaximum_nonneg (A : Matrix m n ℝ) (g : κ → n → ℝ) :
    0 ≤ gaussianResidualMaximum A g := by
  obtain ⟨j⟩ := ‹Nonempty κ›
  exact (norm_nonneg _).trans (le_gaussianResidualMaximum A g j)

omit [IsProbabilityMeasure μ] in
/-- Independent standard Gaussian probes give the exact residual certificate
`P{‖A‖₂ > α sqrt(2/π) maxⱼ ‖A gⱼ‖₂} ≤ α^(-|κ|)`.
The theorem includes rectangular and zero matrices and permits merely a.e.
measurable probes through their native Gaussian laws.
Source: Halko--Martinsson--Tropp (2011), Lemma 4.1.
atlas: gaussian-residual-certificate -/
theorem measure_specNorm_gt_gaussianResidualMaximum_le
    (A : Matrix m n ℝ) {α : ℝ} (hα : 1 < α)
    {g : κ → Ω → n → ℝ} (hg : ∀ j, HasLaw (g j) (gaussianVector n) μ)
    (hind : iIndepFun g μ) :
    μ {ω | α * Real.sqrt (2 / Real.pi) * gaussianResidualMaximum A (fun j => g j ω) <
      specNorm A} ≤ ENNReal.ofReal ((α⁻¹) ^ Fintype.card κ) := by
  have hαpos : 0 < α := lt_trans (by norm_num) hα
  have hc : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  by_cases hA : specNorm A = 0
  · have hempty : {ω | α * Real.sqrt (2 / Real.pi) * gaussianResidualMaximum A (fun j => g j ω) <
        specNorm A} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt, hA]
      exact mul_nonneg (mul_nonneg hαpos.le hc.le) (gaussianResidualMaximum_nonneg A _)
    rw [hempty, measure_empty]
    exact zero_le
  have hm : Nonempty m := by
    by_contra hempty
    have : IsEmpty m := not_nonempty_iff.mp hempty
    have hzero : A = 0 := Matrix.ext fun i _ => isEmptyElim i
    exact hA (by rw [hzero, specNorm_zero])
  obtain ⟨v, hv, hdom⟩ := exists_unit_dotProduct_le_mulVec_norm A hA
  let t : ℝ := (α * Real.sqrt (2 / Real.pi))⁻¹
  let E : κ → Set Ω := fun j => {ω | |v ⬝ᵥ g j ω| ≤ t}
  have hset : MeasurableSet {x : n → ℝ | |v ⬝ᵥ x| ≤ t} := by
    apply measurableSet_le _ measurable_const
    unfold dotProduct
    fun_prop
  have hscalar : MeasurableSet {x : ℝ | |x| ≤ t} :=
    measurableSet_le measurable_id.abs measurable_const
  have hE (j : κ) : μ (E j) ≤ ENNReal.ofReal α⁻¹ := by
    have hl := (hasLaw_dotProduct_gaussianVector v hv).comp (hg j)
    have heq : μ (E j) = gaussianReal 0 1 {x : ℝ | |x| ≤ t} := by
      exact hl.measure_eq hscalar
    rw [heq]
    apply (gaussianReal_abs_le_le_sqrt_two_div_pi t).trans_eq
    congr 1
    dsimp [t]
    field_simp
  have hsub : {ω | α * Real.sqrt (2 / Real.pi) * gaussianResidualMaximum A (fun j => g j ω) <
      specNorm A} ⊆ ⋂ j, E j := by
    intro ω hω
    change α * Real.sqrt (2 / Real.pi) * gaussianResidualMaximum A (fun j => g j ω) <
      specNorm A at hω
    apply Set.mem_iInter.mpr
    intro j
    have hpos : 0 < specNorm A := lt_of_le_of_ne (specNorm_nonneg A) (Ne.symm hA)
    have hdom' := (hdom (g j ω)).trans (le_gaussianResidualMaximum A (fun j => g j ω) j)
    have hprod : (α * Real.sqrt (2 / Real.pi)) * |v ⬝ᵥ g j ω| < 1 := by
      have hh := mul_le_mul_of_nonneg_left hdom' (mul_nonneg hαpos.le hc.le)
      have : specNorm A * ((α * Real.sqrt (2 / Real.pi)) * |v ⬝ᵥ g j ω|) <
          specNorm A * 1 := by
        calc
          _ = α * Real.sqrt (2 / Real.pi) * (specNorm A * |v ⬝ᵥ g j ω|) := by ring
          _ ≤ _ := hh
          _ < _ := by simpa only [mul_one] using hω
      exact (mul_lt_mul_iff_right₀ hpos).mp this
    change |v ⬝ᵥ g j ω| ≤ t
    rw [show t = 1 / (α * Real.sqrt (2 / Real.pi)) by simp [t]]
    exact ((lt_div_iff₀ (mul_pos hαpos hc)).2 (by simpa [mul_comm] using hprod)).le
  calc
    μ _ ≤ μ (⋂ j, E j) := measure_mono hsub
    _ = ∏ j, μ (E j) := hind.meas_iInter (fun j => ⟨_, hset, rfl⟩)
    _ ≤ ∏ _j : κ, ENNReal.ofReal α⁻¹ :=
      Finset.prod_le_prod (fun _ _ => zero_le) (fun j _ => hE j)
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ, ← ENNReal.ofReal_pow (inv_nonneg.mpr hαpos.le)]

end NLAlib
