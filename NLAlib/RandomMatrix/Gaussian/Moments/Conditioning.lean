import NLAlib.RandomMatrix.Gaussian.Invariance.Invariance
import NLAlib.RandomMatrix.Gaussian.Moments.SecondMoment
import NLAlib.Matrix.Measurability.Measurable
import NLAlib.ForMathlib.Probability.Independence

/-!
# Conditioning on independent Gaussian blocks

The tower-property engine that turns the Gaussian moment identities of
`NLAlib.RandomMatrix.Gaussian.Moments.SecondMoment` into the expectation hypotheses taken by the randomized SVD and
generalized Nyström error bounds.

* `integral_frobSq_mul_gaussian_mul_of_indepFun`: `E ‖S Y T(X)‖_F² = ‖S‖_F² E ‖T(X)‖_F²` for a
  standard Gaussian `Y` independent of `X` (no integrability hypotheses: both sides are
  integrals of nonnegative functions and the identity holds in `ℝ≥0∞` first).
* `integral_frobSq_mul_block_mul_pinvR_block`: `E ‖S₂ Ω₂ Ω₁†‖_F² = ‖S₂‖_F² E ‖Ω₁†‖_F²`
  (HMT 2011 Thm 10.5 proof, the step after Prop 10.1), and its transposed twin
  `integral_frobSq_pinvL_block_mul_block_mul`.
* `integral_frobSq_pinvR_block`: `E ‖(V₁ᵀ Ω)†‖_F² = E_{G ~ N(0,1)^{k×t}} ‖G†‖_F²`.

Here a *block* of `Ω` is `Vᵀ Ω` for `V` with orthonormal columns (HMT 2011 §10.2:
`Ω₁ = V₁ᵀ Ω`, `Ω₂ = V₂ᵀ Ω`).

Atlas: `gaussian-conditioning`. No new Gaussian computation is done here; only independence,
Fubini for independent variables (`lintegral_of_indepFun`, `integral_of_indepFun` in
`NLAlib.ForMathlib.Probability.Independence`), the block law (`block-law-indep`) and the sandwiched second moment
(`gaussian-frob-second-moment`). The measurability helpers `measurable_frobSq_of_entries` and
`measurable_pinvR_entry` are in `NLAlib.Matrix.Structured.Measurable`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]

/-! ### The sandwiched Gaussian second moment, conditioned -/

/-- `G ↦ ‖S G T‖_F²` is integrable under the standard Gaussian matrix law. Atlas
`gaussian-conditioning` (integrability side condition of `gaussian-moments`). -/
theorem integrable_frobSq_mul_gaussianMatrix_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p m : Type*} [Fintype p] [Fintype m] (S : Matrix ι p ℝ) (T : Matrix m κ ℝ) :
    Integrable (fun G : Matrix p m ℝ => frobSq (S * G * T))
      (gaussianMatrix p m) := by
  classical
  have hsq : Integrable (fun G : Matrix p m ℝ => frobSq G)
      (gaussianMatrix p m) := by
    simp_rw [frobSq_eq_sum_sq]
    refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
    exact (memLp_gaussianMatrix_entry a b 2 (by simp)).integrable_sq
  have hm : Measurable fun G : Matrix p m ℝ => frobSq (S * G * T) :=
    measurable_frobSq_of_entries (Matrix.measurable_iff_entries.mp
      ((measurable_const.matrix_mul measurable_id).matrix_mul measurable_const))
  refine (hsq.const_mul (frobSq S * frobSq T)).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun G => ?_)
  rw [Real.norm_of_nonneg (frobSq_nonneg _)]
  calc frobSq (S * G * T) ≤ frobSq (S * G) * frobSq T := frobSq_mul_le _ _
    _ ≤ frobSq S * frobSq G * frobSq T :=
        mul_le_mul_of_nonneg_right (frobSq_mul_le _ _) (frobSq_nonneg _)
    _ = frobSq S * frobSq T * frobSq G := by ring

/-- `(x, y) ↦ ‖S y T(x)‖_F²` is measurable when `T` is entrywise measurable. -/
private lemma measurable_frobSq_mul_mul_prod {α ι κ : Type*} [MeasurableSpace α] [Fintype ι]
    [Fintype κ] {p m : Type*} [Fintype p] [Fintype m] (S : Matrix ι p ℝ)
    {T : α → Matrix m κ ℝ}
    (hT : ∀ i j, Measurable fun x => T x i j) :
    Measurable fun q : α × Matrix p m ℝ => frobSq (S * q.2 * T q.1) :=
  measurable_frobSq_of_entries (Matrix.measurable_iff_entries.mp
    ((measurable_const.matrix_mul measurable_snd).matrix_mul
      ((Matrix.measurable_iff_entries.mpr hT).comp measurable_fst)))

/-- `ℝ≥0∞` form of `integral_frobSq_mul_gaussian_mul_of_indepFun`; no integrability needed.
HMT 2011 Prop 10.1 combined with the tower property (proof of Thm 10.5). Atlas
`gaussian-conditioning`. -/
theorem lintegral_frobSq_mul_gaussian_mul_of_indepFun {α ι κ : Type*} [MeasurableSpace α]
    [Fintype ι] [Fintype κ] {p m : Type*} [Fintype p] [Fintype m] {X : Ωs → α}
    {Y : Ωs → Matrix p m ℝ}
    (hX : AEMeasurable X μ) (hY : HasLaw Y (gaussianMatrix p m) μ)
    (hXY : IndepFun X Y μ)
    (S : Matrix ι p ℝ) {T : α → Matrix m κ ℝ}
    (hT : ∀ i j, Measurable fun x => T x i j) :
    ∫⁻ ω, ENNReal.ofReal (frobSq (S * Y ω * T (X ω))) ∂μ =
      ∫⁻ ω, ENNReal.ofReal (frobSq S * frobSq (T (X ω))) ∂μ := by
  have hYm : AEMeasurable Y μ := hY.aemeasurable
  have hFm : Measurable (Function.uncurry fun (x : α) (y : Matrix p m ℝ) =>
      ENNReal.ofReal (frobSq (S * y * T x))) := by
    exact ENNReal.measurable_ofReal.comp (measurable_frobSq_mul_mul_prod S hT)
  have hGm : Measurable fun x : α => ENNReal.ofReal (frobSq S * frobSq (T x)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_frobSq_of_entries hT))
  rw [lintegral_of_indepFun hX hYm hXY hFm.aemeasurable, hY.map_eq,
    ← lintegral_map' hGm.aemeasurable hX]
  congr 1
  funext x
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_frobSq_mul_gaussianMatrix_mul S (T x))
    (ae_of_all _ fun _ => frobSq_nonneg _), integral_frobSq_mul_gaussianMatrix_mul]

/-- **Sandwiched Gaussian second moment, conditioned.** If `Y` is a standard Gaussian
`p × m` matrix independent of `X`, then `E ‖S Y T(X)‖_F² = ‖S‖_F² E ‖T(X)‖_F²`.

No integrability hypothesis: both integrands are nonnegative and the identity holds for the
lower Lebesgue integrals (`lintegral_frobSq_mul_gaussian_mul_of_indepFun`); when the right side
is not integrable both Bochner integrals are `0`. Integrability of the left side is
`integrable_frobSq_mul_gaussian_mul_of_indepFun`.
HMT 2011 Prop 10.1 with the tower property (proof of Thm 10.5). Atlas `gaussian-conditioning`.
Measurability of `T` is stated entrywise.
atlas: gaussian-conditioning -/
theorem integral_frobSq_mul_gaussian_mul_of_indepFun {α ι κ : Type*} [MeasurableSpace α]
    [Fintype ι] [Fintype κ] {p m : Type*} [Fintype p] [Fintype m] {X : Ωs → α}
    {Y : Ωs → Matrix p m ℝ}
    (hX : AEMeasurable X μ) (hY : HasLaw Y (gaussianMatrix p m) μ)
    (hXY : IndepFun X Y μ)
    (S : Matrix ι p ℝ) {T : α → Matrix m κ ℝ}
    (hT : ∀ i j, Measurable fun x => T x i j) :
    ∫ ω, frobSq (S * Y ω * T (X ω)) ∂μ = frobSq S * ∫ ω, frobSq (T (X ω)) ∂μ := by
  have hYm : AEMeasurable Y μ := hY.aemeasurable
  have hL : AEStronglyMeasurable (fun ω => frobSq (S * Y ω * T (X ω))) μ := by
    have hF := measurable_frobSq_mul_mul_prod S hT
    exact (hF.comp_aemeasurable (hX.prodMk hYm)).aestronglyMeasurable
  have hR : AEStronglyMeasurable (fun ω => frobSq S * frobSq (T (X ω))) μ :=
    (measurable_const.mul (measurable_frobSq_of_entries hT)).comp_aemeasurable hX
      |>.aestronglyMeasurable
  rw [← integral_const_mul,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => frobSq_nonneg _) hL,
    integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun _ => mul_nonneg (frobSq_nonneg _) (frobSq_nonneg _)) hR,
    lintegral_frobSq_mul_gaussian_mul_of_indepFun hX hY hXY S hT]

/-- Integrability companion of `integral_frobSq_mul_gaussian_mul_of_indepFun`: if
`‖T(X)‖_F²` is integrable, so is `‖S Y T(X)‖_F²`. Atlas `gaussian-conditioning`. -/
theorem integrable_frobSq_mul_gaussian_mul_of_indepFun {α ι κ : Type*} [MeasurableSpace α]
    [Fintype ι] [Fintype κ] {p m : Type*} [Fintype p] [Fintype m] {X : Ωs → α}
    {Y : Ωs → Matrix p m ℝ}
    (hX : AEMeasurable X μ) (hY : HasLaw Y (gaussianMatrix p m) μ)
    (hXY : IndepFun X Y μ)
    (S : Matrix ι p ℝ) {T : α → Matrix m κ ℝ}
    (hT : ∀ i j, Measurable fun x => T x i j)
    (hTi : Integrable (fun ω => frobSq (T (X ω))) μ) :
    Integrable (fun ω => frobSq (S * Y ω * T (X ω))) μ := by
  have hYm : AEMeasurable Y μ := hY.aemeasurable
  have hF := measurable_frobSq_mul_mul_prod S hT
  refine ⟨(hF.comp_aemeasurable (hX.prodMk hYm)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => frobSq_nonneg _),
    lintegral_frobSq_mul_gaussian_mul_of_indepFun hX hY hXY S hT]
  exact (hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun _ => mul_nonneg (frobSq_nonneg _) (frobSq_nonneg _))).1
    (hTi.const_mul (frobSq S)).hasFiniteIntegral

/-! ### Inverse-moment factorisation (randomized SVD and completion step) -/

/-- **RSVD inverse-moment factorisation.** If `Ω` is an `n × t` standard Gaussian matrix and
`V₁`, `V₂` have orthonormal, mutually orthogonal columns, then
`E ‖S₂ (V₂ᵀΩ) (V₁ᵀΩ)†‖_F² = ‖S₂‖_F² E ‖(V₁ᵀΩ)†‖_F²` for every fixed `S₂`.

HMT 2011 (Halko–Martinsson–Tropp), proof of Thm 10.5 (conditioning on `Ω₁`, then Prop 10.1).
This is hypothesis `hinv` of `NLAlib.rsvd_truncated_main` modulo the inverse moment
`E ‖Ω₁†‖_F² = k/(t−k−1)`. No integrability hypothesis is needed (see
`integral_frobSq_mul_gaussian_mul_of_indepFun`).
Atlas `gaussian-conditioning`.
atlas: gaussian-conditioning -/
theorem integral_frobSq_mul_block_mul_pinvR_block {n k r r' t : ℕ}
    {Ω : Ωs → Matrix (Fin n) (Fin t) ℝ}
    (hΩ : HasLaw Ω (gaussianMatrix (Fin n) (Fin t)) μ) (V₁ : Matrix (Fin n) (Fin k) ℝ)
    (V₂ : Matrix (Fin n) (Fin r') ℝ) (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (hV₁₂ : V₁ᵀ * V₂ = 0) (S₂ : Matrix (Fin r) (Fin r') ℝ) :
    ∫ ω, frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) ∂μ =
      frobSq S₂ * ∫ ω, frobSq (pinvR (V₁ᵀ * Ω ω)) ∂μ :=
  integral_frobSq_mul_gaussian_mul_of_indepFun
    (X := fun ω => V₁ᵀ * Ω ω)
    (Y := fun ω => V₂ᵀ * Ω ω)
    ((measurable_block V₁).comp_aemeasurable hΩ.aemeasurable)
    (hasLaw_gaussianMatrix_block_of_hasLaw hΩ V₂ hV₂)
    (gaussianMatrix_indepFun_block_of_hasLaw hΩ V₁ V₂ hV₁ hV₂ hV₁₂)
    S₂ (T := fun x => pinvR x) measurable_pinvR_entry

/-- Integrability companion of `integral_frobSq_mul_block_mul_pinvR_block` (hypothesis `hZi`
of `NLAlib.rsvd_truncated_main`, given integrability of `‖(V₁ᵀΩ)†‖_F²`). HMT 2011 proof of
Thm 10.5. Atlas `gaussian-conditioning`. -/
theorem integrable_frobSq_mul_block_mul_pinvR_block {n k r r' t : ℕ}
    {Ω : Ωs → Matrix (Fin n) (Fin t) ℝ}
    (hΩ : HasLaw Ω (gaussianMatrix (Fin n) (Fin t)) μ) (V₁ : Matrix (Fin n) (Fin k) ℝ)
    (V₂ : Matrix (Fin n) (Fin r') ℝ) (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (hV₁₂ : V₁ᵀ * V₂ = 0) (S₂ : Matrix (Fin r) (Fin r') ℝ)
    (hi : Integrable (fun ω => frobSq (pinvR (V₁ᵀ * Ω ω))) μ) :
    Integrable
      (fun ω => frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω))) μ :=
  integrable_frobSq_mul_gaussian_mul_of_indepFun
    (X := fun ω => V₁ᵀ * Ω ω)
    (Y := fun ω => V₂ᵀ * Ω ω)
    ((measurable_block V₁).comp_aemeasurable hΩ.aemeasurable)
    (hasLaw_gaussianMatrix_block_of_hasLaw hΩ V₂ hV₂)
    (gaussianMatrix_indepFun_block_of_hasLaw hΩ V₁ V₂ hV₁ hV₂ hV₁₂)
    S₂ (T := fun x => pinvR x) measurable_pinvR_entry hi

/-- **Completion-step inverse-moment factorisation** (transposed form of
`integral_frobSq_mul_block_mul_pinvR_block`). If `Ψ` is an `m × s` standard Gaussian matrix and
`Q`, `Qp` have orthonormal, mutually orthogonal columns, then for every fixed `B`
`E ‖(ΨᵀQ)† (ΨᵀQp) B‖_F² = E ‖(ΨᵀQ)†‖_F² · ‖B‖_F²`.

Generalized Nyström / two-sided sketch analysis (hypothesis `hG₂` of `completion_reduction`);
the conditioning argument of HMT 2011 Thm 10.5 applied to the transposed sketch. Here
`(ΨᵀQ)† = pinvL (ΨᵀQ)`. Atlas `gaussian-conditioning`.
atlas: gaussian-conditioning -/
theorem integral_frobSq_pinvL_block_mul_block_mul {m s q rp : ℕ} {ι : Type*} [Fintype ι]
    {Ψ : Ωs → Matrix (Fin m) (Fin s) ℝ} (hΨ : HasLaw Ψ (gaussianMatrix (Fin m) (Fin s)) μ)
    (Q : Matrix (Fin m) (Fin q) ℝ) (Qp : Matrix (Fin m) (Fin rp) ℝ) (hQ : HasOrthonormalCols Q)
    (hQp : HasOrthonormalCols Qp) (hQQp : Qᵀ * Qp = 0) (B : Matrix (Fin rp) ι ℝ) :
    ∫ ω, frobSq (pinvL ((Ψ ω)ᵀ * Q) * ((Ψ ω)ᵀ * Qp) * B) ∂μ =
      (∫ ω, frobSq (pinvL ((Ψ ω)ᵀ * Q)) ∂μ) * frobSq B := by
  have key := integral_frobSq_mul_gaussian_mul_of_indepFun
    (X := fun ω => Qᵀ * Ψ ω)
    (Y := fun ω => Qpᵀ * Ψ ω)
    ((measurable_block Q).comp_aemeasurable hΨ.aemeasurable)
    (hasLaw_gaussianMatrix_block_of_hasLaw hΨ Qp hQp)
    (gaussianMatrix_indepFun_block_of_hasLaw hΨ Q Qp hQ hQp hQQp)
    Bᵀ (T := fun x => pinvR x) measurable_pinvR_entry
  have h1 : ∀ ω, frobSq (pinvL ((Ψ ω)ᵀ * Q) * ((Ψ ω)ᵀ * Qp) * B) =
      frobSq (Bᵀ * (Qpᵀ * Ψ ω) * pinvR (Qᵀ * Ψ ω)) := by
    intro ω
    rw [← frobSq_transpose]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, pinvL_transpose,
      Matrix.mul_assoc]
  have h2 : ∀ ω, frobSq (pinvL ((Ψ ω)ᵀ * Q)) =
      frobSq (pinvR (Qᵀ * Ψ ω)) := by
    intro ω
    rw [← frobSq_transpose, pinvL_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp_rw [h1, h2, frobSq_transpose] at *
  rw [mul_comm]
  exact key

/-! ### Change of variables through the block law -/

omit [IsProbabilityMeasure μ] in
/-- **Inverse moment of a Gaussian block.** If `Ω` is an `n × t` standard Gaussian matrix and
`V₁` has orthonormal columns, then `E ‖(V₁ᵀΩ)†‖_F² = E_{G} ‖G†‖_F²` for `G` a `k × t` standard Gaussian matrix.
Combined with `integral_frobSq_mul_block_mul_pinvR_block` and the inverse moment of a Gaussian
matrix this closes hypothesis `hinv` of `NLAlib.rsvd_truncated_main`. HMT 2011 §10.2 (block law).
Atlas `gaussian-conditioning`.
atlas: gaussian-conditioning -/
theorem integral_frobSq_pinvR_block {n k t : ℕ} {Ω : Ωs → Matrix (Fin n) (Fin t) ℝ}
    (hΩ : HasLaw Ω (gaussianMatrix (Fin n) (Fin t)) μ) (V₁ : Matrix (Fin n) (Fin k) ℝ)
    (hV₁ : HasOrthonormalCols V₁) :
    ∫ ω, frobSq (pinvR (V₁ᵀ * Ω ω)) ∂μ =
      ∫ G, frobSq (pinvR G) ∂gaussianMatrix (Fin k) (Fin t) := by
  rw [← (hasLaw_gaussianMatrix_block_of_hasLaw hΩ V₁ hV₁).map_eq]
  exact (integral_map (φ := fun ω => V₁ᵀ * Ω ω)
    ((measurable_block V₁).comp_aemeasurable hΩ.aemeasurable)
    (measurable_frobSq_of_entries measurable_pinvR_entry).aestronglyMeasurable).symm

end NLAlib
