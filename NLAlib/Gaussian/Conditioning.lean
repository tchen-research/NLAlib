import NLAlib.Gaussian.Basic
import NLAlib.Gaussian.Invariance
import NLAlib.Gaussian.Moments
import NLAlib.Matrix.Norms
import NLAlib.Matrix.Pseudoinverse
import NLAlib.Matrix.Measurable
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Instances.Matrix

/-!
# Conditioning on independent Gaussian blocks

The tower-property engine that turns the Gaussian moment identities of
`NLAlib.Gaussian.Moments` into the expectation hypotheses taken by the randomized SVD and
generalized Nyström error bounds.

* `integral_of_indepFun`, `lintegral_of_indepFun`: Fubini for independent random variables,
  `E g(X, Y) = ∫∫ g(x, y) d(law Y) d(law X)`.
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
Fubini, the block law (`block-law-indep`) and the sandwiched second moment
(`gaussian-frob-second-moment`). The measurability helpers `measurable_frobSq_of_entries` and
`measurable_pinvR_entry` are in `NLAlib.Matrix.Measurable`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]

/-! ### Fubini for independent random variables -/

/-- **Fubini for independent random variables, `ℝ≥0∞` version.** If `X` and `Y` are independent,
`E g(X, Y) = ∫ (∫ g(x, y) d(law Y)(y)) d(law X)(x)`. Only a.e.-measurability of `g` for the
product of the laws is needed.

Standard (e.g. Durrett, *Probability*, Thm 2.1.12 / Kallenberg Lemma 3.11). Atlas
`gaussian-conditioning`. -/
theorem lintegral_of_indepFun {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {X : Ωs → α} {Y : Ωs → β} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXY : IndepFun X Y μ) {g : α → β → ℝ≥0∞}
    (hg : AEMeasurable (Function.uncurry g) ((μ.map X).prod (μ.map Y))) :
    ∫⁻ ω, g (X ω) (Y ω) ∂μ = ∫⁻ x, ∫⁻ y, g x y ∂(μ.map Y) ∂(μ.map X) := by
  have h := (indepFun_iff_map_prod_eq_prod_map_map hX hY).1 hXY
  have hg' : AEMeasurable (Function.uncurry g) (μ.map fun ω => (X ω, Y ω)) := by rwa [h]
  calc ∫⁻ ω, g (X ω) (Y ω) ∂μ
      = ∫⁻ p, Function.uncurry g p ∂(μ.map fun ω => (X ω, Y ω)) :=
        (lintegral_map' hg' (hX.prodMk hY)).symm
    _ = ∫⁻ p, Function.uncurry g p ∂((μ.map X).prod (μ.map Y)) := by rw [h]
    _ = _ := lintegral_prod _ hg

/-- **Fubini for independent random variables, Bochner version.** If `X` and `Y` are
independent and `(x, y) ↦ g x y` is integrable for the product of the laws, then
`E g(X, Y) = ∫ (∫ g(x, y) d(law Y)(y)) d(law X)(x)`.

Standard (e.g. Durrett, *Probability*, Thm 2.1.12). Atlas `gaussian-conditioning`.
atlas: gaussian-conditioning -/
theorem integral_of_indepFun {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {X : Ωs → α} {Y : Ωs → β} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXY : IndepFun X Y μ) {g : α → β → ℝ}
    (hg : Integrable (fun p : α × β => g p.1 p.2) ((μ.map X).prod (μ.map Y))) :
    ∫ ω, g (X ω) (Y ω) ∂μ = ∫ x, ∫ y, g x y ∂(μ.map Y) ∂(μ.map X) := by
  have h := (indepFun_iff_map_prod_eq_prod_map_map hX hY).1 hXY
  have hg' : AEStronglyMeasurable (fun p : α × β => g p.1 p.2)
      (μ.map fun ω => (X ω, Y ω)) := by rw [h]; exact hg.aestronglyMeasurable
  calc ∫ ω, g (X ω) (Y ω) ∂μ
      = ∫ p : α × β, g p.1 p.2 ∂(μ.map fun ω => (X ω, Y ω)) :=
        (integral_map (hX.prodMk hY) hg').symm
    _ = ∫ p : α × β, g p.1 p.2 ∂((μ.map X).prod (μ.map Y)) := by rw [h]
    _ = _ := integral_prod _ hg

/-! ### Gaussian blocks -/

omit [IsProbabilityMeasure μ] in
/-- If `Ω` has law `gaussianMatrix n t` and `V₁ᵀ V₁ = 1`, then `V₁ᵀ Ω` has law
`gaussianMatrix k t`. HMT 2011 §10.2; atlas `gaussian-conditioning` (uses `block-law-indep`). -/
theorem map_block_eq_gaussianMatrix {n k t : ℕ} {Ω : Ωs → Fin n → Fin t → ℝ}
    (hΩ : μ.map Ω = gaussianMatrix n t) (V₁ : Matrix (Fin n) (Fin k) ℝ) (hV₁ : V₁ᵀ * V₁ = 1) :
    μ.map (fun ω => Matrix.of.symm (V₁ᵀ * Matrix.of (Ω ω))) = gaussianMatrix k t := by
  have hΩm := aemeasurable_of_map_eq_gaussianMatrix hΩ
  have := AEMeasurable.map_map_of_aemeasurable (measurable_block (t := t) V₁).aemeasurable hΩm
  refine this.symm.trans ?_
  rw [hΩ, gaussianMatrix_map_block V₁ hV₁]

/-- If `Ω` has law `gaussianMatrix n t`, `V₁`, `V₂` have orthonormal columns and `V₁ᵀ V₂ = 0`,
then `V₁ᵀ Ω` and `V₂ᵀ Ω` are independent. HMT 2011 §10.2; atlas `gaussian-conditioning`
(uses `block-law-indep`). -/
theorem indepFun_block_of_map_eq {n k r t : ℕ} {Ω : Ωs → Fin n → Fin t → ℝ}
    (hΩ : μ.map Ω = gaussianMatrix n t) (V₁ : Matrix (Fin n) (Fin k) ℝ)
    (V₂ : Matrix (Fin n) (Fin r) ℝ) (hV₁ : V₁ᵀ * V₁ = 1) (hV₂ : V₂ᵀ * V₂ = 1)
    (hV₁₂ : V₁ᵀ * V₂ = 0) :
    IndepFun (fun ω => Matrix.of.symm (V₁ᵀ * Matrix.of (Ω ω)))
      (fun ω => Matrix.of.symm (V₂ᵀ * Matrix.of (Ω ω))) μ := by
  have hΩm := aemeasurable_of_map_eq_gaussianMatrix hΩ
  have hind := gaussianMatrix_indepFun_block (t := t) V₁ V₂ hV₁ hV₂ hV₁₂
  have hm₁ := measurable_block (t := t) V₁
  have hm₂ := measurable_block (t := t) V₂
  rw [← hΩ] at hind
  rw [indepFun_iff_map_prod_eq_prod_map_map hm₁.aemeasurable hm₂.aemeasurable] at hind
  show IndepFun ((fun G : Fin n → Fin t → ℝ => Matrix.of.symm (V₁ᵀ * Matrix.of G)) ∘ Ω)
    ((fun G : Fin n → Fin t → ℝ => Matrix.of.symm (V₂ᵀ * Matrix.of G)) ∘ Ω) μ
  rw [indepFun_iff_map_prod_eq_prod_map_map (hm₁.comp_aemeasurable hΩm)
    (hm₂.comp_aemeasurable hΩm)]
  rw [← AEMeasurable.map_map_of_aemeasurable hm₁.aemeasurable hΩm,
    ← AEMeasurable.map_map_of_aemeasurable hm₂.aemeasurable hΩm, ← hind,
    AEMeasurable.map_map_of_aemeasurable (hm₁.prodMk hm₂).aemeasurable hΩm]
  rfl

/-! ### The sandwiched Gaussian second moment, conditioned -/

/-- `G ↦ ‖S G T‖_F²` is integrable under the standard Gaussian matrix law. Atlas
`gaussian-conditioning` (integrability side condition of `gaussian-moments`). -/
theorem integrable_frobSq_mul_gaussianMatrix_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p m : ℕ} (S : Matrix ι (Fin p) ℝ) (T : Matrix (Fin m) κ ℝ) :
    Integrable (fun G : Fin p → Fin m → ℝ => frobSq (S * Matrix.of G * T))
      (gaussianMatrix p m) := by
  classical
  have hsq : Integrable (fun G : Fin p → Fin m → ℝ => frobSq (Matrix.of G))
      (gaussianMatrix p m) := by
    simp_rw [frobSq_eq_sum_sq]
    refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
    exact (memLp_gaussianMatrix_entry a b 2 (by simp)).integrable_sq
  have hm : Measurable fun G : Fin p → Fin m → ℝ => frobSq (S * Matrix.of G * T) :=
    measurable_frobSq_of_entries fun i j => by
      simp only [Matrix.mul_apply, Matrix.of_apply]; fun_prop
  refine (hsq.const_mul (frobSq S * frobSq T)).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun G => ?_)
  rw [Real.norm_of_nonneg (frobSq_nonneg _)]
  calc frobSq (S * Matrix.of G * T) ≤ frobSq (S * Matrix.of G) * frobSq T := frobSq_mul_le _ _
    _ ≤ frobSq S * frobSq (Matrix.of G) * frobSq T :=
        mul_le_mul_of_nonneg_right (frobSq_mul_le _ _) (frobSq_nonneg _)
    _ = frobSq S * frobSq T * frobSq (Matrix.of G) := by ring

/-- `ℝ≥0∞` form of `integral_frobSq_mul_gaussian_mul_of_indepFun`; no integrability needed.
HMT 2011 Prop 10.1 combined with the tower property (proof of Thm 10.5). Atlas
`gaussian-conditioning`. -/
theorem lintegral_frobSq_mul_gaussian_mul_of_indepFun {α ι κ : Type*} [MeasurableSpace α]
    [Fintype ι] [Fintype κ] {p m : ℕ} {X : Ωs → α} {Y : Ωs → Fin p → Fin m → ℝ}
    (hX : AEMeasurable X μ) (hY : μ.map Y = gaussianMatrix p m) (hXY : IndepFun X Y μ)
    (S : Matrix ι (Fin p) ℝ) {T : α → Matrix (Fin m) κ ℝ}
    (hT : ∀ i j, Measurable fun x => T x i j) :
    ∫⁻ ω, ENNReal.ofReal (frobSq (S * Matrix.of (Y ω) * T (X ω))) ∂μ =
      ∫⁻ ω, ENNReal.ofReal (frobSq S * frobSq (T (X ω))) ∂μ := by
  have hYm : AEMeasurable Y μ := aemeasurable_of_map_eq_gaussianMatrix hY
  have hFm : Measurable (Function.uncurry fun (x : α) (y : Fin p → Fin m → ℝ) =>
      ENNReal.ofReal (frobSq (S * Matrix.of y * T x))) := by
    refine ENNReal.measurable_ofReal.comp (measurable_frobSq_of_entries fun i j => ?_)
    have hT' : ∀ l j, Measurable fun q : α × (Fin p → Fin m → ℝ) => T q.1 l j :=
      fun l j => (hT l j).comp measurable_fst
    simp only [Matrix.mul_apply, Matrix.of_apply]
    refine Finset.measurable_sum _ fun l _ => Measurable.mul ?_ (hT' l j)
    fun_prop
  have hGm : Measurable fun x : α => ENNReal.ofReal (frobSq S * frobSq (T x)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_frobSq_of_entries hT))
  rw [lintegral_of_indepFun hX hYm hXY hFm.aemeasurable, hY, ← lintegral_map' hGm.aemeasurable hX]
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
Measurability of `T` is stated entrywise (`Matrix` carries no `MeasurableSpace` instance).
atlas: gaussian-conditioning -/
theorem integral_frobSq_mul_gaussian_mul_of_indepFun {α ι κ : Type*} [MeasurableSpace α]
    [Fintype ι] [Fintype κ] {p m : ℕ} {X : Ωs → α} {Y : Ωs → Fin p → Fin m → ℝ}
    (hX : AEMeasurable X μ) (hY : μ.map Y = gaussianMatrix p m) (hXY : IndepFun X Y μ)
    (S : Matrix ι (Fin p) ℝ) {T : α → Matrix (Fin m) κ ℝ}
    (hT : ∀ i j, Measurable fun x => T x i j) :
    ∫ ω, frobSq (S * Matrix.of (Y ω) * T (X ω)) ∂μ = frobSq S * ∫ ω, frobSq (T (X ω)) ∂μ := by
  have hYm : AEMeasurable Y μ := aemeasurable_of_map_eq_gaussianMatrix hY
  have hL : AEStronglyMeasurable (fun ω => frobSq (S * Matrix.of (Y ω) * T (X ω))) μ := by
    have hF : Measurable fun q : α × (Fin p → Fin m → ℝ) => frobSq (S * Matrix.of q.2 * T q.1) :=
      measurable_frobSq_of_entries fun i j => by
        have hT' : ∀ l j, Measurable fun q : α × (Fin p → Fin m → ℝ) => T q.1 l j :=
          fun l j => (hT l j).comp measurable_fst
        simp only [Matrix.mul_apply, Matrix.of_apply]
        refine Finset.measurable_sum _ fun l _ => Measurable.mul ?_ (hT' l j)
        fun_prop
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
    [Fintype ι] [Fintype κ] {p m : ℕ} {X : Ωs → α} {Y : Ωs → Fin p → Fin m → ℝ}
    (hX : AEMeasurable X μ) (hY : μ.map Y = gaussianMatrix p m) (hXY : IndepFun X Y μ)
    (S : Matrix ι (Fin p) ℝ) {T : α → Matrix (Fin m) κ ℝ}
    (hT : ∀ i j, Measurable fun x => T x i j)
    (hTi : Integrable (fun ω => frobSq (T (X ω))) μ) :
    Integrable (fun ω => frobSq (S * Matrix.of (Y ω) * T (X ω))) μ := by
  have hYm : AEMeasurable Y μ := aemeasurable_of_map_eq_gaussianMatrix hY
  have hF : Measurable fun q : α × (Fin p → Fin m → ℝ) => frobSq (S * Matrix.of q.2 * T q.1) :=
    measurable_frobSq_of_entries fun i j => by
      have hT' : ∀ l j, Measurable fun q : α × (Fin p → Fin m → ℝ) => T q.1 l j :=
        fun l j => (hT l j).comp measurable_fst
      simp only [Matrix.mul_apply, Matrix.of_apply]
      refine Finset.measurable_sum _ fun l _ => Measurable.mul ?_ (hT' l j)
      fun_prop
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
`integral_frobSq_mul_gaussian_mul_of_indepFun`). `Ω` is array-valued; for a `Matrix`-valued
`Ω'` take `Ω := fun ω => Matrix.of.symm (Ω' ω)` (definitionally `Matrix.of (Ω ω) = Ω' ω`).
Atlas `gaussian-conditioning`.
atlas: gaussian-conditioning -/
theorem integral_frobSq_mul_block_mul_pinvR_block {n k r r' t : ℕ}
    {Ω : Ωs → Fin n → Fin t → ℝ}
    (hΩ : μ.map Ω = gaussianMatrix n t) (V₁ : Matrix (Fin n) (Fin k) ℝ)
    (V₂ : Matrix (Fin n) (Fin r') ℝ) (hV₁ : V₁ᵀ * V₁ = 1) (hV₂ : V₂ᵀ * V₂ = 1)
    (hV₁₂ : V₁ᵀ * V₂ = 0) (S₂ : Matrix (Fin r) (Fin r') ℝ) :
    ∫ ω, frobSq (S₂ * (V₂ᵀ * Matrix.of (Ω ω)) * pinvR (V₁ᵀ * Matrix.of (Ω ω))) ∂μ =
      frobSq S₂ * ∫ ω, frobSq (pinvR (V₁ᵀ * Matrix.of (Ω ω))) ∂μ :=
  integral_frobSq_mul_gaussian_mul_of_indepFun
    (X := fun ω => Matrix.of.symm (V₁ᵀ * Matrix.of (Ω ω)))
    (Y := fun ω => Matrix.of.symm (V₂ᵀ * Matrix.of (Ω ω)))
    ((measurable_block V₁).comp_aemeasurable (aemeasurable_of_map_eq_gaussianMatrix hΩ))
    (map_block_eq_gaussianMatrix hΩ V₂ hV₂) (indepFun_block_of_map_eq hΩ V₁ V₂ hV₁ hV₂ hV₁₂)
    S₂ (T := fun x => pinvR (Matrix.of x)) measurable_pinvR_entry

/-- Integrability companion of `integral_frobSq_mul_block_mul_pinvR_block` (hypothesis `hZi`
of `NLAlib.rsvd_truncated_main`, given integrability of `‖(V₁ᵀΩ)†‖_F²`). HMT 2011 proof of
Thm 10.5. Atlas `gaussian-conditioning`. -/
theorem integrable_frobSq_mul_block_mul_pinvR_block {n k r r' t : ℕ}
    {Ω : Ωs → Fin n → Fin t → ℝ}
    (hΩ : μ.map Ω = gaussianMatrix n t) (V₁ : Matrix (Fin n) (Fin k) ℝ)
    (V₂ : Matrix (Fin n) (Fin r') ℝ) (hV₁ : V₁ᵀ * V₁ = 1) (hV₂ : V₂ᵀ * V₂ = 1)
    (hV₁₂ : V₁ᵀ * V₂ = 0) (S₂ : Matrix (Fin r) (Fin r') ℝ)
    (hi : Integrable (fun ω => frobSq (pinvR (V₁ᵀ * Matrix.of (Ω ω)))) μ) :
    Integrable
      (fun ω => frobSq (S₂ * (V₂ᵀ * Matrix.of (Ω ω)) * pinvR (V₁ᵀ * Matrix.of (Ω ω)))) μ :=
  integrable_frobSq_mul_gaussian_mul_of_indepFun
    (X := fun ω => Matrix.of.symm (V₁ᵀ * Matrix.of (Ω ω)))
    (Y := fun ω => Matrix.of.symm (V₂ᵀ * Matrix.of (Ω ω)))
    ((measurable_block V₁).comp_aemeasurable (aemeasurable_of_map_eq_gaussianMatrix hΩ))
    (map_block_eq_gaussianMatrix hΩ V₂ hV₂) (indepFun_block_of_map_eq hΩ V₁ V₂ hV₁ hV₂ hV₁₂)
    S₂ (T := fun x => pinvR (Matrix.of x)) measurable_pinvR_entry hi

/-- **Completion-step inverse-moment factorisation** (transposed form of
`integral_frobSq_mul_block_mul_pinvR_block`). If `Ψ` is an `m × s` standard Gaussian matrix and
`Q`, `Qp` have orthonormal, mutually orthogonal columns, then for every fixed `B`
`E ‖(ΨᵀQ)† (ΨᵀQp) B‖_F² = E ‖(ΨᵀQ)†‖_F² · ‖B‖_F²`.

Generalized Nyström / two-sided sketch analysis (hypothesis `hG₂` of `completion_reduction`);
the conditioning argument of HMT 2011 Thm 10.5 applied to the transposed sketch. Here
`(ΨᵀQ)† = pinvL (ΨᵀQ)`. Atlas `gaussian-conditioning`.
atlas: gaussian-conditioning -/
theorem integral_frobSq_pinvL_block_mul_block_mul {m s q rp : ℕ} {ι : Type*} [Fintype ι]
    {Ψ : Ωs → Fin m → Fin s → ℝ} (hΨ : μ.map Ψ = gaussianMatrix m s)
    (Q : Matrix (Fin m) (Fin q) ℝ) (Qp : Matrix (Fin m) (Fin rp) ℝ) (hQ : Qᵀ * Q = 1)
    (hQp : Qpᵀ * Qp = 1) (hQQp : Qᵀ * Qp = 0) (B : Matrix (Fin rp) ι ℝ) :
    ∫ ω, frobSq (pinvL ((Matrix.of (Ψ ω))ᵀ * Q) * ((Matrix.of (Ψ ω))ᵀ * Qp) * B) ∂μ =
      (∫ ω, frobSq (pinvL ((Matrix.of (Ψ ω))ᵀ * Q)) ∂μ) * frobSq B := by
  have key := integral_frobSq_mul_gaussian_mul_of_indepFun
    (X := fun ω => Matrix.of.symm (Qᵀ * Matrix.of (Ψ ω)))
    (Y := fun ω => Matrix.of.symm (Qpᵀ * Matrix.of (Ψ ω)))
    ((measurable_block Q).comp_aemeasurable (aemeasurable_of_map_eq_gaussianMatrix hΨ))
    (map_block_eq_gaussianMatrix hΨ Qp hQp) (indepFun_block_of_map_eq hΨ Q Qp hQ hQp hQQp)
    Bᵀ (T := fun x => pinvR (Matrix.of x)) measurable_pinvR_entry
  have h1 : ∀ ω, frobSq (pinvL ((Matrix.of (Ψ ω))ᵀ * Q) * ((Matrix.of (Ψ ω))ᵀ * Qp) * B) =
      frobSq (Bᵀ * (Qpᵀ * Matrix.of (Ψ ω)) * pinvR (Qᵀ * Matrix.of (Ψ ω))) := by
    intro ω
    rw [← frobSq_transpose]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, pinvL_transpose,
      Matrix.mul_assoc]
  have h2 : ∀ ω, frobSq (pinvL ((Matrix.of (Ψ ω))ᵀ * Q)) =
      frobSq (pinvR (Qᵀ * Matrix.of (Ψ ω))) := by
    intro ω
    rw [← frobSq_transpose, pinvL_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp_rw [h1, h2, frobSq_transpose] at *
  rw [mul_comm]
  exact key

/-! ### Change of variables through the block law -/

omit [IsProbabilityMeasure μ] in
/-- **Inverse moment of a Gaussian block.** If `Ω` is an `n × t` standard Gaussian matrix and
`V₁ᵀ V₁ = 1`, then `E ‖(V₁ᵀΩ)†‖_F² = E_{G} ‖G†‖_F²` for `G` a `k × t` standard Gaussian matrix.
Combined with `integral_frobSq_mul_block_mul_pinvR_block` and the inverse moment of a Gaussian
matrix this closes hypothesis `hinv` of `NLAlib.rsvd_truncated_main`. HMT 2011 §10.2 (block law).
Atlas `gaussian-conditioning`.
atlas: gaussian-conditioning -/
theorem integral_frobSq_pinvR_block {n k t : ℕ} {Ω : Ωs → Fin n → Fin t → ℝ}
    (hΩ : μ.map Ω = gaussianMatrix n t) (V₁ : Matrix (Fin n) (Fin k) ℝ)
    (hV₁ : V₁ᵀ * V₁ = 1) :
    ∫ ω, frobSq (pinvR (V₁ᵀ * Matrix.of (Ω ω))) ∂μ =
      ∫ G, frobSq (pinvR (Matrix.of G)) ∂gaussianMatrix k t := by
  rw [← map_block_eq_gaussianMatrix hΩ V₁ hV₁]
  exact (integral_map (φ := fun ω => Matrix.of.symm (V₁ᵀ * Matrix.of (Ω ω)))
    ((measurable_block V₁).comp_aemeasurable (aemeasurable_of_map_eq_gaussianMatrix hΩ))
    (measurable_frobSq_of_entries measurable_pinvR_entry).aestronglyMeasurable).symm

end NLAlib
