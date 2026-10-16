import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Differentiation and continuity along affine random paths

Bounded continuously differentiable tests admit differentiation under the
actual expectation on every neighborhood where the two scalar velocity
coefficients are uniformly bounded. A bounded test also gives endpoint
continuity by dominated convergence.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace NLAlib
variable {Ω E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A globally bounded continuous test has a continuous expectation along
an affine path with continuous scalar coefficients and measurable random data. -/
theorem continuous_integral_affine_path
    (X Z : Ω → E) (hX : AEStronglyMeasurable X μ) (hZ : AEStronglyMeasurable Z μ)
    (c : E) (a b : ℝ → ℝ) (ha : Continuous a) (hb : Continuous b)
    (Φ : E → F) (hΦ : Continuous Φ) (C : ℝ) (hbound : ∀ x, ‖Φ x‖ ≤ C) :
    Continuous (fun t : ℝ => ∫ ω, Φ (c + a t • X ω + b t • Z ω) ∂μ) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro t
    exact hΦ.comp_aestronglyMeasurable
      ((aestronglyMeasurable_const.add (hX.const_smul (a t))).add (hZ.const_smul (b t)))
  · intro t
    exact ae_of_all _ fun ω => hbound _
  · exact integrable_const C
  · exact ae_of_all _ fun ω => hΦ.comp ((continuous_const.add
      (ha.smul continuous_const)).add (hb.smul continuous_const))

/-- Differentiate the actual expected value of a bounded C¹ test along an
affine random path. Bounds on its Fréchet derivative and the two scalar
velocities yield an explicit integrable dominating function. -/
theorem hasDerivAt_integral_affine_path
    (X Z : Ω → E) (hX : Integrable X μ) (hZ : Integrable Z μ)
    (c : E) (a b a' b' : ℝ → ℝ) {t₀ : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t₀)
    (ha : ∀ t ∈ s, HasDerivAt a (a' t) t)
    (hb : ∀ t ∈ s, HasDerivAt b (b' t) t)
    (A B : ℝ) (hab : ∀ t ∈ s, |a' t| ≤ A) (hbb : ∀ t ∈ s, |b' t| ≤ B)
    (Φ : E → F) (DΦ : E → E →L[ℝ] F)
    (hΦ : ∀ x, HasFDerivAt Φ (DΦ x) x) (hDc : Continuous DΦ)
    (C₀ C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hΦb : ∀ x, ‖Φ x‖ ≤ C₀) (hDb : ∀ x, ‖DΦ x‖ ≤ C₁) :
    HasDerivAt (fun t => ∫ ω, Φ (c + a t • X ω + b t • Z ω) ∂μ)
      (∫ ω, DΦ (c + a t₀ • X ω + b t₀ • Z ω)
        (a' t₀ • X ω + b' t₀ • Z ω) ∂μ) t₀ := by
  let Y : ℝ → Ω → E := fun t ω => c + a t • X ω + b t • Z ω
  let V : ℝ → Ω → E := fun t ω => a' t • X ω + b' t • Z ω
  have hY (t : ℝ) : AEStronglyMeasurable (Y t) μ :=
    (aestronglyMeasurable_const.add (hX.aestronglyMeasurable.const_smul (a t))).add
      (hZ.aestronglyMeasurable.const_smul (b t))
  have hV (t : ℝ) : AEStronglyMeasurable (V t) μ :=
    (hX.aestronglyMeasurable.const_smul (a' t)).add
      (hZ.aestronglyMeasurable.const_smul (b' t))
  have hΦc : Continuous Φ := continuous_iff_continuousAt.mpr (fun x => (hΦ x).continuousAt)
  have hFm (t : ℝ) : AEStronglyMeasurable (fun ω => Φ (Y t ω)) μ :=
    hΦc.comp_aestronglyMeasurable (hY t)
  have hFi : Integrable (fun ω => Φ (Y t₀ ω)) μ :=
    (integrable_const C₀).mono' (hFm t₀) (ae_of_all _ fun ω => hΦb _)
  have hDm : AEStronglyMeasurable (fun ω => DΦ (Y t₀ ω) (V t₀ ω)) μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      ((hDc.comp_aestronglyMeasurable (hY t₀)).prodMk (hV t₀))
  have hdom (t : ℝ) (ht : t ∈ s) (ω : Ω) :
      ‖DΦ (Y t ω) (V t ω)‖ ≤ C₁ * (A * ‖X ω‖ + B * ‖Z ω‖) := by
    have hv : ‖V t ω‖ ≤ |a' t| * ‖X ω‖ + |b' t| * ‖Z ω‖ := by
      simpa only [V,norm_smul,Real.norm_eq_abs] using
        norm_add_le (a' t • X ω) (b' t • Z ω)
    calc
      _ ≤ ‖DΦ (Y t ω)‖ * ‖V t ω‖ := (DΦ _).le_opNorm _
      _ ≤ C₁ * (|a' t| * ‖X ω‖ + |b' t| * ‖Z ω‖) :=
        mul_le_mul (hDb _) hv (norm_nonneg _) hC₁
      _ ≤ _ := by gcongr; exact hab t ht; exact hbb t ht
  have hdiff (ω : Ω) (t : ℝ) (ht : t ∈ s) :
      HasDerivAt (fun t => Φ (Y t ω)) (DΦ (Y t ω) (V t ω)) t := by
    have hy : HasDerivAt (fun t => Y t ω) (V t ω) t := by
      simpa only [Y,V,zero_add,Pi.add_def] using
        ((hasDerivAt_const t c).add ((ha t ht).smul_const (X ω))).add
          ((hb t ht).smul_const (Z ω))
    exact (hΦ _).comp_hasDerivAt t hy
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun t ω => Φ (Y t ω)) (F' := fun t ω => DΦ (Y t ω) (V t ω))
    (bound := fun ω => C₁ * (A * ‖X ω‖ + B * ‖Z ω‖)) hs
    (Eventually.of_forall hFm) hFi hDm
    (ae_of_all _ fun ω t ht => hdom t ht ω)
    (((hX.norm.const_mul A).add (hZ.norm.const_mul B)).const_mul C₁)
    (ae_of_all _ hdiff)).2

/-- Along square-root interpolation, the expected bounded C¹ test has its
actual chain-rule derivative at every interior time. Singular endpoint
velocities cause no issue because domination is local in the open interval. -/
theorem hasDerivAt_integral_sqrt_affine_path
    (X Z : Ω → E) (hX : Integrable X μ) (hZ : Integrable Z μ)
    (c : E) (Φ : E → F) (DΦ : E → E →L[ℝ] F)
    (hΦ : ∀ x, HasFDerivAt Φ (DΦ x) x) (hDc : Continuous DΦ)
    (C₀ C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hΦb : ∀ x, ‖Φ x‖ ≤ C₀) (hDb : ∀ x, ‖DΦ x‖ ≤ C₁)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₀ < 1) :
    HasDerivAt (fun t => ∫ ω, Φ (c + Real.sqrt t • X ω + Real.sqrt (1-t) • Z ω) ∂μ)
      (∫ ω, DΦ (c + Real.sqrt t₀ • X ω + Real.sqrt (1-t₀) • Z ω)
        ((1/(2*Real.sqrt t₀)) • X ω - (1/(2*Real.sqrt (1-t₀))) • Z ω) ∂μ) t₀ := by
  let s : Set ℝ := Set.Ioo (t₀/2) ((1+t₀)/2)
  have hs : s ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have h0 (t : ℝ) (ht : t ∈ s) : 0 < t := by dsimp [s] at ht; linarith [ht.1]
  have h1 (t : ℝ) (ht : t ∈ s) : t < 1 := by dsimp [s] at ht; linarith [ht.2]
  have ha (t : ℝ) (ht : t ∈ s) : HasDerivAt Real.sqrt (1/(2*Real.sqrt t)) t :=
    Real.hasDerivAt_sqrt (h0 t ht).ne'
  have hb (t : ℝ) (ht : t ∈ s) :
      HasDerivAt (fun t : ℝ => Real.sqrt (1-t)) (-(1/(2*Real.sqrt (1-t)))) t := by
    have hh : HasDerivAt (fun t : ℝ => 1-t) (-1) t := by
      simpa only [Pi.sub_def,id_eq,zero_sub] using
        (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    simpa only [neg_div] using hh.sqrt (by linarith [h1 t ht])
  have hab (t : ℝ) (ht : t ∈ s) :
      |1/(2*Real.sqrt t)| ≤ 1/(2*Real.sqrt (t₀/2)) := by
    rw [abs_of_nonneg (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
    exact ht.1.le
  have hbb (t : ℝ) (ht : t ∈ s) :
      |-(1/(2*Real.sqrt (1-t)))| ≤ 1/(2*Real.sqrt ((1-t₀)/2)) := by
    rw [abs_neg,abs_of_nonneg (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
    dsimp [s] at ht
    linarith [ht.2]
  have h := hasDerivAt_integral_affine_path X Z hX hZ c Real.sqrt
    (fun t => Real.sqrt (1-t)) (fun t => 1/(2*Real.sqrt t))
    (fun t => -(1/(2*Real.sqrt (1-t)))) hs ha hb
    (1/(2*Real.sqrt (t₀/2))) (1/(2*Real.sqrt ((1-t₀)/2))) hab hbb
    Φ DΦ hΦ hDc C₀ C₁ hC₁ hΦb hDb
  simpa only [neg_smul,sub_eq_add_neg] using h

end NLAlib
