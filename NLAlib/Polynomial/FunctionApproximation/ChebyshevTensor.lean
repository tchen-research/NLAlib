import NLAlib.Polynomial.FunctionApproximation.ChebyshevEnergy
import NLAlib.ForMathlib.Analysis.ChebyshevMeasure
import NLAlib.ForMathlib.MeasureTheory.FiniteBessel
import NLAlib.ForMathlib.MeasureTheory.PiSliceIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Normalized tensor Chebyshev coefficients

The coefficients are actual integrals against the finite product of the
unnormalized Chebyshev measures. Coordinatewise cosine supplies the equivalent
ordinary product-integral formula and mixed sine/cosine orthogonality.
Source: Musco--Musco--Rosenblatt--Singh, arXiv:2408.12385v3, Appendix A.1.
Atlas: `chebyshev-lipschitz-coefficient-energy` (tensor part).
-/

noncomputable section

open Real MeasureTheory Set Finset Polynomial.Chebyshev
open scoped Topology

namespace NLAlib

/-- Normalization of the first-kind Chebyshev basis for the measure of mass `π`. -/
def normalizedChebyshevWeight (k : ℕ) : ℝ := sqrt ((if k = 0 then 1 else 2) / π)

/-- The normalized first-kind Chebyshev polynomial, evaluated on the real line. -/
def normalizedChebyshev (k : ℕ) (x : ℝ) : ℝ :=
  normalizedChebyshevWeight k * (T ℝ (k : ℤ)).eval x

/-- The actual normalized tensor coefficient for the product Chebyshev measure. -/
def tensorChebyshevCoeff {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (α : ι → ℕ) : ℝ :=
  ∫ x : ι → ℝ, f (WithLp.toLp 2 x) * ∏ i, normalizedChebyshev (α i) (x i)
    ∂Measure.pi (fun _ => measureT)

/-- The Euclidean cube on which tensor Chebyshev approximation is defined. -/
def chebyshevCube (ι : Type*) [Fintype ι] : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, x i ∈ Icc (-1 : ℝ) 1}

/-- The product Chebyshev measure is supported on the actual approximation cube. -/
theorem ae_mem_chebyshevCube {ι : Type*} [Fintype ι] :
    ∀ᵐ x : ι → ℝ ∂Measure.pi (fun _ => measureT), WithLp.toLp 2 x ∈ chebyshevCube ι := by
  have h1 : ∀ᵐ x ∂measureT, x ∈ Icc (-1 : ℝ) 1 := by
    have h : ∀ᵐ x ∂measureT, x ∈ Ioc (-1 : ℝ) 1 := by
      unfold measureT
      exact ae_restrict_mem measurableSet_Ioc
    exact h.mono fun x hx => ⟨hx.1.le, hx.2⟩
  exact ae_all_iff.mpr (fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => measureT)).eventually h1)

/-- Tensor coefficients depend only on the values of the function on the cube. -/
theorem tensorChebyshevCoeff_congr {ι : Type*} [Fintype ι]
    {f g : EuclideanSpace ℝ ι → ℝ} (hfg : EqOn f g (chebyshevCube ι)) (α : ι → ℕ) :
    tensorChebyshevCoeff f α = tensorChebyshevCoeff g α := by
  apply integral_congr_ae
  filter_upwards [ae_mem_chebyshevCube (ι := ι)] with x hx
  rw [hfg hx]

/-- Lebesgue angle measure used by the Chebyshev change of variables. -/
def chebyshevAngleMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) π)

instance isFiniteMeasure_chebyshevAngleMeasure : IsFiniteMeasure chebyshevAngleMeasure :=
  inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) π)))

/-- The cosine expression for a normalized Chebyshev polynomial. -/
@[simp] theorem normalizedChebyshev_cos (k : ℕ) (θ : ℝ) :
    normalizedChebyshev k (cos θ) = normalizedChebyshevWeight k * cos ((k : ℝ) * θ) := by
  simp [normalizedChebyshev, T_real_cos]

/-- The square of the Chebyshev normalization includes the zero-frequency case. -/
theorem normalizedChebyshevWeight_sq (k : ℕ) :
    normalizedChebyshevWeight k ^ 2 = (if k = 0 then 1 else 2) / π := by
  rw [normalizedChebyshevWeight, sq_sqrt]
  split_ifs <;> positivity

/-- The constant normalized polynomial has the prescribed value `1 / √π`. -/
@[simp] theorem normalizedChebyshev_zero (x : ℝ) :
    normalizedChebyshev 0 x = 1 / sqrt π := by
  simp [normalizedChebyshev, normalizedChebyshevWeight]

/-- Every continuous function on a finite angle product is integrable there. -/
theorem integrable_pi_chebyshevAngleMeasure_of_continuous
    {ι : Type*} [Fintype ι] {F : (ι → ℝ) → ℝ} (hF : Continuous F) :
    Integrable F (Measure.pi (fun _ => chebyshevAngleMeasure)) := by
  have hc : IsCompact (Set.univ.pi (fun _ : ι => Icc (0 : ℝ) π)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hi := hF.continuousOn.integrableOn_compact (μ := Measure.pi (fun _ : ι => volume)) hc
  have hs : Set.univ.pi (fun _ : ι => Ioc (0 : ℝ) π) ⊆
      Set.univ.pi (fun _ : ι => Icc (0 : ℝ) π) := by
    intro x hx i hi
    exact ⟨(hx i hi).1.le, (hx i hi).2⟩
  have h := hi.mono_set hs
  simpa only [IntegrableOn, Measure.restrict_pi_pi, chebyshevAngleMeasure] using h

/-- The normalized cosine family is orthonormal for ordinary angle integration. -/
theorem integral_normalizedChebyshev_cos_mul (j k : ℕ) :
    (∫ θ, normalizedChebyshev j (cos θ) * normalizedChebyshev k (cos θ)
      ∂chebyshevAngleMeasure) = if j = k then 1 else 0 := by
  have he := integral_measureT_eq_integral_cos
    (f := fun x => normalizedChebyshev j x * normalizedChebyshev k x)
  rw [intervalIntegral.integral_of_le pi_pos.le] at he
  change (∫ θ in Ioc (0 : ℝ) π,
    normalizedChebyshev j (cos θ) * normalizedChebyshev k (cos θ)) = _
  rw [← he]
  have hfactor (x : ℝ) : normalizedChebyshev j x * normalizedChebyshev k x =
      (normalizedChebyshevWeight j * normalizedChebyshevWeight k) *
        ((T ℝ (j : ℤ)).eval x * (T ℝ (k : ℤ)).eval x) := by
    dsimp [normalizedChebyshev]
    ring
  simp_rw [hfactor]
  rw [integral_const_mul]
  by_cases hjk : j = k
  · subst k
    rw [if_pos rfl, ← sq]
    by_cases hj : j = 0
    · subst j
      norm_num only [Nat.cast_zero]
      rw [integral_eval_T_real_mul_self_measureT_zero, normalizedChebyshevWeight_sq]
      simp [pi_ne_zero]
    · rw [integral_T_real_mul_self_measureT_of_ne_zero hj, normalizedChebyshevWeight_sq,
        if_neg hj]
      field_simp
  · rw [integral_eval_T_real_mul_eval_T_real_measureT_of_ne hjk, if_neg hjk, mul_zero]

/-- Positive normalized sine frequencies are orthonormal on the angle interval. -/
theorem integral_normalized_sin_mul {j k : ℕ} (hj : 0 < j) (hk : 0 < k) :
    (∫ θ, (sqrt (2 / π) * sin ((j : ℝ) * θ)) *
        (sqrt (2 / π) * sin ((k : ℝ) * θ)) ∂chebyshevAngleMeasure) =
      if j = k then 1 else 0 := by
  have hfactor (θ : ℝ) : (sqrt (2 / π) * sin ((j : ℝ) * θ)) *
      (sqrt (2 / π) * sin ((k : ℝ) * θ)) =
      (sqrt (2 / π)) ^ 2 * (sin ((j : ℝ) * θ) * sin ((k : ℝ) * θ)) := by ring
  simp_rw [hfactor]
  rw [integral_const_mul, Real.sq_sqrt (by positivity)]
  have he := integral_sin_nat_mul_mul_sin_nat_mul hj hk
  rw [intervalIntegral.integral_of_le pi_pos.le] at he
  change 2 / π * (∫ θ in Ioc (0 : ℝ) π,
    sin ((j : ℝ) * θ) * sin ((k : ℝ) * θ)) = _
  rw [he]
  split_ifs
  · field_simp
  · simp

/-- The tensor coefficient equals its ordinary product cosine integral. -/
theorem tensorChebyshevCoeff_eq_cosine_integral
    {ι : Type*} [Fintype ι] {f : EuclideanSpace ℝ ι → ℝ} (hf : Continuous f) (α : ι → ℕ) :
    tensorChebyshevCoeff f α =
      ∫ θ : ι → ℝ, f (WithLp.toLp 2 (fun i => cos (θ i))) *
        ∏ i, normalizedChebyshev (α i) (cos (θ i))
        ∂Measure.pi (fun _ => chebyshevAngleMeasure) := by
  have hc : Continuous (fun x : ι → ℝ => f (WithLp.toLp 2 x) *
      ∏ i, normalizedChebyshev (α i) (x i)) := by
    apply Continuous.mul (hf.comp (PiLp.continuous_toLp 2 _))
    unfold normalizedChebyshev
    fun_prop
  have h := integral_map (μ := Measure.pi (fun _ : ι => volume.restrict (Ioc (0 : ℝ) π)))
    measurePreserving_pi_cos_chebyshev.measurable.aemeasurable
    hc.aestronglyMeasurable
  rw [measurePreserving_pi_cos_chebyshev.map_eq] at h
  exact h

/-- The mixed tensor trigonometric family used for a chosen coordinate derivative. -/
def tensorChebyshevMixedBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (α : ι → ℕ) (θ : ι → ℝ) : ℝ :=
  ∏ j, if j = i then sqrt (2 / π) * sin ((α j : ℝ) * θ j)
    else normalizedChebyshev (α j) (cos (θ j))

/-- Every mixed tensor basis function is continuous. -/
theorem continuous_tensorChebyshevMixedBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (α : ι → ℕ) : Continuous (tensorChebyshevMixedBasis i α) := by
  unfold tensorChebyshevMixedBasis
  apply continuous_finsetProd
  intro j _
  split_ifs
  · fun_prop
  · unfold normalizedChebyshev
    fun_prop

/-- The mixed tensor family is orthonormal when its sine frequencies are positive. -/
theorem integral_tensorChebyshevMixedBasis_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (α β : ι → ℕ)
    (hα : 0 < α i) (hβ : 0 < β i) :
    (∫ θ, tensorChebyshevMixedBasis i α θ * tensorChebyshevMixedBasis i β θ
      ∂Measure.pi (fun _ => chebyshevAngleMeasure)) = if α = β then 1 else 0 := by
  apply integral_prod_mul_prod_eq_ite _
    (fun (j : ι) (k : ℕ) (t : ℝ) => if j = i then sqrt (2 / π) * sin ((k : ℝ) * t)
      else normalizedChebyshev k (cos t)) α β
  intro j
  by_cases hj : j = i
  · subst j
    simpa using integral_normalized_sin_mul hα hβ
  · simpa only [if_neg hj] using integral_normalizedChebyshev_cos_mul (α j) (β j)

/-- Insertion of one real coordinate into a fixed Euclidean vector is an isometry. -/
theorem isometry_toLp_insertNth {d : ℕ} (i : Fin (d + 1)) (y : Fin d → ℝ) :
    Isometry (fun t : ℝ => (WithLp.toLp 2 (i.insertNth t y) : EuclideanSpace ℝ (Fin (d + 1)))) := by
  apply isometry_iff_dist_eq.mpr
  intro x z
  rw [dist_eq_norm, dist_eq_norm]
  have he : (WithLp.toLp 2 (i.insertNth x y) : EuclideanSpace ℝ (Fin (d + 1))) -
      WithLp.toLp 2 (i.insertNth z y) = PiLp.single 2 i (x - z) := by
    apply (WithLp.equiv 2 _).injective
    funext j
    apply (i.forall_iff_succAbove).mpr ?_ j
    constructor
    · simp
    · intro j
      simp [Fin.succAbove_ne]
  rw [he, PiLp.norm_single]

/-- A coordinate slice of a Euclidean Lipschitz function retains the same constant. -/
theorem lipschitzWith_euclidean_insertNth {d : ℕ} {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    {L : NNReal} (hf : LipschitzWith L f) (i : Fin (d + 1)) (y : Fin d → ℝ) :
    LipschitzWith L (fun t : ℝ => f (WithLp.toLp 2 (i.insertNth t y))) := by
  simpa only [mul_one, Function.comp_def] using hf.comp (isometry_toLp_insertNth i y).lipschitz

/-- Negative derivative of the cosine pullback along one coordinate. -/
def tensorChebyshevCosinePartial {d : ℕ}
    (f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) (i : Fin (d + 1)) (θ : Fin (d + 1) → ℝ) : ℝ :=
  -deriv (fun t : ℝ =>
    f (WithLp.toLp 2 (i.insertNth (cos t) (fun j => cos (θ (i.succAbove j)))))) (θ i)

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate cosine derivative is jointly measurable, without requiring
differentiability of the original Lipschitz function. -/
theorem measurable_tensorChebyshevCosinePartial {d : ℕ}
    {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} (hf : Continuous f) (i : Fin (d + 1)) :
    Measurable (tensorChebyshevCosinePartial f i) := by
  let F (y : Fin d → ℝ) (t : ℝ) :=
    f (WithLp.toLp 2 (i.insertNth (cos t) (fun j => cos (y j))))
  have hc : Continuous F.uncurry := by
    apply hf.comp
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro j
    by_cases hj : j = i
    · subst j
      simp only [Fin.insertNth_apply_same]
      fun_prop
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      simp only [Fin.insertNth_apply_succAbove]
      fun_prop
  have hm : Measurable (fun p : (Fin d → ℝ) × ℝ => -deriv (F p.1) p.2) :=
    (measurable_deriv_with_param (𝕜 := ℝ) (f := F) hc).neg
  change Measurable (fun θ : Fin (d + 1) → ℝ =>
    -deriv (F (fun j => θ (i.succAbove j))) (θ i))
  have hcoords : Measurable (fun θ : Fin (d + 1) → ℝ =>
      fun j : Fin d => θ (i.succAbove j)) :=
    measurable_pi_iff.mpr (fun j => measurable_pi_apply (i.succAbove j))
  have hh := hm.comp (hcoords.prodMk (measurable_pi_apply i))
  exact hh

/-- The coordinate cosine derivative has the sharp pointwise speed bound. -/
theorem abs_tensorChebyshevCosinePartial_le {d : ℕ}
    {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (i : Fin (d + 1)) (θ : Fin (d + 1) → ℝ) :
    |tensorChebyshevCosinePartial f i θ| ≤ L * |sin (θ i)| := by
  simpa only [tensorChebyshevCosinePartial, abs_neg, Function.comp_def] using
    abs_deriv_comp_cos_le_of_lipschitzOnWith
      (lipschitzWith_euclidean_insertNth hf i (fun j => cos (θ (i.succAbove j)))).lipschitzOnWith
      (θ i)

/-- The coordinate cosine derivative is globally bounded by the Lipschitz constant. -/
theorem abs_tensorChebyshevCosinePartial_le_const {d : ℕ}
    {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (i : Fin (d + 1)) (θ : Fin (d + 1) → ℝ) :
    |tensorChebyshevCosinePartial f i θ| ≤ L := by
  exact (abs_tensorChebyshevCosinePartial_le hf i θ).trans
    (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (abs_sin_le_one (θ i)) L.coe_nonneg)

/-- The square of a coordinate cosine derivative is integrable. -/
theorem integrable_tensorChebyshevCosinePartial_sq {d : ℕ}
    {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (i : Fin (d + 1)) :
    Integrable (fun θ => tensorChebyshevCosinePartial f i θ ^ 2)
      (Measure.pi (fun _ => chebyshevAngleMeasure)) := by
  apply (integrable_const ((L : ℝ) ^ 2)).mono'
    ((measurable_tensorChebyshevCosinePartial hf.continuous i).pow_const 2).aestronglyMeasurable
  filter_upwards [] with θ
  have h := mul_self_le_mul_self (abs_nonneg _) (abs_tensorChebyshevCosinePartial_le_const hf i θ)
  simpa only [Real.norm_eq_abs, abs_sq, ← sq, sq_abs] using h

/-- Products needed for finite mixed Bessel coefficients are integrable. -/
theorem integrable_tensorChebyshevCosinePartial_mul_mixed {d : ℕ}
    {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (i : Fin (d + 1)) (α : Fin (d + 1) → ℕ) :
    Integrable (fun θ => tensorChebyshevCosinePartial f i θ * tensorChebyshevMixedBasis i α θ)
      (Measure.pi (fun _ => chebyshevAngleMeasure)) := by
  have hm := integrable_pi_chebyshevAngleMeasure_of_continuous
    (continuous_tensorChebyshevMixedBasis i α).abs
  apply (hm.const_mul (L : ℝ)).mono'
    (((measurable_tensorChebyshevCosinePartial hf.continuous i).mul
      (continuous_tensorChebyshevMixedBasis i α).measurable).aestronglyMeasurable)
  filter_upwards [] with θ
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_tensorChebyshevCosinePartial_le_const hf i θ) (abs_nonneg _)

/-- A coordinate sine square has mass `π^(d+1)/2` under the angle product measure. -/
theorem integral_sin_sq_pi_chebyshevAngleMeasure {d : ℕ} (i : Fin (d + 1)) :
    (∫ θ : Fin (d + 1) → ℝ, sin (θ i) ^ 2
      ∂Measure.pi (fun _ => chebyshevAngleMeasure)) = π ^ (d + 1) / 2 := by
  have hsin : (∫ θ, sin θ ^ 2 ∂chebyshevAngleMeasure) = π / 2 := by
    change (∫ θ in Ioc (0 : ℝ) π, sin θ ^ 2) = _
    rw [← intervalIntegral.integral_of_le pi_pos.le, integral_sin_sq]
    simp
  have hone : (∫ _θ : ℝ, (1 : ℝ) ∂chebyshevAngleMeasure) = π := by
    change (∫ _θ in Ioc (0 : ℝ) π, (1 : ℝ)) = _
    rw [← intervalIntegral.integral_of_le pi_pos.le]
    simp
  have he (θ : Fin (d + 1) → ℝ) : sin (θ i) ^ 2 =
      ∏ j, if j = i then sin (θ j) ^ 2 else 1 := by
    rw [i.prod_univ_succAbove]
    simp [Fin.succAbove_ne]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun j θ => if j = i then sin θ ^ 2 else 1),
    i.prod_univ_succAbove]
  simp only [ite_true, hsin, Fin.succAbove_ne, if_false, hone, prod_const, card_univ,
    Fintype.card_fin]
  rw [pow_succ]
  ring

/-- Each coordinate derivative has square energy at most `π^(d+1) L²/2`. -/
theorem integral_tensorChebyshevCosinePartial_sq_le {d : ℕ}
    {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (i : Fin (d + 1)) :
    (∫ θ, tensorChebyshevCosinePartial f i θ ^ 2
      ∂Measure.pi (fun _ => chebyshevAngleMeasure)) ≤ π ^ (d + 1) * (L : ℝ) ^ 2 / 2 := by
  have hb (θ : Fin (d + 1) → ℝ) :
      tensorChebyshevCosinePartial f i θ ^ 2 ≤ (L : ℝ) ^ 2 * sin (θ i) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg _) (abs_tensorChebyshevCosinePartial_le hf i θ)
    simpa only [← sq, mul_pow, sq_abs] using h
  have hm := integrable_pi_chebyshevAngleMeasure_of_continuous
    (show Continuous (fun θ : Fin (d + 1) → ℝ => (L : ℝ) ^ 2 * sin (θ i) ^ 2) from by fun_prop)
  have h := integral_mono_ae (integrable_tensorChebyshevCosinePartial_sq hf i) hm
    (Filter.Eventually.of_forall hb)
  rw [integral_const_mul, integral_sin_sq_pi_chebyshevAngleMeasure] at h
  calc
    _ ≤ (L : ℝ) ^ 2 * (π ^ (d + 1) / 2) := h
    _ = _ := by ring

/-- Coordinatewise cosine commutes with finite coordinate insertion. -/
theorem cos_insertNth {d : ℕ} (i : Fin (d + 1)) (t : ℝ) (y : Fin d → ℝ) :
    (fun j => cos ((i.insertNth t y : Fin (d + 1) → ℝ) j)) =
      i.insertNth (cos t) (fun j => cos (y j)) := by
  funext j
  apply (i.forall_iff_succAbove).mpr ?_ j
  constructor
  · simp
  · intro k
    simp

/-- A mixed tensor basis factors along its sine coordinate. -/
theorem tensorChebyshevMixedBasis_insertNth {d : ℕ}
    (i : Fin (d + 1)) (α : Fin (d + 1) → ℕ) (t : ℝ) (y : Fin d → ℝ) :
    tensorChebyshevMixedBasis i α (i.insertNth t y) =
      (sqrt (2 / π) * sin ((α i : ℝ) * t)) *
        ∏ j, normalizedChebyshev (α (i.succAbove j)) (cos (y j)) := by
  rw [tensorChebyshevMixedBasis, i.prod_univ_succAbove]
  simp [Fin.succAbove_ne]

/-- The cosine tensor basis factors along any chosen coordinate. -/
theorem prod_normalizedChebyshev_cos_insertNth {d : ℕ}
    (i : Fin (d + 1)) (α : Fin (d + 1) → ℕ) (t : ℝ) (y : Fin d → ℝ) :
    (∏ j, normalizedChebyshev (α j) (cos ((i.insertNth t y : Fin (d + 1) → ℝ) j))) =
      normalizedChebyshev (α i) (cos t) *
        ∏ j, normalizedChebyshev (α (i.succAbove j)) (cos (y j)) := by
  rw [i.prod_univ_succAbove]
  simp

/-- A cosine coordinate derivative simplifies to the ordinary slice derivative. -/
theorem tensorChebyshevCosinePartial_insertNth {d : ℕ}
    (f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) (i : Fin (d + 1))
    (t : ℝ) (y : Fin d → ℝ) :
    tensorChebyshevCosinePartial f i (i.insertNth t y) =
      -deriv ((fun x => f (WithLp.toLp 2 (i.insertNth x (fun j => cos (y j))))) ∘ cos) t := by
  simp only [tensorChebyshevCosinePartial, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove, Function.comp_def]

/-- Direct cosine/sine integration by parts for a Lipschitz input, with no
coefficient normalization left in the identity. -/
theorem integral_neg_deriv_comp_cos_mul_sin_eq_mul_integral_cos
    {f : ℝ → ℝ} {L : NNReal} (hf : LipschitzOnWith L f (Icc (-1 : ℝ) 1))
    {j : ℕ} (hj : 0 < j) :
    (∫ θ, -deriv (f ∘ cos) θ * sin ((j : ℝ) * θ) ∂chebyshevAngleMeasure) =
      (j : ℝ) * ∫ θ, f (cos θ) * cos ((j : ℝ) * θ) ∂chebyshevAngleMeasure := by
  have h := integral_neg_deriv_comp_cos_mul_sin_eq hf hj
  rw [chebyshevCoeff_eq_cosine_integral, if_neg (by omega : j ≠ 0)] at h
  rw [intervalIntegral.integral_of_le pi_pos.le, intervalIntegral.integral_of_le pi_pos.le] at h
  calc
    _ = π / 2 * ((j : ℝ) * (2 / π *
        ∫ θ, f (cos θ) * cos ((j : ℝ) * θ) ∂chebyshevAngleMeasure)) := h
    _ = _ := by field_simp

/-- The actual tensor coefficient is the mixed sine/cosine coefficient of
the coordinate cosine derivative, including arbitrary Lipschitz inputs. -/
theorem integral_tensorChebyshevCosinePartial_mul_mixed_eq {d : ℕ}
    {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (i : Fin (d + 1)) (α : Fin (d + 1) → ℕ) (hα : 0 < α i) :
    (∫ θ, tensorChebyshevCosinePartial f i θ * tensorChebyshevMixedBasis i α θ
      ∂Measure.pi (fun _ => chebyshevAngleMeasure)) = (α i : ℝ) * tensorChebyshevCoeff f α := by
  have hleft := integral_pi_fin_eq_integral_insertNth
    (fun _ : Fin (d + 1) => chebyshevAngleMeasure) i
    (integrable_tensorChebyshevCosinePartial_mul_mixed hf i α)
  have hc : Continuous (fun θ : Fin (d + 1) → ℝ =>
      f (WithLp.toLp 2 (fun j => cos (θ j))) *
        ∏ j, normalizedChebyshev (α j) (cos (θ j))) := by
    apply Continuous.mul (hf.continuous.comp ((PiLp.continuous_toLp 2 _).comp (by fun_prop)))
    unfold normalizedChebyshev
    fun_prop
  rw [hleft, tensorChebyshevCoeff_eq_cosine_integral hf.continuous,
    integral_pi_fin_eq_integral_insertNth _ i (integrable_pi_chebyshevAngleMeasure_of_continuous hc),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp_rw [tensorChebyshevCosinePartial_insertNth, tensorChebyshevMixedBasis_insertNth,
    prod_normalizedChebyshev_cos_insertNth, cos_insertNth, normalizedChebyshev_cos]
  let F (x : ℝ) := f (WithLp.toLp 2 (i.insertNth x (fun j => cos (y j))))
  let K : ℝ := ∏ j, normalizedChebyshevWeight (α (i.succAbove j)) *
    cos ((α (i.succAbove j) : ℝ) * y j)
  have hu := integral_neg_deriv_comp_cos_mul_sin_eq_mul_integral_cos
    (lipschitzWith_euclidean_insertNth hf i (fun j => cos (y j))).lipschitzOnWith hα
  change (∫ t, -deriv (F ∘ cos) t * (sqrt (2 / π) * sin ((α i : ℝ) * t) * K)
      ∂chebyshevAngleMeasure) =
    (α i : ℝ) * ∫ t, F (cos t) * (normalizedChebyshevWeight (α i) * cos ((α i : ℝ) * t) * K)
      ∂chebyshevAngleMeasure
  have hl (t : ℝ) : -deriv (F ∘ cos) t * (sqrt (2 / π) * sin ((α i : ℝ) * t) * K) =
      (sqrt (2 / π) * K) * (-deriv (F ∘ cos) t * sin ((α i : ℝ) * t)) := by ring
  have hr (t : ℝ) : F (cos t) * (normalizedChebyshevWeight (α i) * cos ((α i : ℝ) * t) * K) =
      (normalizedChebyshevWeight (α i) * K) * (F (cos t) * cos ((α i : ℝ) * t)) := by ring
  simp_rw [hl, hr]
  rw [integral_const_mul, integral_const_mul, hu]
  rw [normalizedChebyshevWeight, if_neg (by omega : α i ≠ 0)]
  ring

/-- Every finite set of tensor coefficients has bounded energy in each
coordinate. This applies finite Bessel to the actual coordinate derivative. -/
theorem sum_coordinate_sq_mul_tensorChebyshevCoeff_sq_le {d : ℕ}
    {f : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (i : Fin (d + 1)) (s : Finset (Fin (d + 1) → ℕ)) :
    (∑ α ∈ s, (α i : ℝ) ^ 2 * tensorChebyshevCoeff f α ^ 2) ≤
      π ^ (d + 1) * (L : ℝ) ^ 2 / 2 := by
  classical
  let t := s.filter (fun α => 0 < α i)
  have h := sum_sq_integral_mul_le_integral_sq_of_orthonormal t
    (tensorChebyshevMixedBasis i) (integrable_tensorChebyshevCosinePartial_sq hf i)
    (fun α _ => integrable_tensorChebyshevCosinePartial_mul_mixed hf i α)
    (fun α _ β _ => integrable_pi_chebyshevAngleMeasure_of_continuous
      ((continuous_tensorChebyshevMixedBasis i α).mul (continuous_tensorChebyshevMixedBasis i β)))
    (fun α hα β hβ => integral_tensorChebyshevMixedBasis_mul i α β
      (Finset.mem_filter.mp hα).2 (Finset.mem_filter.mp hβ).2)
  have he : (∑ α ∈ t, (∫ θ, tensorChebyshevCosinePartial f i θ * tensorChebyshevMixedBasis i α θ
      ∂Measure.pi (fun _ => chebyshevAngleMeasure)) ^ 2) =
      ∑ α ∈ s, (α i : ℝ) ^ 2 * tensorChebyshevCoeff f α ^ 2 := by
    rw [show t = s.filter (fun α => 0 < α i) from rfl, sum_filter]
    apply sum_congr rfl
    intro α _
    by_cases hα : 0 < α i
    · rw [if_pos hα, integral_tensorChebyshevCosinePartial_mul_mixed_eq hf i α hα, mul_pow]
    · have hz : α i = 0 := by omega
      simp [hz]
  rw [he] at h
  exact h.trans (integral_tensorChebyshevCosinePartial_sq_le hf i)

/-- Finite normalized tensor Chebyshev energy for a Euclidean Lipschitz function.
The zero-dimensional case is included and has zero energy. -/
theorem sum_norm_sq_mul_tensorChebyshevCoeff_sq_le_of_lipschitzWith {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : NNReal} (hf : LipschitzWith L f)
    (s : Finset (Fin d → ℕ)) :
    (∑ α ∈ s, (∑ i, (α i : ℝ) ^ 2) * tensorChebyshevCoeff f α ^ 2) ≤
      (d : ℝ) * π ^ d * (L : ℝ) ^ 2 / 2 := by
  cases d with
  | zero => simp
  | succ d =>
    calc
      _ = ∑ i : Fin (d + 1), ∑ α ∈ s, (α i : ℝ) ^ 2 * tensorChebyshevCoeff f α ^ 2 := by
        simp_rw [sum_mul]
        rw [sum_comm]
      _ ≤ ∑ _i : Fin (d + 1), π ^ (d + 1) * (L : ℝ) ^ 2 / 2 :=
        sum_le_sum (fun i _ => sum_coordinate_sq_mul_tensorChebyshevCoeff_sq_le hf i s)
      _ = _ := by simp; ring

/-- The full normalized tensor energy is summable for Euclidean Lipschitz inputs. -/
theorem summable_norm_sq_mul_tensorChebyshevCoeff_sq_of_lipschitzWith {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : NNReal} (hf : LipschitzWith L f) :
    Summable (fun α : Fin d → ℕ => (∑ i, (α i : ℝ) ^ 2) * tensorChebyshevCoeff f α ^ 2) := by
  apply summable_of_sum_le (fun α => by positivity)
    (c := (d : ℝ) * π ^ d * (L : ℝ) ^ 2 / 2)
  exact sum_norm_sq_mul_tensorChebyshevCoeff_sq_le_of_lipschitzWith hf

/-- Global Lipschitz inputs satisfy the full normalized tensor coefficient
energy bound. This is an intermediate statement for the cube-only theorem. -/
theorem tsum_norm_sq_mul_tensorChebyshevCoeff_sq_le_of_lipschitzWith {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : NNReal} (hf : LipschitzWith L f) :
    (∑' α : Fin d → ℕ, (∑ i, (α i : ℝ) ^ 2) * tensorChebyshevCoeff f α ^ 2) ≤
      (d : ℝ) * π ^ d * (L : ℝ) ^ 2 / 2 := by
  apply (summable_norm_sq_mul_tensorChebyshevCoeff_sq_of_lipschitzWith hf).tsum_le_of_sum_le
  exact sum_norm_sq_mul_tensorChebyshevCoeff_sq_le_of_lipschitzWith hf

/-- A function Lipschitz only on the Euclidean cube has the full normalized
tensor Chebyshev energy bound. The coefficient integral is for the actual
product Chebyshev measure; no differentiability or series expansion is assumed.
Source: MMRS Appendix A.1, Lemma 31, extended to Lipschitz inputs.
atlas: chebyshev-lipschitz-coefficient-energy -/
theorem tsum_norm_sq_mul_tensorChebyshevCoeff_sq_le_of_lipschitzOnWith {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (chebyshevCube (Fin d))) :
    (∑' α : Fin d → ℕ, (∑ i, (α i : ℝ) ^ 2) * tensorChebyshevCoeff f α ^ 2) ≤
      (d : ℝ) * π ^ d * (L : ℝ) ^ 2 / 2 := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  have he (α : Fin d → ℕ) : tensorChebyshevCoeff f α = tensorChebyshevCoeff g α :=
    tensorChebyshevCoeff_congr hfg α
  simp_rw [he]
  exact tsum_norm_sq_mul_tensorChebyshevCoeff_sq_le_of_lipschitzWith hg

end NLAlib
