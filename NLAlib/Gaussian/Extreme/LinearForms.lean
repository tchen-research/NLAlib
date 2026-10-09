import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import NLAlib.Gaussian.Extreme.Lipschitz

/-!
# Linear forms of a Gaussian matrix

The Gaussian processes of the comparison proofs in `NLAlib.Gaussian.Extreme` are families of
linear forms of a standard Gaussian matrix `G`:

* `linForm c G = ∑ᵢⱼ cᵢⱼ Gᵢⱼ` (the Frobenius pairing `⟨c, G⟩_F` written on the array
  `Fin p → Fin m → ℝ` that carries the Gaussian law; `linForm_eq_frobInner` is the bridge to
  `NLAlib.frobInner`), and `linFormCLM a` packaging a family `(linForm (a t))ₜ` as a continuous
  linear map;
* `hasGaussianLaw_linForm_gaussianMatrix`: any finite family `(⟨a t, G⟩)ₜ` is jointly Gaussian;
* `integral_linForm_gaussianMatrix`, `integral_linForm_sq_gaussianMatrix`: `𝔼⟨c, G⟩ = 0`,
  `𝔼⟨c, G⟩² = ∑ᵢⱼ cᵢⱼ²`;
* entrywise facts: `hasGaussianLaw_id_gaussianMatrix` (and the instance
  `isGaussian_gaussianMatrix`), `𝔼 Gᵢⱼ = 0`, `𝔼 Gᵢⱼ² = 1`, and
  `𝔼 √(∑ⱼ H_{0,σ(j)}²) ≤ √k` (`integral_sqrt_sum_sq_gaussianMatrix_entry_le`).

Ported from the Prove2me solutions `GaussianMatrix.gordon_upper`, `GaussianMatrix.gordon_lower`
and `GaussianMatrix.spectral_second_moment_bound` (identical helper sections, deduplicated).

Atlas: helpers of `gordon`, `spectral-second-moment`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- A vector of independent standard normals has a Gaussian law. Ported from Prove2me solution
`GaussianMatrix.gordon_upper` (helper `gu_hasGaussianLaw_pi`). Atlas: helper of `gordon`. -/
theorem hasGaussianLaw_id_pi_gaussianReal (κ : Type*) [Fintype κ] :
    HasGaussianLaw (fun x : κ → ℝ => x) (Measure.pi fun _ : κ => gaussianReal 0 1) := by
  have h := iIndepFun.hasGaussianLaw (P := Measure.pi fun _ : κ => gaussianReal 0 1)
    (X := fun k (x : κ → ℝ) => x k) (fun k => ⟨by
      have := (measurePreserving_eval (fun _ : κ => gaussianReal (0 : ℝ) 1) k).map_eq
      rw [this]; infer_instance⟩)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  exact h

/-- A standard Gaussian matrix has a Gaussian law (as a random element of
`Fin p → Fin m → ℝ`). Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper
`gu_hasGaussianLaw_id`). Atlas: helper of `gordon`. -/
theorem hasGaussianLaw_id_gaussianMatrix (p m : ℕ) :
    HasGaussianLaw (fun G : Fin p → Fin m → ℝ => G) (gaussianMatrix p m) := by
  have h := iIndepFun.hasGaussianLaw (P := gaussianMatrix p m)
    (X := fun i (G : Fin p → Fin m → ℝ) => G i) (fun i => ⟨by
      have := (measurePreserving_eval
        (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) i).map_eq
      unfold gaussianMatrix
      rw [this]
      have := (hasGaussianLaw_id_pi_gaussianReal (Fin m)).isGaussian_map
      rwa [Measure.map_id'] at this⟩)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  exact h

/-- The law of a standard Gaussian matrix is a Gaussian measure on `Fin p → Fin m → ℝ`.
Ported from Prove2me solution `GaussianMatrix.spectral_second_moment_bound` (instance
`ssb_isGaussian_gm`). -/
instance isGaussian_gaussianMatrix (p m : ℕ) : IsGaussian (gaussianMatrix p m) := by
  have := (hasGaussianLaw_id_gaussianMatrix p m).isGaussian_map
  rwa [Measure.map_id'] at this

/-- `𝔼 f(Gᵢⱼ) = ∫ f dN(0,1)` for measurable `f`. Ported from Prove2me solution
`GaussianMatrix.gordon_upper` (helper `gu_integral_comp_coord`). Atlas: helper of `gordon`. -/
theorem integral_comp_gaussianMatrix_entry_eq {p m : ℕ} (a : Fin p) (b : Fin m) (f : ℝ → ℝ)
    (hf : Measurable f) :
    ∫ G, f (G a b) ∂(gaussianMatrix p m) = ∫ x, f x ∂(gaussianReal 0 1) := by
  rw [← (measurePreserving_gaussianMatrix_entry a b).map_eq, integral_map]
  · exact (measurePreserving_gaussianMatrix_entry a b).measurable.aemeasurable
  · exact hf.aestronglyMeasurable

/-- `𝔼 Gᵢⱼ = 0`. Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper
`gu_integral_coord`). Atlas: helper of `gordon`. -/
theorem integral_gaussianMatrix_entry_eq_zero {p m : ℕ} (a : Fin p) (b : Fin m) :
    ∫ G, G a b ∂(gaussianMatrix p m) = 0 := by
  have := integral_comp_gaussianMatrix_entry_eq a b (fun x => x) measurable_id
  simpa [integral_id_gaussianReal] using this

/-- `𝔼 Gᵢⱼ² = 1`. Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper
`gu_integral_coord_sq`). Atlas: helper of `gordon`. -/
theorem integral_gaussianMatrix_entry_sq_eq_one {p m : ℕ} (a : Fin p) (b : Fin m) :
    ∫ G, G a b ^ 2 ∂(gaussianMatrix p m) = 1 := by
  rw [integral_comp_gaussianMatrix_entry_eq a b (fun x => x ^ 2) (by fun_prop)]
  have h := variance_eq_sub (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp))
  rw [variance_id_gaussianReal] at h
  simp [integral_id_gaussianReal] at h
  exact h.symm

/-- `k Gᵢⱼ Gₖₗ` is integrable. Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper
`gu_integrable_coord_mul`). Atlas: helper of `gordon`. -/
theorem integrable_const_mul_gaussianMatrix_entry_mul {p m : ℕ} (a c : Fin p) (b d : Fin m) (k : ℝ) :
    Integrable (fun G : Fin p → Fin m → ℝ => k * (G a b * G c d)) (gaussianMatrix p m) :=
  ((memLp_gaussianMatrix_entry a b 2 (by simp)).integrable_mul (memLp_gaussianMatrix_entry c d 2 (by simp))).const_mul k


/-- The linear form `⟨c, G⟩ = ∑ᵢⱼ cᵢⱼ Gᵢⱼ` on arrays `Fin p → Fin m → ℝ` (the space carrying
`gaussianMatrix p m`); equal to `frobInner (Matrix.of c) (Matrix.of G)` (`linForm_eq_frobInner`).
Ported from Prove2me solution `GaussianMatrix.gordon_upper` (`guLin`). -/
noncomputable def linForm {p m : ℕ} (c : Fin p → Fin m → ℝ) (G : Fin p → Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * G i j

/-- Bridge to the Frobenius inner product. -/
theorem linForm_eq_frobInner {p m : ℕ} (c G : Fin p → Fin m → ℝ) :
    linForm c G = frobInner (Matrix.of c) (Matrix.of G) := rfl

/-- A finite family of linear forms `(⟨a t, ·⟩)ₜ` as one continuous linear map into `ι → ℝ`.
Ported from Prove2me solution `GaussianMatrix.gordon_upper` (`guLinCLM`). -/
noncomputable def linFormCLM {ι : Type*} {p m : ℕ} (a : ι → Fin p → Fin m → ℝ) :
    (Fin p → Fin m → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun t => ∑ i, ∑ j,
    a t i j • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => Fin m → ℝ) i))

/-- A finite family of linear forms `(⟨a t, G⟩)ₜ` of a standard Gaussian matrix is jointly
Gaussian. Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper
`gu_hasGaussianLaw_lin`). Atlas: helper of `gordon`. -/
theorem hasGaussianLaw_linForm_gaussianMatrix {ι : Type*} [Fintype ι] {p m : ℕ} (a : ι → Fin p → Fin m → ℝ) :
    HasGaussianLaw (fun G t => linForm (a t) G) (gaussianMatrix p m) := by
  have h := (hasGaussianLaw_id_gaussianMatrix p m).map_fun (linFormCLM a)
  have e : (fun G t => linForm (a t) G) = fun G => linFormCLM a G := by
    funext G t
    simp [linFormCLM, linForm]
  rw [e]; exact h


/-- `⟨c, G⟩` is integrable. Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper
`gu_integrable_lin`). Atlas: helper of `gordon`. -/
theorem integrable_linForm_gaussianMatrix {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    Integrable (linForm c) (gaussianMatrix p m) := by
  unfold linForm
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((memLp_gaussianMatrix_entry i j 2 (by simp)).integrable (by simp)).const_mul _

/-- `G ↦ ⟨c, G⟩` is continuous. Ported from Prove2me solution `GaussianMatrix.gordon_upper`
(helper `gu_continuous_lin`). -/
theorem continuous_linForm {p m : ℕ} (c : Fin p → Fin m → ℝ) : Continuous (linForm c) := by
  unfold linForm; fun_prop

/-- `𝔼⟨c, G⟩ = 0`. Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper
`gu_integral_lin`). Atlas: helper of `gordon`. -/
theorem integral_linForm_gaussianMatrix {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    ∫ G, linForm c G ∂(gaussianMatrix p m) = 0 := by
  unfold linForm
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((memLp_gaussianMatrix_entry i j 2 (by simp)).integrable (by simp)).const_mul _]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun j _ =>
    ((memLp_gaussianMatrix_entry i j 2 (by simp)).integrable (by simp)).const_mul _]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul, integral_gaussianMatrix_entry_eq_zero, mul_zero]

/-- `⟨c, G⟩ - ⟨d, G⟩ = ⟨c - d, G⟩`. Ported from Prove2me solution `GaussianMatrix.gordon_upper`
(helper `gu_lin_sub`). -/
theorem linForm_sub_linForm {p m : ℕ} (c d : Fin p → Fin m → ℝ) (G : Fin p → Fin m → ℝ) :
    linForm c G - linForm d G = linForm (c - d) G := by
  simp only [linForm, ← Finset.sum_sub_distrib, Pi.sub_apply, sub_mul]

/-- `𝔼⟨c, G⟩² = ∑ᵢⱼ cᵢⱼ²`. Ported from Prove2me solution `GaussianMatrix.gordon_upper`
(helper `gu_integral_lin_sq`). Atlas: helper of `gordon`. -/
theorem integral_linForm_sq_gaussianMatrix {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    ∫ G, linForm c G ^ 2 ∂(gaussianMatrix p m) = ∑ i, ∑ j, c i j ^ 2 := by
  have hexp : ∀ G : Fin p → Fin m → ℝ, linForm c G ^ 2 =
      ∑ i, ∑ k, ∑ j, ∑ l, c i j * c k l * (G i j * G k l) := by
    intro G
    unfold linForm
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    integrable_const_mul_gaussianMatrix_entry_mul i k j l _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    integrable_const_mul_gaussianMatrix_entry_mul i k j l _]
  rw [Finset.sum_eq_single i]
  · rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
      integrable_const_mul_gaussianMatrix_entry_mul i i j l _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => integrable_const_mul_gaussianMatrix_entry_mul i i j l _]
    rw [Finset.sum_eq_single j]
    · rw [integral_const_mul, integral_gaussianMatrix_entry_mul]; simp [sq]
    · intro l _ hl
      rw [integral_const_mul, integral_gaussianMatrix_entry_mul]; simp [Ne.symm hl]
    · simp
  · intro k _ hk
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
      integrable_const_mul_gaussianMatrix_entry_mul i k j l _]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_finsetSum _ fun l _ => integrable_const_mul_gaussianMatrix_entry_mul i k j l _]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [integral_const_mul, integral_gaussianMatrix_entry_mul]; simp [Ne.symm hk]
  · simp




/-- `⟨c, G⟩ ∈ L²`. Ported from Prove2me solution
`GaussianMatrix.spectral_second_moment_bound` (helper `ssb_memLp_lin`). Atlas: helper of
`spectral-second-moment`. -/
theorem memLp_linForm_gaussianMatrix {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    MemLp (linForm c) 2 (gaussianMatrix p m) := by
  unfold linForm
  exact memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ =>
    (memLp_gaussianMatrix_entry i j 2 (by simp)).const_mul _


/-- `𝔼 √(∑ⱼ H_{0,σ(j)}²) ≤ √k` for `k` coordinates of a Gaussian row (Jensen). Ported from
Prove2me solution `GaussianMatrix.gordon_upper` (helper `gu_integral_sqrt_sumsq_le`). Atlas:
helper of `gordon`. -/
theorem integral_sqrt_sum_sq_gaussianMatrix_entry_le {k m : ℕ} (σ : Fin k → Fin m) :
    ∫ H, Real.sqrt (∑ j, H 0 (σ j) ^ 2) ∂(gaussianMatrix 1 m) ≤ Real.sqrt k := by
  have hQ : Integrable (fun H : Fin 1 → Fin m → ℝ => ∑ j, H 0 (σ j) ^ 2) (gaussianMatrix 1 m) :=
    integrable_finsetSum _ fun j _ => (memLp_gaussianMatrix_entry 0 (σ j) 2 (by simp)).integrable_sq
  have hQ0 : ∀ H : Fin 1 → Fin m → ℝ, 0 ≤ ∑ j, H 0 (σ j) ^ 2 := fun H =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcont : Continuous (fun H : Fin 1 → Fin m → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2)) := by
    fun_prop
  have hS : Integrable (fun H : Fin 1 → Fin m → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2))
      (gaussianMatrix 1 m) := by
    refine Integrable.mono' ((integrable_const 1).add hQ) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun H => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 := Real.sq_sqrt (hQ0 H)
    have h2 := Real.sqrt_nonneg (∑ j, H 0 (σ j) ^ 2)
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (Real.sqrt (∑ j, H 0 (σ j) ^ 2) - 1)]
  have hS2 : Integrable (fun H : Fin 1 → Fin m → ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2) ^ 2)
      (gaussianMatrix 1 m) := by
    refine hQ.congr (Filter.Eventually.of_forall fun H => ?_)
    exact (Real.sq_sqrt (hQ0 H)).symm
  refine integral_le_of_integral_sq_le _ _ hS hS2 _ (Real.sqrt_nonneg _) (le_of_eq ?_)
  rw [Real.sq_sqrt (Nat.cast_nonneg k)]
  simp_rw [Real.sq_sqrt (hQ0 _)]
  rw [integral_finsetSum _ fun j _ => (memLp_gaussianMatrix_entry 0 (σ j) 2 (by simp)).integrable_sq]
  simp [integral_gaussianMatrix_entry_sq_eq_one]


end NLAlib
