import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Matrix.Mul

/-!
# Standard Gaussian matrices

`NLAlib.gaussianMatrix p m` is the law of a `p × m` matrix with i.i.d. `N(0,1)` entries, as the
product measure on `Fin p → Fin m → ℝ`; `Matrix.of` is the matrix view. This is the convention of
the Gaussian Random Matrices series and of the LRA project, so results port without change.

The file holds the definition and its unfolding-level API:

* `measurePreserving_gaussianMatrix_entry`, `memLp_gaussianMatrix_entry`: each entry is `N(0,1)`;
* `integral_comp_gaussianMatrix_entry_eq`, `integral_gaussianMatrix_entry_eq_zero`,
  `integral_gaussianMatrix_entry_sq_eq_one`, `integral_gaussianMatrix_entry_mul`:
  `E f(G_ab) = ∫ f dN(0,1)`, `E G_ab = 0`, `E G_ab² = 1`, `E[G_ab G_cd] = δ_ac δ_bd`;
* `gaussianMatrix_map_uncurry`, `gaussianMatrix_eq_map_curry`: flattening gives the product
  measure on `Fin p × Fin m → ℝ`, and conversely;
* `hasGaussianLaw_id_pi_gaussianReal`, `hasGaussianLaw_id_gaussianMatrix` and the instance
  `isGaussian_gaussianMatrix`: the law is a Gaussian measure;
* `aemeasurable_of_map_eq_gaussianMatrix`, `measurable_block`: measurability of a random
  variable with this law and of the block map `G ↦ Vᵀ G`.

Atlas: `gaussian-matrix-def`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- Law of a `p × m` matrix with independent standard Gaussian entries. Atlas:
`gaussian-matrix-def`.
atlas: gaussian-matrix-def -/
def gaussianMatrix (p m : ℕ) : Measure (Fin p → Fin m → ℝ) :=
  Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1

/-- `gaussianMatrix p m` is a probability measure. Atlas: `gaussian-matrix-def`. -/
instance isProbabilityMeasure_gaussianMatrix (p m : ℕ) :
    IsProbabilityMeasure (gaussianMatrix p m) := by
  unfold gaussianMatrix; infer_instance

/-! ### Entries of a Gaussian matrix -/

/-- Each entry of a standard Gaussian matrix is `N(0,1)`. Atlas: `gaussian-matrix-def`. -/
theorem measurePreserving_gaussianMatrix_entry {p m : ℕ} (a : Fin p) (b : Fin m) :
    MeasurePreserving (fun G : Fin p → Fin m → ℝ => G a b) (gaussianMatrix p m)
      (gaussianReal 0 1) :=
  (measurePreserving_eval (fun _ : Fin m => gaussianReal 0 1) b).comp
    (measurePreserving_eval (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal 0 1) a)

/-- Each entry of a standard Gaussian matrix has finite moments of every finite order.
Atlas: `gaussian-matrix-def`. -/
theorem memLp_gaussianMatrix_entry {p m : ℕ} (a : Fin p) (b : Fin m) (q : ENNReal)
    (hq : q ≠ ⊤) : MemLp (fun G : Fin p → Fin m → ℝ => G a b) q (gaussianMatrix p m) :=
  (memLp_id_gaussianReal' q hq).comp_measurePreserving
    (measurePreserving_gaussianMatrix_entry a b)

/-- `𝔼 f(Gᵢⱼ) = ∫ f dN(0,1)` for measurable `f`. Ported from Prove2me solution
`GaussianMatrix.gordon_upper` (helper `gu_integral_comp_coord`). Atlas: `gaussian-matrix-def`. -/
theorem integral_comp_gaussianMatrix_entry_eq {p m : ℕ} (a : Fin p) (b : Fin m) (f : ℝ → ℝ)
    (hf : Measurable f) :
    ∫ G, f (G a b) ∂(gaussianMatrix p m) = ∫ x, f x ∂(gaussianReal 0 1) := by
  rw [← (measurePreserving_gaussianMatrix_entry a b).map_eq, integral_map]
  · exact (measurePreserving_gaussianMatrix_entry a b).measurable.aemeasurable
  · exact hf.aestronglyMeasurable

/-- `𝔼 Gᵢⱼ = 0`. Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper
`gu_integral_coord`). Atlas: `gaussian-matrix-def`. -/
theorem integral_gaussianMatrix_entry_eq_zero {p m : ℕ} (a : Fin p) (b : Fin m) :
    ∫ G, G a b ∂(gaussianMatrix p m) = 0 := by
  have := integral_comp_gaussianMatrix_entry_eq a b (fun x => x) measurable_id
  simpa [integral_id_gaussianReal] using this

/-- `𝔼 Gᵢⱼ² = 1`. Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper
`gu_integral_coord_sq`). Atlas: `gaussian-matrix-def`. -/
theorem integral_gaussianMatrix_entry_sq_eq_one {p m : ℕ} (a : Fin p) (b : Fin m) :
    ∫ G, G a b ^ 2 ∂(gaussianMatrix p m) = 1 := by
  rw [integral_comp_gaussianMatrix_entry_eq a b (fun x => x ^ 2) (by fun_prop)]
  have h := variance_eq_sub (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp))
  rw [variance_id_gaussianReal] at h
  simp [integral_id_gaussianReal] at h
  exact h.symm

/-- `k Gᵢⱼ Gₖₗ` is integrable. Ported from Prove2me solution `GaussianMatrix.gordon_upper`
(helper `gu_integrable_coord_mul`). Atlas: `gaussian-matrix-def`. -/
theorem integrable_const_mul_gaussianMatrix_entry_mul {p m : ℕ} (a c : Fin p) (b d : Fin m)
    (k : ℝ) :
    Integrable (fun G : Fin p → Fin m → ℝ => k * (G a b * G c d)) (gaussianMatrix p m) :=
  ((memLp_gaussianMatrix_entry a b 2 (by simp)).integrable_mul
    (memLp_gaussianMatrix_entry c d 2 (by simp))).const_mul k

/-- Second moments of the entries of a standard Gaussian matrix:
`E[G_ab G_cd] = δ_ac δ_bd`. Atlas: `gaussian-matrix-def` (used for
`gaussian-frob-second-moment`). -/
theorem integral_gaussianMatrix_entry_mul {p m : ℕ} (a c : Fin p) (b d : Fin m) :
    ∫ G, G a b * G c d ∂(gaussianMatrix p m) = if a = c ∧ b = d then 1 else 0 := by
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd
      simpa [← pow_two] using integral_gaussianMatrix_entry_sq_eq_one a b
    · simp only [hbd, and_false, if_false]
      have hrow := measurePreserving_eval
        (fun _ : Fin p => Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) a
      have h1 : ∫ G, G a b * G a d ∂(gaussianMatrix p m)
          = ∫ x, x b * x d ∂(Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) := by
        have := integral_map (μ := gaussianMatrix p m) hrow.measurable.aemeasurable
          (f := fun x : Fin m → ℝ => x b * x d) (by fun_prop)
        unfold gaussianMatrix at this ⊢
        rw [hrow.map_eq] at this
        exact this.symm
      rw [h1]
      have hind : iIndepFun (fun (i : Fin m) (ω : Fin m → ℝ) => ω i)
          (Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) :=
        iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
      rw [(hind.indepFun hbd).integral_fun_mul_eq_mul_integral
        (measurable_pi_apply b).aestronglyMeasurable (measurable_pi_apply d).aestronglyMeasurable]
      have h0 : ∫ x, x b ∂(Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1) = 0 := by
        have hb := measurePreserving_eval (fun _ : Fin m => gaussianReal (0 : ℝ) 1) b
        have := integral_map (μ := Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1)
          hb.measurable.aemeasurable (f := fun x : ℝ => x) (by fun_prop)
        rw [hb.map_eq, integral_id_gaussianReal] at this
        exact this.symm
      simp [h0]
  · simp only [hac, false_and, if_false]
    have hind : iIndepFun (fun (i : Fin p) (ω : Fin p → Fin m → ℝ) => ω i)
        (gaussianMatrix p m) :=
      iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
    have h2 := (hind.indepFun hac).comp (measurable_pi_apply b) (measurable_pi_apply d)
    have := h2.integral_fun_mul_eq_mul_integral
      (by
        have : Measurable (fun ω : Fin p → Fin m → ℝ => ω a b) := by fun_prop
        exact this.aestronglyMeasurable)
      (by
        have : Measurable (fun ω : Fin p → Fin m → ℝ => ω c d) := by fun_prop
        exact this.aestronglyMeasurable)
    simp only [Function.comp_def] at this
    rw [this, integral_gaussianMatrix_entry_eq_zero]
    simp

/-! ### Flattening -/

/-- Flattening a standard Gaussian matrix gives i.i.d. standard Gaussians indexed by
`Fin p × Fin m`. Atlas: `gaussian-matrix-def`. -/
theorem gaussianMatrix_map_uncurry (p m : ℕ) :
    Measure.map (fun G : Fin p → Fin m → ℝ => fun ab : Fin p × Fin m => G ab.1 ab.2)
      (gaussianMatrix p m) = Measure.pi fun _ : Fin p × Fin m => gaussianReal 0 1 := by
  symm
  have hmeas : Measurable fun G : Fin p → Fin m → ℝ => fun ab : Fin p × Fin m => G ab.1 ab.2 :=
    measurable_pi_lambda _ fun ab => (measurable_pi_apply ab.2).comp (measurable_pi_apply ab.1)
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun G : Fin p → Fin m → ℝ => fun ab : Fin p × Fin m => G ab.1 ab.2) ⁻¹'
      Set.univ.pi s = Set.univ.pi fun a => Set.univ.pi fun b => s (a, b) := by
    ext G
    simp only [Set.mem_preimage, Set.mem_univ_pi, Prod.forall]
  rw [hpre, gaussianMatrix, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- A standard Gaussian matrix is the currying of i.i.d. standard Gaussians indexed by
`Fin p × Fin m` (the converse of `gaussianMatrix_map_uncurry`). Atlas: `gaussian-matrix-def`. -/
theorem gaussianMatrix_eq_map_curry (p m : ℕ) :
    gaussianMatrix p m =
      (Measure.pi fun _ : Fin p × Fin m => gaussianReal 0 1).map
        (MeasurableEquiv.curry (Fin p) (Fin m) ℝ) := by
  have := Measure.infinitePi_map_curry (fun (_ : Fin p) (_ : Fin m) => gaussianReal 0 1)
  simp only [Measure.infinitePi_eq_pi] at this
  rw [gaussianMatrix, this]

/-! ### Gaussian law -/

/-- A vector of independent standard normals has a Gaussian law. Ported from Prove2me solution
`GaussianMatrix.gordon_upper` (helper `gu_hasGaussianLaw_pi`). Atlas: `gaussian-matrix-def`. -/
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
`gu_hasGaussianLaw_id`). Atlas: `gaussian-matrix-def`. -/
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
`ssb_isGaussian_gm`). Atlas: `gaussian-matrix-def`.
atlas: gaussian-matrix-def -/
instance isGaussian_gaussianMatrix (p m : ℕ) : IsGaussian (gaussianMatrix p m) := by
  have := (hasGaussianLaw_id_gaussianMatrix p m).isGaussian_map
  rwa [Measure.map_id'] at this

/-! ### Measurability -/

/-- A random variable with law `gaussianMatrix n t` is a.e.-measurable. Atlas
`gaussian-matrix-def` (helper for `gaussian-conditioning`). -/
theorem aemeasurable_of_map_eq_gaussianMatrix {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n t : ℕ} {X : Ω → Fin n → Fin t → ℝ} (hX : μ.map X = gaussianMatrix n t) :
    AEMeasurable X μ :=
  AEMeasurable.of_map_ne_zero (by rw [hX]; exact IsProbabilityMeasure.ne_zero _)

/-- The block map `G ↦ Vᵀ G` (on the array view) is measurable. Atlas `gaussian-matrix-def`
(helper for `block-law-indep`, `gaussian-conditioning`). -/
theorem measurable_block {n k t : ℕ} (V : Matrix (Fin n) (Fin k) ℝ) :
    Measurable fun G : Fin n → Fin t → ℝ => Matrix.of.symm (Vᵀ * Matrix.of G) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply]
  fun_prop

end NLAlib
