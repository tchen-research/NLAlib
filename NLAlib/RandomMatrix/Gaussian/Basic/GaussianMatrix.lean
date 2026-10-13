import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.HasLaw
import Mathlib.Probability.ProductMeasure
import NLAlib.ForMathlib.MeasureTheory.Matrix
import NLAlib.Probability.Gaussian.Basic.StandardVector
import NLAlib.Matrix.Norms.Core

/-!
# Standard Gaussian matrices

`NLAlib.gaussianMatrix m n` is the law of an `m × n` real matrix with i.i.d. `N(0,1)` entries: the
product measure on `m → n → ℝ` pushed to `Matrix m n ℝ` by `Matrix.of` (a measurable equivalence
for `Matrix.instMeasurableSpace`, `NLAlib.ForMathlib.MeasureTheory.Matrix`). A random
matrix is `X : Ω → Matrix m n ℝ`, and "`X` is a standard Gaussian matrix under `μ`" is Mathlib's
`HasLaw X (gaussianMatrix m n) μ`. The `p × m` matrices of the Gaussian Random Matrices series
are `gaussianMatrix (Fin p) (Fin m)`.

The file holds the definition and its unfolding-level API:

* `measurePreserving_ofMeasurableEquiv_gaussianMatrix`: the definition, `Matrix.of` pushes the
  product measure on `m → n → ℝ` to `gaussianMatrix m n`; `integral_gaussianMatrix_eq`,
  `integrable_gaussianMatrix_iff`: integrals and integrability move to the product measure;
* `measurePreserving_gaussianMatrix_entry`, `memLp_gaussianMatrix_entry`: each entry is `N(0,1)`;
* `iIndepFun_gaussianMatrix_entry`: the entries are independent;
  `measurePreserving_gaussianMatrix_row`, `iIndepFun_gaussianMatrix_row`: the rows are independent
  standard Gaussian vectors;
* `integral_comp_gaussianMatrix_entry_eq`, `integral_gaussianMatrix_entry_eq_zero`,
  `integral_gaussianMatrix_entry_sq_eq_one`, `integral_gaussianMatrix_entry_mul`:
  `E f(G_ab) = ∫ f dN(0,1)`, `E G_ab = 0`, `E G_ab² = 1`, `E[G_ab G_cd] = δ_ac δ_bd`;
* `gaussianMatrix_map_uncurry`,
  `gaussianMatrix_eq_map_curry`: flattening gives the product measure on `m × n → ℝ`, and
  conversely;
* the instance `isGaussian_gaussianMatrix` and `hasGaussianLaw_id_gaussianMatrix`: the law is a
  Gaussian measure (from `hasGaussianLaw_id_pi_gaussianReal`,
  `NLAlib.Probability.Gaussian.Basic.StandardVector`);
* `linForm c G = ∑ᵢⱼ cᵢⱼ Gᵢⱼ`, the linear forms of a Gaussian matrix, with `linForm_eq_frobInner`
  and `continuous_linForm`;
* `measurable_block`: measurability of the block map `G ↦ Vᵀ G`.

Foundation change F2 (`docs/FOUNDATIONS_BRIEF.md` §2): the law used to live on arrays
`Fin p → Fin m → ℝ` with `Matrix.of` as the matrix view.

Atlas: `gaussian-matrix-def`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Law of an `m × n` matrix with independent standard Gaussian entries: the product measure
`⊗ᵢ ⊗ⱼ N(0,1)` on the array type `m → n → ℝ`, pushed to `Matrix m n ℝ` by `Matrix.of`.
Atlas: `gaussian-matrix-def`.
atlas: gaussian-matrix-def -/
def gaussianMatrix (m n : Type*) [Fintype m] [Fintype n] : Measure (Matrix m n ℝ) :=
  (Measure.pi fun _ : m => Measure.pi fun _ : n => gaussianReal 0 1).map Matrix.ofMeasurableEquiv

/-- `Matrix.of` carries the product of i.i.d. Gaussian rows on the array type `m → n → ℝ` to
`gaussianMatrix m n`; with `MeasurePreserving.integral_comp'` this turns an integral against
`gaussianMatrix m n` into one against the product measure. Atlas: `gaussian-matrix-def`. -/
theorem measurePreserving_ofMeasurableEquiv_gaussianMatrix :
    MeasurePreserving (Matrix.ofMeasurableEquiv : (m → n → ℝ) ≃ᵐ Matrix m n ℝ)
      (Measure.pi fun _ : m => Measure.pi fun _ : n => gaussianReal 0 1) (gaussianMatrix m n) :=
  ⟨Matrix.ofMeasurableEquiv.measurable, rfl⟩

/-- An integral against `gaussianMatrix m n` is an integral against the product measure on the
array type `m → n → ℝ`. Atlas: `gaussian-matrix-def`. -/
theorem integral_gaussianMatrix_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Matrix m n ℝ → E) :
    ∫ G, F G ∂(gaussianMatrix m n) =
      ∫ x, F (Matrix.of x) ∂(Measure.pi fun _ : m => Measure.pi fun _ : n => gaussianReal 0 1) :=
  (measurePreserving_ofMeasurableEquiv_gaussianMatrix.integral_comp' F).symm

/-- Integrability against `gaussianMatrix m n` is integrability against the product measure on the
array type `m → n → ℝ`. Atlas: `gaussian-matrix-def`. -/
theorem integrable_gaussianMatrix_iff {E : Type*} [NormedAddCommGroup E] {F : Matrix m n ℝ → E} :
    Integrable F (gaussianMatrix m n) ↔
      Integrable (fun x => F (Matrix.of x))
        (Measure.pi fun _ : m => Measure.pi fun _ : n => gaussianReal 0 1) :=
  (measurePreserving_ofMeasurableEquiv_gaussianMatrix.integrable_comp_emb
    Matrix.ofMeasurableEquiv.measurableEmbedding).symm

/-- `gaussianMatrix m n` is a probability measure. Atlas: `gaussian-matrix-def`. -/
instance isProbabilityMeasure_gaussianMatrix (m n : Type*) [Fintype m] [Fintype n] :
    IsProbabilityMeasure (gaussianMatrix m n) := by
  unfold gaussianMatrix
  exact Measure.isProbabilityMeasure_map Matrix.ofMeasurableEquiv.measurable.aemeasurable

/-! ### Entries of a Gaussian matrix -/

/-- Each entry of a standard Gaussian matrix is `N(0,1)`. Atlas: `gaussian-matrix-def`. -/
theorem measurePreserving_gaussianMatrix_entry (a : m) (b : n) :
    MeasurePreserving (fun G : Matrix m n ℝ => G a b) (gaussianMatrix m n)
      (gaussianReal 0 1) :=
  ((measurePreserving_eval (fun _ : n => gaussianReal 0 1) b).comp
    (measurePreserving_eval (fun _ : m => Measure.pi fun _ : n => gaussianReal 0 1) a)).comp
    measurePreserving_ofMeasurableEquiv_gaussianMatrix.symm

/-- Each row of a standard Gaussian matrix is a standard Gaussian vector. Atlas:
`gaussian-matrix-def`. -/
theorem measurePreserving_gaussianMatrix_row (a : m) :
    MeasurePreserving (fun G : Matrix m n ℝ => G a) (gaussianMatrix m n)
      (Measure.pi fun _ : n => gaussianReal 0 1) :=
  (measurePreserving_eval (fun _ : m => Measure.pi fun _ : n => gaussianReal 0 1) a).comp
    measurePreserving_ofMeasurableEquiv_gaussianMatrix.symm

/-- The rows of a standard Gaussian matrix are independent. Atlas: `gaussian-matrix-def`. -/
theorem iIndepFun_gaussianMatrix_row :
    iIndepFun (fun (a : m) (G : Matrix m n ℝ) => G a) (gaussianMatrix m n) := by
  have hrowm : ∀ a : m, Measurable fun G : Matrix m n ℝ => G a := fun a =>
    measurable_pi_lambda _ fun j => Matrix.measurable_entry a j
  refine (iIndepFun_iff_map_fun_eq_pi_map (f := fun (a : m) (G : Matrix m n ℝ) => G a)
    (fun a => (hrowm a).aemeasurable)).mpr ?_
  simp_rw [(measurePreserving_gaussianMatrix_row _).map_eq]
  exact measurePreserving_ofMeasurableEquiv_gaussianMatrix.symm.map_eq

/-- Each entry of a standard Gaussian matrix has finite moments of every finite order.
Atlas: `gaussian-matrix-def`. -/
theorem memLp_gaussianMatrix_entry (a : m) (b : n) (q : ENNReal) (hq : q ≠ ⊤) :
    MemLp (fun G : Matrix m n ℝ => G a b) q (gaussianMatrix m n) :=
  (memLp_id_gaussianReal' q hq).comp_measurePreserving
    (measurePreserving_gaussianMatrix_entry a b)

/-! ### Flattening -/

/-- Flattening a standard Gaussian matrix gives i.i.d. standard Gaussians indexed by
`m × n`. Atlas: `gaussian-matrix-def`. -/
theorem gaussianMatrix_map_uncurry :
    Measure.map (fun G : Matrix m n ℝ => fun ab : m × n => G ab.1 ab.2)
      (gaussianMatrix m n) = Measure.pi fun _ : m × n => gaussianReal 0 1 := by
  have hmeas : Measurable fun G : Matrix m n ℝ => fun ab : m × n => G ab.1 ab.2 :=
    measurable_pi_lambda _ fun ab => Matrix.measurable_entry ab.1 ab.2
  have harr : Measure.map (fun G : m → n → ℝ => fun ab : m × n => G ab.1 ab.2)
      (Measure.pi fun _ : m => Measure.pi fun _ : n => gaussianReal 0 1) =
      Measure.pi fun _ : m × n => gaussianReal 0 1 := by
    symm
    have hmeas' : Measurable fun G : m → n → ℝ => fun ab : m × n => G ab.1 ab.2 :=
      measurable_pi_lambda _ fun ab => (measurable_pi_apply ab.2).comp (measurable_pi_apply ab.1)
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hmeas' (MeasurableSet.univ_pi hs)]
    have hpre : (fun G : m → n → ℝ => fun ab : m × n => G ab.1 ab.2) ⁻¹'
        Set.univ.pi s = Set.univ.pi fun a => Set.univ.pi fun b => s (a, b) := by
      ext G
      simp only [Set.mem_preimage, Set.mem_univ_pi, Prod.forall]
    rw [hpre, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  rw [gaussianMatrix, Measure.map_map hmeas Matrix.ofMeasurableEquiv.measurable]
  exact harr

/-- A standard Gaussian matrix is the currying of i.i.d. standard Gaussians indexed by
`m × n` (the converse of `gaussianMatrix_map_uncurry`). Atlas: `gaussian-matrix-def`. -/
theorem gaussianMatrix_eq_map_curry :
    gaussianMatrix m n =
      (Measure.pi fun _ : m × n => gaussianReal 0 1).map
        ((MeasurableEquiv.curry m n ℝ).trans Matrix.ofMeasurableEquiv) := by
  have := Measure.infinitePi_map_curry (fun (_ : m) (_ : n) => gaussianReal 0 1)
  simp only [Measure.infinitePi_eq_pi] at this
  rw [gaussianMatrix, ← this, Measure.map_map Matrix.ofMeasurableEquiv.measurable
    (MeasurableEquiv.curry m n ℝ).measurable]
  rfl

/-- The entries of a standard Gaussian matrix are independent. Atlas: `gaussian-matrix-def`. -/
theorem iIndepFun_gaussianMatrix_entry :
    iIndepFun (fun (ab : m × n) (G : Matrix m n ℝ) => G ab.1 ab.2) (gaussianMatrix m n) := by
  refine (iIndepFun_iff_map_fun_eq_pi_map
    (f := fun (ab : m × n) (G : Matrix m n ℝ) => G ab.1 ab.2)
    (fun ab => (Matrix.measurable_entry ab.1 ab.2).aemeasurable)).mpr ?_
  refine gaussianMatrix_map_uncurry.trans ?_
  congr 1
  funext ab
  exact (measurePreserving_gaussianMatrix_entry ab.1 ab.2).map_eq.symm

/-! ### Moments of the entries -/

/-- `𝔼 f(Gᵢⱼ) = ∫ f dN(0,1)` for measurable `f`. Ported from Prove2me solution
`GaussianMatrix.gordon_upper` (helper `gu_integral_comp_coord`). Atlas: `gaussian-matrix-def`. -/
theorem integral_comp_gaussianMatrix_entry_eq (a : m) (b : n) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ G, f (G a b) ∂(gaussianMatrix m n) = ∫ x, f x ∂(gaussianReal 0 1) := by
  rw [← (measurePreserving_gaussianMatrix_entry a b).map_eq, integral_map]
  · exact (measurePreserving_gaussianMatrix_entry a b).measurable.aemeasurable
  · exact hf.aestronglyMeasurable

/-- `𝔼 Gᵢⱼ = 0`. Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper
`gu_integral_coord`). Atlas: `gaussian-matrix-def`. -/
theorem integral_gaussianMatrix_entry_eq_zero (a : m) (b : n) :
    ∫ G, G a b ∂(gaussianMatrix m n) = 0 := by
  have := integral_comp_gaussianMatrix_entry_eq a b (fun x => x) measurable_id
  simpa [integral_id_gaussianReal] using this

/-- `𝔼 Gᵢⱼ² = 1`. Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper
`gu_integral_coord_sq`). Atlas: `gaussian-matrix-def`. -/
theorem integral_gaussianMatrix_entry_sq_eq_one (a : m) (b : n) :
    ∫ G, G a b ^ 2 ∂(gaussianMatrix m n) = 1 := by
  rw [integral_comp_gaussianMatrix_entry_eq a b (fun x => x ^ 2) (by fun_prop)]
  have h := variance_eq_sub (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp))
  rw [variance_id_gaussianReal] at h
  simp [integral_id_gaussianReal] at h
  exact h.symm

/-- `k Gᵢⱼ Gₖₗ` is integrable. Ported from Prove2me solution `GaussianMatrix.gordon_upper`
(helper `gu_integrable_coord_mul`). Atlas: `gaussian-matrix-def`. -/
theorem integrable_const_mul_gaussianMatrix_entry_mul (a c : m) (b d : n) (k : ℝ) :
    Integrable (fun G : Matrix m n ℝ => k * (G a b * G c d)) (gaussianMatrix m n) :=
  ((memLp_gaussianMatrix_entry a b 2 (by simp)).integrable_mul
    (memLp_gaussianMatrix_entry c d 2 (by simp))).const_mul k

/-- Second moments of the entries of a standard Gaussian matrix:
`E[G_ab G_cd] = δ_ac δ_bd`. Atlas: `gaussian-matrix-def` (used for
`gaussian-frob-second-moment`). -/
theorem integral_gaussianMatrix_entry_mul [DecidableEq m] [DecidableEq n] (a c : m) (b d : n) :
    ∫ G, G a b * G c d ∂(gaussianMatrix m n) = if a = c ∧ b = d then 1 else 0 := by
  by_cases h : (a, b) = (c, d)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simpa [← pow_two] using integral_gaussianMatrix_entry_sq_eq_one a b
  · have hne : ¬(a = c ∧ b = d) := fun h' => h (by rw [h'.1, h'.2])
    simp only [hne, if_false]
    have := (iIndepFun_gaussianMatrix_entry.indepFun h).integral_fun_mul_eq_mul_integral
      (Matrix.measurable_entry a b).aestronglyMeasurable
      (Matrix.measurable_entry c d).aestronglyMeasurable
    rw [this, integral_gaussianMatrix_entry_eq_zero, zero_mul]

/-! ### Gaussian law -/

/-- The law of a standard Gaussian matrix is a Gaussian measure on `Matrix m n ℝ`.
Ported from Prove2me solution `GaussianMatrix.spectral_second_moment_bound` (instance
`ssb_isGaussian_gm`). Atlas: `gaussian-matrix-def`.
atlas: gaussian-matrix-def -/
instance isGaussian_gaussianMatrix (m n : Type*) [Fintype m] [Fintype n] :
    IsGaussian (gaussianMatrix m n) := by
  have h := iIndepFun.hasGaussianLaw
    (P := Measure.pi fun _ : m => Measure.pi fun _ : n => gaussianReal (0 : ℝ) 1)
    (X := fun i (G : m → n → ℝ) => G i) (fun i => ⟨by
      rw [(measurePreserving_eval
        (fun _ : m => Measure.pi fun _ : n => gaussianReal (0 : ℝ) 1) i).map_eq]
      have := (hasGaussianLaw_id_pi_gaussianReal n).isGaussian_map
      rwa [Measure.map_id'] at this⟩)
    (iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id))
  have hpi := h.isGaussian_map
  rw [Measure.map_id'] at hpi
  let L : (m → n → ℝ) →L[ℝ] Matrix m n ℝ :=
    { toLinearMap := (Matrix.ofLinearEquiv ℝ).toLinearMap, cont := continuous_id }
  have hL : gaussianMatrix m n =
      (Measure.pi fun _ : m => Measure.pi fun _ : n => gaussianReal (0 : ℝ) 1).map L := rfl
  rw [hL]
  have := hpi
  exact isGaussian_map_of_measurable (L := L) Matrix.measurable_of

/-- A standard Gaussian matrix has a Gaussian law (as a random element of `Matrix m n ℝ`).
Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper `gu_hasGaussianLaw_id`).
Atlas: `gaussian-matrix-def`. -/
theorem hasGaussianLaw_id_gaussianMatrix (m n : Type*) [Fintype m] [Fintype n] :
    HasGaussianLaw (fun G : Matrix m n ℝ => G) (gaussianMatrix m n) :=
  ⟨by rw [Measure.map_id']; infer_instance⟩

/-! ### Measurability -/

/-- The block map `G ↦ Vᵀ G` is measurable. Atlas `gaussian-matrix-def`
(helper for `block-law-indep`, `gaussian-conditioning`). -/
theorem measurable_block {k t : Type*} [Fintype k] (V : Matrix m k ℝ) :
    Measurable fun G : Matrix m t ℝ => Vᵀ * G :=
  measurable_const.matrix_mul measurable_id

/-! ### Linear forms -/

/-- The linear form `⟨c, G⟩ = ∑ᵢⱼ cᵢⱼ Gᵢⱼ` on `Matrix m n ℝ` (the space carrying
`gaussianMatrix m n`), with coefficient array `c : m → n → ℝ`; equal to
`frobInner (Matrix.of c) G` (`linForm_eq_frobInner`).
Ported from Prove2me solution `GaussianMatrix.gordon_upper` (`guLin`). -/
noncomputable def linForm (c : m → n → ℝ) (G : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * G i j

/-- Bridge to the Frobenius inner product. -/
theorem linForm_eq_frobInner (c : m → n → ℝ) (G : Matrix m n ℝ) :
    linForm c G = frobInner (Matrix.of c) G := rfl

/-- `G ↦ ⟨c, G⟩` is continuous. Ported from Prove2me solution `GaussianMatrix.gordon_upper`
(helper `gu_continuous_lin`). -/
theorem continuous_linForm (c : m → n → ℝ) : Continuous (linForm c) := by
  unfold linForm; fun_prop

end NLAlib
