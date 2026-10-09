/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu

Ported from HighDimProb commit c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae,
HighDimProb/Concentration/HansonWright.lean, to Lean 4.33.1.
The original Apache-2.0 copyright notice is retained. Only the two used legacy
vocabulary definitions are supplied locally; there is no HighDimProb dependency.
-/
import NLAlib.Matrix.Norms
import NLAlib.Concentration.OrliczMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Hanson–Wright proof: Geometry

A focused leaf of the transported independent-coordinate proof.
Shared helper declarations live in `NLAlib.HansonWrightProof`; the canonical
public bounds are in `NLAlib.Estimation.HansonWright`.
Atlas: `hanson-wright`. Source: HighDimProb commit c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal Matrix.Norms.L2Operator

noncomputable section
set_option maxRecDepth 5000

namespace NLAlib
namespace HansonWrightProof

variable {Ω : Type*} [MeasurableSpace Ω]
/-- Proof-local double-sum form of the quadratic form, retained for source transport. -/
def matrixQuadraticForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : ℝ := ∑ i, ∑ j, x i * A i j * x j

/-- Proof-local name for Mathlib's actual Euclidean operator norm. -/
def deterministicOperatorNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ‖A‖

/-- Source-transport helper `real_inner_mul` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma real_inner_mul (a b : ℝ) : inner ℝ a b = a * b := by
  calc
    inner ℝ a b = inner ℝ (a • (1 : ℝ)) (b • (1 : ℝ)) := by simp
    _ = a * b * inner ℝ (1 : ℝ) (1 : ℝ) := by
      rw [real_inner_smul_left, real_inner_smul_right]
      simp
    _ = a * b := by norm_num

/-- Source-transport helper `mgf_innerSL_stdGaussian` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma mgf_innerSL_stdGaussian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (v : E) (t : ℝ) :
    mgf (fun x : E => inner ℝ v x) (stdGaussian E) t =
      exp (‖v‖ ^ 2 * t ^ 2 / 2) := by
  let L : StrongDual ℝ E := innerSL ℝ v
  have hmap : (stdGaussian E).map L =
      gaussianReal ((stdGaussian E)[L]) Var[L; stdGaussian E].toNNReal :=
    IsGaussian.map_eq_gaussianReal L
  have hmgf := mgf_gaussianReal hmap t
  have hmean : (stdGaussian E)[L] = 0 := integral_strongDual_stdGaussian L
  have hvar : (Var[L; stdGaussian E].toNNReal : ℝ) = ‖v‖ ^ 2 := by
    rw [variance_dual_stdGaussian L]
    simp [L, innerSL_apply_norm]
  change mgf (⇑L) (stdGaussian E) t = exp (‖v‖ ^ 2 * t ^ 2 / 2)
  rw [hmgf, hmean, hvar]
  ring_nf

/-- Source-transport helper `integrable_exp_innerSL_stdGaussian` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integrable_exp_innerSL_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : E) (t : ℝ) :
    Integrable (fun x : E => exp (t * inner ℝ v x)) (stdGaussian E) := by
  rw [← mgf_pos_iff]
  rw [mgf_innerSL_stdGaussian v t]
  exact exp_pos _

/-- Source-transport helper `integral_exp_innerSL_stdGaussian` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma integral_exp_innerSL_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : E) (t : ℝ) :
    ∫ x : E, exp (t * inner ℝ v x) ∂(stdGaussian E) =
      exp (‖v‖ ^ 2 * t ^ 2 / 2) := by
  exact mgf_innerSL_stdGaussian v t

/-- Source-transport helper `hasSubgaussianMGF_id_gaussianReal_zero_one` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma hasSubgaussianMGF_id_gaussianReal_zero_one :
    HasSubgaussianMGF id (1 : ℝ≥0) (gaussianReal 0 1) where
  integrable_exp_mul t := by
    simpa only [id_eq] using integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t
  mgf_le t := by
    rw [mgf_id_gaussianReal]
    simp only [zero_mul, NNReal.coe_one, one_mul, zero_add]
    rfl

/-- Source-transport helper `symmetric_inner_apply_eq_sum_eigenvalues_repr` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma symmetric_inner_apply_eq_sum_eigenvalues_repr {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (x : E) :
    inner ℝ (T x) x =
      ∑ i : Fin (Module.finrank ℝ E),
        hT.eigenvalues rfl i * ((hT.eigenvectorBasis rfl).repr x i) ^ 2 := by
  let b := hT.eigenvectorBasis (by rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  calc
    inner ℝ (T x) x = inner ℝ (b.repr (T x)) (b.repr x) := by
      rw [b.repr.inner_map_map]
    _ = ∑ i : Fin (Module.finrank ℝ E),
        hT.eigenvalues rfl i * ((hT.eigenvectorBasis rfl).repr x i) ^ 2 := by
      have hcoord :
          ∀ i : Fin (Module.finrank ℝ E),
            b.repr (T x) i = hT.eigenvalues rfl i * b.repr x i := by
        intro i
        simpa [b] using hT.eigenvectorBasis_apply_self_apply
          (by rfl : Module.finrank ℝ E = Module.finrank ℝ E) x i
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoord i]
      change inner ℝ ((hT.eigenvalues rfl i) • (b.repr x).ofLp i) ((b.repr x).ofLp i) = _
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [Real.norm_eq_abs, sq_abs, b]

/-- Source-transport helper `orthonormalBasis_repr_sum_smul` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma orthonormalBasis_repr_sum_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (z : Fin (Module.finrank ℝ E) → ℝ) (i : Fin (Module.finrank ℝ E)) :
    b.repr (∑ i, z i • b i) i = z i := by
  simp only [OrthonormalBasis.repr_apply_apply, inner_sum, inner_smul_right]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [b.inner_eq_zero hji.symm]
    simp
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The random quadratic form associated to a random vector `X`. -/
def randomQuadraticForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => matrixQuadraticForm A fun i => X i ω

/-- The coordinate random vector as an element of Euclidean space. -/
def randomVector {n : ℕ} (X : Fin n → Ω → ℝ) : Ω → EuclideanSpace ℝ (Fin n) :=
  fun ω => WithLp.toLp 2 fun i => X i ω

omit [MeasurableSpace Ω] in
/-- Source-transport helper `randomVector_apply` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
@[simp]
lemma randomVector_apply {n : ℕ} (X : Fin n → Ω → ℝ) (ω : Ω) (i : Fin n) :
    randomVector X ω i = X i ω := rfl

/-- Source-transport helper `randomVector_aemeasurable` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma randomVector_aemeasurable {μ : Measure Ω} {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    AEMeasurable (randomVector X) μ := by
  exact (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.comp_aemeasurable
    (aemeasurable_pi_lambda _ hX_meas)

omit [MeasurableSpace Ω] in
/-- Source-transport helper `measure_map_prod_map_of_aemeasurable` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma measure_map_prod_map_of_aemeasurable {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α → γ} {g : β → δ} (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) :
    (μ.map f).prod (ν.map g) =
      (μ.prod ν).map (fun p : α × β => (f p.1, g p.2)) := by
  let f' := hf.mk f
  let g' := hg.mk g
  have hf_map : μ.map f = μ.map f' := Measure.map_congr hf.ae_eq_mk
  have hg_map : ν.map g = ν.map g' := Measure.map_congr hg.ae_eq_mk
  have hpair :
      (fun p : α × β => (f p.1, g p.2)) =ᵐ[μ.prod ν]
        Prod.map f' g' := by
    exact
      ((Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp hf.ae_eq_mk).prodMk
        ((Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp hg.ae_eq_mk)
  calc
    (μ.map f).prod (ν.map g)
        = (μ.map f').prod (ν.map g') := by rw [hf_map, hg_map]
    _ = (μ.prod ν).map (Prod.map f' g') :=
        Measure.map_prod_map μ ν hf.measurable_mk hg.measurable_mk
    _ = (μ.prod ν).map (fun p : α × β => (f p.1, g p.2)) :=
        Measure.map_congr hpair.symm

/-- The centered random quadratic form `Xᵀ A X - E Xᵀ A X`. -/
def centeredQuadraticForm {n : ℕ} (μ : Measure Ω) (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => randomQuadraticForm A X ω - ∫ ω, randomQuadraticForm A X ω ∂μ

/-- The squared Frobenius norm of a finite real matrix. -/
def frobeniusNormSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- The Frobenius norm of a finite real matrix, computed from its entries. -/
def deterministicFrobeniusNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sqrt (frobeniusNormSq A)

/-- The entrywise `ℓ¹` norm of a finite real matrix. -/
def entrywiseL1Norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, |A i j|

/-- The matrix obtained by deleting the diagonal entries. -/
def offDiagonalMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 0 else A i j

/-- The matrix keeping only rows in `s` and columns outside `s`. -/
def cutMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i ∈ s ∧ j ∉ s then A i j else 0

/-- Coordinate projection onto a finite set of coordinates. -/
def coordinateMask {n : ℕ} (s : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => if i ∈ s then x i else 0

/-- Source-transport helper `coordinateMask_apply` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
@[simp]
lemma coordinateMask_apply {n : ℕ} (s : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    coordinateMask s x i = if i ∈ s then x i else 0 := rfl

/-- Embed a tuple indexed by a finite set into Euclidean space, filling other coordinates by zero. -/
def subtypeMask {n : ℕ} (s : Finset (Fin n)) (x : s → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => if h : i ∈ s then x ⟨i, h⟩ else 0

/-- Source-transport helper `subtypeMask_apply` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
@[simp]
lemma subtypeMask_apply {n : ℕ} (s : Finset (Fin n)) (x : s → ℝ) (i : Fin n) :
    subtypeMask s x i = if h : i ∈ s then x ⟨i, h⟩ else 0 := rfl

/-- Source-transport helper `measurable_subtypeMask` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma measurable_subtypeMask {n : ℕ} (s : Finset (Fin n)) :
    Measurable (subtypeMask (n := n) s) := by
  exact (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.comp
    (measurable_pi_lambda _ fun i => by
      by_cases hi : i ∈ s
      · simpa [hi] using
          (measurable_pi_apply (⟨i, hi⟩ : s) : Measurable fun x : s → ℝ => x ⟨i, hi⟩)
      · simp [hi])

omit [MeasurableSpace Ω] in
/-- Source-transport helper `subtypeMask_subtype_randomVector` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma subtypeMask_subtype_randomVector {n : ℕ} (s : Finset (Fin n))
    (X : Fin n → Ω → ℝ) :
    (fun ω => subtypeMask s (fun i : s => X i ω)) =
      fun ω => coordinateMask s (randomVector X ω) := by
  ext ω i
  by_cases hi : i ∈ s
  · simp [hi]
  · simp [hi]

/-- Source-transport helper `coordinateMask_aemeasurable` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma coordinateMask_aemeasurable {μ : Measure Ω} {n : ℕ} (s : Finset (Fin n))
    {X : Fin n → Ω → ℝ} (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    AEMeasurable (fun ω => coordinateMask s (randomVector X ω)) μ := by
  rw [← subtypeMask_subtype_randomVector s X]
  exact (measurable_subtypeMask s).aemeasurable.comp_aemeasurable
    (aemeasurable_pi_lambda _ fun i => hX_meas i)

/-- Source-transport helper `coordinateMask_indepFun_compl` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma coordinateMask_indepFun_compl {μ : Measure Ω} {n : ℕ} {X : Fin n → Ω → ℝ}
    (h_indep : iIndepFun X μ) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (s : Finset (Fin n)) :
    (fun ω => coordinateMask ((Finset.univ : Finset (Fin n)) \ s) (randomVector X ω))
      ⟂ᵢ[μ]
    (fun ω => coordinateMask s (randomVector X ω)) := by
  classical
  let t : Finset (Fin n) := (Finset.univ : Finset (Fin n)) \ s
  have hdisj : Disjoint t s := by
    dsimp [t]
    exact Finset.sdiff_disjoint
  have hblocks :
      (fun ω (i : t) => X i ω) ⟂ᵢ[μ] (fun ω (i : s) => X i ω) :=
    h_indep.indepFun_finset₀ t s hdisj hX_meas
  have hcomp :
      ((subtypeMask t) ∘ fun ω (i : t) => X i ω) ⟂ᵢ[μ]
        ((subtypeMask s) ∘ fun ω (i : s) => X i ω) :=
    hblocks.comp (measurable_subtypeMask t) (measurable_subtypeMask s)
  refine hcomp.congr ?_ ?_
  · filter_upwards with ω
    ext i
    by_cases hi : i ∈ t
    · simp [t, coordinateMask, subtypeMask]
    · simp [t, coordinateMask, subtypeMask]
  · filter_upwards with ω
    ext i
    by_cases hi : i ∈ s
    · simp [coordinateMask, subtypeMask, hi]
    · simp [coordinateMask, subtypeMask, hi]

/-- Source-transport helper `frobeniusNormSq_nonneg` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma frobeniusNormSq_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ frobeniusNormSq A := by
  unfold frobeniusNormSq
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Source-transport helper `frobeniusNorm_nonneg` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma frobeniusNorm_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ deterministicFrobeniusNorm A :=
  sqrt_nonneg _

/-- Source-transport helper `operatorNorm_nonneg` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma operatorNorm_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ deterministicOperatorNorm A :=
  norm_nonneg _

/-- Source-transport helper `entrywiseL1Norm_nonneg` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma entrywiseL1Norm_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ entrywiseL1Norm A := by
  unfold entrywiseL1Norm
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Source-transport helper `coordinateMask_norm_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma coordinateMask_norm_le {n : ℕ} (s : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖coordinateMask s x‖ ≤ ‖x‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  calc
    ‖coordinateMask s x‖ ^ 2
        = ∑ i : Fin n, (coordinateMask s x i) ^ 2 := by
            rw [EuclideanSpace.real_norm_sq_eq]
    _ ≤ ∑ i : Fin n, x i ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hi : i ∈ s
        · simp [hi]
        · simp [hi, sq_nonneg]
    _ = ‖x‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]

/-- Source-transport helper `toEuclideanCLM_cutMatrix_apply` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma toEuclideanCLM_cutMatrix_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s : Finset (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (cutMatrix A s) x =
      coordinateMask s
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A
          (coordinateMask ((Finset.univ : Finset (Fin n)) \ s) x)) := by
  ext i
  by_cases hi : i ∈ s
  · simp [Matrix.toEuclideanCLM_toLp, coordinateMask, cutMatrix, Matrix.mulVec, dotProduct, hi]
  · simp [Matrix.toEuclideanCLM_toLp, coordinateMask, cutMatrix, Matrix.mulVec, dotProduct, hi]

/-- Source-transport helper `inner_toEuclideanCLM_cutMatrix_eq_inner_masks` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma inner_toEuclideanCLM_cutMatrix_eq_inner_masks {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (s : Finset (Fin n))
    (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (cutMatrix A s) x) y =
      inner ℝ
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A
          (coordinateMask ((Finset.univ : Finset (Fin n)) \ s) x))
        (coordinateMask s y) := by
  rw [toEuclideanCLM_cutMatrix_apply]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [coordinateMask_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ s
  · simp [hi]
  · simp [hi]

/-- Source-transport helper `operatorNorm_cutMatrix_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma operatorNorm_cutMatrix_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s : Finset (Fin n)) :
    deterministicOperatorNorm (cutMatrix A s) ≤ deterministicOperatorNorm A := by
  unfold deterministicOperatorNorm
  let T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) A
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x => ?_
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cutMatrix A s) x‖ ≤ ‖T‖ * ‖x‖
  rw [toEuclideanCLM_cutMatrix_apply]
  calc
    ‖coordinateMask s (T (coordinateMask ((Finset.univ : Finset (Fin n)) \ s) x))‖
        ≤ ‖T (coordinateMask ((Finset.univ : Finset (Fin n)) \ s) x)‖ :=
          coordinateMask_norm_le s _
    _ ≤ ‖T‖ * ‖coordinateMask ((Finset.univ : Finset (Fin n)) \ s) x‖ :=
          T.le_opNorm _
    _ ≤ ‖T‖ * ‖x‖ :=
          mul_le_mul_of_nonneg_left
            (coordinateMask_norm_le ((Finset.univ : Finset (Fin n)) \ s) x) (norm_nonneg T)

/-- Source-transport helper `frobeniusNormSq_cutMatrix_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma frobeniusNormSq_cutMatrix_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s : Finset (Fin n)) :
    frobeniusNormSq (cutMatrix A s) ≤ frobeniusNormSq A := by
  unfold frobeniusNormSq cutMatrix
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases h : i ∈ s ∧ j ∉ s
  · simp [h]
  · simp [h, sq_nonneg]

/-- Source-transport helper `frobeniusNorm_sq` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma frobeniusNorm_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    deterministicFrobeniusNorm A ^ 2 = frobeniusNormSq A := by
  unfold deterministicFrobeniusNorm
  rw [sq_sqrt (frobeniusNormSq_nonneg A)]

/-- Source-transport helper `frobeniusNorm_cutMatrix_sq_le` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma frobeniusNorm_cutMatrix_sq_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s : Finset (Fin n)) :
    deterministicFrobeniusNorm (cutMatrix A s) ^ 2 ≤ deterministicFrobeniusNorm A ^ 2 := by
  rw [frobeniusNorm_sq, frobeniusNorm_sq]
  exact frobeniusNormSq_cutMatrix_le A s

/-- Source-transport helper `card_powerset_filter_mem_notMem_eq` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma card_powerset_filter_mem_notMem_eq {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (((Finset.univ : Finset (Fin n)).powerset.filter
      (fun s => i ∈ s ∧ j ∉ s)).card) =
      (((((Finset.univ : Finset (Fin n)).erase i).erase j).powerset).card) := by
  classical
  let S : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powerset.filter (fun s => i ∈ s ∧ j ∉ s)
  let T : Finset (Finset (Fin n)) :=
    (((Finset.univ : Finset (Fin n)).erase i).erase j).powerset
  change S.card = T.card
  refine Finset.card_nbij' (fun u => u.erase i) (fun u => insert i u) ?_ ?_ ?_ ?_
  · intro u hu
    have hu' :
        u ∈ (Finset.univ : Finset (Fin n)).powerset.filter
          (fun s => i ∈ s ∧ j ∉ s) := by
      simpa [S] using hu
    dsimp [T]
    change u.erase i ∈ ((((Finset.univ : Finset (Fin n)).erase i).erase j).powerset)
    rw [Finset.mem_filter, Finset.mem_powerset] at hu'
    rw [Finset.mem_powerset]
    intro k hk
    rw [Finset.mem_erase] at hk ⊢
    refine ⟨?_, ?_⟩
    · intro hkj
      exact hu'.2.2 (by simpa [hkj] using hk.2)
    · rw [Finset.mem_erase]
      exact ⟨hk.1, Finset.mem_univ k⟩
  · intro u hu
    have hu_set : (u : Set (Fin n)) ⊆ (Set.univ \ {i}) \ {j} := by
      simpa [T, Finset.mem_powerset] using hu
    have hu_sub : u ⊆ (((Finset.univ : Finset (Fin n)).erase i).erase j) := by
      intro k hk
      have hkset := hu_set hk
      rw [Finset.mem_erase, Finset.mem_erase]
      simp at hkset
      exact ⟨hkset.2, hkset.1, Finset.mem_univ k⟩
    dsimp [S]
    change insert i u ∈
      ((Finset.univ : Finset (Fin n)).powerset.filter (fun s => i ∈ s ∧ j ∉ s))
    rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro k hk
      exact Finset.mem_univ k
    · constructor
      · exact Finset.mem_insert_self i u
      · intro hju
        rw [Finset.mem_insert] at hju
        rcases hju with hji | hju
        · exact hij hji.symm
        · have hj_erase := hu_sub hju
          exact (Finset.mem_erase.mp hj_erase).1 rfl
  · intro u hu
    have hu' :
        u ∈ (Finset.univ : Finset (Fin n)).powerset.filter
          (fun s => i ∈ s ∧ j ∉ s) := by
      simpa [S] using hu
    rw [Finset.mem_filter] at hu'
    exact Finset.insert_erase hu'.2.1
  · intro u hu
    dsimp [T] at hu
    have hi_not : i ∉ u := by
      intro hiu
      have hi_erase := (Finset.mem_powerset.mp hu) hiu
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hi_erase).2).1 rfl
    exact Finset.erase_insert hi_not

end HansonWrightProof
end NLAlib
