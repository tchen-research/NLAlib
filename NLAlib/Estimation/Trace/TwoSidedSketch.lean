import NLAlib.Matrix.Norms.Frobenius
import NLAlib.ForMathlib.MeasureTheory.Matrix
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-!
# Centered errors of two-sided sketch corrections

The two-sided correction cancels the first-order errors of both sketches. Independent
entry-integrable sketches with identity means therefore give an unbiased estimator, without
Gaussian, symmetry or positivity assumptions.

Source: Chen--Halikias--Musco--Persson, Hutch#, equations (2) and (7); the centered
reformulation in `estimation-krylov-solvers-derivations-2026-10-26/estimation.tex`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {m n Ω : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The two-sided trace correction for a rectangular real matrix. -/
def twoSidedSketchEstimate (A : Matrix m n ℝ) (L : Matrix m m ℝ) (R : Matrix n n ℝ) : ℝ :=
  (Aᵀ * A * R).trace + (Aᵀ * L * A).trace - (Aᵀ * L * A * R).trace

/-- The error is the product of the two centered sketch errors. No symmetry is needed.
Source: Hutch#, equations (2), (7), by trace linearity.
atlas: two-sided-sketch-centered-error (partial) -/
theorem twoSidedSketchEstimate_sub_frobSq (A : Matrix m n ℝ)
    (L : Matrix m m ℝ) (R : Matrix n n ℝ) :
    twoSidedSketchEstimate A L R - frobSq A =
      -(Aᵀ * (L - 1) * A * (R - 1)).trace := by
  have hA : frobSq A = (Aᵀ * A).trace := by
    simpa using frobSq_eq_re_trace_conjTranspose_mul_self A
  simp only [twoSidedSketchEstimate, hA, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, Matrix.trace_sub]
  ring

omit [DecidableEq m] [DecidableEq n] in
private theorem trace_sandwich_eq_sum (A : Matrix m n ℝ)
    (L : Matrix m m ℝ) (R : Matrix n n ℝ) :
    (Aᵀ * L * A * R).trace =
      ∑ i, ∑ l, ∑ k, ∑ j, A j i * L j k * A k l * R l i := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq m] [DecidableEq n] [IsProbabilityMeasure μ] in
private theorem integrable_trace_sandwich (A : Matrix m n ℝ)
    {L : Ω → Matrix m m ℝ} {R : Ω → Matrix n n ℝ} (hind : IndepFun L R μ)
    (hL : ∀ i j, Integrable (fun ω => L ω i j) μ)
    (hR : ∀ i j, Integrable (fun ω => R ω i j) μ) :
    Integrable (fun ω => (Aᵀ * L ω * A * R ω).trace) μ := by
  simp_rw [trace_sandwich_eq_sum]
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => ?_
  have hij : IndepFun (fun ω => L ω j k) (fun ω => R ω l i) μ :=
    hind.comp (Matrix.measurable_entry j k) (Matrix.measurable_entry l i)
  have hi := (hij.integrable_mul (hL j k) (hR l i)).const_mul (A j i * A k l)
  exact hi.congr (ae_of_all _ fun ω => by simp only [Pi.mul_apply]; ring)

omit [DecidableEq m] [DecidableEq n] [IsProbabilityMeasure μ] in
private theorem integral_trace_sandwich_eq_zero (A : Matrix m n ℝ)
    {L : Ω → Matrix m m ℝ} {R : Ω → Matrix n n ℝ} (hind : IndepFun L R μ)
    (hL : ∀ i j, Integrable (fun ω => L ω i j) μ)
    (hR : ∀ i j, Integrable (fun ω => R ω i j) μ)
    (hzero : ∀ i j, ∫ ω, L ω i j ∂μ = 0) :
    ∫ ω, (Aᵀ * L ω * A * R ω).trace ∂μ = 0 := by
  have hint (i l : n) (k j : m) :
      Integrable (fun ω => A j i * L ω j k * A k l * R ω l i) μ := by
    have hij : IndepFun (fun ω => L ω j k) (fun ω => R ω l i) μ :=
      hind.comp (Matrix.measurable_entry j k) (Matrix.measurable_entry l i)
    have hi := (hij.integrable_mul (hL j k) (hR l i)).const_mul (A j i * A k l)
    exact hi.congr (ae_of_all _ fun ω => by simp only [Pi.mul_apply]; ring)
  simp_rw [trace_sandwich_eq_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hint i l k j]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun j _ => hint i l k j]
  apply Finset.sum_eq_zero
  intro l _
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hint i l k j]
  apply Finset.sum_eq_zero
  intro k _
  rw [integral_finsetSum _ fun j _ => hint i l k j]
  apply Finset.sum_eq_zero
  intro j _
  have hij : IndepFun (fun ω => L ω j k) (fun ω => R ω l i) μ :=
    hind.comp (Matrix.measurable_entry j k) (Matrix.measurable_entry l i)
  simp_rw [show ∀ ω, A j i * L ω j k * A k l * R ω l i =
    (A j i * A k l) * (L ω j k * R ω l i) by intro ω; ring]
  rw [integral_const_mul, hij.integral_fun_mul_eq_mul_integral
    (hL j k).aestronglyMeasurable (hR l i).aestronglyMeasurable, hzero]
  ring

/-- Independent sketches with integrable entries give an integrable unbiased correction
as soon as the left sketch has identity expectation. In particular both sketches may be
unbiased; no assumption on the right expectation is necessary. Empty dimensions are included.
Source: Hutch#, equations (2), (7), with independent product integration.
atlas: two-sided-sketch-centered-error (partial) -/
theorem integrable_and_integral_twoSidedSketchEstimate
    (A : Matrix m n ℝ) {L : Ω → Matrix m m ℝ} {R : Ω → Matrix n n ℝ}
    (hind : IndepFun L R μ)
    (hL : ∀ i j, Integrable (fun ω => L ω i j) μ)
    (hR : ∀ i j, Integrable (fun ω => R ω i j) μ)
    (hmeanL : ∀ i j, ∫ ω, L ω i j ∂μ = (1 : Matrix m m ℝ) i j) :
    Integrable (fun ω => twoSidedSketchEstimate A (L ω) (R ω)) μ ∧
      (∫ ω, twoSidedSketchEstimate A (L ω) (R ω) ∂μ) = frobSq A := by
  have hind' : IndepFun (fun ω => L ω - 1) (fun ω => R ω - 1) μ :=
    hind.comp (show Measurable (fun T : Matrix m m ℝ => T - 1) by fun_prop)
      (show Measurable (fun T : Matrix n n ℝ => T - 1) by fun_prop)
  have hL' (i j : m) : Integrable (fun ω => (L ω - 1) i j) μ :=
    (hL i j).sub (integrable_const _)
  have hR' (i j : n) : Integrable (fun ω => (R ω - 1) i j) μ :=
    (hR i j).sub (integrable_const _)
  have hz (i j : m) : ∫ ω, (L ω - 1) i j ∂μ = 0 := by
    simp only [Matrix.sub_apply, integral_sub (hL i j) (integrable_const _),
      integral_const, probReal_univ, one_smul, hmeanL, sub_self]
  have hi := integrable_trace_sandwich A hind' hL' hR'
  have he := integral_trace_sandwich_eq_zero A hind' hL' hR' hz
  have hid (ω : Ω) : twoSidedSketchEstimate A (L ω) (R ω) =
      frobSq A - (Aᵀ * (L ω - 1) * A * (R ω - 1)).trace := by
    linarith [twoSidedSketchEstimate_sub_frobSq A (L ω) (R ω)]
  simp_rw [hid]
  refine ⟨(integrable_const _).sub hi, ?_⟩
  rw [integral_sub (integrable_const _) hi, integral_const, probReal_univ, one_smul, he, sub_zero]

end NLAlib
