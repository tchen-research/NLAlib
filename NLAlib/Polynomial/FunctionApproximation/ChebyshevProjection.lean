import NLAlib.ForMathlib.Analysis.DirichletKernelBounds
import NLAlib.Polynomial.FunctionApproximation.FejerChebyshev
import NLAlib.Polynomial.BestApproximation.MinimaxError
import Mathlib.Topology.Order.ProjIcc

/-!
# Chebyshev projection and its sharp logarithmic norm bound

The genuine coefficient truncation defines a bounded projection on continuous
functions on the unit interval. Its Dirichlet kernel supplies the sharp logarithmic
upper bound and the corresponding near-best approximation estimate.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev Finset Real Set MeasureTheory
open scoped NLAlib.TwoPi

namespace NLAlib

/-- Chebyshev coefficients depend only on the unit-interval restriction.
Source: the actual cosine integral; helper for `chebyshev-projection-lebesgue-constant`. -/
theorem chebyshevCoeff_congr {f g : ℝ → ℝ} (hfg : EqOn f g (Icc (-1 : ℝ) 1)) (k : ℕ) :
    chebyshevCoeff f k = chebyshevCoeff g k := by
  simp only [chebyshevCoeff_eq_cosine_integral]
  rw [intervalIntegral.integral_congr (fun θ _ =>
    congrArg (fun y => y * cos ((k : ℝ) * θ))
      (hfg ⟨neg_one_le_cos θ, cos_le_one θ⟩))]

/-- Genuine Chebyshev truncations depend only on the unit-interval restriction.
Source: the actual coefficient integrals; helper for `chebyshev-projection-lebesgue-constant`. -/
theorem chebyshevTrunc_congr {f g : ℝ → ℝ} (hfg : EqOn f g (Icc (-1 : ℝ) 1)) (n : ℕ) :
    chebyshevTrunc f n = chebyshevTrunc g n := by
  simp only [chebyshevTrunc, chebyshevCoeff_congr hfg]

/-- Chebyshev projection on continuous unit-interval functions is the restriction
of their genuine coefficient truncation. Clamping provides a canonical extension
whose values outside the interval do not affect any coefficient.
Source: Trefethen, ATAP, Chapters 3 and 15. -/
def chebyshevProjectionLinearMap (n : ℕ) :
    C(Icc (-1 : ℝ) 1, ℝ) →ₗ[ℝ] C(Icc (-1 : ℝ) 1, ℝ) where
  toFun f := (chebyshevTrunc (IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f) n).toContinuousMapOn _
  map_add' f g := by
    ext x
    have hf : ContinuousOn (IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f) (Icc (-1 : ℝ) 1) :=
      f.continuous.Icc_extend'.continuousOn
    have hg : ContinuousOn (IccExtend (by norm_num : (-1 : ℝ) ≤ 1) g) (Icc (-1 : ℝ) 1) :=
      g.continuous.Icc_extend'.continuousOn
    change (chebyshevTrunc (fun y => IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f y +
      IccExtend (by norm_num : (-1 : ℝ) ≤ 1) g y) n).eval (x : ℝ) = _
    simp only [chebyshevTrunc, chebyshevCoeff_add hf hg, eval_finsetSum,
      eval_mul, eval_C, ContinuousMap.add_apply, toContinuousMapOn_apply,
      toContinuousMap_apply, add_mul, sum_add_distrib]
  map_smul' c f := by
    ext x
    change (chebyshevTrunc (fun y => c * IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f y) n).eval (x : ℝ) = _
    simp only [chebyshevTrunc, chebyshevCoeff_const_mul, eval_finsetSum,
      eval_mul, eval_C, ContinuousMap.smul_apply, smul_eq_mul,
      toContinuousMapOn_apply, toContinuousMap_apply, mul_assoc, mul_sum, RingHom.id_apply]

/-- The coefficient projection fixes every polynomial of degree at most its cutoff.
Source: exact finite Chebyshev reconstruction; ATAP, Chapter 15. -/
theorem chebyshevProjectionLinearMap_eq_self (n : ℕ)
    (p : C(Icc (-1 : ℝ) 1, ℝ)) (hp : p ∈ polynomialApproximationSpace (Icc (-1 : ℝ) 1) n) :
    chebyshevProjectionLinearMap n p = p := by
  obtain ⟨q, hq, rfl⟩ := mem_polynomialApproximationSpace_iff.mp hp
  have hcongr : EqOn (IccExtend (by norm_num : (-1 : ℝ) ≤ 1)
      (q.toContinuousMapOn (Icc (-1 : ℝ) 1))) q.eval (Icc (-1 : ℝ) 1) := by
    intro x hx
    rw [IccExtend_of_mem _ _ hx]
    rfl
  change (chebyshevTrunc _ n).toContinuousMapOn _ = _
  rw [chebyshevTrunc_congr hcongr, chebyshevTrunc_eval_eq_of_degree_le hq]

/-- The absolute Dirichlet kernel bounds every actual Chebyshev truncation.
Source: finite convolution; focused rederivations `thm:projection`. -/
theorem abs_eval_chebyshevTrunc_le_dirichletIntegral {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) {M : ℝ}
    (hM : ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ M) (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(chebyshevTrunc f n).eval x| ≤
      (∫ t : AddCircle (2 * π), |dirichletCircleKernel n t| ∂AddCircle.haarAddCircle) * M := by
  have hxcos : (fourier 1 (Real.arccos x : AddCircle (2 * π))).re = x := by
    rw [show (fourier 1 (Real.arccos x : AddCircle (2 * π))).re = cos (arccos x) by
      simpa using re_fourier_nat_coe_eq_cos 1 (arccos x), cos_arccos hx.1 hx.2]
  rw [← hxcos, ← integral_dirichletCircleKernel_mul_realChebyshevCircleFunction hf,
    ← Real.norm_eq_abs]
  have hki : Integrable (fun t : AddCircle (2 * π) => M * |dirichletCircleKernel n t|)
      AddCircle.haarAddCircle :=
    (continuous_const.mul (continuous_dirichletCircleKernel n).abs).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine (norm_integral_le_of_norm_le hki (Filter.Eventually.of_forall (fun t => ?_))).trans_eq ?_
  · rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left (hM _ (re_fourier_one_mem_Icc _)) (abs_nonneg _)).trans_eq
      (mul_comm _ _)
  · rw [integral_const_mul, mul_comm]

/-- The actual coefficient projection has norm bounded by the absolute Dirichlet integral.
Source: finite convolution; focused rederivations `thm:projection`. -/
theorem norm_chebyshevProjectionLinearMap_le_dirichletIntegral (n : ℕ)
    (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    ‖chebyshevProjectionLinearMap n f‖ ≤
      (∫ t : AddCircle (2 * π), |dirichletCircleKernel n t| ∂AddCircle.haarAddCircle) * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (integral_nonneg (fun _ => abs_nonneg _))
    (norm_nonneg _))).mpr
  intro x
  rw [Real.norm_eq_abs]
  change |(chebyshevTrunc (IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f) n).eval (x : ℝ)| ≤ _
  apply abs_eval_chebyshevTrunc_le_dirichletIntegral f.continuous.Icc_extend'.continuousOn
    (fun y hy => ?_) n x.property
  rw [IccExtend_of_mem _ _ hy]
  exact f.norm_coe_le_norm ⟨y, hy⟩

/-- Chebyshev projection as a bounded linear operator on continuous unit-interval functions.
Source: Trefethen, ATAP, Chapters 3 and 15. -/
def chebyshevProjectionOperator (n : ℕ) :
    C(Icc (-1 : ℝ) 1, ℝ) →L[ℝ] C(Icc (-1 : ℝ) 1, ℝ) :=
  (chebyshevProjectionLinearMap n).mkContinuous
    (∫ t : AddCircle (2 * π), |dirichletCircleKernel n t| ∂AddCircle.haarAddCircle)
    (norm_chebyshevProjectionLinearMap_le_dirichletIntegral n)

/-- The bounded Chebyshev projection is the genuine algebraic coefficient projection.
Source: Trefethen, ATAP, Chapters 3 and 15. -/
@[simp] theorem chebyshevProjectionOperator_apply (n : ℕ) (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    chebyshevProjectionOperator n f = chebyshevProjectionLinearMap n f := rfl

/-- A continuous smoothed sign has magnitude at most one and its product
approximates absolute value to within the smoothing parameter.
Source: the extremizing kernel test; focused rederivations `thm:projection`. -/
theorem abs_sub_mul_smoothedSign_le (u ε : ℝ) (hε : 0 < ε) :
    |u / sqrt (u ^ 2 + ε ^ 2)| ≤ 1 ∧
      |u| ≤ u * (u / sqrt (u ^ 2 + ε ^ 2)) + ε := by
  have hsq : 0 < u ^ 2 + ε ^ 2 := by positivity
  have hv : 0 < sqrt (u ^ 2 + ε ^ 2) := sqrt_pos.mpr hsq
  have hv2 : sqrt (u ^ 2 + ε ^ 2) ^ 2 = u ^ 2 + ε ^ 2 := sq_sqrt hsq.le
  have hAu : |u| ^ 2 = u ^ 2 := sq_abs u
  have hl : |u| ≤ sqrt (u ^ 2 + ε ^ 2) := by nlinarith [abs_nonneg u]
  have hu : sqrt (u ^ 2 + ε ^ 2) ≤ |u| + ε := by nlinarith [abs_nonneg u]
  constructor
  · rw [abs_div, abs_of_pos hv]
    exact (div_le_one hv).mpr hl
  · rw [show u * (u / sqrt (u ^ 2 + ε ^ 2)) + ε =
        (u ^ 2 + ε * sqrt (u ^ 2 + ε ^ 2)) / sqrt (u ^ 2 + ε ^ 2) by field_simp]
    apply (le_div_iff₀ hv).mpr
    have hprod : 0 ≤ (sqrt (u ^ 2 + ε ^ 2) - |u|) * ε :=
      mul_nonneg (sub_nonneg.mpr hl) hε.le
    have hprod' : 0 ≤ |u| * (|u| + ε - sqrt (u ^ 2 + ε ^ 2)) :=
      mul_nonneg (abs_nonneg _) (sub_nonneg.mpr hu)
    nlinarith

/-- The norm of actual Chebyshev projection equals the normalized absolute
Dirichlet integral. Continuous smoothed signs attain its norm in the limit.
Source: Trefethen, ATAP, Chapter 15; focused rederivations `thm:projection`. -/
theorem norm_chebyshevProjectionOperator_eq_dirichletIntegral (n : ℕ) :
    ‖chebyshevProjectionOperator n‖ =
      ∫ t : AddCircle (2 * π), |dirichletCircleKernel n t| ∂AddCircle.haarAddCircle := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg (fun _ => abs_nonneg _))
      (norm_chebyshevProjectionLinearMap_le_dirichletIntegral n)
  · apply le_of_forall_pos_le_add
    intro ε hε
    let d : ℝ → ℝ := fun x => 1 + 2 * ∑ k ∈ range n, (T ℝ ((k + 1 : ℕ) : ℤ)).eval x
    have hd : Continuous d := by dsimp [d]; fun_prop
    have hden : ∀ x : ℝ, sqrt (d x ^ 2 + ε ^ 2) ≠ 0 := by
      intro x
      exact (sqrt_pos.mpr (by positivity)).ne'
    let f : C(Icc (-1 : ℝ) 1, ℝ) := ⟨fun x => d x / sqrt (d x ^ 2 + ε ^ 2),
      ((hd.div (by fun_prop) hden).comp continuous_subtype_val)⟩
    have hf : ‖f‖ ≤ 1 := by
      apply (ContinuousMap.norm_le f (by norm_num : (0 : ℝ) ≤ 1)).mpr
      intro x
      exact (abs_sub_mul_smoothedSign_le (d x) ε hε).1
    let g : ℝ → ℝ := IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f
    have hg : ContinuousOn g (Icc (-1 : ℝ) 1) := f.continuous.Icc_extend'.continuousOn
    have hdcircle : ∀ t : AddCircle (2 * π), d ((fourier 1 t).re) = dirichletCircleKernel n t := by
      intro t
      simp only [d, dirichletCircleKernel, eval_T_re_fourier_one]
    have hgcircle : ∀ t : AddCircle (2 * π), realChebyshevCircleFunction g (-t) =
        dirichletCircleKernel n t / sqrt (dirichletCircleKernel n t ^ 2 + ε ^ 2) := by
      intro t
      rw [even_realChebyshevCircleFunction]
      change IccExtend (by norm_num : (-1 : ℝ) ≤ 1) f ((fourier 1 t).re) = _
      rw [IccExtend_of_mem _ _ (re_fourier_one_mem_Icc t)]
      change d ((fourier 1 t).re) / sqrt (d ((fourier 1 t).re) ^ 2 + ε ^ 2) = _
      rw [hdcircle]
    have hvalue : chebyshevProjectionOperator n f ⟨1, by norm_num⟩ =
        ∫ t : AddCircle (2 * π), dirichletCircleKernel n t *
          (dirichletCircleKernel n t / sqrt (dirichletCircleKernel n t ^ 2 + ε ^ 2))
            ∂AddCircle.haarAddCircle := by
      have h := integral_dirichletCircleKernel_mul_realChebyshevCircleFunction hg n 0
      simp only [zero_sub, hgcircle, fourier_eval_zero, Complex.one_re] at h
      exact h.symm
    have hint : Integrable (fun t : AddCircle (2 * π) => dirichletCircleKernel n t *
        (dirichletCircleKernel n t / sqrt (dirichletCircleKernel n t ^ 2 + ε ^ 2)) + ε)
          AddCircle.haarAddCircle := by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      have hnz : ∀ t : AddCircle (2 * π), sqrt (dirichletCircleKernel n t ^ 2 + ε ^ 2) ≠ 0 := by
        intro t
        exact (sqrt_pos.mpr (by positivity)).ne'
      exact ((continuous_dirichletCircleKernel n).mul
        ((continuous_dirichletCircleKernel n).div
          (((continuous_dirichletCircleKernel n).pow 2).add continuous_const).sqrt hnz)).add continuous_const
    have hI := integral_mono
      ((continuous_dirichletCircleKernel n).abs.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) hint
      (fun t => (abs_sub_mul_smoothedSign_le (dirichletCircleKernel n t) ε hε).2)
    have hint' : Integrable (fun t : AddCircle (2 * π) => dirichletCircleKernel n t *
        (dirichletCircleKernel n t / sqrt (dirichletCircleKernel n t ^ 2 + ε ^ 2)))
          AddCircle.haarAddCircle := by
      exact (hint.sub (integrable_const ε)).congr (ae_of_all _ (fun t => by simp))
    rw [integral_add hint' (integrable_const ε), integral_const] at hI
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hI
    rw [← hvalue] at hI
    have hval := (chebyshevProjectionOperator n f).apply_le_norm ⟨1, by norm_num⟩
    have hnorm := (chebyshevProjectionOperator n).le_opNorm f
    have hnorm' : ‖chebyshevProjectionOperator n‖ * ‖f‖ ≤ ‖chebyshevProjectionOperator n‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hf (norm_nonneg (chebyshevProjectionOperator n))
    linarith

/-- Projection onto constants has norm exactly one.
Source: normalized constant coefficient; focused rederivations `thm:projection`. -/
@[simp] theorem norm_chebyshevProjectionOperator_zero :
    ‖chebyshevProjectionOperator 0‖ = 1 := by
  rw [norm_chebyshevProjectionOperator_eq_dirichletIntegral]
  simp [dirichletCircleKernel]

/-- The exact Chebyshev projection norm is the standard symmetric-period
Dirichlet integral.
Source: Trefethen, ATAP, Chapter 15; focused rederivations `thm:projection`. -/
theorem norm_chebyshevProjectionOperator_eq_intervalIntegral (n : ℕ) :
    ‖chebyshevProjectionOperator n‖ = (1 / (2 * π)) *
      ∫ t in -π..π, |dirichletCircleKernel n (t : AddCircle (2 * π))| := by
  rw [norm_chebyshevProjectionOperator_eq_dirichletIntegral,
    AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * π) (-π)]
  rw [show -π + 2 * π = π by ring]
  simp only [smul_eq_mul, one_div]

/-- Chebyshev projection has the matching harmonic lower bound, so its
logarithmic coefficient `4/π²` is sharp.
Source: complete-period Dirichlet estimates; focused rederivations `thm:projection`.
atlas: chebyshev-projection-lebesgue-constant (partial) -/
theorem harmonic_le_norm_chebyshevProjectionOperator (n : ℕ) :
    (4 / π ^ 2) * (harmonic n : ℝ) ≤ ‖chebyshevProjectionOperator n‖ := by
  rw [norm_chebyshevProjectionOperator_eq_dirichletIntegral]
  exact harmonic_le_integral_abs_dirichletCircleKernel n

/-- Chebyshev projection has the sharp logarithmic norm coefficient `4/π²`.
Source: Trefethen, ATAP, Chapter 15; focused rederivations `thm:projection`.
atlas: chebyshev-projection-lebesgue-constant (partial) -/
theorem norm_chebyshevProjectionOperator_le_log (n : ℕ) :
    ‖chebyshevProjectionOperator n‖ ≤ 3 + (4 / π ^ 2) * log (n + 1 : ℕ) := by
  apply le_trans _ (integral_abs_dirichletCircleKernel_le_log n)
  exact ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg (fun _ => abs_nonneg _))
    (norm_chebyshevProjectionLinearMap_le_dirichletIntegral n)

/-- Genuine Chebyshev truncation is near-best with the sharp logarithmic coefficient.
Source: Trefethen, ATAP, Theorem 15.1; focused rederivations operator consequences.
atlas: chebyshev-projection-lebesgue-constant -/
theorem norm_sub_chebyshevProjection_le_minimaxError (n : ℕ) (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    ‖f - chebyshevProjectionOperator n f‖ ≤
      (4 + (4 / π ^ 2) * log (n + 1 : ℕ)) * minimaxError n f := by
  have h := norm_sub_projection_le_minimaxError n (chebyshevProjectionLinearMap n)
    (3 + (4 / π ^ 2) * log (n + 1 : ℕ)) (chebyshevProjectionLinearMap_eq_self n)
    (fun g => (norm_chebyshevProjectionLinearMap_le_dirichletIntegral n g).trans
      (mul_le_mul_of_nonneg_right (integral_abs_dirichletCircleKernel_le_log n) (norm_nonneg g))) f
  rw [chebyshevProjectionOperator_apply]
  convert h using 1
  ring

end NLAlib
