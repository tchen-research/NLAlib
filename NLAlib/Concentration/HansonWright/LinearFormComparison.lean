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
import NLAlib.Concentration.HansonWright.Centering

/-!
# Hanson–Wright proof: LinearFormComparison

A focused leaf of the transported independent-coordinate proof.
Shared helper declarations live in `NLAlib.HansonWrightProof`; the canonical
public bounds are in `NLAlib.Concentration.HansonWright`.
Atlas: `hanson-wright`. Source: HighDimProb commit c0cb8d9e0ff2c3408c92681eb8bf0232e4673bae.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal Matrix.Norms.L2Operator

noncomputable section
set_option maxRecDepth 5000

namespace NLAlib
namespace HansonWrightProof

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Source-transport helper `centeredQuadraticForm_eq_diagonal_add_offDiagonal` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma centeredQuadraticForm_eq_diagonal_add_offDiagonal {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {K : ℝ}
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ) :
    centeredQuadraticForm μ A X =
      fun ω => diagonalCenteredQuadraticForm μ A X ω +
        matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω) := by
  classical
  have hdiag_term_int : ∀ i, Integrable (fun ω => A i i * X i ω ^ 2) μ := by
    intro i
    exact ((integrable_pow_of_integrable_exp_mul
      (X := X i) (t := 1) one_ne_zero
      ((hX_subG i).integrable_exp_mul 1)
      ((hX_subG i).integrable_exp_mul (-1)) 2).const_mul (A i i))
  have hdiag_int :
      Integrable (fun ω => ∑ i, A i i * X i ω ^ 2) μ :=
    MeasureTheory.integrable_finsetSum _ fun i _ => hdiag_term_int i
  have hoff_int :
      Integrable (fun ω => matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω)) μ :=
    integrable_randomQuadraticForm_offDiagonal_of_subgaussian A h_indep hX_subG
  have hqfun :
      (fun ω => randomQuadraticForm A X ω) =
        fun ω => (∑ i, A i i * X i ω ^ 2) +
          matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω) := by
    ext ω
    exact quadraticForm_eq_diag_add_offDiagonal A (fun i => X i ω)
  ext ω
  unfold centeredQuadraticForm diagonalCenteredQuadraticForm
  rw [show randomQuadraticForm A X ω =
      (∑ i, A i i * X i ω ^ 2) +
        matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω) by
        exact congrFun hqfun ω]
  rw [show (∫ ω, randomQuadraticForm A X ω ∂μ) =
      ∫ ω, (∑ i, A i i * X i ω ^ 2) +
        matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω) ∂μ by rw [hqfun]]
  rw [integral_add hdiag_int hoff_int]
  have hoff_zero :
      ∫ a, matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i a) ∂μ = 0 := by
    simpa only [randomQuadraticForm] using
      integral_randomQuadraticForm_offDiagonal_eq_zero A h_indep hX_subG
  rw [hoff_zero]
  rw [MeasureTheory.integral_finsetSum]
  · calc
      (∑ i, A i i * X i ω ^ 2) + matrixQuadraticForm (offDiagonalMatrix A)
          (fun i => X i ω) - (∑ i, ∫ (ω : Ω), A i i * X i ω ^ 2 ∂μ + 0)
          = (∑ i, (A i i * X i ω ^ 2 -
              ∫ (ω : Ω), A i i * X i ω ^ 2 ∂μ)) +
              matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω) := by
              let O : ℝ := matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω)
              let f : Fin n → ℝ := fun i => A i i * X i ω ^ 2
              let g : Fin n → ℝ := fun i => ∫ (ω : Ω), A i i * X i ω ^ 2 ∂μ
              have hsum_sub : (∑ i, f i) - ∑ i, g i = ∑ i, (f i - g i) := by
                rw [← Finset.sum_sub_distrib]
              change (∑ i, f i) + O - (∑ i, g i + 0) =
                (∑ i, (f i - g i)) + O
              rw [← hsum_sub]
              ring
      _ = (∑ i, A i i * (X i ω ^ 2 - ∫ (ω : Ω), X i ω ^ 2 ∂μ)) +
            matrixQuadraticForm (offDiagonalMatrix A) (fun i => X i ω) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_const_mul]
          ring
  · intro i _
    exact hdiag_term_int i

/-- Source-transport helper `hasSubgaussianMGF_mono_param` for Hanson–Wright.
HighDimProb commit c0cb8d9; atlas `hanson-wright`. -/
lemma hasSubgaussianMGF_mono_param {μ : Measure Ω} {X : Ω → ℝ} {c d : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (hcd : (c : ℝ) ≤ d) :
    HasSubgaussianMGF X d μ where
  integrable_exp_mul t := h.integrable_exp_mul t
  mgf_le t := by
    have hmul : (c : ℝ) * t ^ 2 ≤ (d : ℝ) * t ^ 2 :=
      mul_le_mul_of_nonneg_right hcd (sq_nonneg t)
    calc
      mgf X μ t ≤ exp ((c : ℝ) * t ^ 2 / 2) := h.mgf_le t
      _ ≤ exp ((d : ℝ) * t ^ 2 / 2) := by
          exact exp_le_exp.mpr (by linarith)

/-- A finite independent linear combination of sub-Gaussian variables is sub-Gaussian. -/
lemma hasSubgaussianMGF_finset_sum_const_mul_of_iIndepFun {ι : Type*} {μ : Measure Ω}
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ι → ℝ≥0}
    {s : Finset ι} (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ)
    (a : ι → ℝ) :
    HasSubgaussianMGF (fun ω => ∑ i ∈ s, a i * X i ω)
      (∑ i ∈ s, Real.toNNReal (a i ^ 2) * c i) μ := by
  have h_indep_mul :
      iIndepFun (fun i => fun ω => a i * X i ω) μ := by
    simpa [Function.comp_def] using
      h_indep.comp (fun i x => a i * x) (fun i => by fun_prop)
  have h_subG_mul :
      ∀ i ∈ s, HasSubgaussianMGF (fun ω => a i * X i ω)
      (Real.toNNReal (a i ^ 2) * c i) μ := by
    intro i hi
    convert (h_subG i hi).const_mul (a i) using 1
    rw [Real.toNNReal_of_nonneg (sq_nonneg (a i))]
    rfl
  exact HasSubgaussianMGF.sum_of_iIndepFun h_indep_mul h_subG_mul

/-- Fixed linear forms of an independent sub-Gaussian coordinate vector are sub-Gaussian. -/
lemma inner_randomVector_hasSubgaussianMGF_of_iIndepFun {μ : Measure Ω}
    {n : ℕ} {X : Fin n → Ω → ℝ} {K : ℝ}
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (v : EuclideanSpace ℝ (Fin n)) :
    HasSubgaussianMGF (fun ω => inner ℝ v (randomVector X ω))
      ⟨K ^ 2 * ‖v‖ ^ 2, mul_nonneg (sq_nonneg K) (sq_nonneg ‖v‖)⟩ μ := by
  let cK : ℝ≥0 := Real.toNNReal (K ^ 2)
  have hcK : cK = (⟨K ^ 2, sq_nonneg K⟩ : ℝ≥0) := by
    ext
    exact Real.coe_toNNReal (K ^ 2) (sq_nonneg K)
  have hX_subG' :
      ∀ i ∈ (Finset.univ : Finset (Fin n)), HasSubgaussianMGF (X i) cK μ := by
    intro i _
    rw [hcK]
    exact hX_subG i
  have hsum :=
    hasSubgaussianMGF_finset_sum_const_mul_of_iIndepFun
      (μ := μ) h_indep (s := Finset.univ) hX_subG' (fun i => v i)
  have hsum_inner :
      HasSubgaussianMGF (fun ω => inner ℝ v (randomVector X ω))
        (∑ i ∈ (Finset.univ : Finset (Fin n)), Real.toNNReal (v i ^ 2) * cK) μ := by
    refine hsum.congr (ae_of_all _ fun ω => ?_)
    change (∑ i : Fin n, v i * X i ω) = inner ℝ v (randomVector X ω)
    rw [PiLp.inner_apply]
    simp only [randomVector_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact (real_inner_mul _ _).symm
  have hparam :
      (((∑ i ∈ (Finset.univ : Finset (Fin n)), Real.toNNReal (v i ^ 2) * cK) : ℝ≥0) :
          ℝ) ≤ K ^ 2 * ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [cK, NNReal.coe_sum, NNReal.coe_mul]
    rw [Finset.mul_sum]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.coe_toNNReal (v i ^ 2) (sq_nonneg (v i)),
      Real.coe_toNNReal (K ^ 2) (sq_nonneg K)]
    ring
  exact hasSubgaussianMGF_mono_param hsum_inner hparam

/-- Gaussian-comparison square-exponential bound for a linear image of an independent
sub-Gaussian vector. -/
lemma integral_exp_norm_toEuclideanCLM_randomVector_sq_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {X : Fin n → Ω → ℝ} {K θ : ℝ} (hθ : 0 ≤ θ)
    (h_indep : iIndepFun X μ)
    (hX_subG : ∀ i, HasSubgaussianMGF (X i) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (hsmall : θ * K ^ 2 * deterministicOperatorNorm A ^ 2 * exp 1 ≤ 1 / 2) :
    ∫ ω, exp (θ *
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (randomVector X ω)‖ ^ 2) ∂μ ≤
      exp (2 * exp 1 ^ 2 * θ * K ^ 2 * deterministicFrobeniusNorm A ^ 2) := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ : Measure E := stdGaussian E
  let T : E →L[ℝ] E := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let U : E →L[ℝ] E := ContinuousLinearMap.adjoint T
  let S : E →L[ℝ] E := ContinuousLinearMap.adjoint U ∘L U
  let hSpos : S.toLinearMap.IsPositive :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self U).toLinearMap
  let s : ℝ := sqrt (2 * θ)
  let f : E × Ω → ℝ := fun p => exp (s * inner ℝ (U p.1) (randomVector X p.2))
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact sqrt_nonneg _
  have hs_sq : s ^ 2 = 2 * θ := by
    dsimp [s]
    rw [sq_sqrt]
    nlinarith
  have hKθ_nonneg : 0 ≤ K ^ 2 * θ := mul_nonneg (sq_nonneg K) hθ
  have hUnorm : ‖U‖ = deterministicOperatorNorm A := by
    dsimp [U, T, deterministicOperatorNorm]
    exact ContinuousLinearMap.adjoint.norm_map _
  have hsmall_eig :
      ∀ i : Fin (Module.finrank ℝ E),
        (K ^ 2 * θ) * hSpos.isSymmetric.eigenvalues rfl i * exp 1 ≤ 1 / 2 := by
    intro i
    have heig_le : hSpos.isSymmetric.eigenvalues rfl i ≤ ‖U‖ ^ 2 := by
      simpa only [S, hSpos] using eigenvalue_adjoint_comp_le_opNorm_sq U i
    have hstep :
        (K ^ 2 * θ) * hSpos.isSymmetric.eigenvalues rfl i * exp 1 ≤
          (K ^ 2 * θ) * ‖U‖ ^ 2 * exp 1 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left heig_le hKθ_nonneg) (exp_nonneg 1)
    exact hstep.trans (by
      rw [hUnorm]
      nlinarith [hsmall])
  have hsmall_eig_lt :
      ∀ i : Fin (Module.finrank ℝ E),
        (K ^ 2 * θ) * hSpos.isSymmetric.eigenvalues rfl i * exp 1 < 1 := by
    intro i
    linarith [hsmall_eig i]
  have hquad_int :
      Integrable (fun g : E => exp ((K ^ 2 * θ) * inner ℝ (S g) g)) γ :=
    integrable_exp_quadratic_stdGaussian S hSpos hKθ_nonneg hsmall_eig_lt
  have hf_aesm : AEStronglyMeasurable f (γ.prod μ) := by
    have hX_aemeas : AEMeasurable (randomVector X) μ :=
      randomVector_aemeasurable fun i => (hX_subG i).aemeasurable
    have hU_aemeas :
        AEMeasurable (fun p : E × Ω => U p.1) (γ.prod μ) :=
      AEMeasurable.comp_fst (μ := γ) (ν := μ) U.continuous.aemeasurable
    have hX_prod :
        AEMeasurable (fun p : E × Ω => randomVector X p.2) (γ.prod μ) :=
      AEMeasurable.comp_snd (μ := γ) (ν := μ) hX_aemeas
    have hinner :
        AEMeasurable
          (fun p : E × Ω => inner ℝ (U p.1) (randomVector X p.2)) (γ.prod μ) := by
      exact AEMeasurable.inner hU_aemeas hX_prod
    exact ((hinner.const_mul s).exp).aestronglyMeasurable
  have hinner_bound : (fun g : E => ∫ ω, f (g, ω) ∂μ) ≤ᵐ[γ]
      fun g : E => exp ((K ^ 2 * θ) * inner ℝ (S g) g) := by
    filter_upwards with g
    have hlin := inner_randomVector_hasSubgaussianMGF_of_iIndepFun h_indep hX_subG (U g)
    have hmgf := hlin.mgf_le s
    have hnorm_sq : ‖U g‖ ^ 2 = inner ℝ (S g) g := by
      simpa [S] using ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left U g
    calc
      ∫ ω, f (g, ω) ∂μ
          = mgf (fun ω => inner ℝ (U g) (randomVector X ω)) μ s := by
            rfl
      _ ≤ exp ((K ^ 2 * ‖U g‖ ^ 2) * s ^ 2 / 2) := hmgf
      _ = exp ((K ^ 2 * θ) * inner ℝ (S g) g) := by
            rw [hs_sq, hnorm_sq]
            congr 1
            ring
  have hnorm_inner_bound : (fun g : E => ∫ ω, ‖f (g, ω)‖ ∂μ) ≤ᵐ[γ]
      fun g : E => exp ((K ^ 2 * θ) * inner ℝ (S g) g) := by
    filter_upwards [hinner_bound] with g hg
    have hnorm_eq : ∫ ω, ‖f (g, ω)‖ ∂μ = ∫ ω, f (g, ω) ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      dsimp [f]
      rw [abs_of_nonneg (exp_nonneg _)]
    rwa [hnorm_eq]
  have hf_int : Integrable f (γ.prod μ) := by
    rw [integrable_prod_iff hf_aesm]
    constructor
    · filter_upwards with g
      exact
        (inner_randomVector_hasSubgaussianMGF_of_iIndepFun h_indep hX_subG (U g)).integrable_exp_mul s
    · have hnorm_outer_bound :
          (fun g : E => ‖∫ ω, ‖f (g, ω)‖ ∂μ‖) ≤ᵐ[γ]
            fun g : E => exp ((K ^ 2 * θ) * inner ℝ (S g) g) := by
        filter_upwards [hnorm_inner_bound] with g hg
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact hg
        · exact integral_nonneg fun ω => norm_nonneg _
      exact Integrable.mono' hquad_int hf_aesm.norm.integral_prod_right' hnorm_outer_bound
  have hsum_eq :
      (∑ i : Fin (Module.finrank ℝ E), hSpos.isSymmetric.eigenvalues rfl i) =
        frobeniusNormSq A := by
    have htrace_eigs :
        (LinearMap.trace ℝ E) S.toLinearMap =
          ∑ i : Fin (Module.finrank ℝ E), hSpos.isSymmetric.eigenvalues rfl i := by
      simpa using hSpos.isSymmetric.trace_eq_sum_eigenvalues
        (by rfl : Module.finrank ℝ E = Module.finrank ℝ E)
    have htrace_frob :
        (LinearMap.trace ℝ E) S.toLinearMap = frobeniusNormSq A := by
      have hUeq : U = Matrix.toEuclideanCLM (𝕜 := ℝ) A.conjTranspose := by
        dsimp [U, T]
        exact toEuclideanCLM_adjoint A
      calc
        (LinearMap.trace ℝ E) S.toLinearMap
            = (LinearMap.trace ℝ E)
                ((ContinuousLinearMap.adjoint U ∘L U).toLinearMap) := by
                rfl
        _ = (LinearMap.trace ℝ E)
                ((ContinuousLinearMap.adjoint
                    (Matrix.toEuclideanCLM (𝕜 := ℝ) A.conjTranspose) ∘L
                  Matrix.toEuclideanCLM (𝕜 := ℝ) A.conjTranspose).toLinearMap) := by
                rw [hUeq]
        _ = frobeniusNormSq A.conjTranspose :=
                trace_adjoint_comp_toEuclideanCLM_eq_frobeniusNormSq A.conjTranspose
        _ = frobeniusNormSq A := frobeniusNormSq_conjTranspose A
    exact htrace_eigs.symm.trans htrace_frob
  have hprod_bound :
      ∫ p : E × Ω, f p ∂(γ.prod μ) ≤
        exp (2 * exp 1 ^ 2 * θ * K ^ 2 * deterministicFrobeniusNorm A ^ 2) := by
    calc
      ∫ p : E × Ω, f p ∂(γ.prod μ)
          = ∫ g : E, ∫ ω, f (g, ω) ∂μ ∂γ := by
              rw [integral_prod f hf_int]
      _ ≤ ∫ g : E, exp ((K ^ 2 * θ) * inner ℝ (S g) g) ∂γ := by
              exact integral_mono_ae hf_int.integral_prod_left hquad_int hinner_bound
      _ ≤ exp (2 * exp 1 ^ 2 * (K ^ 2 * θ) *
            (∑ i : Fin (Module.finrank ℝ E), hSpos.isSymmetric.eigenvalues rfl i)) :=
              integral_exp_quadratic_stdGaussian_le S hSpos hKθ_nonneg hsmall_eig
      _ = exp (2 * exp 1 ^ 2 * θ * K ^ 2 * deterministicFrobeniusNorm A ^ 2) := by
              rw [hsum_eq, frobeniusNorm_sq]
              congr 1
              ring
  have hleft_eq :
      ∫ ω, exp (θ * ‖T (randomVector X ω)‖ ^ 2) ∂μ =
        ∫ ω, ∫ g : E, f (g, ω) ∂γ ∂μ := by
    apply integral_congr_ae
    filter_upwards with ω
    have hfg : (fun g : E => f (g, ω)) =
        fun g : E => exp (s * inner ℝ (T (randomVector X ω)) g) := by
      ext g
      dsimp [f, U]
      rw [ContinuousLinearMap.adjoint_inner_left T (randomVector X ω) g]
      rw [real_inner_comm]
    rw [hfg, integral_exp_innerSL_stdGaussian (E := E) (T (randomVector X ω)) s]
    rw [hs_sq]
    congr 1
    ring
  calc
      ∫ ω, exp (θ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (randomVector X ω)‖ ^ 2) ∂μ
          = ∫ ω, exp (θ * ‖T (randomVector X ω)‖ ^ 2) ∂μ := by rfl
      _ = ∫ ω, ∫ g : E, f (g, ω) ∂γ ∂μ := hleft_eq
      _ = ∫ q : Ω × E, f q.swap ∂(μ.prod γ) := by
          exact (integral_prod (fun q : Ω × E => f q.swap) hf_int.swap).symm
      _ ≤ exp (2 * exp 1 ^ 2 * θ * K ^ 2 * deterministicFrobeniusNorm A ^ 2) := by
          rw [integral_prod_swap f]
          exact hprod_bound

end HansonWrightProof
end NLAlib
