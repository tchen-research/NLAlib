/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu

Ported from HighDimProb (Y. Zhang, J. D. Lee, F. Liu; Apache-2.0),
HighDimProb/Concentration/HansonWright.lean, to Lean 4.33.1.
The original Apache-2.0 copyright notice is retained. The proof is stated in NLAlib's matrix
vocabulary (`quadForm`, `frobSq`, `frobNorm`, `specNorm`); there is no HighDimProb dependency.
-/
import NLAlib.Probability.Concentration.QuadraticForms.CutAverages
import NLAlib.Probability.SubGaussian.ExpSquare
import NLAlib.Probability.Gaussian.Basic.StandardGaussian
import Mathlib.Analysis.InnerProductSpace.Trace
/-!
# Hanson–Wright proof: GaussianProductIntegrability

A focused leaf of the transported independent-coordinate proof.
Its declarations live in namespace `NLAlib` (generic scalar sub-Gaussian facts are in
`NLAlib.Probability.SubGaussian.*`); the public bounds are in `NLAlib.Probability.Concentration.QuadraticForms.HansonWright`.
Atlas: `hanson-wright`. Source: HighDimProb (Zhang–Lee–Liu, Apache-2.0).
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

noncomputable section
set_option maxRecDepth 5000

namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- Source-transport helper `toEuclideanCLM_adjoint` for Hanson–Wright.
Atlas `hanson-wright` (helper). -/
lemma toEuclideanCLM_adjoint {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) A) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) A.conjTranspose := by
  change LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A).adjoint =
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A.conjTranspose)
  congr 1
  exact (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm

open scoped Matrix.Norms.L2Operator in
/-- Source-transport helper `trace_adjoint_comp_toEuclideanCLM_eq_frobSq` for Hanson–Wright.
Atlas `hanson-wright` (helper). -/
lemma trace_adjoint_comp_toEuclideanCLM_eq_frobSq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)))
      ((ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) A) ∘L
        Matrix.toEuclideanCLM (𝕜 := ℝ) A).toLinearMap) = frobSq A := by
  let T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearMap.adjoint T ∘L T
  change (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))) S.toLinearMap = frobSq A
  rw [LinearMap.trace_eq_sum_inner S.toLinearMap (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp only [frobSq_eq_sum_sq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [S, T]
  have hbasis (i : Fin n) :
      (EuclideanSpace.basisFun (Fin n) ℝ j).ofLp i =
        if i = j then (1 : ℝ) else 0 := by
    simp [EuclideanSpace.basisFun_apply]
  rw [Matrix.toEuclideanCLM_toLp]
  rw [toEuclideanCLM_adjoint]
  rw [Matrix.toEuclideanCLM_toLp]
  rw [PiLp.inner_apply]
  simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.mulVec,
    dotProduct]
  have hsum_basis (k : Fin n) :
      (∑ x, A x k * ∑ x_1, A x x_1 *
        ((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp x_1) =
        ∑ x, A x k * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro x _
    apply congrArg (fun z => A x k * z)
    apply Finset.sum_congr rfl
    intro x_1 _
    apply congrArg (fun z => A x x_1 * z)
    exact hbasis x_1
  rw [Finset.sum_eq_single j]
  · have hsum_step :
        inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp j)
            (∑ x, A x j * ∑ x_1, A x x_1 *
              ((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp x_1) =
          inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp j)
            (∑ x, A x j * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)) :=
      congrArg (fun z => inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp j) z)
        (hsum_basis j)
    calc
      inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp j)
          (∑ x, A x j * ∑ x_1, A x x_1 *
            ((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp x_1) =
          inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp j)
          (∑ x, A x j * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)) :=
        hsum_step
      _ = inner ℝ (if j = j then (1 : ℝ) else 0)
            (∑ x, A x j * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)) :=
        congrArg (fun z => inner ℝ z
          (∑ x, A x j * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)))
          (hbasis j)
      _ = ∑ x, A x j ^ 2 := by
        simp
        ring_nf
  · intro i _ hij
    have hsum_step :
        inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp i)
            (∑ x, A x i * ∑ x_1, A x x_1 *
              ((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp x_1) =
          inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp i)
            (∑ x, A x i * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)) :=
      congrArg (fun z => inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp i) z)
        (hsum_basis i)
    calc
      inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp i)
          (∑ x, A x i * ∑ x_1, A x x_1 *
            ((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp x_1) =
          inner ℝ (((EuclideanSpace.basisFun (Fin n) ℝ) j).ofLp i)
          (∑ x, A x i * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)) :=
        hsum_step
      _ = inner ℝ (if i = j then (1 : ℝ) else 0)
            (∑ x, A x i * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)) :=
        congrArg (fun z => inner ℝ z
          (∑ x, A x i * ∑ x_1, A x x_1 * (if x_1 = j then (1 : ℝ) else 0)))
          (hbasis i)
      _ = 0 := by simp [hij]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

open scoped Matrix.Norms.L2Operator in
/-- Source-transport helper `eigenvalue_adjoint_comp_le_opNorm_sq` for Hanson–Wright.
Atlas `hanson-wright` (helper). -/
lemma eigenvalue_adjoint_comp_le_opNorm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (i : Fin (Module.finrank ℝ E)) :
    let S : E →L[ℝ] E := ContinuousLinearMap.adjoint T ∘L T
    let hSpos : S.toLinearMap.IsPositive :=
      (ContinuousLinearMap.isPositive_adjoint_comp_self T).toLinearMap
    hSpos.isSymmetric.eigenvalues rfl i ≤ ‖T‖ ^ 2 := by
  intro S hSpos
  let hsym := hSpos.isSymmetric
  let b := hsym.eigenvectorBasis (by rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let e := b i
  let lam := hsym.eigenvalues rfl i
  have heig : S.toLinearMap e = lam • e := by
    exact hsym.apply_eigenvectorBasis (by rfl : Module.finrank ℝ E = Module.finrank ℝ E) i
  have hinner : inner ℝ (S e) e = lam := by
    rw [show S e = S.toLinearMap e by rfl, heig]
    rw [inner_smul_left]
    rw [inner_self_eq_norm_sq_to_K]
    simp [e, b]
  have hnorm_sq : ‖T e‖ ^ 2 = inner ℝ (S e) e := by
    simpa [S] using ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left T e
  have hnorm_le : ‖T e‖ ≤ ‖T‖ := by
    have h := T.le_opNorm e
    simpa [e, b, OrthonormalBasis.norm_eq_one] using h
  have hnorm_nonneg : 0 ≤ ‖T e‖ := norm_nonneg _
  have hop_nonneg : 0 ≤ ‖T‖ := norm_nonneg _
  calc
    lam = ‖T e‖ ^ 2 := by rw [← hinner, ← hnorm_sq]
    _ ≤ ‖T‖ ^ 2 := by nlinarith

open scoped Matrix.Norms.L2Operator in
/-- Gaussian square-form bound for a positive symmetric operator, proved by spectral
diagonalization and one-dimensional square-exponential estimates. -/
lemma integral_exp_quadratic_stdGaussian_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (T : E →L[ℝ] E) (hTpos : T.toLinearMap.IsPositive) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsmall : ∀ i : Fin (Module.finrank ℝ E),
      θ * hTpos.isSymmetric.eigenvalues rfl i * exp 1 ≤ 1 / 2) :
    ∫ x : E, exp (θ * inner ℝ (T x) x) ∂(stdGaussian E) ≤
      exp (2 * exp 1 ^ 2 * θ *
        (∑ i : Fin (Module.finrank ℝ E), hTpos.isSymmetric.eigenvalues rfl i)) := by
  let hsym := hTpos.isSymmetric
  let b := hsym.eigenvectorBasis (by rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let lam : Fin (Module.finrank ℝ E) → ℝ := fun i => hsym.eigenvalues rfl i
  have hnonneg : ∀ i : Fin (Module.finrank ℝ E), 0 ≤ lam i := by
    intro i
    simpa [lam, hsym] using hTpos.nonneg_eigenvalues
      (by rfl : Module.finrank ℝ E = Module.finrank ℝ E) i
  have hsynth_aemeas :
      AEMeasurable (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ i, z i • b i)
        (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1) := by
    exact (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).smul continuous_const).aemeasurable
  have hf_aesm :
      AEStronglyMeasurable (fun x : E => exp (θ * inner ℝ (T x) x))
        (Measure.map (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ i, z i • b i)
          (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1)) := by
    fun_prop
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  rw [integral_map hsynth_aemeas hf_aesm]
  have hpoint : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      exp (θ * inner ℝ (T (∑ i, z i • b i)) (∑ i, z i • b i)) =
        ∏ i : Fin (Module.finrank ℝ E), exp ((θ * lam i) * z i ^ 2) := by
    intro z
    change exp (θ * inner ℝ (T.toLinearMap (∑ i, z i • b i)) (∑ i, z i • b i)) =
      ∏ i : Fin (Module.finrank ℝ E), exp ((θ * lam i) * z i ^ 2)
    have hquad :=
      symmetric_inner_apply_eq_sum_eigenvalues_repr T.toLinearMap hsym (∑ i, z i • b i)
    rw [hquad]
    have hsum_eq :
        (∑ i : Fin (Module.finrank ℝ E),
            hsym.eigenvalues rfl i * (hsym.eigenvectorBasis rfl).repr
              (∑ i, z i • b i) i ^ 2) =
          ∑ i : Fin (Module.finrank ℝ E), lam i * z i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      have hcoord :
          (hsym.eigenvectorBasis rfl).repr (∑ i, z i • b i) i = z i := by
        change b.repr (∑ i, z i • b i) i = z i
        exact orthonormalBasis_repr_sum_smul b z i
      rw [hcoord]
    rw [hsum_eq]
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    ∫ (x : Fin (Module.finrank ℝ E) → ℝ),
        exp (θ * inner ℝ (T (∑ i, x i • b i)) (∑ i, x i • b i))
        ∂Measure.pi (fun x => gaussianReal 0 1)
        = ∫ (x : Fin (Module.finrank ℝ E) → ℝ),
          ∏ i : Fin (Module.finrank ℝ E), exp ((θ * lam i) * x i ^ 2)
        ∂Measure.pi (fun x => gaussianReal 0 1) := by
          apply integral_congr_ae
          filter_upwards with z
          exact hpoint z
    _ = ∏ i : Fin (Module.finrank ℝ E),
          ∫ x : ℝ, exp ((θ * lam i) * x ^ 2) ∂gaussianReal 0 1 := by
          exact (integral_fintype_prod_eq_prod (𝕜 := ℝ)
            (ι := Fin (Module.finrank ℝ E)) (E := fun _ => ℝ)
            (f := fun i x => exp ((θ * lam i) * x ^ 2))
            (μ := fun _ => gaussianReal 0 1))
    _ ≤ ∏ i : Fin (Module.finrank ℝ E),
          exp (2 * exp 1 * ((θ * lam i) * 1 * exp 1)) := by
          apply Finset.prod_le_prod
          · intro i _
            exact integral_nonneg_of_ae (ae_of_all _ fun x => exp_nonneg _)
          · intro i _
            have hθi : 0 ≤ θ * lam i := mul_nonneg hθ (hnonneg i)
            have hle := integral_exp_mul_sq_le_exp_linear_of_hasSubgaussianMGF_of_le
              (μ := gaussianReal 0 1) (hasSubgaussianMGF_id_gaussianReal 1)
              (θ := θ * lam i) (C0 := 1) hθi (by norm_num) (by norm_num) ?_
            · simpa only [id_eq] using hle
            · convert hsmall i using 1; ring
    _ = exp (2 * exp 1 ^ 2 * θ *
          (∑ i : Fin (Module.finrank ℝ E), lam i)) := by
          rw [← Real.exp_sum]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring

open scoped Matrix.Norms.L2Operator in
/-- Gaussian square-form integrability for a positive symmetric operator, under the
strict version of the same coordinate smallness condition. -/
lemma integrable_exp_quadratic_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (T : E →L[ℝ] E) (hTpos : T.toLinearMap.IsPositive) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsmall : ∀ i : Fin (Module.finrank ℝ E),
      θ * hTpos.isSymmetric.eigenvalues rfl i * exp 1 < 1) :
    Integrable (fun x : E => exp (θ * inner ℝ (T x) x)) (stdGaussian E) := by
  let hsym := hTpos.isSymmetric
  let b := hsym.eigenvectorBasis (by rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let lam : Fin (Module.finrank ℝ E) → ℝ := fun i => hsym.eigenvalues rfl i
  have hnonneg : ∀ i : Fin (Module.finrank ℝ E), 0 ≤ lam i := by
    intro i
    simpa [lam, hsym] using hTpos.nonneg_eigenvalues
      (by rfl : Module.finrank ℝ E = Module.finrank ℝ E) i
  have hsynth_aemeas :
      AEMeasurable (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ i, z i • b i)
        (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1) := by
    exact (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).smul continuous_const).aemeasurable
  have hf_aesm :
      AEStronglyMeasurable (fun x : E => exp (θ * inner ℝ (T x) x))
        (Measure.map (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ i, z i • b i)
          (Measure.pi fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1)) := by
    fun_prop
  have hpoint : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      exp (θ * inner ℝ (T (∑ i, z i • b i)) (∑ i, z i • b i)) =
        ∏ i : Fin (Module.finrank ℝ E), exp ((θ * lam i) * z i ^ 2) := by
    intro z
    change exp (θ * inner ℝ (T.toLinearMap (∑ i, z i • b i)) (∑ i, z i • b i)) =
      ∏ i : Fin (Module.finrank ℝ E), exp ((θ * lam i) * z i ^ 2)
    have hquad :=
      symmetric_inner_apply_eq_sum_eigenvalues_repr T.toLinearMap hsym (∑ i, z i • b i)
    rw [hquad]
    have hsum_eq :
        (∑ i : Fin (Module.finrank ℝ E),
            hsym.eigenvalues rfl i * (hsym.eigenvectorBasis rfl).repr
              (∑ i, z i • b i) i ^ 2) =
          ∑ i : Fin (Module.finrank ℝ E), lam i * z i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      have hcoord :
          (hsym.eigenvectorBasis rfl).repr (∑ i, z i • b i) i = z i := by
        change b.repr (∑ i, z i • b i) i = z i
        exact orthonormalBasis_repr_sum_smul b z i
      rw [hcoord]
    rw [hsum_eq]
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  rw [integrable_map_measure hf_aesm hsynth_aemeas]
  refine (MeasureTheory.Integrable.fintype_prod (𝕜 := ℝ)
    (ι := Fin (Module.finrank ℝ E)) (E := ℝ)
    (f := fun i x => exp ((θ * lam i) * x ^ 2))
    (μ := fun _ => gaussianReal 0 1) ?_).congr ?_
  · intro i
    have hθi : 0 ≤ θ * lam i := mul_nonneg hθ (hnonneg i)
    exact integrable_exp_mul_sq_of_hasSubgaussianMGF_of_le
      (μ := gaussianReal 0 1) (hasSubgaussianMGF_id_gaussianReal 1)
      (θ := θ * lam i) (C0 := 1) hθi (by norm_num) (by norm_num) (by
        simpa [mul_assoc] using hsmall i)
  · filter_upwards with z
    exact (hpoint z).symm

open scoped Matrix.Norms.L2Operator in
/-- Integrability of the exponential of a Gaussian bilinear form. -/
lemma integrable_exp_inner_toEuclideanCLM_prod_stdGaussian {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {l : ℝ}
    (hsmall : (l ^ 2 / 2) * specNorm A ^ 2 * exp 1 < 1) :
    Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        exp (l * inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) A p.1) p.2))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ : Measure E := stdGaussian E
  let T : E →L[ℝ] E := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let S : E →L[ℝ] E := ContinuousLinearMap.adjoint T ∘L T
  let hSpos : S.toLinearMap.IsPositive :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self T).toLinearMap
  let f : E × E → ℝ := fun p => exp (l * inner ℝ (T p.1) p.2)
  have hf_aesm : AEStronglyMeasurable f (γ.prod γ) := by
    dsimp [f]
    fun_prop
  have hθ_nonneg : 0 ≤ l ^ 2 / 2 := by positivity
  have hsmall_eig :
      ∀ i : Fin (Module.finrank ℝ E),
        (l ^ 2 / 2) * hSpos.isSymmetric.eigenvalues rfl i * exp 1 < 1 := by
    intro i
    have heig_le : hSpos.isSymmetric.eigenvalues rfl i ≤ ‖T‖ ^ 2 := by
      simpa only [S, hSpos] using eigenvalue_adjoint_comp_le_opNorm_sq T i
    have hcoef_nonneg : 0 ≤ l ^ 2 / 2 := by positivity
    have hstep :
        (l ^ 2 / 2) * hSpos.isSymmetric.eigenvalues rfl i * exp 1 ≤
          (l ^ 2 / 2) * ‖T‖ ^ 2 * exp 1 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left heig_le hcoef_nonneg) (exp_nonneg 1)
    have hnorm : ‖T‖ = specNorm A := (Matrix.cstar_norm_def A).symm
    rw [hnorm] at hstep
    exact lt_of_le_of_lt hstep hsmall
  have hquad_int :
      Integrable (fun y : E => exp ((l ^ 2 / 2) * inner ℝ (S y) y)) γ :=
    integrable_exp_quadratic_stdGaussian S hSpos hθ_nonneg hsmall_eig
  rw [integrable_prod_iff hf_aesm]
  constructor
  · filter_upwards with y
    change Integrable (fun x : E => exp (l * inner ℝ (T y) x)) γ
    exact integrable_exp_innerSL_stdGaussian (E := E) (T y) l
  · have houter_eq :
        (fun y : E => ∫ x : E, ‖f (y, x)‖ ∂γ) =ᵐ[γ]
          fun y : E => exp ((l ^ 2 / 2) * inner ℝ (S y) y) := by
      filter_upwards with y
      have hinner :
          ∫ x : E, ‖f (y, x)‖ ∂γ =
            ∫ x : E, exp (l * inner ℝ (T y) x) ∂γ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [f]
        rw [abs_of_nonneg (exp_nonneg _)]
      rw [hinner, integral_exp_innerSL_stdGaussian (E := E) (T y) l]
      have hnorm_sq : ‖T y‖ ^ 2 = inner ℝ (S y) y := by
        simpa [S] using ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left T y
      rw [hnorm_sq]
      ring_nf
    exact hquad_int.congr houter_eq.symm

open scoped Matrix.Norms.L2Operator in
/-- A Frobenius-scale bound for the exponential moment of a Gaussian bilinear form. -/
lemma integral_exp_inner_toEuclideanCLM_prod_stdGaussian_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {l : ℝ}
    (hsmall : (l ^ 2 / 2) * specNorm A ^ 2 * exp 1 ≤ 1 / 2) :
    ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        exp (l * inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) A p.1) p.2)
      ∂((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) ≤
      exp (exp 1 ^ 2 * l ^ 2 * frobNorm A ^ 2) := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ : Measure E := stdGaussian E
  let T : E →L[ℝ] E := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let S : E →L[ℝ] E := ContinuousLinearMap.adjoint T ∘L T
  let hSpos : S.toLinearMap.IsPositive :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self T).toLinearMap
  let f : E × E → ℝ := fun p => exp (l * inner ℝ (T p.1) p.2)
  have hf_int : Integrable f (γ.prod γ) :=
    integrable_exp_inner_toEuclideanCLM_prod_stdGaussian A (by
      exact lt_of_le_of_lt hsmall (by norm_num))
  have hθ_nonneg : 0 ≤ l ^ 2 / 2 := by positivity
  have hsmall_eig :
      ∀ i : Fin (Module.finrank ℝ E),
        (l ^ 2 / 2) * hSpos.isSymmetric.eigenvalues rfl i * exp 1 ≤ 1 / 2 := by
    intro i
    have heig_le : hSpos.isSymmetric.eigenvalues rfl i ≤ ‖T‖ ^ 2 := by
      simpa only [S, hSpos] using eigenvalue_adjoint_comp_le_opNorm_sq T i
    have hcoef_nonneg : 0 ≤ l ^ 2 / 2 := by positivity
    have hstep :
        (l ^ 2 / 2) * hSpos.isSymmetric.eigenvalues rfl i * exp 1 ≤
          (l ^ 2 / 2) * ‖T‖ ^ 2 * exp 1 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left heig_le hcoef_nonneg) (exp_nonneg 1)
    have hnorm : ‖T‖ = specNorm A := (Matrix.cstar_norm_def A).symm
    rw [hnorm] at hstep
    exact hstep.trans hsmall
  have hsum_eq :
      (∑ i : Fin (Module.finrank ℝ E), hSpos.isSymmetric.eigenvalues rfl i) =
        frobSq A := by
    have htrace_eigs :
        (LinearMap.trace ℝ E) S.toLinearMap =
          ∑ i : Fin (Module.finrank ℝ E), hSpos.isSymmetric.eigenvalues rfl i := by
      simpa using hSpos.isSymmetric.trace_eq_sum_eigenvalues
        (by rfl : Module.finrank ℝ E = Module.finrank ℝ E)
    have htrace_frob :
        (LinearMap.trace ℝ E) S.toLinearMap = frobSq A := by
      simpa [E, S, T] using trace_adjoint_comp_toEuclideanCLM_eq_frobSq A
    exact htrace_eigs.symm.trans htrace_frob
  have hinner_eq :
      (fun y : E => ∫ x : E, f (y, x) ∂γ) =ᵐ[γ]
        fun y : E => exp ((l ^ 2 / 2) * inner ℝ (S y) y) := by
    filter_upwards with y
    rw [integral_exp_innerSL_stdGaussian (E := E) (T y) l]
    have hnorm_sq : ‖T y‖ ^ 2 = inner ℝ (S y) y := by
      simpa [S] using ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left T y
    rw [hnorm_sq]
    ring_nf
  calc
    ∫ p : E × E, f p ∂(γ.prod γ)
        = ∫ y : E, ∫ x : E, f (y, x) ∂γ ∂γ := by
          rw [integral_prod f hf_int]
    _ = ∫ y : E, exp ((l ^ 2 / 2) * inner ℝ (S y) y) ∂γ := by
          exact integral_congr_ae hinner_eq
    _ ≤ exp (2 * exp 1 ^ 2 * (l ^ 2 / 2) *
          (∑ i : Fin (Module.finrank ℝ E), hSpos.isSymmetric.eigenvalues rfl i)) :=
          integral_exp_quadratic_stdGaussian_le S hSpos hθ_nonneg hsmall_eig
    _ = exp (exp 1 ^ 2 * l ^ 2 * frobNorm A ^ 2) := by
          rw [hsum_eq, frobNorm_sq]
          congr 1
          ring

end NLAlib
