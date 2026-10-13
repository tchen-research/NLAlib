import NLAlib.Probability.Concentration.Matrix.HermitianBernstein
import NLAlib.Probability.Concentration.Matrix.DilationVariance
import NLAlib.Probability.Concentration.Matrix.IntrinsicBernstein

/-!
# Theorem 6.1.1 — Matrix Bernstein for rectangular matrices

Main declaration: `NLAlib.matrix_bernstein`.

Atlas: `matrix-bernstein`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorem 6.1.1, equations (6.1.1–4), printed pp. 76.
-/
open MeasureTheory ProbabilityTheory

namespace NLAlib

open NLAlib

open scoped Matrix.Norms.L2Operator in
/-- The conjugate transpose is real-linear. -/
private noncomputable def ctLin (m n : Type*) : Matrix m n ℂ →ₗ[ℝ] Matrix n m ℂ where
  toFun := Matrix.conjTranspose
  map_add' X Y := Matrix.conjTranspose_add X Y
  map_smul' c X := by simp [Matrix.conjTranspose_smul]

open scoped Matrix.Norms.L2Operator in
/-- The reindexed dilation `A ↦ reindex (dilation A)` on `Fin (m + n)`. -/
private noncomputable def phiLin (m n : ℕ) :
    Matrix (Fin m) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
  (Matrix.reindexLinearEquiv ℝ ℂ finSumFinEquiv finSumFinEquiv).toLinearMap ∘ₗ
    dilationLinearMap (Fin m) (Fin n)

open scoped Matrix.Norms.L2Operator in
private lemma phiLin_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    phiLin m n A = Matrix.reindex finSumFinEquiv finSumFinEquiv (dilation A) := rfl

open scoped Matrix.Norms.L2Operator in
private lemma measurable_phiLin (m n : ℕ) : Measurable (phiLin m n) :=
  (phiLin m n).continuous_of_finiteDimensional.measurable

open scoped Matrix.Norms.L2Operator in
private lemma measurable_ct (m n : ℕ) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℂ => A.conjTranspose) :=
  (continuous_id.matrix_conjTranspose).measurable

open scoped Matrix.Norms.L2Operator in
private lemma integral_phiLin {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m n : ℕ}
    (X : Ω → Matrix (Fin m) (Fin n) ℂ) (hX : Integrable X μ) :
    ∫ ω, phiLin m n (X ω) ∂μ = phiLin m n (∫ ω, X ω ∂μ) :=
  (LinearMap.toContinuousLinearMap (phiLin m n)).integral_comp_comm hX

open scoped Matrix.Norms.L2Operator in
private lemma integral_ct {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m n : ℕ}
    (X : Ω → Matrix (Fin m) (Fin n) ℂ) (hX : Integrable X μ) :
    ∫ ω, (X ω).conjTranspose ∂μ = (∫ ω, X ω ∂μ).conjTranspose :=
  (LinearMap.toContinuousLinearMap (ctLin (Fin m) (Fin n))).integral_comp_comm hX

open scoped Matrix.Norms.L2Operator in
private lemma lambdaMax_phiLin {m n : ℕ} [NeZero m] [NeZero n] (A : Matrix (Fin m) (Fin n) ℂ) :
    lambdaMax (phiLin m n A) = ‖A‖ := by
  rw [phiLin_apply, lambdaMax_reindex]
  exact (dilation_identities A).2.2.1.trans (dilation_identities A).2.2.2

open scoped Matrix.Norms.L2Operator in
private lemma norm_phiLin {m n : ℕ} [NeZero m] [NeZero n] (A : Matrix (Fin m) (Fin n) ℂ) :
    ‖phiLin m n A‖ = ‖A‖ := by
  rw [phiLin_apply, norm_reindex]
  exact (dilation_identities A).2.2.2

end NLAlib

open NLAlib

open scoped Matrix.Norms.L2Operator in
/-- The three conclusions of Tropp's rectangular Bernstein inequality, bundled for the proof. -/
private lemma NLAlib.matrix_bernstein_package {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m n N : ℕ} [NeZero m] [NeZero n]
    (S : Fin N → Ω → Matrix (Fin m) (Fin n) ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hMeas : ∀ k, Measurable (S k)) (hIndep : iIndepFun S μ)
    (hMean : ∀ k, (∫ ω, S k ω ∂μ) = 0)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) :
    let Z := fun ω => ∑ k, S k ω
    let v := rectSecondMoment μ Z
    v = max (specNorm (∑ k, ∫ ω, S k ω * (S k ω).conjTranspose ∂μ))
      (specNorm (∑ k, ∫ ω, (S k ω).conjTranspose * S k ω ∂μ)) ∧
    (∫ ω, specNorm (Z ω) ∂μ) ≤
      Real.sqrt (2 * v * Real.log (m + n)) + L * Real.log (m + n) / 3 ∧
    ∀ t : ℝ, 0 ≤ t → μ.real {ω | t ≤ specNorm (Z ω)} ≤
      bernsteinTail (m + n) v L t := by
  intro Z v
  simp only [specNorm_eq_norm] at hBound
  -- Square integrability of the summands and their adjoints.
  have hSL2 : ∀ k, MemLp (S k) 2 μ := fun k =>
    MemLp.of_bound (hMeas k).aestronglyMeasurable L (hBound k)
  have hSint : ∀ k, Integrable (S k) μ := fun k => (hSL2 k).integrable (by norm_num)
  have hSL2h : ∀ k, MemLp (fun ω => (S k ω).conjTranspose) 2 μ := by
    intro k
    refine MemLp.of_bound ((measurable_ct m n).comp (hMeas k)).aestronglyMeasurable L ?_
    filter_upwards [hBound k] with ω hω
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hω
  have hSmeanh : ∀ k, (∫ ω, (S k ω).conjTranspose ∂μ) = 0 := by
    intro k
    rw [integral_ct μ (S k) (hSint k), hMean k, Matrix.conjTranspose_zero]
  -- Step 1: the variance statistic.
  have hZh : ∀ ω, (Z ω).conjTranspose = ∑ k, (S k ω).conjTranspose := by
    intro ω
    simp only [Z, Matrix.conjTranspose_sum]
  have hZZ : ∫ ω, Z ω * (Z ω).conjTranspose ∂μ =
      ∑ k, ∫ ω, S k ω * (S k ω).conjTranspose ∂μ := by
    simp_rw [hZh]
    exact integral_sum_mul_sum_eq_sum_integral_mul μ S id Matrix.conjTranspose measurable_id
      (measurable_ct m n) hMeas hIndep hSL2 hSL2h hMean
  have hZhZ : ∫ ω, (Z ω).conjTranspose * Z ω ∂μ =
      ∑ k, ∫ ω, (S k ω).conjTranspose * S k ω ∂μ := by
    simp_rw [hZh]
    exact integral_sum_mul_sum_eq_sum_integral_mul μ S Matrix.conjTranspose id
      (measurable_ct m n) measurable_id hMeas hIndep hSL2h hSL2 hSmeanh
  have hv1 : v = max (specNorm (∑ k, ∫ ω, S k ω * (S k ω).conjTranspose ∂μ))
      (specNorm (∑ k, ∫ ω, (S k ω).conjTranspose * S k ω ∂μ)) := by
    show max (specNorm (∫ ω, Z ω * (Z ω).conjTranspose ∂μ))
      (specNorm (∫ ω, (Z ω).conjTranspose * Z ω ∂μ)) = _
    rw [hZZ, hZhZ]
  -- Step 2: `Z` is centered, measurable and square integrable.
  have hZint : ∫ ω, Z ω ∂μ = 0 := by
    simp only [Z]
    rw [integral_finsetSum _ (fun k _ => hSint k)]
    simp [hMean]
  have hZmeas : Measurable Z := Finset.measurable_sum _ (fun k _ => hMeas k)
  have hZL2 : MemLp Z 2 μ := memLp_finsetSum _ (fun k _ => hSL2 k)
  have hdv := hermitianSecondMoment_dilation_eq_rectSecondMoment μ Z hZL2
  rw [hZint] at hdv
  simp only [sub_zero] at hdv
  -- Step 3: the Hermitian dilations on `Fin (m + n)`.
  have : NeZero (m + n) := ⟨by have := NeZero.ne m; omega⟩
  let X : Fin N → Ω → Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
    fun k ω => phiLin m n (S k ω)
  have hXmeas : ∀ k, Measurable (X k) := fun k => (measurable_phiLin m n).comp (hMeas k)
  have hXherm : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian := fun k =>
    Filter.Eventually.of_forall (fun ω => (dilation_identities (S k ω)).1.submatrix _)
  have hXL2 : ∀ k, MemLp (X k) 2 μ := by
    intro k
    refine MemLp.of_bound (hXmeas k).aestronglyMeasurable L ?_
    filter_upwards [hBound k] with ω hω
    simp only [X]
    rw [norm_phiLin]
    exact hω
  have hXindep : iIndepFun X μ :=
    hIndep.comp (fun _ => phiLin m n) (fun _ => measurable_phiLin m n)
  have hXmean : ∀ k, (∫ ω, X k ω ∂μ) = 0 := by
    intro k
    simp only [X]
    rw [integral_phiLin μ (S k) (hSint k), hMean k, map_zero]
  have hXbound : ∀ k, ∀ᵐ ω ∂μ, lambdaMax (X k ω) ≤ L := by
    intro k
    filter_upwards [hBound k] with ω hω
    simp only [X]
    rw [lambdaMax_phiLin]
    exact hω
  have hY : ∀ ω, ∑ k, phiLin m n (S k ω) = phiLin m n (Z ω) := by
    intro ω
    simp only [Z, map_sum]
  have hlam : ∀ ω, lambdaMax (∑ k, phiLin m n (S k ω)) = specNorm (Z ω) := by
    intro ω
    rw [hY ω, lambdaMax_phiLin, specNorm_eq_norm]
  have hvY : hermitianSecondMoment μ (fun ω => ∑ k, phiLin m n (S k ω)) = v := by
    have hsq : ∀ ω, (phiLin m n (Z ω)) ^ 2 =
        Matrix.reindex finSumFinEquiv finSumFinEquiv (dilation (Z ω) ^ 2) := by
      intro ω
      rw [phiLin_apply, ← Matrix.coe_reindexAlgEquiv ℝ, map_pow]
    unfold hermitianSecondMoment
    simp_rw [hY, hsq]
    rw [integral_reindex, specNorm_reindex]
    exact hdv
  have hvX : specNorm (∑ k, ∫ ω, X k ω ^ 2 ∂μ) = v := by
    rw [← hermitianSecondMoment_sum_eq μ X hXmeas hXL2 hXindep hXmean]
    exact hvY
  have H2 := integral_lambdaMax_sum_le_of_lambdaMax_le μ X hL hXmeas hXherm hXL2 hXindep hXmean
    hXbound
  refine ⟨hv1, ?_, ?_⟩
  · simp only [X, hlam] at H2
    rw [hvX] at H2
    simpa [Nat.cast_add] using H2
  · intro t ht
    have := measureReal_lambdaMax_sum_ge_le_bernsteinTail μ X hL hXmeas hXherm hXL2 hXindep hXmean
      hXbound ht
    simp only [X, hlam] at this
    rwa [hvX] at this

namespace NLAlib

section MatrixBernstein

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m n N : ℕ}
  [NeZero m] [NeZero n] (S : Fin N → Ω → Matrix (Fin m) (Fin n) ℂ)

open scoped Matrix.Norms.L2Operator in
/-- **Variance of an independent rectangular sum**: for independent, centred, bounded summands,
`rectSecondMoment μ (∑ k, S k) = max ‖∑ k, 𝔼 S k S kᴴ‖ ‖∑ k, 𝔼 S kᴴ S k‖`. Tropp 2015, eq. (6.1.2).
atlas: matrix-bernstein -/
theorem rectSecondMoment_sum_eq {L : ℝ} (hL : 0 ≤ L) (hMeas : ∀ k, Measurable (S k))
    (hIndep : iIndepFun S μ) (hMean : ∀ k, (∫ ω, S k ω ∂μ) = 0)
    (hBound : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) :
    rectSecondMoment μ (fun ω => ∑ k, S k ω) =
      max (specNorm (∑ k, ∫ ω, S k ω * (S k ω).conjTranspose ∂μ))
        (specNorm (∑ k, ∫ ω, (S k ω).conjTranspose * S k ω ∂μ)) :=
  (matrix_bernstein_package μ S L hL hMeas hIndep hMean hBound).1

open scoped Matrix.Norms.L2Operator in
/-- **Matrix Bernstein, rectangular case, expectation bound**: for independent, centred summands
with `‖S k‖ ≤ L` a.e., `𝔼 ‖∑ k, S k‖ ≤ √(2 v log (m + n)) + L log (m + n) / 3` with
`v = max ‖∑ k, 𝔼 S k S kᴴ‖ ‖∑ k, 𝔼 S kᴴ S k‖`. Tropp 2015, Thm 6.1.1, eq. (6.1.3).
atlas: matrix-bernstein -/
theorem integral_specNorm_sum_le_of_specNorm_le {L : ℝ} (hL : 0 ≤ L)
    (hMeas : ∀ k, Measurable (S k)) (hIndep : iIndepFun S μ)
    (hMean : ∀ k, (∫ ω, S k ω ∂μ) = 0) (hBound : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) :
    (∫ ω, specNorm (∑ k, S k ω) ∂μ) ≤
      Real.sqrt (2 * max (specNorm (∑ k, ∫ ω, S k ω * (S k ω).conjTranspose ∂μ))
        (specNorm (∑ k, ∫ ω, (S k ω).conjTranspose * S k ω ∂μ)) * Real.log (m + n)) +
        L * Real.log (m + n) / 3 := by
  obtain ⟨hv, hE, -⟩ := matrix_bernstein_package μ S L hL hMeas hIndep hMean hBound
  rwa [hv] at hE

open scoped Matrix.Norms.L2Operator in
/-- **Matrix Bernstein, rectangular case, tail bound**: for independent, centred summands with
`‖S k‖ ≤ L` a.e. and `t ≥ 0`, `P{‖∑ k, S k‖ ≥ t} ≤ bernsteinTail (m + n) v L t`. Tropp 2015,
Thm 6.1.1, eq. (6.1.4).
atlas: matrix-bernstein -/
theorem measureReal_specNorm_sum_ge_le_bernsteinTail {L : ℝ} (hL : 0 ≤ L)
    (hMeas : ∀ k, Measurable (S k)) (hIndep : iIndepFun S μ)
    (hMean : ∀ k, (∫ ω, S k ω ∂μ) = 0) (hBound : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ k, S k ω)} ≤
      bernsteinTail (m + n) (max (specNorm (∑ k, ∫ ω, S k ω * (S k ω).conjTranspose ∂μ))
        (specNorm (∑ k, ∫ ω, (S k ω).conjTranspose * S k ω ∂μ))) L t := by
  obtain ⟨hv, -, hT⟩ := matrix_bernstein_package μ S L hL hMeas hIndep hMean hBound
  have := hT t ht
  rwa [hv] at this

end MatrixBernstein

end NLAlib
