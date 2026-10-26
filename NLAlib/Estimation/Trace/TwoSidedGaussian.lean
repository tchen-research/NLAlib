import NLAlib.Estimation.Trace.GaussianControlVariate
import NLAlib.RandomMatrix.Gaussian.Moments.ApproxMultiplication

/-!
# Exact variance of a two-sided Gaussian Frobenius estimator

The two sketch widths need not agree. Conditioning on the left sketch turns the
estimator into an independent Gaussian control variate; Gaussian approximate
matrix multiplication evaluates the remaining residual moment exactly.

Source: Chen--Halikias--Musco--Persson, Hutch#, equations (2), (7) and Gaussian
variance calculation; the supplied Estimation derivations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {m n r s : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype s]

/-- The two-sided Frobenius correction with the two sketch widths normalized separately. -/
def twoSidedGaussianFrobEstimate (A : Matrix m n ℝ)
    (G : Matrix n r ℝ) (H : Matrix m s ℝ) : ℝ :=
  frobSq (A * G) / Fintype.card r + frobSq (Hᵀ * A) / Fintype.card s -
    frobSq (Hᵀ * A * G) / ((Fintype.card r : ℝ) * Fintype.card s)

private theorem hutchinsonEstimate_gram (A : Matrix m n ℝ) (G : Matrix n r ℝ) :
    hutchinsonEstimate (Aᵀ * A) G = frobSq (A * G) / Fintype.card r := by
  rw [hutchinsonEstimate, frobSq_eq_sum_sq]
  congr 1
  have hq (k : r) : quadForm (Aᵀ * A) (fun i => G i k) =
      ∑ j, (A * G) j k ^ 2 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, star_trivial,
      dotProduct, Matrix.mulVec, Matrix.mul_apply, pow_two] using
      quadForm_conjTranspose_mul_self A (fun i => G i k)
  simp_rw [hq]
  exact Finset.sum_comm

private theorem hutchinsonEstimate_sub (M B : Matrix n n ℝ) (G : Matrix n r ℝ) :
    hutchinsonEstimate (M - B) G = hutchinsonEstimate M G - hutchinsonEstimate B G := by
  simp only [hutchinsonEstimate, quadForm, Matrix.sub_mulVec, dotProduct_sub,
    Finset.sum_sub_distrib, sub_div]

private theorem hutchinsonEstimate_smul (c : ℝ) (B : Matrix n n ℝ) (G : Matrix n r ℝ) :
    hutchinsonEstimate (c • B) G = c * hutchinsonEstimate B G := by
  simp only [hutchinsonEstimate, quadForm, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, ← Finset.mul_sum]
  ring

/-- The two-sided estimator is the control variate obtained from the other sketch's Gram matrix. -/
theorem twoSidedGaussianFrobEstimate_eq_controlVariate (A : Matrix m n ℝ)
    (G : Matrix n r ℝ) (H : Matrix m s ℝ) :
    twoSidedGaussianFrobEstimate A G H =
      gaussianControlVariateEstimate (Aᵀ * A)
        ((Fintype.card s : ℝ)⁻¹ • ((Hᵀ * A)ᵀ * (Hᵀ * A))) G := by
  have hf (T : Matrix s n ℝ) : (Tᵀ * T).trace = frobSq T := by
    simpa using (frobSq_eq_re_trace_conjTranspose_mul_self T).symm
  rw [gaussianControlVariateEstimate, Matrix.trace_smul, hf,
    hutchinsonEstimate_sub, hutchinsonEstimate_smul,
    hutchinsonEstimate_gram, hutchinsonEstimate_gram]
  simp only [twoSidedGaussianFrobEstimate, smul_eq_mul]
  ring

section FiniteMatrices

variable {a b u v : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem twoSidedGaussian_moments_of_measurable
    (A : Matrix (Fin a) (Fin b) ℝ) (hu : 0 < u) (hv : 0 < v)
    {G : Ω → Matrix (Fin b) (Fin u) ℝ} {H : Ω → Matrix (Fin a) (Fin v) ℝ}
    (hG : HasLaw G (gaussianMatrix (Fin b) (Fin u)) μ)
    (hH : HasLaw H (gaussianMatrix (Fin a) (Fin v)) μ)
    (hHm : Measurable H) (hind : IndepFun H G μ) :
    MemLp (fun ω => twoSidedGaussianFrobEstimate A (G ω) (H ω)) 2 μ ∧
    (∫ ω, twoSidedGaussianFrobEstimate A (G ω) (H ω) ∂μ) = frobSq A ∧
    Var[fun ω => twoSidedGaussianFrobEstimate A (G ω) (H ω); μ] =
      2 / ((u : ℝ) * v) * (frobSq (Aᵀ * A) + frobSq A ^ 2) ∧
    Var[fun ω => twoSidedGaussianFrobEstimate A (G ω) (H ω); μ] ≤
      4 / ((u : ℝ) * v) * frobSq A ^ 2 := by
  let : Nonempty (Fin u) := Fin.pos_iff_nonempty.mp hu
  let B : Matrix (Fin a) (Fin v) ℝ → Matrix (Fin b) (Fin b) ℝ := fun X =>
    (v : ℝ)⁻¹ • ((Xᵀ * A)ᵀ * (Xᵀ * A))
  have hBm : Measurable B := by
    dsimp [B]
    fun_prop
  have hBeq (X : Matrix (Fin a) (Fin v) ℝ) :
      B X = Aᵀ * ((1 / (v : ℝ)) • (X * Xᵀ)) * A := by
    simp only [B, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      Matrix.mul_smul, Matrix.smul_mul, one_div]
  have he : ∫ ω, frobSq (Aᵀ * A - B (H ω)) ∂μ =
      (frobSq A * frobSq A + frobSq (Aᵀ * A)) / v := by
    simp_rw [frobSq_sub_comm (Aᵀ * A), hBeq]
    simpa only [Matrix.transpose_transpose, frobSq_transpose] using
      (integral_frobSq_mul_gram_mul_transpose_sub_of_hasLaw hH hv Aᵀ Aᵀ).1
  have hi : Integrable (fun ω => frobSq (Aᵀ * A - B (H ω))) μ := by
    by_cases hA : A = 0
    · simp [hA, B]
    · apply Integrable.of_integral_ne_zero
      rw [he]
      have hp : 0 < frobSq A := lt_of_le_of_ne (frobSq_nonneg A)
        (Ne.symm ((frobSq_eq_zero_iff A).not.mpr hA))
      exact (div_pos (add_pos_of_pos_of_nonneg (mul_pos hp hp) (frobSq_nonneg _))
        (Nat.cast_pos.mpr hv)).ne'
  have hM : (Aᵀ * A).IsHermitian := by
    simpa using Matrix.isHermitian_conjTranspose_mul_self A
  have hB : ∀ᵐ ω ∂μ, (B (H ω)).IsHermitian := ae_of_all _ fun ω => by
    apply Matrix.IsHermitian.smul _ (by simp)
    simpa using Matrix.isHermitian_conjTranspose_mul_self ((H ω)ᵀ * A)
  have hInd : IndepFun (fun ω => B (H ω)) G μ := hind.comp hBm measurable_id
  obtain ⟨hLp, hmean, hvar, _⟩ :=
    gaussianControlVariateEstimate_moments_of_indepFun hM (hBm.comp hHm) hB hG hInd hi
  have hest (ω : Ω) : twoSidedGaussianFrobEstimate A (G ω) (H ω) =
      gaussianControlVariateEstimate (Aᵀ * A) (B (H ω)) (G ω) := by
    simpa only [Fintype.card_fin] using twoSidedGaussianFrobEstimate_eq_controlVariate A (G ω) (H ω)
  change MemLp (fun ω => gaussianControlVariateEstimate (Aᵀ * A) (B (H ω)) (G ω)) 2 μ at hLp
  change (∫ ω, gaussianControlVariateEstimate (Aᵀ * A) (B (H ω)) (G ω) ∂μ) = _ at hmean
  change Var[fun ω => gaussianControlVariateEstimate (Aᵀ * A) (B (H ω)) (G ω); μ] = _ at hvar
  simp_rw [← hest] at hLp hmean hvar
  have htrace : (Aᵀ * A).trace = frobSq A := by
    simpa using (frobSq_eq_re_trace_conjTranspose_mul_self A).symm
  rw [htrace] at hmean
  simp only [Function.comp_apply, Fintype.card_fin, he] at hvar
  have hvar' : Var[fun ω => twoSidedGaussianFrobEstimate A (G ω) (H ω); μ] =
      2 / ((u : ℝ) * v) * (frobSq (Aᵀ * A) + frobSq A ^ 2) := hvar.trans (by ring)
  refine ⟨hLp, hmean, hvar', ?_⟩
  rw [hvar']
  have hle : frobSq (Aᵀ * A) ≤ frobSq A ^ 2 := by
    simpa only [frobSq_transpose, pow_two] using frobSq_mul_le Aᵀ A
  calc
    2 / ((u : ℝ) * v) * (frobSq (Aᵀ * A) + frobSq A ^ 2) ≤
        2 / ((u : ℝ) * v) * (frobSq A ^ 2 + frobSq A ^ 2) := by gcongr
    _ = _ := by ring

/-- Independent standard Gaussian sketches give the exact two-sided Frobenius
variance, with unequal positive widths and arbitrary rectangular input. In
particular the estimator is square integrable, including zero and empty inputs.
Source: Hutch#, Theorem 1.1 and Fact 2.2; unequal-width extension by the same calculation.
atlas: two-sided-gaussian-frobenius-variance -/
theorem twoSidedGaussianFrobEstimate_moments_of_indepFun
    (A : Matrix (Fin a) (Fin b) ℝ) (hu : 0 < u) (hv : 0 < v)
    {G : Ω → Matrix (Fin b) (Fin u) ℝ} {H : Ω → Matrix (Fin a) (Fin v) ℝ}
    (hG : HasLaw G (gaussianMatrix (Fin b) (Fin u)) μ)
    (hH : HasLaw H (gaussianMatrix (Fin a) (Fin v)) μ)
    (hind : IndepFun H G μ) :
    MemLp (fun ω => twoSidedGaussianFrobEstimate A (G ω) (H ω)) 2 μ ∧
    (∫ ω, twoSidedGaussianFrobEstimate A (G ω) (H ω) ∂μ) = frobSq A ∧
    Var[fun ω => twoSidedGaussianFrobEstimate A (G ω) (H ω); μ] =
      2 / ((u : ℝ) * v) * (frobSq (Aᵀ * A) + frobSq A ^ 2) ∧
    Var[fun ω => twoSidedGaussianFrobEstimate A (G ω) (H ω); μ] ≤
      4 / ((u : ℝ) * v) * frobSq A ^ 2 := by
  let H' := hH.aemeasurable.mk H
  have hHH : H =ᵐ[μ] H' := hH.aemeasurable.ae_eq_mk
  obtain ⟨hLp, hmean, hvar, hbound⟩ := twoSidedGaussian_moments_of_measurable A hu hv hG
    (hH.congr hHH.symm) hH.aemeasurable.measurable_mk (hind.congr hHH Filter.EventuallyEq.rfl)
  have he : (fun ω => twoSidedGaussianFrobEstimate A (G ω) (H ω)) =ᵐ[μ]
      fun ω => twoSidedGaussianFrobEstimate A (G ω) (H' ω) :=
    hHH.mono fun ω hω => congrArg (twoSidedGaussianFrobEstimate A (G ω)) hω
  exact ⟨(memLp_congr_ae he).2 hLp, (integral_congr_ae he).trans hmean,
    (variance_congr he).trans hvar, (variance_congr he).trans_le hbound⟩

end FiniteMatrices
end NLAlib
