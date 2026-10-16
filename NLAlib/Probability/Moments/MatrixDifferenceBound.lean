import NLAlib.Probability.Moments.MatrixDifference

/-! # Bounded centered summands control actual matrix difference third moments

The normalized independent-copy Schatten cubic moment is at most four times
the centered spectral bound times the actual variance norm. All integrability
and independent-copy second-moment identities are proved from the laws.
Source: final bounded-summand paragraph of the reroute for
`cauchy-transform-gaussian-universality`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped Matrix ComplexOrder MatrixOrder
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

open scoped Matrix.Norms.L2Operator in
private theorem re_trace_sq_nonneg {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    0 ≤ (A ^ 2).trace.re := by
  rw [re_trace_pow_eq_sum_eigenvalues_pow A hA]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

open scoped Matrix.Norms.L2Operator in
private theorem integrable_re_trace {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → Matrix n n ℂ} (hf : Integrable f μ) :
    Integrable (fun x => (f x).trace.re) μ := by
  simpa [Matrix.traceLinearMap] using
    ((Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap.integrable_comp hf).re

open scoped Matrix.Norms.L2Operator in
/-- The genuine independent-copy cubic Schatten moment is integrable under an
almost-everywhere Hermitian law and a bounded centered spectral norm. -/
theorem integrable_schattenNormReal_matrix_sub_copy_pow_three
    (ν : Measure (Matrix n n ℂ)) [IsProbabilityMeasure ν] {L : ℝ} (hL : 0 ≤ L)
    (hHerm : ∀ᵐ S ∂ν, S.IsHermitian)
    (hbound : ∀ᵐ S ∂ν, specNorm (S - ∫ T, T ∂ν) ≤ L) :
    Integrable (fun p : Matrix n n ℂ × Matrix n n ℂ =>
      schattenNormReal (p.1 - p.2) 3 ^ 3) (ν.prod ν) := by
  have hm : AEStronglyMeasurable (fun p : Matrix n n ℂ × Matrix n n ℂ =>
      schattenNormReal (p.1 - p.2) 3 ^ 3) (ν.prod ν) :=
    (((continuous_schattenNormReal (by norm_num : (0 : ℝ) < 3)).comp
      (continuous_fst.sub continuous_snd)).pow 3).aestronglyMeasurable
  apply (MemLp.of_bound hm ((2 * L) * (Fintype.card n * (2 * L) ^ 2)) ?_ :
    MemLp _ 1 (ν.prod ν)).integrable le_rfl
  filter_upwards [ae_specNorm_matrix_sub_copy_le ν hbound,
    Measure.quasiMeasurePreserving_fst.ae hHerm,
    Measure.quasiMeasurePreserving_snd.ae hHerm] with p hp hH1 hH2
  have hH := hH1.sub hH2
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (schattenNormReal_nonneg _ _) _)]
  have htr : ((p.1 - p.2) ^ 2).trace.re ≤ Fintype.card n * (2 * L) ^ 2 := by
    apply (Complex.re_le_norm _).trans
    apply (norm_trace_le_card_mul_specNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact (norm_pow_le _ 2).trans (pow_le_pow_left₀ (norm_nonneg _) hp 2)
  calc
    _ ≤ specNorm (p.1 - p.2) * ((p.1 - p.2) ^ 2).trace.re :=
      schattenNormReal_pow_three_le_specNorm_mul_re_trace_sq hH
    _ ≤ (2 * L) * (Fintype.card n * (2 * L) ^ 2) :=
      mul_le_mul hp htr (re_trace_sq_nonneg hH) (by positivity)

open scoped Matrix.Norms.L2Operator in
/-- The independent-copy third moment of one bounded centered Hermitian matrix
law is controlled by four times its actual centered second trace moment. -/
theorem integral_schattenNormReal_matrix_sub_copy_pow_three_div_card_le
    (ν : Measure (Matrix n n ℂ)) [IsProbabilityMeasure ν] {L : ℝ} (hL : 0 ≤ L)
    (hHerm : ∀ᵐ S ∂ν, S.IsHermitian)
    (hbound : ∀ᵐ S ∂ν, specNorm (S - ∫ T, T ∂ν) ≤ L) :
    (∫ p : Matrix n n ℂ × Matrix n n ℂ,
      schattenNormReal (p.1 - p.2) 3 ^ 3 / (Fintype.card n : ℝ) ∂ν.prod ν) ≤
      4 * L * ((∫ S : Matrix n n ℂ, (S - ∫ T, T ∂ν) ^ 2 ∂ν).trace.re /
        (Fintype.card n : ℝ)) := by
  have hcubic := integrable_schattenNormReal_matrix_sub_copy_pow_three ν hL hHerm hbound
  have hsq := integrable_matrix_sub_copy_sq ν hL hbound
  have htr := integrable_re_trace hsq
  have hh := integral_mono_ae hcubic (htr.const_mul (2 * L)) ?_
  swap
  · filter_upwards [ae_specNorm_matrix_sub_copy_le ν hbound,
      Measure.quasiMeasurePreserving_fst.ae hHerm,
      Measure.quasiMeasurePreserving_snd.ae hHerm] with p hp hH1 hH2
    have hH := hH1.sub hH2
    exact (schattenNormReal_pow_three_le_specNorm_mul_re_trace_sq hH).trans
      (mul_le_mul_of_nonneg_right hp (re_trace_sq_nonneg hH))
  rw [integral_const_mul] at hh
  have he : (∫ p : Matrix n n ℂ × Matrix n n ℂ, ((p.1 - p.2) ^ 2).trace.re ∂ν.prod ν) =
      2 * (∫ S : Matrix n n ℂ, (S - ∫ T, T ∂ν) ^ 2 ∂ν).trace.re := by
    have ht : (∫ p : Matrix n n ℂ × Matrix n n ℂ, (p.1 - p.2) ^ 2 ∂ν.prod ν).trace.re =
        ∫ p : Matrix n n ℂ × Matrix n n ℂ, ((p.1 - p.2) ^ 2).trace.re ∂ν.prod ν := by
      simpa only [RCLike.re_eq_complex_re] using Matrix.re_trace_integral hsq
    rw [← ht, integral_matrix_sub_copy_sq ν hL hbound]
    simp [two_smul, two_mul]
  rw [integral_div]
  calc
    _ ≤ ((2 * L) * ∫ p : Matrix n n ℂ × Matrix n n ℂ,
        ((p.1 - p.2) ^ 2).trace.re ∂ν.prod ν) / (Fintype.card n : ℝ) :=
      div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)
    _ = _ := by rw [he]; ring

open scoped Matrix.Norms.L2Operator in
/-- The actual independent-copy normalized Schatten cubic parameter satisfies
`M3 ≤ 4 L sigma²`, with the actual centered variance matrix. No moment,
covariance, or conclusion-shaped interface is assumed. Zero bound, zero
variance and empty summand families are included.
Source: bounded-summand reroute, final paragraph.
atlas: cauchy-transform-gaussian-universality (partial)
-/
theorem matrixDifferenceThirdMoment_le_four_mul_bound_mul_variance
    {ι : Type*} [Fintype ι] (ν : ι → Measure (Matrix n n ℂ))
    [∀ i, IsProbabilityMeasure (ν i)] {L : ℝ} (hL : 0 ≤ L)
    (hHerm : ∀ i, ∀ᵐ S ∂ν i, S.IsHermitian)
    (hbound : ∀ i, ∀ᵐ S ∂ν i, specNorm (S - ∫ T, T ∂ν i) ≤ L) :
    matrixDifferenceThirdMoment ν ≤
      4 * L * specNorm (∑ i, ∫ S : Matrix n n ℂ, (S - ∫ T, T ∂ν i) ^ 2 ∂ν i) := by
  let V := ∑ i, ∫ S : Matrix n n ℂ, (S - ∫ T, T ∂ν i) ^ 2 ∂ν i
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have htrace : V.trace.re / (Fintype.card n : ℝ) ≤ specNorm V := by
    calc
      _ ≤ ‖V.trace‖ / (Fintype.card n : ℝ) :=
        div_le_div_of_nonneg_right (Complex.re_le_norm _) hd.le
      _ ≤ ((Fintype.card n : ℝ) * specNorm V) / (Fintype.card n : ℝ) :=
        div_le_div_of_nonneg_right (norm_trace_le_card_mul_specNorm V) hd.le
      _ = _ := by field_simp
  calc
    _ ≤ ∑ i, 4 * L * ((∫ S : Matrix n n ℂ, (S - ∫ T, T ∂ν i) ^ 2 ∂ν i).trace.re /
        (Fintype.card n : ℝ)) := Finset.sum_le_sum (fun i _ =>
      integral_schattenNormReal_matrix_sub_copy_pow_three_div_card_le (ν i) hL (hHerm i) (hbound i))
    _ = 4 * L * (V.trace.re / (Fintype.card n : ℝ)) := by
      simp only [V, Matrix.trace_sum, Complex.re_sum, Finset.sum_div, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left htrace (by positivity)

end NLAlib
