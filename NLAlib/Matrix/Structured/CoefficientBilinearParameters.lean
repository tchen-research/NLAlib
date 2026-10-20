import NLAlib.Matrix.Structured.CoefficientTraceFrame
import NLAlib.Matrix.Norms.BilinearProbes
import NLAlib.Matrix.Basic.RankOneCorrection
import NLAlib.Matrix.Spectral.PositiveTraceNorm

/-! # Actual bilinear, variance and entry-covariance coefficient parameters

The source sigma-star is the genuine bilinear square-energy supremum.
Its comparisons with the actual matrix variance and full unnormalized
entry covariance are proved directly from coefficient matrices.
Source: arXiv:2108.06312v2, Section 2; arXiv:2406.11453v2, Section 2.
Atlas: gaussian-free-spectrum-two-sided (partial).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix ComplexOrder MatrixOrder
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

omit [DecidableEq ι] in
/-- The actual bilinear coefficient variance is at most the usual matrix
series variance for Hermitian coefficients, including empty dimensions. -/
theorem bilinearSquareMass_le_specNorm_coefficientVariance
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) :
    bilinearSquareMass A Finset.univ ≤ specNorm (coefficientVariance A) := by
  obtain ⟨v, w, hv, hw, he⟩ := exists_bilinearSquareMass_eq A Finset.univ
  rw [he]
  calc
    _ ≤ ∑ i : ι, ‖WithLp.toLp 2 (A i *ᵥ w.ofLp)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := norm_inner_le_norm (𝕜 := ℂ) v (WithLp.toLp 2 (A i *ᵥ w.ofLp))
      have heq : inner ℂ v (WithLp.toLp 2 (A i *ᵥ w.ofLp)) =
          star v.ofLp ⬝ᵥ (A i *ᵥ w.ofLp) := by
        rw [← WithLp.toLp_ofLp 2 v, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
      rw [heq] at hi
      exact pow_le_pow_left₀ (norm_nonneg _)
        (hi.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hv (norm_nonneg _))) 2
    _ ≤ specNorm (∑ i : ι, (A i)ᴴ * A i) :=
      sum_norm_sq_mulVec_le_specNorm_sum_gram A Finset.univ w hw
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun C => C * A i) (hA i).eq

open scoped Matrix.Norms.L2Operator in
/-- The actual bilinear coefficient variance is at most the full
unnormalized vectorized covariance norm. This needs no Hermitian hypothesis. -/
theorem bilinearSquareMass_le_specNorm_coefficientCovariance
    (A : ι → Matrix n n ℂ) :
    bilinearSquareMass A Finset.univ ≤ specNorm (coefficientCovariance A) := by
  obtain ⟨v, w, hv, hw, he⟩ := exists_bilinearSquareMass_eq A Finset.univ
  let U : Matrix n n ℂ := Matrix.vecMulVec w.ofLp (star v.ofLp)
  have htrace (i : ι) : (U * A i).trace = star v.ofLp ⬝ᵥ (A i *ᵥ w.ofLp) := by
    rw [Matrix.trace_mul_comm]
    simp only [U, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  have hF : frobSq U ≤ 1 := by
    dsimp only [U]
    rw [frobSq_vecMulVec_star, WithLp.toLp_ofLp, WithLp.toLp_ofLp]
    have hv' : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
    have hw' : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
    simpa only [one_mul] using mul_le_mul hw' hv' (sq_nonneg ‖v‖) (by norm_num : (0 : ℝ) ≤ 1)
  rw [he]
  calc
    _ = ∑ i, ‖(U * A i).trace‖ ^ 2 := by simp only [htrace]
    _ ≤ specNorm (coefficientCovariance A) * frobSq U :=
      sum_norm_trace_mul_sq_le_coefficientCovariance_mul_frobSq A U
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hF (specNorm_nonneg _)

omit [DecidableEq ι] in
open scoped Matrix.Norms.L2Operator in
/-- Coordinate unit probes control the true Hermitian matrix variance by
dimension squared times the actual bilinear coefficient variance. -/
theorem specNorm_coefficientVariance_le_card_sq_mul_bilinearSquareMass
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) :
    specNorm (coefficientVariance A) ≤
      (Fintype.card n : ℝ) ^ 2 * bilinearSquareMass A Finset.univ := by
  have hpos : (coefficientVariance A).PosSemidef := by
    change (∑ i, A i * A i).PosSemidef
    exact Matrix.posSemidef_sum _ fun i _ => by
      simpa only [(hA i).eq] using Matrix.posSemidef_conjTranspose_mul_self (A i)
  let e (j : n) : EuclideanSpace ℂ n := EuclideanSpace.single j 1
  have heval (j k : n) (B : Matrix n n ℂ) :
      star (e j).ofLp ⬝ᵥ (B *ᵥ (e k).ofLp) = B j k := by simp [e]
  have he (j k : n) : (∑ i : ι, ‖A i j k‖ ^ 2) ≤ bilinearSquareMass A Finset.univ := by
    simpa only [heval] using sum_bilinear_sq_le_bilinearSquareMass A Finset.univ
      (e j) (e k) (by simp [e]) (by simp [e])
  have htrace : (coefficientVariance A).trace.re =
      ∑ i : ι, ∑ j : n, ∑ k : n, ‖A i j k‖ ^ 2 := by
    simp only [coefficientVariance, Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hsq : (A i * A i).trace.re = frobSq (A i) := by
      simpa only [(hA i).eq, RCLike.re_eq_complex_re] using
        (frobSq_eq_re_trace_conjTranspose_mul_self (A i)).symm
    rw [hsq, frobSq_eq_sum_norm_sq]
  calc
    _ ≤ (coefficientVariance A).trace.re := hpos.specNorm_le_re_trace
    _ = ∑ j : n, ∑ k : n, ∑ i : ι, ‖A i j k‖ ^ 2 := by
      rw [htrace, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ ≤ ∑ _j : n, ∑ _k : n, bilinearSquareMass A Finset.univ :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => he j k
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

open scoped Matrix.Norms.L2Operator in
/-- The literal sigma-star is bounded by the Gaussian/free geometric
variance-covariance scale, without changing any covariance normalization.
Source: arXiv:2406.11453v2, Section 2.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem sqrt_bilinearSquareMass_le_sqrt_variance_covariance
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) :
    Real.sqrt (bilinearSquareMass A Finset.univ) ≤
      Real.sqrt (Real.sqrt (specNorm (coefficientVariance A)) *
        Real.sqrt (specNorm (coefficientCovariance A))) := by
  have hv := Real.sqrt_le_sqrt (bilinearSquareMass_le_specNorm_coefficientVariance A hA)
  have hc := Real.sqrt_le_sqrt (bilinearSquareMass_le_specNorm_coefficientCovariance A)
  apply (Real.le_sqrt (Real.sqrt_nonneg _) (by positivity)).mpr
  simpa only [pow_two] using mul_le_mul hv hc (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

open scoped Matrix.Norms.L2Operator in
/-- The actual matrix-series standard deviation is at most dimension
times the literal sigma-star; empty dimensions are included. -/
theorem sqrt_variance_le_card_mul_sqrt_bilinearSquareMass
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) :
    Real.sqrt (specNorm (coefficientVariance A)) ≤
      (Fintype.card n : ℝ) * Real.sqrt (bilinearSquareMass A Finset.univ) := by
  have h := Real.sqrt_le_sqrt (specNorm_coefficientVariance_le_card_sq_mul_bilinearSquareMass A hA)
  simpa only [Real.sqrt_mul (sq_nonneg (Fintype.card n : ℝ)),
    Real.sqrt_sq (Nat.cast_nonneg (Fintype.card n))] using h

open scoped Matrix.Norms.L2Operator in
/-- The full entry-covariance standard deviation is at least the usual
matrix-series standard deviation divided by dimension, in nonempty shape. -/
theorem sqrt_variance_div_card_le_sqrt_covariance [Nonempty n]
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian) :
    Real.sqrt (specNorm (coefficientVariance A)) / (Fintype.card n : ℝ) ≤
      Real.sqrt (specNorm (coefficientCovariance A)) := by
  rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card n)]
  calc
    _ ≤ (Fintype.card n : ℝ) * Real.sqrt (bilinearSquareMass A Finset.univ) :=
      sqrt_variance_le_card_mul_sqrt_bilinearSquareMass A hA
    _ ≤ _ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (bilinearSquareMass_le_specNorm_coefficientCovariance A)) (Nat.cast_nonneg _)

end NLAlib
