import NLAlib.Probability.Concentration.Matrix.MatrixBernstein
import NLAlib.Probability.Concentration.Basic.MatrixCalculus
import NLAlib.Matrix.Norms.Reindex

/-!
# Bernstein bounds for arbitrary finite Hermitian families

The existing rectangular Bernstein theorem is transported to arbitrary
finite matrix and summand index types. For Hermitian increments both
rectangular variance matrices are the actual sum of square expectations.
Source: Tropp (2015), Theorem 6.1.1; arXiv:2201.05142v3, Lemma 7.5.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

variable {ι n Ω : Type*} [Fintype ι] [Fintype n] [DecidableEq n] [Nonempty n]
  [MeasurableSpace Ω]

open scoped Matrix.Norms.L2Operator in
/-- Actual bounded independent centered Hermitian increments satisfy the
Bernstein expectation and tail bounds with their literal matrix variance.
The summand family may be empty. -/
theorem integral_and_measureReal_specNorm_sum_le_bernstein_hermitian
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ι → Ω → Matrix n n ℂ)
    {R : ℝ} (hR : 0 ≤ R) (hZm : ∀ i, Measurable (Z i))
    (hIndep : iIndepFun Z μ)
    (hZH : ∀ i, ∀ᵐ ω ∂μ, (Z i ω).IsHermitian)
    (hZ : ∀ i, ∀ᵐ ω ∂μ, specNorm (Z i ω) ≤ R)
    (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0) :
    ((∫ ω, specNorm (∑ i, Z i ω) ∂μ) ≤
      Real.sqrt (2*specNorm (∑ i, ∫ ω, Z i ω^2 ∂μ)*Real.log (2*Fintype.card n)) +
        R*Real.log (2*Fintype.card n)/3) ∧
    (∀ t : ℝ, 0 ≤ t → μ.real {ω | t ≤ specNorm (∑ i, Z i ω)} ≤
      bernsteinTail (2*Fintype.card n) (specNorm (∑ i, ∫ ω, Z i ω^2 ∂μ)) R t) := by
  classical
  let : NeZero (Fintype.card n) := ⟨Fintype.card_ne_zero⟩
  let e := Fintype.equivFin n
  let f := (Fintype.equivFin ι).symm
  let E : Matrix n n ℂ ≃ₗ[ℝ] Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ :=
    Matrix.reindexLinearEquiv ℝ ℂ e e
  let Y : Fin (Fintype.card ι) → Ω →
      Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ :=
    fun k ω => E (Z (f k) ω)
  have hEMeas : Measurable E := E.toContinuousLinearEquiv.continuous.measurable
  have hYm : ∀ k, Measurable (Y k) := fun k => hEMeas.comp (hZm (f k))
  have hYind : iIndepFun Y μ := (iIndepFun.precomp f.injective hIndep).comp
    (fun _ => E) (fun _ => hEMeas)
  have hYbound : ∀ k, ∀ᵐ ω ∂μ, specNorm (Y k ω) ≤ R := by
    intro k
    filter_upwards [hZ (f k)] with ω hω
    change specNorm ((Z (f k) ω).reindex e e) ≤ R
    rwa [specNorm_reindex]
  have hYmean : ∀ k, ∫ ω, Y k ω ∂μ = 0 := by
    intro k
    rw [show (∫ ω, Y k ω ∂μ) = E (∫ ω, Z (f k) ω ∂μ) from
      integral_reindex μ e (Z (f k)), hmean, map_zero]
  have hsum (ω : Ω) : (∑ k, Y k ω) = E (∑ i, Z i ω) := by
    change (∑ k, E (Z (f k) ω)) = _
    rw [← map_sum]
    exact congrArg E (f.sum_comp (fun i => Z i ω))
  have hnorm (ω : Ω) : specNorm (∑ k, Y k ω) = specNorm (∑ i, Z i ω) := by
    rw [hsum]
    exact specNorm_reindex _ e e
  have hprod (k : Fin (Fintype.card ι)) :
      (∫ ω, Y k ω * (Y k ω)ᴴ ∂μ) = E (∫ ω, Z (f k) ω^2 ∂μ) ∧
      (∫ ω, (Y k ω)ᴴ * Y k ω ∂μ) = E (∫ ω, Z (f k) ω^2 ∂μ) := by
    have hp : ∀ᵐ ω ∂μ, Y k ω * (Y k ω)ᴴ = E (Z (f k) ω^2) ∧
        (Y k ω)ᴴ * Y k ω = E (Z (f k) ω^2) := by
      filter_upwards [hZH (f k)] with ω hω
      have hH : (Y k ω).IsHermitian := hω.submatrix e.symm
      have he : E (Z (f k) ω^2) = (Y k ω)^2 :=
        (Matrix.reindexAlgEquiv ℂ ℂ e).map_pow _ 2
      rw [he, pow_two, hH.eq]
      exact ⟨rfl, rfl⟩
    exact ⟨(integral_congr_ae (hp.mono fun _ h => h.1)).trans
        (integral_reindex μ e (fun ω => Z (f k) ω^2)),
      (integral_congr_ae (hp.mono fun _ h => h.2)).trans
        (integral_reindex μ e (fun ω => Z (f k) ω^2))⟩
  have hvar :
      (∑ k, ∫ ω, Y k ω*(Y k ω)ᴴ ∂μ) = E (∑ i, ∫ ω, Z i ω^2 ∂μ) ∧
      (∑ k, ∫ ω, (Y k ω)ᴴ*Y k ω ∂μ) = E (∑ i, ∫ ω, Z i ω^2 ∂μ) := by
    have he : (∑ k, E (∫ ω, Z (f k) ω^2 ∂μ)) = E (∑ i, ∫ ω, Z i ω^2 ∂μ) := by
      rw [← map_sum]
      exact congrArg E (f.sum_comp (fun i => ∫ ω, Z i ω^2 ∂μ))
    exact ⟨(Finset.sum_congr rfl fun k _ => (hprod k).1).trans he,
      (Finset.sum_congr rfl fun k _ => (hprod k).2).trans he⟩
  have he := integral_specNorm_sum_le_of_specNorm_le μ Y hR hYm hYind hYmean hYbound
  simp only [hvar.1, hvar.2, show ∀ A : Matrix n n ℂ, specNorm (E A) = specNorm A from
    fun A => specNorm_reindex A e e, max_self, hnorm] at he
  constructor
  · simpa only [two_mul, Nat.cast_add] using he
  · intro t hpos
    have ht := measureReal_specNorm_sum_ge_le_bernsteinTail μ Y hR hYm hYind hYmean hYbound hpos
    simpa only [hvar.1, hvar.2, show ∀ A : Matrix n n ℂ, specNorm (E A) = specNorm A from
      fun A => specNorm_reindex A e e, max_self, hnorm, two_mul] using ht

open scoped Matrix.Norms.L2Operator in
/-- At a moment order above log dimension, the actual independent centered
sum has expected norm at most `2*σ*sqrt(p)+R*p`. The variance budget bounds
the actual sum of square expectations. Source: arXiv:2201.05142v3, Lemma 7.5.
atlas: independent-sum-spectrum-universality (partial) -/
theorem integral_specNorm_sum_pi_le_two_mul_sqrt_add_of_log_le
    (ν : ι → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (Z : ι → Ω → Matrix n n ℂ) (hZm : ∀ i, Measurable (Z i))
    {R σ p : ℝ} (hR : 0 ≤ R) (hσ : 0 ≤ σ) (hp : 0 ≤ p)
    (hd : 2 ≤ Fintype.card n) (hlog : Real.log (Fintype.card n) ≤ p)
    (hZH : ∀ i, ∀ᵐ ω ∂ν i, (Z i ω).IsHermitian)
    (hZ : ∀ i, ∀ᵐ ω ∂ν i, specNorm (Z i ω) ≤ R)
    (hmean : ∀ i, ∫ ω, Z i ω ∂ν i = 0)
    (hvariance : specNorm (∑ i, ∫ ω, Z i ω^2 ∂ν i) ≤ σ^2) :
    (∫ x : ι → Ω, specNorm (∑ i, Z i (x i)) ∂Measure.pi ν) ≤
      2*σ*Real.sqrt p + R*p := by
  classical
  let Y (i : ι) (x : ι → Ω) := Z i (x i)
  have hYm : ∀ i, Measurable (Y i) := fun i => (hZm i).comp (measurable_pi_apply i)
  have hYH : ∀ i, ∀ᵐ x ∂Measure.pi ν, (Y i x).IsHermitian := fun i =>
    (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hZH i)
  have hYB : ∀ i, ∀ᵐ x ∂Measure.pi ν, specNorm (Y i x) ≤ R := fun i =>
    (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hZ i)
  have hYmean : ∀ i, ∫ x, Y i x ∂Measure.pi ν = 0 := by
    intro i
    rw [show (∫ x, Y i x ∂Measure.pi ν) = ∫ ω, Z i ω ∂ν i from
      integral_comp_eval (μ := ν) (i := i) (hZm i).aestronglyMeasurable, hmean]
  have hYsq : (∑ i, ∫ x, Y i x^2 ∂Measure.pi ν) = ∑ i, ∫ ω, Z i ω^2 ∂ν i := by
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Y, pow_two] using integral_comp_eval (μ := ν) (i := i)
      ((hZm i).matrix_mul (hZm i)).aestronglyMeasurable
  have he := (integral_and_measureReal_specNorm_sum_le_bernstein_hermitian
    (Measure.pi ν) Y hR hYm (iIndepFun_pi fun i => (hZm i).aemeasurable)
      hYH hYB hYmean).1
  rw [hYsq] at he
  have hdR : (2 : ℝ) ≤ Fintype.card n := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < Fintype.card n := by positivity
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log (Fintype.card n) :=
    Real.log_le_log (by norm_num) hdR
  have hlogsum : Real.log (2*(Fintype.card n : ℝ)) ≤ 2*p := by
    rw [Real.log_mul (by norm_num) hdpos.ne']
    linarith
  have hlognonneg : 0 ≤ Real.log (2*(Fintype.card n : ℝ)) :=
    Real.log_nonneg (by linarith)
  have harg : 2*specNorm (∑ i, ∫ ω, Z i ω^2 ∂ν i)*Real.log (2*(Fintype.card n : ℝ)) ≤
      2*σ^2*(2*p) := mul_le_mul
    (mul_le_mul_of_nonneg_left hvariance (by norm_num : (0 : ℝ) ≤ 2)) hlogsum
      hlognonneg (by positivity)
  have hsqrt := Real.sqrt_le_sqrt harg
  have hsqrteq : Real.sqrt (2*σ^2*(2*p)) = 2*σ*Real.sqrt p := by
    rw [show 2*σ^2*(2*p) = (2*σ)^2*p by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hsqrteq] at hsqrt
  have hlin : R*Real.log (2*(Fintype.card n : ℝ))/3 ≤ R*p := by
    have hh := mul_le_mul_of_nonneg_left hlogsum hR
    have hnonneg : 0 ≤ R*p := mul_nonneg hR hp
    linarith
  exact he.trans (add_le_add hsqrt hlin)

end NLAlib
