import NLAlib.Polynomial.Quadrature.GaussMeasureRemainder
import NLAlib.Krylov.Quadrature.MomentOrthogonality

/-! # The derivative remainder of actual Lanczos quadrature

Moment uniqueness identifies the Golub–Welsch nodes and weights of every valid Lanczos
decomposition with the constructed Gauss rule of its spectral measure. The monic norm
is exactly the squared Euclidean length of the characteristic polynomial applied to the
starting vector. This includes Krylov termination.
-/

noncomputable section
open scoped Matrix
open Polynomial MeasureTheory Finset Set

namespace NLAlib.LanczosDecomp

variable {n : Type*} [Fintype n] [DecidableEq n]
  {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- Every actual Lanczos Gauss estimate has the classical derivative remainder with
the squared norm of `χ_q(A)b`, including a terminal Krylov space. The characteristic
polynomial is monic `χ_q(t)=det(tI−T_q)`.
Source: Gautschi (2004), Theorem 1.48 and its matrix corollary; operator derivations (AQ6).
atlas: gauss-quadrature-derivative-remainder (partial) -/
theorem exists_quadForm_sub_cfc_T_eq_iteratedDeriv_mul_norm
    (D : NLAlib.LanczosDecomp A b q) (hA : A.IsHermitian) (hq : 0 < q)
    {a c : ℝ} (hac : a < c) (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q) f) (Ioo a c)) :
    ∃ ξ ∈ Ioo a c,
      quadForm (cfc f A) b - ‖WithLp.toLp 2 b‖ ^ 2 * cfc f D.T ⟨0, hq⟩ ⟨0, hq⟩ =
        iteratedDeriv (2 * q) f ξ / (2 * q).factorial *
          ‖WithLp.toLp 2 (aeval A D.T.charpoly *ᵥ b)‖ ^ 2 := by
  let μ := spectralMeasure hA b
  have hμ : ∀ᵐ x ∂μ, x ∈ Icc a c := by
    have hrange : ∀ᵐ x ∂μ, x ∈ Set.range hA.eigenvalues := by
      rw [ae_iff]
      exact spectralMeasure_compl_range_eigenvalues hA b
    filter_upwards [hrange] with x hx
    obtain ⟨i, rfl⟩ := hx
    exact hspec i
  let hMom := hasPolynomialMoments_of_ae_mem_Icc hμ
  have hn : (q : ℕ∞) ≤ μ.support.encard := by
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast D.le_krylovGrade
  let θ := (D.isHermitian_T hA).eigenvalues
  let w : Fin q → ℝ := fun i => (b ⬝ᵥ b) * ((D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩) ^ 2
  have hmoment : ∀ k < 2 * q, (∫ x, x ^ k ∂μ) = ∑ i, w i * θ i ^ k := by
    intro k hk
    have hp : (X ^ k : ℝ[X]).degree < (2 * q : ℕ) := by
      simp only [degree_pow, degree_X, nsmul_eq_mul, mul_one]
      exact_mod_cast hk
    have h := D.dotProduct_aeval_mulVec_eq_sum hA hq (p := X ^ k) hp
    rw [← integral_eval_spectralMeasure hA b] at h
    simpa only [Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum, w, θ,
      mul_assoc, mul_left_comm, mul_comm] using h
  obtain ⟨e, heθ, hew⟩ := rule_eq_gaussNodes_gaussWeights_of_moments hMom hq hn
    θ w (D.eigenvalues_T_injective hA) hmoment
  have hsum : (∑ i, w i * f (θ i)) =
      ∑ i, gaussWeights μ hMom q i * f (gaussNodes μ hMom q i) := by
    calc _ = ∑ i, w (e i) * f (θ (e i)) := (Equiv.sum_comp e _).symm
      _ = _ := sum_congr rfl fun i _ => by rw [heθ i, hew i]
  have hvalue : (∑ i, gaussWeights μ hMom q i * f (gaussNodes μ hMom q i)) =
      ‖WithLp.toLp 2 b‖ ^ 2 * cfc f D.T ⟨0, hq⟩ ⟨0, hq⟩ := by
    rw [← hsum, norm_toLp_sq_eq_dotProduct_self, D.cfc_T_apply_zero_zero hA hq]
    rw [Finset.mul_sum]
    exact sum_congr rfl fun i _ => by dsimp only [w, θ]; ring
  have hnorm : orthogonalPolynomialNorm (polynomialIntegral μ hMom) q =
      ‖WithLp.toLp 2 (aeval A D.T.charpoly *ᵥ b)‖ ^ 2 := by
    change (∫ x, (monicOrthogonalPolynomial (polynomialIntegral μ hMom) q ^ 2).eval x ∂μ) = _
    rw [D.monicOrthogonalPolynomial_spectralMeasure_eq_charpoly_T hA]
    rw [norm_toLp_sq_eq_dotProduct_self]
    simpa only [Polynomial.eval_pow, pow_two, Polynomial.eval_mul] using
      integral_eval_mul_eval_spectralMeasure hA b D.T.charpoly D.T.charpoly
  obtain ⟨ξ, hξ, he⟩ := exists_integral_sub_gaussRule_eq_iteratedDeriv_mul_norm
    hac hμ hq hn hf hf' hD
  rw [hvalue, hnorm, integral_spectralMeasure_eq_quadForm] at he
  exact ⟨ξ, hξ, he⟩

/-- A nonnegative even derivative makes actual Lanczos Gauss quadrature a lower bound
for the matrix quadratic form. This includes zero error at Krylov termination.
Source: Gautschi (2004), corollary to Theorem 1.48; operator derivations after (AQ6).
atlas: gauss-quadrature-derivative-remainder (partial) -/
theorem norm_sq_mul_cfc_T_le_quadForm_of_iteratedDeriv_nonneg
    (D : NLAlib.LanczosDecomp A b q) (hA : A.IsHermitian) (hq : 0 < q)
    {a c : ℝ} (hac : a < c) (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q) f) (Ioo a c))
    (hpos : ∀ x ∈ Ioo a c, 0 ≤ iteratedDeriv (2 * q) f x) :
    ‖WithLp.toLp 2 b‖ ^ 2 * cfc f D.T ⟨0, hq⟩ ⟨0, hq⟩ ≤ quadForm (cfc f A) b := by
  obtain ⟨ξ, hξ, he⟩ := D.exists_quadForm_sub_cfc_T_eq_iteratedDeriv_mul_norm
    hA hq hac hspec hf hf' hD
  have hnon : 0 ≤ iteratedDeriv (2 * q) f ξ / (2 * q).factorial *
      ‖WithLp.toLp 2 (aeval A D.T.charpoly *ᵥ b)‖ ^ 2 :=
    mul_nonneg (div_nonneg (hpos ξ hξ) (by positivity)) (sq_nonneg _)
  linarith

/-- A nonpositive even derivative makes actual Lanczos Gauss quadrature an upper bound
for the matrix quadratic form. Source: Gautschi (2004), corollary to Theorem 1.48.
atlas: gauss-quadrature-derivative-remainder (partial) -/
theorem quadForm_le_norm_sq_mul_cfc_T_of_iteratedDeriv_nonpos
    (D : NLAlib.LanczosDecomp A b q) (hA : A.IsHermitian) (hq : 0 < q)
    {a c : ℝ} (hac : a < c) (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q) f) (Ioo a c))
    (hneg : ∀ x ∈ Ioo a c, iteratedDeriv (2 * q) f x ≤ 0) :
    quadForm (cfc f A) b ≤ ‖WithLp.toLp 2 b‖ ^ 2 * cfc f D.T ⟨0, hq⟩ ⟨0, hq⟩ := by
  obtain ⟨ξ, hξ, he⟩ := D.exists_quadForm_sub_cfc_T_eq_iteratedDeriv_mul_norm
    hA hq hac hspec hf hf' hD
  have hnon : iteratedDeriv (2 * q) f ξ / (2 * q).factorial *
      ‖WithLp.toLp 2 (aeval A D.T.charpoly *ᵥ b)‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (hneg ξ hξ) (by positivity))
      (sq_nonneg _)
  linarith

end NLAlib.LanczosDecomp
