import NLAlib.Krylov.Quadrature.MomentOrthogonality
import NLAlib.Polynomial.Quadrature.RadauJacobiRemainder
import NLAlib.Polynomial.Quadrature.LobattoJacobiRemainder
import NLAlib.Polynomial.Quadrature.EndpointJacobiSigns

/-! # Actual endpoint matrix quadrature bounds for an operator and starting vector

The operator's native spectral measure supplies the original moment system.
Its support cardinality is exactly the Krylov grade and its mass is the squared
starting-vector norm. These consumers therefore expose the constructed endpoint
matrix estimates directly as bounds on the original matrix quadratic form.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Set
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

private theorem spectralMeasure_ae_mem_interval (hA : A.IsHermitian) (b : n → ℝ)
    {a c : ℝ} (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c) :
    ∀ᵐ x ∂spectralMeasure hA b, x ∈ Icc a c := by
  have hrange : ∀ᵐ x ∂spectralMeasure hA b, x ∈ Set.range hA.eigenvalues := by
    rw [ae_iff]
    exact spectralMeasure_compl_range_eigenvalues hA b
  filter_upwards [hrange] with x hx
  obtain ⟨i, rfl⟩ := hx
  exact hspec i

private theorem spectral_polynomialIntegral_one (hA : A.IsHermitian) (b : n → ℝ) :
    (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)) 1 =
      ‖WithLp.toLp 2 b‖ ^ 2 := by
  rw [polynomialIntegral_apply, integral_eval_spectralMeasure, norm_toLp_sq_eq_dotProduct_self]
  simp

/-- A positive odd derivative makes the actual left Radau Schur matrix estimate
a lower bound on the operator quadratic form. The grade threshold includes original
termination. Source: Gautschi (2004), Theorem 3.7; operator derivations (AQ9).
atlas: gauss-radau-lobatto (partial) -/
theorem norm_sq_mul_cfc_leftRadauJacobiMatrix_le_quadForm_of_iteratedDeriv_nonneg
    (hA : A.IsHermitian) (b : n → ℝ) {a c : ℝ} (hac : a < c)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c) (q : ℕ) (hq : q + 1 ≤ krylovGrade A b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 1) f) (Ioo a c))
    (hpos : ∀ x ∈ Ioo a c, 0 ≤ iteratedDeriv (2 * q + 1) f x) :
    let L := polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)
    ‖WithLp.toLp 2 b‖ ^ 2 * cfc f (leftRadauJacobiMatrix L q a) 0 0 ≤ quadForm (cfc f A) b := by
  dsimp only
  have hs : (q + 1 : ℕ∞) ≤ (spectralMeasure hA b).support.encard := by
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast hq
  have h := mass_mul_cfc_leftRadauJacobiMatrix_le_integral_of_iteratedDeriv_nonneg
    (hasPolynomialMoments_spectralMeasure hA b) hac (spectralMeasure_ae_mem_interval hA b hspec)
    q hs hf hf' hD hpos
  rw [spectral_polynomialIntegral_one, integral_spectralMeasure_eq_quadForm] at h
  exact h

/-- A positive odd derivative makes the actual right Radau Schur matrix estimate
an upper bound on the operator quadratic form, including terminal exactness.
Source: Gautschi (2004), Theorem 3.7; operator derivations (AQ10).
atlas: gauss-radau-lobatto (partial) -/
theorem quadForm_le_norm_sq_mul_cfc_rightRadauJacobiMatrix_of_iteratedDeriv_nonneg
    (hA : A.IsHermitian) (b : n → ℝ) {a c : ℝ} (hac : a < c)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c) (q : ℕ) (hq : q + 1 ≤ krylovGrade A b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 1) f) (Ioo a c))
    (hpos : ∀ x ∈ Ioo a c, 0 ≤ iteratedDeriv (2 * q + 1) f x) :
    let L := polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)
    quadForm (cfc f A) b ≤ ‖WithLp.toLp 2 b‖ ^ 2 * cfc f (rightRadauJacobiMatrix L q c) 0 0 := by
  dsimp only
  have hs : (q + 1 : ℕ∞) ≤ (spectralMeasure hA b).support.encard := by
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast hq
  have h := integral_le_mass_mul_cfc_rightRadauJacobiMatrix_of_iteratedDeriv_nonneg
    (hasPolynomialMoments_spectralMeasure hA b) hac (spectralMeasure_ae_mem_interval hA b hspec)
    q hs hf hf' hD hpos
  rw [spectral_polynomialIntegral_one, integral_spectralMeasure_eq_quadForm] at h
  exact h

/-- A positive even derivative makes the actual Lobatto Schur matrix estimate an
upper bound on the operator quadratic form. The repaired clean grade threshold is
`q+2`; a weaker grade alone does not determine a nondegenerate `(q+2)`-node rule.
Source: Gautschi (2004), Theorem 3.7; operator derivations (AQ11).
atlas: gauss-radau-lobatto (partial) -/
theorem quadForm_le_norm_sq_mul_cfc_lobattoJacobiMatrix_of_iteratedDeriv_nonneg
    (hA : A.IsHermitian) (b : n → ℝ) {a c : ℝ} (hac : a < c)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c) (q : ℕ) (hq : q + 2 ≤ krylovGrade A b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q + 2, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 2) f) (Ioo a c))
    (hpos : ∀ x ∈ Ioo a c, 0 ≤ iteratedDeriv (2 * q + 2) f x) :
    let L := polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)
    quadForm (cfc f A) b ≤ ‖WithLp.toLp 2 b‖ ^ 2 * cfc f (lobattoJacobiMatrix L q a c) 0 0 := by
  dsimp only
  have hs : (q + 2 : ℕ∞) ≤ (spectralMeasure hA b).support.encard := by
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast hq
  have hs' : (q + 1 : ℕ∞) ≤ (spectralMeasure hA b).support.encard :=
    ((by exact_mod_cast (show q + 1 ≤ q + 2 by omega) : (q + 1 : ℕ∞) ≤ q + 2).trans hs)
  have hμac := spectralMeasure_ae_mem_interval hA b hspec
  obtain ⟨hJa, hJc⟩ := orthogonalPolynomialJacobiMatrix_endpoint_shifts_posDef
    (hasPolynomialMoments_spectralMeasure hA b) hμac (q + 1) (by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hs)
  have h := integral_le_mass_mul_cfc_lobattoJacobiMatrix_of_iteratedDeriv_nonneg
    (hasPolynomialMoments_spectralMeasure hA b) hac hμac q hs' hJa hJc hf hf' hD hpos
  rw [spectral_polynomialIntegral_one, integral_spectralMeasure_eq_quadForm] at h
  exact h

/-- A nonpositive odd derivative gives the actual left Radau upper bound on the
original quadratic form, the orientation used by reciprocal functions on a
positive interval. Source: Gautschi (2004), Theorem 3.7; operator derivations (AQ9).
atlas: gauss-radau-lobatto (partial) -/
theorem quadForm_le_norm_sq_mul_cfc_leftRadauJacobiMatrix_of_iteratedDeriv_nonpos
    (hA : A.IsHermitian) (b : n → ℝ) {a c : ℝ} (hac : a < c)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c) (q : ℕ) (hq : q + 1 ≤ krylovGrade A b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 1) f) (Ioo a c))
    (hneg : ∀ x ∈ Ioo a c, iteratedDeriv (2 * q + 1) f x ≤ 0) :
    let L := polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)
    quadForm (cfc f A) b ≤ ‖WithLp.toLp 2 b‖ ^ 2 * cfc f (leftRadauJacobiMatrix L q a) 0 0 := by
  dsimp only
  have hs : (q + 1 : ℕ∞) ≤ (spectralMeasure hA b).support.encard := by
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast hq
  have h := integral_le_mass_mul_cfc_leftRadauJacobiMatrix_of_iteratedDeriv_nonpos
    (hasPolynomialMoments_spectralMeasure hA b) hac (spectralMeasure_ae_mem_interval hA b hspec)
    q hs hf hf' hD hneg
  rw [spectral_polynomialIntegral_one, integral_spectralMeasure_eq_quadForm] at h
  exact h

/-- A nonpositive odd derivative gives the actual right Radau lower bound on the
original quadratic form, including finite Krylov termination.
Source: Gautschi (2004), Theorem 3.7; operator derivations (AQ10).
atlas: gauss-radau-lobatto (partial) -/
theorem norm_sq_mul_cfc_rightRadauJacobiMatrix_le_quadForm_of_iteratedDeriv_nonpos
    (hA : A.IsHermitian) (b : n → ℝ) {a c : ℝ} (hac : a < c)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c) (q : ℕ) (hq : q + 1 ≤ krylovGrade A b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q + 1, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 1) f) (Ioo a c))
    (hneg : ∀ x ∈ Ioo a c, iteratedDeriv (2 * q + 1) f x ≤ 0) :
    let L := polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)
    ‖WithLp.toLp 2 b‖ ^ 2 * cfc f (rightRadauJacobiMatrix L q c) 0 0 ≤ quadForm (cfc f A) b := by
  dsimp only
  have hs : (q + 1 : ℕ∞) ≤ (spectralMeasure hA b).support.encard := by
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast hq
  have h := mass_mul_cfc_rightRadauJacobiMatrix_le_integral_of_iteratedDeriv_nonpos
    (hasPolynomialMoments_spectralMeasure hA b) hac (spectralMeasure_ae_mem_interval hA b hspec)
    q hs hf hf' hD hneg
  rw [spectral_polynomialIntegral_one, integral_spectralMeasure_eq_quadForm] at h
  exact h

/-- A nonpositive even derivative gives the actual Lobatto lower bound on the
original quadratic form, under the repaired nondegenerate grade threshold.
Source: Gautschi (2004), Theorem 3.7; operator derivations (AQ11).
atlas: gauss-radau-lobatto (partial) -/
theorem norm_sq_mul_cfc_lobattoJacobiMatrix_le_quadForm_of_iteratedDeriv_nonpos
    (hA : A.IsHermitian) (b : n → ℝ) {a c : ℝ} (hac : a < c)
    (hspec : ∀ i, hA.eigenvalues i ∈ Icc a c) (q : ℕ) (hq : q + 2 ≤ krylovGrade A b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a c))
    (hf' : ∀ k < 2 * q + 2, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a c))
    (hD : ContinuousOn (iteratedDeriv (2 * q + 2) f) (Ioo a c))
    (hneg : ∀ x ∈ Ioo a c, iteratedDeriv (2 * q + 2) f x ≤ 0) :
    let L := polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)
    ‖WithLp.toLp 2 b‖ ^ 2 * cfc f (lobattoJacobiMatrix L q a c) 0 0 ≤ quadForm (cfc f A) b := by
  dsimp only
  have hs : (q + 2 : ℕ∞) ≤ (spectralMeasure hA b).support.encard := by
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast hq
  have hs' : (q + 1 : ℕ∞) ≤ (spectralMeasure hA b).support.encard :=
    ((by exact_mod_cast (show q + 1 ≤ q + 2 by omega) : (q + 1 : ℕ∞) ≤ q + 2).trans hs)
  have hμac := spectralMeasure_ae_mem_interval hA b hspec
  obtain ⟨hJa, hJc⟩ := orthogonalPolynomialJacobiMatrix_endpoint_shifts_posDef
    (hasPolynomialMoments_spectralMeasure hA b) hμac (q + 1) (by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hs)
  have h := mass_mul_cfc_lobattoJacobiMatrix_le_integral_of_iteratedDeriv_nonpos
    (hasPolynomialMoments_spectralMeasure hA b) hac hμac q hs' hJa hJc hf hf' hD hneg
  rw [spectral_polynomialIntegral_one, integral_spectralMeasure_eq_quadForm] at h
  exact h

end NLAlib
