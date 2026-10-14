import NLAlib.Polynomial.OrthogonalPolynomials.StieltjesTransform
import NLAlib.Polynomial.Quadrature.GaussSpectralWeights
import NLAlib.Matrix.Functions.ComplexResolvent
import NLAlib.Matrix.Structured.JacobiFractionComplex
import NLAlib.Polynomial.OrthogonalPolynomials.JacobiCoefficients

/-! # Second-kind ratios are actual complex Jacobi resolvents

The constructed Gauss weights and finite spectral resolvent identify the second-kind
numerator/denominator ratio with the original mass times the actual first-coordinate
resolvent. Its finite moment matching comes from the constructed Jacobi moments.
-/

noncomputable section
open Polynomial Matrix MeasureTheory Finset Set
open scoped Matrix

namespace NLAlib

/-- The actual second-kind ratio is the Gauss atomic Stieltjes fraction at any
complex point outside the actual Gauss-node spectrum, including real gaps in the
support enclosure. Its final denominator is proved nonzero from the nodal product.
Source: operator derivations (AQ18).
atlas: jacobi-matrix-identities (partial), jacobi-fraction-second-kind (partial) -/
theorem eval_map_secondKindPolynomial_div_eq_sum_gaussWeights_div_of_ne_gaussNodes
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) {z : ℂ}
    (hz : ∀ i : Fin n, z ≠ (gaussNodes μ hμ n i : ℂ)) :
    ((secondKindPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z /
      ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z =
        ∑ i : Fin n, (gaussWeights μ hμ n i : ℂ) / (z - (gaussNodes μ hμ n i : ℂ)) := by
  apply eval_map_secondKindPolynomial_div_eq_sum_weight_div Complex.ofRealHom
    (polynomialIntegral μ hμ) n hn0
    (fun k hk => hankelMomentDet_ne_zero_of_le_support_encard μ hμ
      ((by exact_mod_cast hk : (k : ℕ∞) ≤ n).trans hn))
  · intro i
    exact (eval_monicOrthogonalPolynomial_eq_zero_iff_exists_gaussNodes hμ hn _).mpr ⟨i, rfl⟩
  · intro p hp
    exact integral_eval_eq_sum_gaussWeights_mul_eval hμ hn0 hn
      (hp.trans_le (by exact_mod_cast (show n ≤ 2 * n by omega)))
  · rw [← nodal_gaussNodes_eq_monicOrthogonalPolynomial hμ hn, Lagrange.nodal_eq,
      Polynomial.map_prod, eval_prod]
    apply prod_ne_zero_iff.mpr
    intro i _
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, eval_sub, eval_X, eval_C]
    exact sub_ne_zero.mpr (hz i)
  · exact hz

/-- The second-kind ratio is the original mass times the actual complex moment
Jacobi resolvent entry at every point outside its actual node spectrum. No assumed
resolvent or quadrature certificate is used. Source: operator derivations (OF27), (AQ18).
atlas: jacobi-matrix-identities (partial), jacobi-fraction-second-kind (partial) -/
theorem eval_map_secondKindPolynomial_div_eq_mass_mul_jacobi_resolvent
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) {z : ℂ}
    (hz : ∀ i : Fin n, z ≠ (gaussNodes μ hμ n i : ℂ)) :
    ((secondKindPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z /
      ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z =
      (∫ _ : ℝ, (1 : ℝ) ∂μ : ℝ) *
        (z • (1 : Matrix (Fin n) (Fin n) ℂ) -
          (orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) n).map Complex.ofRealHom)⁻¹
            ⟨0, hn0⟩ ⟨0, hn0⟩ := by
  let hJ := isHermitian_orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) n
  have hzJ (i : Fin n) : z ≠ Complex.ofRealHom (hJ.eigenvalues i) :=
    hz i
  rw [eval_map_secondKindPolynomial_div_eq_sum_gaussWeights_div_of_ne_gaussNodes hμ hn0 hn hz,
    inv_smul_one_sub_map_apply_eq_sum hJ Complex.ofRealHom hzJ, mul_sum]
  apply sum_congr rfl
  intro i _
  rw [gaussWeights_eq_mass_mul_sq_eigenvectorBasis_apply_zero hμ hn0 hn i]
  change _ = (∫ _ : ℝ, (1 : ℝ) ∂μ : ℝ) *
    (Complex.ofRealHom ((hJ.eigenvectorBasis i : Fin n → ℝ) ⟨0, hn0⟩) *
      Complex.ofRealHom ((hJ.eigenvectorBasis i : Fin n → ℝ) ⟨0, hn0⟩) /
        (z - (gaussNodes μ hμ n i : ℂ)))
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofRealHom_eq_coe]
  ring

/-- An off-enclosure point in particular satisfies the exact off-node hypothesis
of the actual complex second-kind/Jacobi resolvent bridge. -/
theorem eval_map_secondKindPolynomial_div_eq_mass_mul_jacobi_resolvent_of_off_Icc
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {a b : ℝ}
    (hs : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) {z : ℂ}
    (hz : ∀ x ∈ Icc a b, z ≠ (x : ℂ)) :
    ((secondKindPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z /
      ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z =
      (∫ _ : ℝ, (1 : ℝ) ∂μ : ℝ) *
        (z • (1 : Matrix (Fin n) (Fin n) ℂ) -
          (orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) n).map Complex.ofRealHom)⁻¹
            ⟨0, hn0⟩ ⟨0, hn0⟩ :=
  eval_map_secondKindPolynomial_div_eq_mass_mul_jacobi_resolvent hμ hn0 hn
    (fun i => hz _ (gaussNodes_mem_Icc hμ hs hn i))


/-- The actual canonical moment Jacobi matrix has its ordinary finite complex
continued fraction at every nonreal shift. Its coefficient realization is proved
from the constructed orthogonal polynomials. Source: operator derivations (OF25).
atlas: jacobi-matrix-identities (partial) -/
theorem inv_smul_one_sub_map_orthogonalPolynomialJacobiMatrix_apply_zero_zero
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) {z : ℂ} (hz : z.im ≠ 0) :
    (z • (1 : Matrix (Fin n) (Fin n) ℂ) -
      (orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) n).map Complex.ofRealHom)⁻¹
        ⟨0, hn0⟩ ⟨0, hn0⟩ =
      jacobiFraction (Complex.ofRealHom ∘ orthogonalRecurrenceAlpha (polynomialIntegral μ hμ))
        (Complex.ofRealHom ∘ fun i => Real.sqrt (orthogonalRecurrenceBeta (polynomialIntegral μ hμ) i))
        z n 0 := by
  rw [orthogonalPolynomialJacobiMatrix_eq_jacobiMatrix _ n
    (fun k hk => hankelMomentDet_ne_zero_of_le_support_encard μ hμ
      ((by exact_mod_cast hk : (k : ℕ∞) ≤ n).trans hn))
    (fun k hk => orthogonalPolynomialNorm_pos_of_lt_support_encard μ hμ
      ((by exact_mod_cast (show k + 1 ≤ n by omega) : (k + 1 : ℕ∞) ≤ n).trans hn))]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact inv_smul_one_sub_map_jacobiMatrix_apply_zero_zero _ _ m hz

/-- The actual second-kind rational approximant is its original mass times the
ordinary complex Jacobi fraction away from the real axis. Source: operator
derivations (OF25), (OF27), (AQ18).
atlas: jacobi-matrix-identities (partial), jacobi-fraction-second-kind (partial) -/
theorem eval_map_secondKindPolynomial_div_eq_mass_mul_jacobiFraction
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) {z : ℂ} (hz : z.im ≠ 0) :
    ((secondKindPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z /
      ((monicOrthogonalPolynomial (polynomialIntegral μ hμ) n).map Complex.ofRealHom).eval z =
      (∫ _ : ℝ, (1 : ℝ) ∂μ : ℝ) *
        jacobiFraction (Complex.ofRealHom ∘ orthogonalRecurrenceAlpha (polynomialIntegral μ hμ))
          (Complex.ofRealHom ∘ fun i => Real.sqrt (orthogonalRecurrenceBeta (polynomialIntegral μ hμ) i))
          z n 0 := by
  rw [eval_map_secondKindPolynomial_div_eq_mass_mul_jacobi_resolvent hμ hn0 hn
    (fun i h => hz (by simpa using congrArg Complex.im h)),
    inv_smul_one_sub_map_orthogonalPolynomialJacobiMatrix_apply_zero_zero hμ hn0 hn hz]

end NLAlib
