import NLAlib.Polynomial.Quadrature.GaussDerivativeRemainder
import NLAlib.Polynomial.OrthogonalPolynomials.JacobiLocation

/-! # Derivative remainder for the constructed measure Gauss rule

The canonical nodes and weights satisfy the complete derivative remainder, including
finite-support termination. The coefficient is the actual squared monic-polynomial norm.
-/

noncomputable section
open Polynomial MeasureTheory Finset Set

namespace NLAlib

/-- The actual `n`-node Gauss rule of a finite measure on a nontrivial compact interval
has the order-`2n` derivative remainder at one point in the open interval. Terminal
finite support is included: its monic norm and error both vanish. Differentiability is
needed only on the open interval, with continuity of the top derivative there.
Source: Gautschi (2004), Theorem 1.48; operator derivations, (AQ3)–(AQ6).
atlas: gauss-quadrature-derivative-remainder (partial) -/
theorem exists_integral_sub_gaussRule_eq_iteratedDeriv_mul_norm
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b) {n : ℕ} (hn0 : 0 < n)
    (hn : (n : ℕ∞) ≤ μ.support.encard) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ k < 2 * n, DifferentiableOn ℝ (iteratedDeriv k f) (Ioo a b))
    (hD : ContinuousOn (iteratedDeriv (2 * n) f) (Ioo a b)) :
    let hMom := hasPolynomialMoments_of_ae_mem_Icc hμ
    ∃ ξ ∈ Ioo a b,
      (∫ x, f x ∂μ) - ∑ i : Fin n, gaussWeights μ hMom n i * f (gaussNodes μ hMom n i) =
        iteratedDeriv (2 * n) f ξ / (2 * n).factorial *
          orthogonalPolynomialNorm (polynomialIntegral μ hMom) n := by
  dsimp only
  let hMom := hasPolynomialMoments_of_ae_mem_Icc hμ
  have hv := gaussNodes_injective hMom hn
  have hexact := fun p hp => integral_eval_eq_sum_gaussWeights_mul_eval hMom hn0 hn
    (p := p) hp
  have hnorm : (∫ x, (Lagrange.nodal univ (gaussNodes μ hMom n)).eval x ^ 2 ∂μ) =
      orthogonalPolynomialNorm (polynomialIntegral μ hMom) n := by
    change _ = ∫ x, (monicOrthogonalPolynomial (polynomialIntegral μ hMom) n ^ 2).eval x ∂μ
    simp_rw [nodal_gaussNodes_eq_monicOrthogonalPolynomial hMom hn, eval_pow]
  by_cases hnplus : (n + 1 : ℕ∞) ≤ μ.support.encard
  · obtain ⟨ξ, hξ, he⟩ := exists_integral_sub_quadrature_eq_iteratedDeriv_mul_nodal_sq
      hab hμ hn0 (gaussNodes μ hMom n) (gaussWeights μ hMom n) hv
      (gaussNodes_mem_Ioo hMom hμ hnplus) hexact hf hf' hD
    rw [hnorm] at he
    exact ⟨ξ, hξ, he⟩
  · have hcard : μ.support.encard = (n : ℕ∞) := by
      apply le_antisymm _ hn
      exact ENat.lt_natCast_add_one_iff.mp (not_le.mp hnplus)
    have hfinite := Set.finite_of_encard_eq_coe hcard
    have hncard : hfinite.toFinset.card = n := by
      exact_mod_cast (hfinite.encard_eq_coe_toFinset_card.symm.trans hcard)
    have hzero := orthogonalPolynomialNorm_eq_zero_of_finite_support μ hMom hfinite
    rw [hncard] at hzero
    have hnodalzero : (∫ x, (Lagrange.nodal univ (gaussNodes μ hMom n)).eval x ^ 2 ∂μ) = 0 :=
      hnorm.trans hzero
    have he := integral_eq_quadrature_of_integral_nodal_sq_eq_zero hμ hn0
      (gaussNodes μ hMom n) (gaussWeights μ hMom n) hv hexact hnodalzero f
    exact ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, by simp [he, hzero]⟩

end NLAlib
