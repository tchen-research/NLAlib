import NLAlib.Krylov.Quadrature.MomentOrthogonality
import NLAlib.Polynomial.OrthogonalPolynomials.SupportGaps

/-! # Actual Lanczos nodes in support intervals and gaps

The moment-polynomial zero theorems apply to actual Lanczos compressions,
including support termination. Spectral support is finite, so its infimum
and supremum give the sharp support enclosure without ambient inactive nodes.
Source: Gautschi (2004), Theorem 1.19.
-/

noncomputable section

open Polynomial MeasureTheory Set

namespace NLAlib

/-- Nonterminal Gauss nodes lie between the support infimum and supremum
whenever the support is bounded. Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem gaussNodes_mem_Ioo_sInf_sSup_support {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    {n : ℕ} (hn : (n + 1 : ℕ∞) ≤ μ.support.encard)
    (hlo : BddBelow μ.support) (hhi : BddAbove μ.support) (i : Fin n) :
    gaussNodes μ hμ n i ∈ Ioo (sInf μ.support) (sSup μ.support) := by
  apply gaussNodes_mem_Ioo hμ _ hn
  filter_upwards [μ.support_mem_ae] with x hx
  exact ⟨csInf_le hlo hx, le_csSup hhi hx⟩

/-- A support gap contains at most one canonical Gauss node, with terminal
orders included. Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem eq_of_gaussNodes_mem_support_gap {μ : Measure ℝ} (hμ : HasPolynomialMoments μ)
    {n : ℕ} (hn : (n : ℕ∞) ≤ μ.support.encard) {a c : ℝ}
    (hg : Disjoint (Ioo a c) μ.support) {i j : Fin n}
    (hi : gaussNodes μ hμ n i ∈ Ioo a c) (hj : gaussNodes μ hμ n j ∈ Ioo a c) : i = j := by
  apply gaussNodes_injective hμ hn
  apply eq_of_eval_monicOrthogonalPolynomial_eq_zero_of_mem_support_gap_le hμ hn hg hi hj
  · exact (eval_monicOrthogonalPolynomial_eq_zero_iff_exists_gaussNodes hμ hn _).mpr ⟨i, rfl⟩
  · exact (eval_monicOrthogonalPolynomial_eq_zero_iff_exists_gaussNodes hμ hn _).mpr ⟨j, rfl⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Matrix ι ι ℝ} {b : ι → ℝ} {q : ℕ}

namespace LanczosDecomp

private theorem monic_spectral_eval_eigenvalue_eq_zero (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (i : Fin q) :
    (monicOrthogonalPolynomial
      (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)) q).eval
      ((D.isHermitian_T hA).eigenvalues i) = 0 := by
  rw [D.monicOrthogonalPolynomial_spectralMeasure_eq_charpoly_T hA,
    (D.isHermitian_T hA).charpoly_eq, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

/-- Every actual nonterminal Lanczos node lies strictly between the active
spectral support extrema. Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem eigenvalues_T_mem_Ioo_sInf_sSup_support (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (hq : q < krylovGrade A b) (i : Fin q) :
    (D.isHermitian_T hA).eigenvalues i ∈
      Ioo (sInf (spectralMeasure hA b).support) (sSup (spectralMeasure hA b).support) := by
  have hs : (spectralMeasure hA b).support.Finite := Set.finite_of_encard_le_coe
    (by rw [support_encard_spectralMeasure_eq_krylovGrade])
  apply D.eigenvalues_T_mem_Ioo_of_spectralMeasure hA hq
  filter_upwards [(spectralMeasure hA b).support_mem_ae] with x hx
  exact ⟨csInf_le hs.bddBelow hx, le_csSup hs.bddAbove hx⟩

/-- A gap in the active spectral support contains at most one actual Lanczos
node, including grade termination. Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem eq_of_eigenvalues_T_mem_support_gap (D : LanczosDecomp A b q) (hA : A.IsHermitian)
    {a c : ℝ} (hg : Disjoint (Ioo a c) (spectralMeasure hA b).support) {i j : Fin q}
    (hi : (D.isHermitian_T hA).eigenvalues i ∈ Ioo a c)
    (hj : (D.isHermitian_T hA).eigenvalues j ∈ Ioo a c) : i = j := by
  apply D.eigenvalues_T_injective hA
  apply eq_of_eval_monicOrthogonalPolynomial_eq_zero_of_mem_support_gap_le
    (hasPolynomialMoments_spectralMeasure hA b) _ hg hi hj
    (D.monic_spectral_eval_eigenvalue_eq_zero hA i) (D.monic_spectral_eval_eigenvalue_eq_zero hA j)
  rw [support_encard_spectralMeasure_eq_krylovGrade]
  exact_mod_cast D.le_krylovGrade

end LanczosDecomp

end NLAlib
