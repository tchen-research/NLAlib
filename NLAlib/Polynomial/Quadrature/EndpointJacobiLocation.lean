import NLAlib.Polynomial.OrthogonalPolynomials.JacobiOrder
import NLAlib.Polynomial.Quadrature.EndpointJacobiWeights
import NLAlib.Matrix.Structured.JacobiBorderSpectrum

/-! # Location of the constructed measure endpoint rules

The original measure support proves the Schur hypotheses of the actual endpoint
matrices. These statements retain the original Jacobi matrix in the Radau order
chain and do not assume interval location of the output nodes.
-/

noncomputable section
open Matrix Polynomial MeasureTheory Set
open scoped Matrix MatrixOrder

namespace NLAlib

/-- Original interval support and `q+1` support points put the actual Radau matrices
in the interval and retain their designated endpoint eigenvalues, including original
finite-support termination. Source: focused reroutes, Section 3 (BL2)–(BL5).
atlas: gauss-radau-lobatto (partial) -/
theorem radauJacobiMatrices_bounds_and_endpoints {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {a c : ℝ} (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c)
    (q : ℕ) (hs : (q + 1 : ℕ∞) ≤ μ.support.encard) :
    let L := polynomialIntegral μ hμ
    a • 1 ≤ leftRadauJacobiMatrix L q a ∧
      leftRadauJacobiMatrix L q a ≤ orthogonalPolynomialJacobiMatrix L (q + 1) ∧
      orthogonalPolynomialJacobiMatrix L (q + 1) ≤ rightRadauJacobiMatrix L q c ∧
      rightRadauJacobiMatrix L q c ≤ c • 1 ∧
      a ∈ spectrum ℝ (leftRadauJacobiMatrix L q a) ∧
      c ∈ spectrum ℝ (rightRadauJacobiMatrix L q c) := by
  dsimp only
  let L := polynomialIntegral μ hμ
  let J := orthogonalPolynomialJacobiMatrix L q
  let v := momentJacobiLastCoupling L q
  let d := orthogonalPolynomialJacobiMatrix L (q + 1) (Fin.last q) (Fin.last q)
  obtain ⟨hJa, hJc⟩ := orthogonalPolynomialJacobiMatrix_endpoint_shifts_posDef hμ hμac q hs
  obtain ⟨hMa, hMc⟩ := orthogonalPolynomialJacobiMatrix_endpoint_shifts_posSemidef hμ hμac (q + 1) hs
  have ha := reindex_le_reindex finSumFinEquiv.symm ((Matrix.le_iff).mpr hMa)
  have hc := reindex_le_reindex finSumFinEquiv.symm ((Matrix.le_iff).mpr hMc)
  rw [orthogonalPolynomialJacobiMatrix_eq_finSymmetricBorder] at ha hc
  simp only [finSymmetricBorder, ← Matrix.reindex_symm,
    Equiv.symm_apply_apply] at ha hc
  rw [Matrix.reindex_symm, reindex_smul_one] at ha hc
  have h := finRadauSchurBorders_bounds_and_endpoints J v d a c hJa hJc
    ((Matrix.le_iff).mp ha) ((Matrix.le_iff).mp hc)
  simpa only [leftRadauJacobiMatrix, rightRadauJacobiMatrix, J, v, d,
    ← orthogonalPolynomialJacobiMatrix_eq_finSymmetricBorder] using h

/-- `q+2` original support points prove the endpoint positive definite shifts for
the actual Lobatto matrix, hence interval bounds and both endpoint eigenvalues.
Source: focused reroutes, Section 3 (BL7)–(BL9).
atlas: gauss-radau-lobatto (partial) -/
theorem lobattoJacobiMatrix_bounds_and_endpoints {μ : Measure ℝ}
    (hμ : HasPolynomialMoments μ) {a c : ℝ} (hac : a < c)
    (hμac : ∀ᵐ x ∂μ, x ∈ Icc a c) (q : ℕ)
    (hs : (q + 2 : ℕ∞) ≤ μ.support.encard) :
    let L := polynomialIntegral μ hμ
    a • 1 ≤ lobattoJacobiMatrix L q a c ∧ lobattoJacobiMatrix L q a c ≤ c • 1 ∧
      a ∈ spectrum ℝ (lobattoJacobiMatrix L q a c) ∧
      c ∈ spectrum ℝ (lobattoJacobiMatrix L q a c) := by
  dsimp only
  obtain ⟨ha, hc⟩ := orthogonalPolynomialJacobiMatrix_endpoint_shifts_posDef hμ hμac (q + 1) (by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hs)
  exact finLobattoSchurBorder_bounds_and_endpoints hac ha hc (by
    intro h
    have hz := congrFun h (Fin.last q)
    simp at hz)

end NLAlib
