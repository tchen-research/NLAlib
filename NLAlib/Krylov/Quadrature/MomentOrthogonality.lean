import NLAlib.Krylov.Quadrature.SpectralMoments
import NLAlib.Krylov.Quadrature.JacobiSpectrum
import NLAlib.Polynomial.OrthogonalPolynomials.MeasureOrthogonality
import NLAlib.Polynomial.Quadrature.MeasureExactness
import NLAlib.Krylov.Spaces.MinimalPolynomial
import NLAlib.Polynomial.OrthogonalPolynomials.JacobiLocation
import NLAlib.Polynomial.OrthogonalPolynomials.Interlacing
import NLAlib.Polynomial.OrthogonalPolynomials.SupportGaps
import NLAlib.Matrix.Spectral.EigenvalueEquality

/-! # The finite-moment construction and spectral measures

The canonical monic moment polynomial of a spectral measure is the
characteristic polynomial of every valid Lanczos compression. This connects
general-measure orthogonality with the existing matrix quadrature theory.
Source: Gautschi (2004), Chapter 1; operator derivations OP1–OP4.
-/

noncomputable section

open Matrix Polynomial MeasureTheory Finset
open scoped Matrix Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace LanczosDecomp

variable {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- The characteristic polynomial of a Lanczos Jacobi matrix satisfies the
general-measure monic orthogonality specification. The last polynomial at
finite-support termination is included. Source: Gautschi (2004), Theorem 1.27.
atlas: orthogonal-polynomials-measure-def (partial) -/
theorem isMonicOrthogonalPolynomial_charpoly_T (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) :
    IsMonicOrthogonalPolynomial
      (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b))
      q D.T.charpoly := by
  refine ⟨D.charpoly_T_monic.1, D.charpoly_T_monic.2, ?_⟩
  intro p hp
  simpa only [polynomialIntegral_apply, eval_mul] using
    D.integral_eval_charpoly_mul_eq_zero hA hp

/-- The finite-moment monic polynomial of a spectral measure is exactly the
characteristic polynomial of its Lanczos compression, including termination.
Source: Gautschi (2004), Theorem 1.27; operator derivations OP4.
atlas: orthogonal-polynomials-measure-def (partial), orthogonal-polynomial-zeros (partial) -/
theorem monicOrthogonalPolynomial_spectralMeasure_eq_charpoly_T
    (D : LanczosDecomp A b q) (hA : A.IsHermitian) :
    monicOrthogonalPolynomial
      (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b))
      q = D.T.charpoly := by
  let L := polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)
  have hnondeg : ∀ p : ℝ[X], p.degree < q → p ≠ 0 → L (p ^ 2) ≠ 0 := by
    intro p hp hp0 hzero
    apply hp0
    apply eq_zero_of_aeval_mulVec_eq_zero (A := A) (b := b)
    · exact hp.trans_le (by exact_mod_cast D.le_krylovGrade)
    · have hz : (aeval A p *ᵥ b) ⬝ᵥ (aeval A p *ᵥ b) = 0 := by
        simpa only [L, polynomialIntegral_apply, eval_pow, pow_two, eval_mul,
          integral_eval_mul_eval_spectralMeasure] using hzero
      simpa using (dotProduct_self_eq_zero.mp hz)
  have hdet : hankelMomentDet L q ≠ 0 := by
    apply hankelMomentDet_ne_zero_of_existsUnique_isMonicOrthogonalPolynomial L
    refine ⟨D.T.charpoly, D.isMonicOrthogonalPolynomial_charpoly_T hA, ?_⟩
    intro p hp
    exact hp.eq_of_nonzero_sq (D.isMonicOrthogonalPolynomial_charpoly_T hA) hnondeg
  exact (isMonicOrthogonalPolynomial_monicOrthogonalPolynomial L hdet).eq_of_nonzero_sq
    (D.isMonicOrthogonalPolynomial_charpoly_T hA) hnondeg

private theorem spectral_hankel_nonzero (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (k : ℕ) (hk : k ≤ q) :
    hankelMomentDet
      (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)) k ≠ 0 := by
  apply hankelMomentDet_ne_zero_of_le_support_encard
  rw [support_encard_spectralMeasure_eq_krylovGrade]
  exact_mod_cast (hk.trans D.le_krylovGrade)

private theorem spectral_norm_pos (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (k : ℕ) (hk : k < q) :
    0 < orthogonalPolynomialNorm
      (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)) k := by
  apply orthogonalPolynomialNorm_pos_of_lt_support_encard
  rw [support_encard_spectralMeasure_eq_krylovGrade]
  exact_mod_cast ((Nat.succ_le_of_lt hk).trans D.le_krylovGrade)

/-- The actual Lanczos compression and the canonical moment Jacobi matrix have
the same sorted spectrum, independently of the basis signs.
Source: Gautschi (2004), Theorem 1.27.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem eigenvalues₀_T_eq_orthogonalPolynomialJacobiMatrix (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) :
    (D.isHermitian_T hA).eigenvalues₀ =
      (isHermitian_orthogonalPolynomialJacobiMatrix
        (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)) q).eigenvalues₀ := by
  apply eigenvalues₀_eq_of_charpoly_eq
  rw [← D.monicOrthogonalPolynomial_spectralMeasure_eq_charpoly_T hA]
  exact (charpoly_orthogonalPolynomialJacobiMatrix _
    (D.spectral_hankel_nonzero hA) (D.spectral_norm_pos hA)).symm

/-- Consecutive actual Lanczos compressions strictly interlace before breakdown.
Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial), jacobi-matrix-identities (partial) -/
theorem eigenvalues₀_restrict_T_strict_interlacing {q : ℕ}
    (D : LanczosDecomp A b (q + 1)) (hA : A.IsHermitian) (i : Fin q) :
    (D.isHermitian_T hA).eigenvalues₀ (Fin.cast (Fintype.card_fin (q + 1)).symm i.succ) <
      (LanczosDecomp.isHermitian_T (D.restrict (Nat.le_succ q)) hA).eigenvalues₀
        (Fin.cast (Fintype.card_fin q).symm i) ∧
      (LanczosDecomp.isHermitian_T (D.restrict (Nat.le_succ q)) hA).eigenvalues₀
        (Fin.cast (Fintype.card_fin q).symm i) <
      (D.isHermitian_T hA).eigenvalues₀ (Fin.cast (Fintype.card_fin (q + 1)).symm i.castSucc) := by
  rw [D.eigenvalues₀_T_eq_orthogonalPolynomialJacobiMatrix hA,
    LanczosDecomp.eigenvalues₀_T_eq_orthogonalPolynomialJacobiMatrix (D.restrict (Nat.le_succ q)) hA]
  exact eigenvalues₀_orthogonalPolynomialJacobiMatrix_strict_interlacing _
    (D.spectral_hankel_nonzero hA) (D.spectral_norm_pos hA) i

/-- Every nonterminal actual Lanczos Gauss node lies in the open interval
containing the spectral measure support. Source: Gautschi (2004), Theorem 1.19.
atlas: orthogonal-polynomial-zeros (partial) -/
theorem eigenvalues_T_mem_Ioo_of_spectralMeasure (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (hq : q < krylovGrade A b) {a c : ℝ}
    (hs : ∀ᵐ x ∂spectralMeasure hA b, x ∈ Set.Icc a c) (j : Fin q) :
    (D.isHermitian_T hA).eigenvalues j ∈ Set.Ioo a c := by
  have hn : (q : ℕ∞) ≤ (spectralMeasure hA b).support.encard := by
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast D.le_krylovGrade
  have hroot : (monicOrthogonalPolynomial
      (polynomialIntegral (spectralMeasure hA b) (hasPolynomialMoments_spectralMeasure hA b)) q).eval
      ((D.isHermitian_T hA).eigenvalues j) = 0 := by
    rw [D.monicOrthogonalPolynomial_spectralMeasure_eq_charpoly_T hA,
      (D.isHermitian_T hA).charpoly_eq, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp
  obtain ⟨i, hi⟩ := (eval_monicOrthogonalPolynomial_eq_zero_iff_exists_gaussNodes
    (hasPolynomialMoments_spectralMeasure hA b) hn _).mp hroot
  rw [← hi]
  apply gaussNodes_mem_Ioo (hasPolynomialMoments_spectralMeasure hA b) hs _ i
  rw [support_encard_spectralMeasure_eq_krylovGrade]
  exact_mod_cast (Nat.succ_le_of_lt hq)

/-- Every distinct-node rule matching the first `2q` actual matrix moments is
the Lanczos Gauss rule, up to permutation. This includes exact grade termination.
Source: Gautschi (2004), Gauss-rule characterization; operator derivations AQ2.
atlas: quadrature-exactness-characterisation (partial) -/
theorem rule_eq_up_to_permutation_of_moments (D : LanczosDecomp A b q)
    (hA : A.IsHermitian) (hq : 0 < q) (v w : Fin q → ℝ) (hv : Function.Injective v)
    (hm : ∀ k < 2 * q, b ⬝ᵥ ((A ^ k) *ᵥ b) = ∑ i, w i * v i ^ k) :
    ∃ e : Equiv.Perm (Fin q),
      (∀ i, v (e i) = (D.isHermitian_T hA).eigenvalues i) ∧
      (∀ i, w (e i) = (b ⬝ᵥ b) * ((D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩) ^ 2) := by
  have hn : (q : ℕ∞) ≤ (spectralMeasure hA b).support.encard := by
    rw [support_encard_spectralMeasure_eq_krylovGrade]
    exact_mod_cast D.le_krylovGrade
  apply quadrature_rule_eq_up_to_permutation_of_moments
    (hasPolynomialMoments_spectralMeasure hA b) hq hn
    (D.isHermitian_T hA).eigenvalues v
    (fun i => (b ⬝ᵥ b) * ((D.isHermitian_T hA).eigenvectorBasis i ⟨0, hq⟩) ^ 2) w
    (D.eigenvalues_T_injective hA) hv
  · intro k hk
    rw [integral_pow_spectralMeasure]
    have h := D.dotProduct_aeval_mulVec_eq_sum hA hq (p := X ^ k) (by
      rw [degree_X_pow]
      exact_mod_cast hk)
    simpa only [map_pow, aeval_X, eval_pow, eval_X, Finset.mul_sum,
      mul_assoc, mul_comm, mul_left_comm] using h
  · intro k hk
    rw [integral_pow_spectralMeasure]
    exact hm k hk

end LanczosDecomp

end NLAlib
