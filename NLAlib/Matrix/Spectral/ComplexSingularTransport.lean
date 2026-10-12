import NLAlib.Matrix.Spectral.ComplexSquareSingularBasis
import NLAlib.Matrix.Spectral.ComplexBestRankApproximation
import NLAlib.Matrix.Functions.ComplexDiagonalFilter
import NLAlib.Matrix.Spectral.GramSingularValues
import NLAlib.Matrix.Spectral.FiniteIndexTransport
/-!
# Complex singular values under unitary changes and real extension

The actual singular-value sequence is preserved by unitary changes and by
complexifying a real matrix, with no dimension doubling or extra multiplicity.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Real complexification preserves the actual singular-value sequence,
including every padded zero index. Horn–Johnson 2013, Section 2.6;
the dimensions and multiplicities are unchanged. -/
theorem singularValues_map_ofReal {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) (k : ℕ) :
    singularValues (A.map Complex.ofReal) k = singularValues A k := by
  classical
  let G := Aᴴ * A
  have hG : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  have hGC : (G.map Complex.ofReal).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_map_ofReal]
    have ht : Gᵀ = G := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hG.eq
    rw [ht]
  have hGram : (A.map Complex.ofReal)ᴴ * A.map Complex.ofReal = G.map Complex.ofReal := by
    rw [conjTranspose_map_ofReal, ← map_ofReal_mul]
    rfl
  by_cases hk : k < Fintype.card n
  · have h₁ := sq_singularValues_eq_eigenvalues₀ (A.map Complex.ofReal) ⟨k, hk⟩
    have h₂ := sq_singularValues_eq_eigenvalues₀ A ⟨k, hk⟩
    have he := congrFun (eigenvalues₀_eq_of_charpoly_eq
      (Matrix.isHermitian_conjTranspose_mul_self (A.map Complex.ofReal)) hGC
      (congrArg Matrix.charpoly hGram)) ⟨k, hk⟩
    have hm := congrFun (eigenvalues₀_map_ofReal hG hGC) ⟨k, hk⟩
    have hs : singularValues (A.map Complex.ofReal) k ^ 2 =
        singularValues A k ^ 2 := h₁.trans (he.trans (hm.trans h₂.symm))
    nlinarith [singularValues_nonneg (A.map Complex.ofReal) k,
      singularValues_nonneg A k]
  · rw [singularValues_eq_linearMap, singularValues_eq_linearMap,
      LinearMap.singularValues_of_finrank_le, LinearMap.singularValues_of_finrank_le] <;>
      simpa only [finrank_euclideanSpace] using Nat.le_of_not_gt hk

/-- Left multiplication by a complex column isometry preserves every
actual singular value. Horn–Johnson 2013, Section 2.6. -/
theorem complex_singularValues_isometry_mul {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
    {H : Matrix m p ℂ} (hH : Hᴴ * H = 1) (A : Matrix p n ℂ) (k : ℕ) :
    singularValues (H * A) k = singularValues A k := by
  apply singularValues_eq_of_gram_charpoly_eq
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Hᴴ H A, hH, Matrix.one_mul]

/-- Right multiplication by a square complex unitary preserves every
actual singular value. Horn–Johnson 2013, Section 2.6. -/
theorem complex_singularValues_mul_unitary {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (U : Matrix.unitaryGroup n ℂ) (k : ℕ) :
    singularValues (A * (U : Matrix n n ℂ)) k = singularValues A k := by
  apply singularValues_eq_of_gram_charpoly_eq
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc Aᴴ A (U : Matrix n n ℂ),
    Matrix.mul_assoc (Aᴴ * A),
    show (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 from Unitary.coe_mul_star_self U,
    Matrix.mul_one]

/-- The leading actual singular value of a complex square matrix is its
Euclidean operator norm, also in empty dimension. Horn–Johnson 2013,
Section 2.6; complex oblique norm helper. -/
theorem complex_singularValues_zero_eq_norm {n : Type*}
    [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : singularValues A 0 = ‖A‖ := by
  classical
  by_cases hn : Fintype.card n = 0
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    have hA : A = 0 := by ext i; exact isEmptyElim i
    simp only [hA, singularValues_eq_linearMap, map_zero, LinearMap.singularValues_zero,
      Finsupp.zero_apply, norm_zero]
  · obtain ⟨V, W, hD⟩ := exists_unitary_conjTranspose_mul_mul_eq_diagonal_singularValues A
    have hnorm : ‖A‖ = ‖Matrix.diagonal
        (fun i => (singularValues A ((Fintype.equivFin n) i) : ℂ))‖ := by
      rw [← hD, CStarRing.norm_mul_coe_unitary]
      exact (CStarRing.norm_coe_unitary_mul (star V) A).symm
    rw [hnorm, Matrix.l2_opNorm_diagonal]
    apply le_antisymm
    · let i : n := (Fintype.equivFin n).symm ⟨0, Nat.pos_of_ne_zero hn⟩
      have h := norm_le_pi_norm (fun i => (singularValues A ((Fintype.equivFin n) i) : ℂ)) i
      simpa only [i, Equiv.apply_symm_apply, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (singularValues_nonneg A 0)] using h
    · apply (pi_norm_le_iff_of_nonneg (singularValues_nonneg A 0)).mpr
      intro i
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (singularValues_nonneg A _)]
      exact singularValues_antitone A (Nat.zero_le _)

/-- Complexifying a real square matrix preserves its Euclidean operator
norm exactly. Horn–Johnson 2013, Section 2.6; no dimension doubling. -/
theorem norm_map_ofReal_eq_specNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : ‖A.map Complex.ofReal‖ = specNorm A := by
  rw [← complex_singularValues_zero_eq_norm, singularValues_map_ofReal]
  exact singularValues_zero_eq_specNorm A

/-- A complex and a real matrix with identical native singular-value
sequences have equal ranks. Horn–Johnson 2013, Section 2.6; all padded
zeros are included in the hypothesis. -/
theorem rank_eq_of_complex_real_singularValues_eq {m n p q : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q] (A : Matrix m n ℂ) (B : Matrix p q ℝ)
    (h : ∀ i, singularValues A i = singularValues B i) :
    A.rank = B.rank := by
  have he : (Matrix.toEuclideanLin A).singularValues = (Matrix.toEuclideanLin B).singularValues :=
    Finsupp.ext h
  have hc := congrArg (fun f : ℕ →₀ ℝ => f.support.card) he
  rw [LinearMap.card_support_singularValues, LinearMap.card_support_singularValues] at hc
  exact (A.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun m ℂ).toBasis
    (EuclideanSpace.basisFun n ℂ).toBasis).trans (hc.trans
      (B.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun p ℝ).toBasis
        (EuclideanSpace.basisFun q ℝ).toBasis).symm)

end NLAlib
