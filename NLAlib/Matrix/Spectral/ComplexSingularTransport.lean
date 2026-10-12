import NLAlib.Matrix.Spectral.ComplexSquareSingularBasis
import NLAlib.Matrix.Spectral.ComplexBestRankApproximation
import NLAlib.Matrix.Functions.ComplexDiagonalFilter
import NLAlib.Matrix.Spectral.SingularValueSpectrum
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

/-- Complex Hermitian matrices with equal characteristic polynomials have
the same ordered real eigenvalue list. Horn–Johnson 2013, Section 4.1;
complex singular-value transport helper. -/
theorem complex_eigenvalues₀_eq_of_charpoly {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A.charpoly = B.charpoly) : hA.eigenvalues₀ = hB.eigenvalues₀ := by
  apply List.ofFn_inj.mp
  rw [← hA.sort_roots_charpoly_eq_eigenvalues₀,
    ← hB.sort_roots_charpoly_eq_eigenvalues₀, h]

/-- Complexification preserves the full ordered spectrum of a real
symmetric matrix. Horn–Johnson 2013, Section 4.1; eigenvalues have exactly
their original multiplicities. -/
theorem eigenvalues₀_map_ofReal {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (hC : (A.map Complex.ofReal).IsHermitian) :
    hC.eigenvalues₀ = hA.eigenvalues₀ := by
  have hmap : (A.map Complex.ofReal).charpoly = A.charpoly.map Complex.ofRealHom :=
    Matrix.charpoly_map A Complex.ofRealHom
  apply List.ofFn_inj.mp
  rw [← hC.sort_roots_charpoly_eq_eigenvalues₀,
    ← hA.sort_roots_charpoly_eq_eigenvalues₀, hmap,
    hA.splits_charpoly.roots_map]
  simp only [Multiset.map_map, Function.comp_def, RCLike.re_to_real]
  rfl

/-- Complex matrices whose Gram characteristic polynomials agree have the
same actual singular values, including padded zeros and different row spaces.
Horn–Johnson 2013, Section 2.6. -/
theorem complex_singularValues_eq_of_gram_charpoly {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]
    (A : Matrix m n ℂ) (B : Matrix p n ℂ)
    (h : (Aᴴ * A).charpoly = (Bᴴ * B).charpoly) (k : ℕ) :
    A.toEuclideanLin.singularValues k = B.toEuclideanLin.singularValues k := by
  classical
  by_cases hk : k < Fintype.card n
  · have he := congrFun (complex_eigenvalues₀_eq_of_charpoly
      (Matrix.isHermitian_conjTranspose_mul_self A) (Matrix.isHermitian_conjTranspose_mul_self B) h)
      ⟨k, hk⟩
    have hs : A.toEuclideanLin.singularValues k ^ 2 = B.toEuclideanLin.singularValues k ^ 2 :=
      (sq_singularValues_eq_eigenvalues₀ A ⟨k, hk⟩).trans
        (he.trans (sq_singularValues_eq_eigenvalues₀ B ⟨k, hk⟩).symm)
    nlinarith [A.toEuclideanLin.singularValues_nonneg k, B.toEuclideanLin.singularValues_nonneg k]
  · rw [LinearMap.singularValues_of_finrank_le, LinearMap.singularValues_of_finrank_le] <;>
      simpa only [finrank_euclideanSpace] using Nat.le_of_not_gt hk

/-- Real complexification preserves the actual singular-value sequence,
including every padded zero index. Horn–Johnson 2013, Section 2.6;
the dimensions and multiplicities are unchanged. -/
theorem toEuclideanLin_singularValues_map_ofReal {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) (k : ℕ) :
    (A.map Complex.ofReal).toEuclideanLin.singularValues k = A.toEuclideanLin.singularValues k := by
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
    have he := congrFun (complex_eigenvalues₀_eq_of_charpoly
      (Matrix.isHermitian_conjTranspose_mul_self (A.map Complex.ofReal)) hGC
      (congrArg Matrix.charpoly hGram)) ⟨k, hk⟩
    have hm := congrFun (eigenvalues₀_map_ofReal hG hGC) ⟨k, hk⟩
    have hs : (A.map Complex.ofReal).toEuclideanLin.singularValues k ^ 2 =
        A.toEuclideanLin.singularValues k ^ 2 := h₁.trans (he.trans (hm.trans h₂.symm))
    nlinarith [(A.map Complex.ofReal).toEuclideanLin.singularValues_nonneg k,
      A.toEuclideanLin.singularValues_nonneg k]
  · rw [LinearMap.singularValues_of_finrank_le, LinearMap.singularValues_of_finrank_le] <;>
      simpa only [finrank_euclideanSpace] using Nat.le_of_not_gt hk

/-- Left multiplication by a complex column isometry preserves every
actual singular value. Horn–Johnson 2013, Section 2.6. -/
theorem complex_singularValues_isometry_mul {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
    {H : Matrix m p ℂ} (hH : Hᴴ * H = 1) (A : Matrix p n ℂ) (k : ℕ) :
    (H * A).toEuclideanLin.singularValues k = A.toEuclideanLin.singularValues k := by
  apply complex_singularValues_eq_of_gram_charpoly
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Hᴴ H A, hH, Matrix.one_mul]

/-- Right multiplication by a square complex unitary preserves every
actual singular value. Horn–Johnson 2013, Section 2.6. -/
theorem complex_singularValues_mul_unitary {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (U : Matrix.unitaryGroup n ℂ) (k : ℕ) :
    (A * (U : Matrix n n ℂ)).toEuclideanLin.singularValues k = A.toEuclideanLin.singularValues k := by
  apply complex_singularValues_eq_of_gram_charpoly
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc Aᴴ A (U : Matrix n n ℂ),
    Matrix.mul_assoc (Aᴴ * A),
    show (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 from Unitary.coe_mul_star_self U,
    Matrix.mul_one]

/-- The leading actual singular value of a complex square matrix is its
Euclidean operator norm, also in empty dimension. Horn–Johnson 2013,
Section 2.6; complex oblique norm helper. -/
theorem complex_singularValues_zero_eq_norm {n : Type*}
    [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : A.toEuclideanLin.singularValues 0 = ‖A‖ := by
  classical
  by_cases hn : Fintype.card n = 0
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    have hA : A = 0 := by ext i; exact isEmptyElim i
    simp only [hA, map_zero, LinearMap.singularValues_zero, Finsupp.zero_apply, norm_zero]
  · obtain ⟨V, W, hD⟩ := exists_unitary_conjTranspose_mul_mul_eq_diagonal_singularValues A
    have hnorm : ‖A‖ = ‖Matrix.diagonal
        (fun i => (A.toEuclideanLin.singularValues ((Fintype.equivFin n) i) : ℂ))‖ := by
      rw [← hD, CStarRing.norm_mul_coe_unitary]
      exact (CStarRing.norm_coe_unitary_mul (star V) A).symm
    rw [hnorm, Matrix.l2_opNorm_diagonal]
    apply le_antisymm
    · let i : n := (Fintype.equivFin n).symm ⟨0, Nat.pos_of_ne_zero hn⟩
      have h := norm_le_pi_norm (fun i => (A.toEuclideanLin.singularValues ((Fintype.equivFin n) i) : ℂ)) i
      simpa only [i, Equiv.apply_symm_apply, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (A.toEuclideanLin.singularValues_nonneg 0)] using h
    · apply (pi_norm_le_iff_of_nonneg (A.toEuclideanLin.singularValues_nonneg 0)).mpr
      intro i
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (A.toEuclideanLin.singularValues_nonneg _)]
      exact A.toEuclideanLin.singularValues_antitone (Nat.zero_le _)

/-- Complexifying a real square matrix preserves its Euclidean operator
norm exactly. Horn–Johnson 2013, Section 2.6; no dimension doubling. -/
theorem norm_map_ofReal_eq_specNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : ‖A.map Complex.ofReal‖ = specNorm A := by
  rw [← complex_singularValues_zero_eq_norm, toEuclideanLin_singularValues_map_ofReal]
  exact (congrFun (singularValues_reindex A (Fintype.equivFin _) (Fintype.equivFin _)) 0).symm.trans
    (singularValues_reindex_zero_eq_specNorm A)

/-- A complex and a real matrix with identical native singular-value
sequences have equal ranks. Horn–Johnson 2013, Section 2.6; all padded
zeros are included in the hypothesis. -/
theorem rank_eq_of_complex_real_singularValues_eq {m n p q : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q] (A : Matrix m n ℂ) (B : Matrix p q ℝ)
    (h : ∀ i, A.toEuclideanLin.singularValues i = B.toEuclideanLin.singularValues i) :
    A.rank = B.rank := by
  have he : A.toEuclideanLin.singularValues = B.toEuclideanLin.singularValues := Finsupp.ext h
  have hc := congrArg (fun f : ℕ →₀ ℝ => f.support.card) he
  rw [LinearMap.card_support_singularValues, LinearMap.card_support_singularValues] at hc
  exact (A.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun m ℂ).toBasis
    (EuclideanSpace.basisFun n ℂ).toBasis).trans (hc.trans
      (B.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun p ℝ).toBasis
        (EuclideanSpace.basisFun q ℝ).toBasis).symm)

end NLAlib
