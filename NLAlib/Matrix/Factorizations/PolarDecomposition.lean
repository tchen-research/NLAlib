import NLAlib.Matrix.Subspaces.RectangularGramIsometry
import NLAlib.Matrix.Subspaces.PolarFrame
import NLAlib.Matrix.Basic.MoorePenroseRank
import NLAlib.Matrix.Basic.Gram
/-!
# Polar decompositions at arbitrary rank

The positive factor is the square root of the Gram matrix. Equality of Gram
matrices supplies an isometry also at deficient rank. Horn–Johnson 2013,
Theorem 7.3.1; atlas `polar-decomposition`.
-/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Every real matrix with at least as many rows as columns has a polar
isometry, without a full-rank assumption. Empty spaces are included.
Horn–Johnson 2013, Theorem 7.3.1.
atlas: polar-decomposition (partial) -/
theorem exists_isometry_mul_sqrt_gram_eq [DecidableEq m] (A : Matrix m n ℝ)
    (hCard : Fintype.card n ≤ Fintype.card m) :
    ∃ U : Matrix m n ℝ, HasOrthonormalCols U ∧ U * CFC.sqrt (Aᵀ * A) = A := by
  have hNonneg : 0 ≤ Aᵀ * A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  have hSym : (CFC.sqrt (Aᵀ * A))ᵀ = CFC.sqrt (Aᵀ * A) := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg (Aᵀ * A)).star_eq
  apply exists_isometry_mul_eq_of_gram_eq (CFC.sqrt (Aᵀ * A)) A hCard
  rw [hSym, CFC.sqrt_mul_sqrt_self _ hNonneg]

/-- The positive factor in any polar isometry factorization is the unique
positive square root of the column Gram matrix. Horn–Johnson 2013, Thm 7.3.1.
atlas: polar-decomposition (partial) -/
theorem eq_sqrt_gram_of_isometry_mul_eq {A U : Matrix m n ℝ} {Q : Matrix n n ℝ}
    (hU : HasOrthonormalCols U) (hQ : Q.PosSemidef) (hA : U * Q = A) :
    Q = CFC.sqrt (Aᵀ * A) := by
  symm
  apply CFC.sqrt_unique _ hQ.nonneg
  rw [← hA, Matrix.transpose_mul]
  have hSym : Qᵀ = Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.isHermitian.eq
  rw [hSym, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U Q, (show Uᵀ * U = 1 from hU), Matrix.one_mul]

/-- A wide real matrix has a coisometry on the right of its row-Gram square
root. Orthonormal rows are the dimensionally correct wide formulation.
Horn–Johnson 2013, Theorem 7.3.1.
atlas: polar-decomposition (partial) -/
theorem exists_sqrt_rowGram_mul_coisometry_eq [DecidableEq m] (A : Matrix m n ℝ)
    (hCard : Fintype.card m ≤ Fintype.card n) :
    ∃ U : Matrix m n ℝ, U * Uᵀ = 1 ∧ CFC.sqrt (A * Aᵀ) * U = A := by
  obtain ⟨V, hV, hEq⟩ := exists_isometry_mul_sqrt_gram_eq Aᵀ hCard
  refine ⟨Vᵀ, ?_, ?_⟩
  · change Vᵀ * V = 1
    exact hV
  · have hSym : (CFC.sqrt (A * Aᵀ))ᵀ = CFC.sqrt (A * Aᵀ) := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
        (CFC.sqrt_nonneg (A * Aᵀ)).star_eq
    have h := congrArg Matrix.transpose hEq
    simpa only [Matrix.transpose_transpose, Matrix.transpose_mul, hSym] using h

/-- At full column rank a polar isometry equals the explicit inverse-square-
root formula and hence is unique. Horn–Johnson 2013, Theorem 7.3.1.
atlas: polar-decomposition (partial) -/
theorem eq_polarFrame_of_isometry_mul_sqrt_gram_eq {A U : Matrix m n ℝ}
    (hRank : A.rank = Fintype.card n) (hA : U * CFC.sqrt (Aᵀ * A) = A) :
    U = polarFrame A := by
  have hGram : IsUnit (Aᵀ * A) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    apply det_ne_zero_of_rank_eq
    rwa [Matrix.rank_transpose_mul_self]
  have hNonneg : 0 ≤ Aᵀ * A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  have hSqrt := (CFC.isUnit_sqrt_iff _ hNonneg).mpr hGram
  have hInv := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hSqrt)
  have h := congrArg (fun M : Matrix m n ℝ => M * (CFC.sqrt (Aᵀ * A))⁻¹) hA
  simpa only [Matrix.mul_assoc, hInv, Matrix.mul_one, polarFrame] using h

/-- Rank deficiency gives a second polar isometry: reflect the orthogonal
complement of the positive factor's range. Horn–Johnson 2013, Thm 7.3.1.
atlas: polar-decomposition (partial) -/
theorem exists_ne_isometry_mul_sqrt_gram_eq_of_rank_lt {A U : Matrix m n ℝ}
    (hU : HasOrthonormalCols U) (hA : U * CFC.sqrt (Aᵀ * A) = A)
    (hRank : A.rank < Fintype.card n) :
    ∃ V : Matrix m n ℝ, HasOrthonormalCols V ∧
      V * CFC.sqrt (Aᵀ * A) = A ∧ V ≠ U := by
  let Q := CFC.sqrt (Aᵀ * A)
  let P := Q * moorePenroseInverse Q
  let T := P + P - 1
  have hP : P * P = P := mul_moorePenroseInverse_isIdempotentElem Q
  have hPs : Pᵀ = P := (mul_moorePenroseInverse_isSymm Q).eq
  have hT : Tᵀ * T = 1 := by
    dsimp [T]
    simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one, hPs,
      Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hP]
    abel
  have hPQ : P * Q = Q := mul_moorePenroseInverse_mul Q
  have hTQ : T * Q = Q := by
    dsimp [T]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, hPQ]
    abel
  refine ⟨U * T, ?_, ?_, ?_⟩
  · change (U * T)ᵀ * (U * T) = 1
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U T,
      (show Uᵀ * U = 1 from hU), Matrix.one_mul, hT]
  · change (U * T) * Q = A
    rw [Matrix.mul_assoc, hTQ]
    exact hA
  · intro hEq
    have hTI : T = 1 := by
      have h := congrArg (fun M : Matrix m n ℝ => Uᵀ * M) hEq
      rwa [← Matrix.mul_assoc, (show Uᵀ * U = 1 from hU), Matrix.one_mul] at h
    have hPI : P = 1 := by
      ext i j
      have h := congrArg (fun M : Matrix n n ℝ => M i j) hTI
      change P i j + P i j - (1 : Matrix n n ℝ) i j = (1 : Matrix n n ℝ) i j at h
      linarith
    have hQRank : Q.rank = Fintype.card n := by
      have h := rank_mul_moorePenroseInverse Q
      change P.rank = Q.rank at h
      rw [hPI, Matrix.rank_one] at h
      exact h.symm
    have hLeft : Q = Uᵀ * A := by
      rw [← hA, ← Matrix.mul_assoc, (show Uᵀ * U = 1 from hU), Matrix.one_mul]
    have hBound : Q.rank ≤ A.rank := by
      rw [hLeft]
      exact Matrix.rank_mul_le_right _ _
    omega

/-- Among polar isometries, uniqueness holds exactly at full column rank,
including the empty column space. Horn–Johnson 2013, Theorem 7.3.1.
atlas: polar-decomposition (partial) -/
theorem polar_isometry_unique_iff_rank_eq_card {A U : Matrix m n ℝ}
    (hU : HasOrthonormalCols U) (hA : U * CFC.sqrt (Aᵀ * A) = A) :
    (∀ V : Matrix m n ℝ, HasOrthonormalCols V →
      V * CFC.sqrt (Aᵀ * A) = A → V = U) ↔ A.rank = Fintype.card n := by
  constructor
  · intro h
    by_contra hRank
    have hlt := lt_of_le_of_ne A.rank_le_card_width hRank
    obtain ⟨V, hV, hVA, hVU⟩ := exists_ne_isometry_mul_sqrt_gram_eq_of_rank_lt hU hA hlt
    exact hVU (h V hV hVA)
  · intro hRank V _ hVA
    exact (eq_polarFrame_of_isometry_mul_sqrt_gram_eq hRank hVA).trans
      (eq_polarFrame_of_isometry_mul_sqrt_gram_eq hRank hA).symm

/-- In the square case the same orthogonal factor works on both sides of the
two Gram square roots, even at zero rank. Horn–Johnson 2013, Theorem 7.3.1.
atlas: polar-decomposition (partial) -/
theorem sqrt_rowGram_mul_eq_of_isometry_mul_sqrt_gram_eq {A U : Matrix n n ℝ}
    (hU : HasOrthonormalCols U) (hA : U * CFC.sqrt (Aᵀ * A) = A) :
    CFC.sqrt (A * Aᵀ) * U = A := by
  let Q := CFC.sqrt (Aᵀ * A)
  let P := U * Q * Uᵀ
  have hAQ : U * Q = A := hA
  have hQ : Q.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hP : P.PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hQ.mul_mul_conjTranspose_same U
  have hQs : Qᵀ = Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.isHermitian.eq
  have hSq : P * P = A * Aᵀ := by
    change (U * Q * Uᵀ) * (U * Q * Uᵀ) = A * Aᵀ
    calc
      _ = U * Q * Q * Uᵀ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᵀ U (Q * Uᵀ), (show Uᵀ * U = 1 from hU), Matrix.one_mul]
      _ = A * Aᵀ := by
        rw [← hAQ]
        simp only [Matrix.transpose_mul, hQs, Matrix.mul_assoc]
  have hRoot : CFC.sqrt (A * Aᵀ) = P := CFC.sqrt_unique hSq hP.nonneg
  rw [hRoot]
  change (U * Q * Uᵀ) * U = A
  rw [Matrix.mul_assoc, (show Uᵀ * U = 1 from hU), Matrix.mul_one]
  exact hA

omit [DecidableEq n] in
/-- Coisometry uniqueness in the wide formulation holds exactly at full row
rank. Horn–Johnson 2013, Theorem 7.3.1.
atlas: polar-decomposition (partial) -/
theorem polar_coisometry_unique_iff_rank_eq_card [DecidableEq m]
    {A U : Matrix m n ℝ} (hU : U * Uᵀ = 1)
    (hA : CFC.sqrt (A * Aᵀ) * U = A) :
    (∀ V : Matrix m n ℝ, V * Vᵀ = 1 →
      CFC.sqrt (A * Aᵀ) * V = A → V = U) ↔ A.rank = Fintype.card m := by
  have hSym : (CFC.sqrt (A * Aᵀ))ᵀ = CFC.sqrt (A * Aᵀ) := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg (A * Aᵀ)).star_eq
  have hUt : HasOrthonormalCols Uᵀ := by
    simpa only [hasOrthonormalCols_iff_conjTranspose_mul_self,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
  have hAt : Uᵀ * CFC.sqrt (Aᵀᵀ * Aᵀ) = Aᵀ := by
    simpa only [Matrix.transpose_mul, hSym, Matrix.transpose_transpose] using
      congrArg Matrix.transpose hA
  rw [← Matrix.rank_transpose A, ← polar_isometry_unique_iff_rank_eq_card hUt hAt]
  constructor
  · intro h V hV hVA
    apply Matrix.transpose_injective
    have hVr : Vᵀ * Vᵀᵀ = 1 := by
      simpa only [Matrix.transpose_transpose] using (show Vᵀ * V = 1 from hV)
    have hVar : CFC.sqrt (A * Aᵀ) * Vᵀ = A := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hSym] using
        congrArg Matrix.transpose hVA
    simpa only [Matrix.transpose_transpose] using h Vᵀ hVr hVar
  · intro h V hV hVA
    apply Matrix.transpose_injective
    have hVt : HasOrthonormalCols Vᵀ := by
      simpa only [hasOrthonormalCols_iff_conjTranspose_mul_self,
        Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using hV
    apply h Vᵀ hVt
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hSym] using
      congrArg Matrix.transpose hVA

end NLAlib
