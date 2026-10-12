import NLAlib.Matrix.CanonicalCS
import NLAlib.Matrix.OrthogonalBlockCompletion
import NLAlib.Matrix.SquareSingularBasis
import NLAlib.Matrix.GramIsometry

/-!
# Cosine–sine decomposition of an orthogonal block matrix

One actual block SVD, equal-Gram transport and orthogonal completion produce
the full canonical form without dividing by a cosine or sine. Arbitrary finite
labels and empty blocks are included. Horn–Johnson 2013, Theorem 2.7.1.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

private theorem orthogonal_blockDiagonal {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    {A : Matrix p p ℝ} {B : Matrix q q ℝ}
    (hA : HasOrthonormalCols A) (hB : HasOrthonormalCols B) :
    HasOrthonormalCols (Matrix.fromBlocks A 0 0 B) := by
  change Aᵀ * A = 1 at hA
  change Bᵀ * B = 1 at hB
  change (Matrix.fromBlocks A 0 0 B)ᵀ * Matrix.fromBlocks A 0 0 B = 1
  simp only [Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, hA, hB, Matrix.fromBlocks_one]

/-- An orthogonal matrix split over finite `p,q` labels has a full CS
decomposition relative to any fixed isometric embedding of the first block
into the second. The cosines are exactly the ordered singular values of the
upper-left block and belong to `[0,1]`; the canonical matrix fixes the
embedding's orthogonal complement. Coordinate inclusion gives the ordinary
`p,p,q-p` display, including angles zero and pi/2 and `p = 0`.
Horn–Johnson 2013, Theorem 2.7.1; derivations §alg:cs.
atlas: cs-decomposition (partial) -/
theorem exists_cs_decomposition {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (U : Matrix (p ⊕ q) (p ⊕ q) ℝ) (hU : HasOrthonormalCols U)
    (E : Matrix q p ℝ) (hE : HasOrthonormalCols E) :
    let c := fun i : p => U.toBlocks₁₁.toEuclideanLin.singularValues
      ((Fintype.equivFin p) i)
    (∀ i, c i ∈ Set.Icc (0 : ℝ) 1) ∧
    ∃ V₁ W₁ : Matrix p p ℝ, ∃ V₂ W₂ : Matrix q q ℝ,
      HasOrthonormalCols V₁ ∧ HasOrthonormalCols W₁ ∧
      HasOrthonormalCols V₂ ∧ HasOrthonormalCols W₂ ∧
      (Matrix.fromBlocks V₁ 0 0 V₂)ᵀ * U * Matrix.fromBlocks W₁ 0 0 W₂ =
        csCanonicalMatrix c E := by
  dsimp only
  let c := fun i : p => U.toBlocks₁₁.toEuclideanLin.singularValues
    ((Fintype.equivFin p) i)
  let C := Matrix.diagonal c
  let S := Matrix.diagonal (fun i => Real.sqrt (1 - c i ^ 2))
  obtain ⟨V, W, hV, hW, hVW⟩ :=
    exists_orthogonal_transpose_mul_mul_eq_diagonal_singularValues U.toBlocks₁₁
  change Vᵀ * U.toBlocks₁₁ * W = C at hVW
  have hOneP : HasOrthonormalCols (1 : Matrix p p ℝ) := by simp [HasOrthonormalCols]
  have hOneQ : HasOrthonormalCols (1 : Matrix q q ℝ) := by simp [HasOrthonormalCols]
  let D := U.toBlocks₂₁ * W
  let M := Matrix.fromBlocks C (Vᵀ * U.toBlocks₁₂) D U.toBlocks₂₂
  have hMForm : Matrix.fromBlocks Vᵀ 0 0 (1 : Matrix q q ℝ) * U *
      Matrix.fromBlocks W 0 0 (1 : Matrix q q ℝ) = M := by
    conv_lhs => arg 1; arg 2; rw [← Matrix.fromBlocks_toBlocks U]
    simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.one_mul, Matrix.mul_one, zero_add, add_zero, hVW]
    rfl
  have hM : HasOrthonormalCols M := by
    rw [← hMForm]
    exact ((orthogonal_blockDiagonal hV.transpose hOneQ).mul hU).mul
      (orthogonal_blockDiagonal hW hOneQ)
  have hGram : C * C + Dᵀ * D = 1 := by
    have h := congrArg Matrix.toBlocks₁₁ hM
    simpa only [M, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.toBlocks_fromBlocks₁₁, show Cᵀ = C from Matrix.diagonal_transpose _,
      show (1 : Matrix (p ⊕ q) (p ⊕ q) ℝ).toBlocks₁₁ = 1 by
        ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]] using h
  have hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    have hci : 0 ≤ c i := LinearMap.singularValues_nonneg _ _
    have hdiag := congrArg (fun A : Matrix p p ℝ => A i i) hGram
    have hnonneg : 0 ≤ (Dᵀ * D) i i :=
      dotProduct_self_nonneg (fun j => D j i)
    simp only [Matrix.add_apply, C, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at hdiag
    exact ⟨hci, by nlinarith⟩
  have hCS : C * C + S * S = 1 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      rw [Real.mul_self_sqrt (by nlinarith [(hc i).1, (hc i).2])]
      ring
    · simp [Matrix.add_apply, hij]
  have hSD : (-E * S)ᵀ * (-E * S) = Dᵀ * D := by
    simp only [Matrix.transpose_mul, Matrix.transpose_neg,
      show Sᵀ = S from Matrix.diagonal_transpose _, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Eᵀ E S, hE, Matrix.one_mul]
    exact add_left_cancel (hCS.trans hGram.symm)
  obtain ⟨O, hO, hOD⟩ := exists_orthogonal_mul_eq_of_gram_eq (-E * S) D hSD
  let N := Matrix.fromBlocks (1 : Matrix p p ℝ) 0 0 O * M
  have hN : HasOrthonormalCols N := (orthogonal_blockDiagonal hOneP hO).mul hM
  have hFirst : N.submatrix id Sum.inl = (csCanonicalMatrix c E).submatrix id Sum.inl := by
    dsimp [N, M, csCanonicalMatrix]
    simp only [Matrix.fromBlocks_multiply, Matrix.one_mul,
      Matrix.zero_mul, add_zero, zero_add, hOD]
    ext i j
    cases i <;> rfl
  obtain ⟨Z, hZ, hNZ⟩ := exists_orthogonal_right_block_of_first_columns_eq
    N (csCanonicalMatrix c E) hN (hasOrthonormalCols_csCanonicalMatrix c E hE hc) hFirst
  refine ⟨hc, V, W, Oᵀ, Z, hV, hW, hO.transpose, hZ, ?_⟩
  have hLeft : Matrix.fromBlocks (1 : Matrix p p ℝ) 0 0 O *
      Matrix.fromBlocks Vᵀ 0 0 (1 : Matrix q q ℝ) =
      (Matrix.fromBlocks V 0 0 Oᵀ)ᵀ := by
    simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose]
  have hRight : Matrix.fromBlocks W 0 0 (1 : Matrix q q ℝ) *
      Matrix.fromBlocks (1 : Matrix p p ℝ) 0 0 Z = Matrix.fromBlocks W 0 0 Z := by
    simp [Matrix.fromBlocks_multiply]
  dsimp only [N] at hNZ
  rw [← hMForm] at hNZ
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hLeft, Matrix.mul_assoc,
    Matrix.mul_assoc, hRight] at hNZ
  simpa only [Matrix.mul_assoc] using hNZ

/-- The full CS factorization with a literal coordinate inclusion into the
larger block. The four basis factors have the required sizes `p,p,q,q`.
Any injective coordinate placement works; a placement exists exactly when
`card p ≤ card q`. Horn–Johnson 2013, Theorem 2.7.1.
atlas: cs-decomposition (partial) -/
theorem exists_cs_decomposition_of_embedding {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (U : Matrix (p ⊕ q) (p ⊕ q) ℝ) (hU : HasOrthonormalCols U) (e : p ↪ q) :
    let c := fun i : p => U.toBlocks₁₁.toEuclideanLin.singularValues
      ((Fintype.equivFin p) i)
    (∀ i, c i ∈ Set.Icc (0 : ℝ) 1) ∧
    ∃ V₁ W₁ : Matrix p p ℝ, ∃ V₂ W₂ : Matrix q q ℝ,
      HasOrthonormalCols V₁ ∧ HasOrthonormalCols W₁ ∧
      HasOrthonormalCols V₂ ∧ HasOrthonormalCols W₂ ∧
      (Matrix.fromBlocks V₁ 0 0 V₂)ᵀ * U * Matrix.fromBlocks W₁ 0 0 W₂ =
        csCanonicalMatrix c ((1 : Matrix q q ℝ).submatrix id e) := by
  have hOne : HasOrthonormalCols (1 : Matrix q q ℝ) := by simp [HasOrthonormalCols]
  exact exists_cs_decomposition U hU _ (hOne.submatrix_cols e)

end NLAlib
