import NLAlib.Matrix.ComplexSquareSingularBasis
import NLAlib.Matrix.UnitaryBlockCompletion
import NLAlib.Matrix.CanonicalCS
import NLAlib.Matrix.ComplexDiagonalFilter

/-!
# Complex unitary cosine-sine decomposition

Complex singular bases and an isometry between equal-Gram ranges give a full
unitary CS factorization, including singular cosine and sine endpoints.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

private theorem unitary_gram_mul {n : Type*} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (hX : Xᴴ * X = 1) (hY : Yᴴ * Y = 1) :
    (X * Y)ᴴ * (X * Y) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Xᴴ X Y,
    hX, Matrix.one_mul, hY]

private theorem unitary_gram_blockDiagonal {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    {A : Matrix p p ℂ} {B : Matrix q q ℂ} (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) :
    (Matrix.fromBlocks A 0 0 B)ᴴ * Matrix.fromBlocks A 0 0 B = 1 := by
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, hA, hB, Matrix.fromBlocks_one]

/-- Every complex unitary block matrix has a full cosine-sine decomposition
by four complex unitary factors of sizes `p,p,q,q`. The cosines are its
upper-left block's actual singular values; the right side is the complexified
real canonical CS matrix with the specified coordinate inclusion. Empty blocks
and zero/pi/2 angles are included. Horn–Johnson 2013, Theorem 2.7.1.
atlas: cs-decomposition (partial) -/
theorem exists_complex_cs_decomposition_of_embedding {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    (U : Matrix (p ⊕ q) (p ⊕ q) ℂ) (hU : Uᴴ * U = 1) (e : p ↪ q) :
    let c := fun i : p => U.toBlocks₁₁.toEuclideanLin.singularValues ((Fintype.equivFin p) i)
    (∀ i, c i ∈ Set.Icc (0 : ℝ) 1) ∧
    ∃ V₁ W₁ : Matrix p p ℂ, ∃ V₂ W₂ : Matrix q q ℂ,
      V₁ᴴ * V₁ = 1 ∧ W₁ᴴ * W₁ = 1 ∧ V₂ᴴ * V₂ = 1 ∧ W₂ᴴ * W₂ = 1 ∧
      (Matrix.fromBlocks V₁ 0 0 V₂)ᴴ * U * Matrix.fromBlocks W₁ 0 0 W₂ =
        (csCanonicalMatrix c ((1 : Matrix q q ℝ).submatrix id e)).map Complex.ofReal := by
  dsimp only
  let c := fun i : p => U.toBlocks₁₁.toEuclideanLin.singularValues ((Fintype.equivFin p) i)
  let C : Matrix p p ℂ := Matrix.diagonal (fun i => (c i : ℂ))
  let S : Matrix p p ℂ := Matrix.diagonal (fun i => (Real.sqrt (1 - c i ^ 2) : ℂ))
  let E₀ := (1 : Matrix q q ℝ).submatrix id e
  let E := E₀.map Complex.ofReal
  have hE₀ : HasOrthonormalCols E₀ := by
    have h : HasOrthonormalCols (1 : Matrix q q ℝ) := by simp [HasOrthonormalCols]
    exact h.submatrix_cols e
  have hE : Eᴴ * E = 1 := by
    rw [show Eᴴ = E₀ᵀ.map Complex.ofReal from conjTranspose_map_ofReal E₀,
      ← map_ofReal_mul, hE₀]
    simp
  obtain ⟨V₀, W₀, hVW⟩ := exists_unitary_conjTranspose_mul_mul_eq_diagonal_singularValues U.toBlocks₁₁
  let V := (V₀ : Matrix p p ℂ)
  let W := (W₀ : Matrix p p ℂ)
  have hV : Vᴴ * V = 1 := Unitary.coe_star_mul_self V₀
  have hW : Wᴴ * W = 1 := Unitary.coe_star_mul_self W₀
  have hVt : V * Vᴴ = 1 := Unitary.coe_mul_star_self V₀
  change Vᴴ * U.toBlocks₁₁ * W = C at hVW
  let D := U.toBlocks₂₁ * W
  let M := Matrix.fromBlocks C (Vᴴ * U.toBlocks₁₂) D U.toBlocks₂₂
  have hMForm : Matrix.fromBlocks Vᴴ 0 0 (1 : Matrix q q ℂ) * U *
      Matrix.fromBlocks W 0 0 (1 : Matrix q q ℂ) = M := by
    conv_lhs => arg 1; arg 2; rw [← Matrix.fromBlocks_toBlocks U]
    simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.one_mul, Matrix.mul_one, zero_add, add_zero, hVW]
    rfl
  have hM : Mᴴ * M = 1 := by
    rw [← hMForm]
    exact unitary_gram_mul (unitary_gram_mul
      (unitary_gram_blockDiagonal (by simpa using hVt) (by simp)) hU)
      (unitary_gram_blockDiagonal hW (by simp))
  have hCt : Cᴴ = C := by simp [C, Matrix.diagonal_conjTranspose]
  have hSt : Sᴴ = S := by simp [S, Matrix.diagonal_conjTranspose]
  have hGram : C * C + Dᴴ * D = 1 := by
    have h := congrArg Matrix.toBlocks₁₁ hM
    simpa only [M, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.toBlocks_fromBlocks₁₁, hCt,
      show (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ).toBlocks₁₁ = 1 by
        ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]] using h
  have hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    have hci : 0 ≤ c i := LinearMap.singularValues_nonneg _ _
    have hdiag := congrArg (fun A : Matrix p p ℂ => (A i i).re) hGram
    have hnonneg : 0 ≤ (Dᴴ * D) i i := (Matrix.posSemidef_conjTranspose_mul_self D).diag_nonneg
    have hnonneg' : 0 ≤ ((Dᴴ * D) i i).re := (RCLike.nonneg_iff.mp hnonneg).1
    simp only [Matrix.add_apply, C, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.one_re] at hdiag
    exact ⟨hci, by nlinarith⟩
  have hCS : C * C + S * S = 1 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      have hs := Real.mul_self_sqrt (show 0 ≤ 1 - c i ^ 2 by nlinarith [(hc i).1, (hc i).2])
      norm_cast
      nlinarith [hs]
    · simp [Matrix.add_apply, hij]
  have hSD : (-E * S)ᴴ * (-E * S) = Dᴴ * D := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, hSt,
      Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Eᴴ E S, hE, Matrix.one_mul]
    exact add_left_cancel (hCS.trans hGram.symm)
  obtain ⟨O₀, hOD⟩ := exists_unitary_mul_eq_of_gram_eq (-E * S) D hSD
  let O := (O₀ : Matrix q q ℂ)
  have hOD' : O * D = -E * S := hOD
  have hO : Oᴴ * O = 1 := Unitary.coe_star_mul_self O₀
  let N := Matrix.fromBlocks (1 : Matrix p p ℂ) 0 0 O * M
  have hN : Nᴴ * N = 1 := unitary_gram_mul (unitary_gram_blockDiagonal (by simp) hO) hM
  let K := (csCanonicalMatrix c E₀).map Complex.ofReal
  have hK : Kᴴ * K = 1 := by
    rw [show Kᴴ = (csCanonicalMatrix c E₀)ᵀ.map Complex.ofReal from conjTranspose_map_ofReal _,
      ← map_ofReal_mul, hasOrthonormalCols_csCanonicalMatrix c E₀ hE₀ hc]
    simp
  have hFirst : N.submatrix id Sum.inl = K.submatrix id Sum.inl := by
    dsimp [N, M, K, csCanonicalMatrix]
    simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul,
      add_zero, zero_add, hOD', Matrix.fromBlocks_map]
    ext i j
    cases i with
    | inl i => simp [C, Matrix.diagonal_apply]
    | inr i =>
      change (-E * S) i j = ((-E₀ * Matrix.diagonal (fun i => Real.sqrt (1 - c i ^ 2))).map Complex.ofReal) i j
      rw [map_ofReal_mul]
      simp [E, S, Matrix.mul_apply, Matrix.diagonal_apply]
  obtain ⟨Z, hZ, hNZ⟩ := exists_unitary_right_block_of_first_columns_eq N K hN hK hFirst
  refine ⟨hc, V, W, Oᴴ, Z, hV, hW, ?_, hZ, ?_⟩
  · simpa only [Matrix.conjTranspose_conjTranspose] using (mul_eq_one_comm.mp hO)
  · have hLeft : Matrix.fromBlocks (1 : Matrix p p ℂ) 0 0 O *
        Matrix.fromBlocks Vᴴ 0 0 (1 : Matrix q q ℂ) = (Matrix.fromBlocks V 0 0 Oᴴ)ᴴ := by
      simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
    have hRight : Matrix.fromBlocks W 0 0 (1 : Matrix q q ℂ) *
        Matrix.fromBlocks (1 : Matrix p p ℂ) 0 0 Z = Matrix.fromBlocks W 0 0 Z := by
      simp [Matrix.fromBlocks_multiply]
    dsimp only [N] at hNZ
    rw [← hMForm] at hNZ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hLeft, Matrix.mul_assoc,
      Matrix.mul_assoc, hRight] at hNZ
    simpa only [Matrix.mul_assoc] using hNZ

end NLAlib
