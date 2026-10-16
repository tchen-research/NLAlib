import NLAlib.Matrix.Norms.BlockDiagonalBounds
import NLAlib.Matrix.Subspaces.CoordinateFrames
import NLAlib.Matrix.Structured.KroneckerNormRank

/-!
# Exact spectral norm of dependent rectangular block diagonal matrices

Unequal finite block sizes and arbitrary real or complex scalar fields are
allowed. Repetition by a nonempty identity factor preserves every block norm.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Kronecker
namespace NLAlib

/-- Selecting distinct matrix rows and columns cannot increase spectral norm.
The selected row and column types may be empty. -/
theorem specNorm_submatrix_le {𝕜 m n r s : Type*} [RCLike 𝕜]
    [Fintype m] [Fintype n] [Fintype r] [Fintype s]
    [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s]
    (A : Matrix m n 𝕜) (f : r → m) (g : s → n)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    specNorm (A.submatrix f g) ≤ specNorm A := by
  let P : Matrix m r 𝕜 := coordinateFrame f
  let Q : Matrix n s 𝕜 := coordinateFrame g
  have hP : specNorm Pᴴ ≤ 1 := by
    rw [specNorm_conjTranspose]
    exact specNorm_le_one_of_orthonormal (hasOrthonormalCols_coordinateFrame hf)
  have hQ : specNorm Q ≤ 1 :=
    specNorm_le_one_of_orthonormal (hasOrthonormalCols_coordinateFrame hg)
  have he : Pᴴ * A * Q = A.submatrix f g := by
    dsimp [P, Q, coordinateFrame]
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
    have hl := Matrix.one_submatrix_mul f (Equiv.refl m) A
    simp only [Equiv.coe_refl, Equiv.refl_symm, Function.id_comp] at hl
    rw [hl]
    have hr := Matrix.mul_submatrix_one (Equiv.refl n) g (A.submatrix f id)
    simpa only [Equiv.coe_refl, Equiv.refl_symm, Function.id_comp,
      Matrix.submatrix_submatrix, Function.comp_id] using hr
  rw [← he]
  calc
    _ ≤ specNorm (Pᴴ * A) * specNorm Q := specNorm_mul_le _ _
    _ ≤ (specNorm Pᴴ * specNorm A) * specNorm Q :=
      mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
    _ ≤ (1 * specNorm A) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hP (specNorm_nonneg _)) hQ
        (specNorm_nonneg _) (by simpa only [one_mul] using specNorm_nonneg A)
    _ = specNorm A := by ring

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
  {m n : ι → Type*} [∀ i, Fintype (m i)] [∀ i, Fintype (n i)]
  [∀ i, DecidableEq (m i)] [∀ i, DecidableEq (n i)]

/-- A dependent block diagonal matrix acts separately on every vector block. -/
theorem blockDiagonal'_mulVec_apply (B : ∀ i, Matrix (m i) (n i) 𝕜)
    (x : (Σ i, n i) → 𝕜) (i : ι) (a : m i) :
    (Matrix.blockDiagonal' B *ᵥ x) ⟨i, a⟩ = (B i *ᵥ fun b => x ⟨i, b⟩) a := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro j hj hji
    apply Finset.sum_eq_zero
    intro b hb
    rw [Matrix.blockDiagonal'_apply_ne B a b hji.symm, zero_mul]
  · simp

/-- A common bound on all dependent rectangular block norms bounds the full
block diagonal matrix, including empty blocks and an empty block family. -/
theorem specNorm_blockDiagonal'_le (B : ∀ i, Matrix (m i) (n i) 𝕜)
    {c : ℝ} (hc : 0 ≤ c) (hB : ∀ i, specNorm (B i) ≤ c) :
    specNorm (Matrix.blockDiagonal' B) ≤ c := by
  apply specNorm_le_of_sum_norm_sq_mulVec_le hc
  intro x
  simp only [Fintype.sum_sigma, blockDiagonal'_mulVec_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact (sum_norm_sq_mulVec_le_specNorm_sq (B i) (fun b => x ⟨i, b⟩)).trans
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (specNorm_nonneg _) (hB i) 2)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- Every individual block norm is bounded by the norm of the entire dependent
block diagonal matrix. This includes empty row or column blocks. -/
theorem specNorm_block_le_blockDiagonal' (B : ∀ i, Matrix (m i) (n i) 𝕜) (i : ι) :
    specNorm (B i) ≤ specNorm (Matrix.blockDiagonal' B) := by
  have h := specNorm_submatrix_le (Matrix.blockDiagonal' B)
    (fun a : m i => (⟨i, a⟩ : Σ j, m j)) (fun b : n i => (⟨i, b⟩ : Σ j, n j))
    (by intro a b h; exact eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    (by intro a b h; exact eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  have he : (Matrix.blockDiagonal' B).submatrix
      (fun a : m i => (⟨i, a⟩ : Σ j, m j)) (fun b : n i => (⟨i, b⟩ : Σ j, n j)) = B i := by
    ext a b
    exact Matrix.blockDiagonal'_apply_eq B i a b
  rw [he] at h
  exact h

/-- The exact spectral norm of an unequal-size finite rectangular block
diagonal matrix is the maximum of its block spectral norms. -/
theorem specNorm_blockDiagonal'_eq_max [Nonempty ι]
    (B : ∀ i, Matrix (m i) (n i) 𝕜) :
    specNorm (Matrix.blockDiagonal' B) =
      Finset.univ.sup' Finset.univ_nonempty (fun i => specNorm (B i)) := by
  apply le_antisymm
  · apply specNorm_blockDiagonal'_le
    · let i : ι := Classical.choice inferInstance
      exact (specNorm_nonneg (B i)).trans
        (Finset.le_sup' (fun j => specNorm (B j)) (Finset.mem_univ i))
    · intro i
      exact Finset.le_sup' (fun j => specNorm (B j)) (Finset.mem_univ i)
  · apply Finset.sup'_le
    intro i hi
    exact specNorm_block_le_blockDiagonal' B i

/-- Repeating each dependent rectangular block by a nonempty identity factor
does not alter the maximum block spectral norm. This retains the representation
multiplicities used by finite-group Fourier decomposition. -/
theorem specNorm_blockDiagonal'_one_kronecker_eq_max [Nonempty ι]
    {r : ι → Type*} [∀ i, Fintype (r i)] [∀ i, DecidableEq (r i)] [∀ i, Nonempty (r i)]
    (B : ∀ i, Matrix (m i) (n i) 𝕜) :
    specNorm (Matrix.blockDiagonal' (fun i => (1 : Matrix (r i) (r i) 𝕜) ⊗ₖ B i)) =
      Finset.univ.sup' Finset.univ_nonempty (fun i => specNorm (B i)) := by
  rw [specNorm_blockDiagonal'_eq_max]
  congr 1
  funext i
  rw [specNorm_kronecker]
  have hI : specNorm (1 : Matrix (r i) (r i) 𝕜) = 1 := by
    rw [specNorm_eq_norm, ← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp
  rw [hI, one_mul]

end NLAlib
