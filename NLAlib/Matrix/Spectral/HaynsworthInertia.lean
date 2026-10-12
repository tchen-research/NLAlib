import NLAlib.Matrix.Spectral.Inertia

/-!
# Haynsworth inertia additivity

An invertible Hermitian leading block reduces a symmetric block matrix
by a triangular congruence to the direct sum of that block and its Schur
complement. Positive and negative indices add, and nullity comes entirely
from the Schur complement. Source: Horn--Johnson (2013), Exercise 4.5.P21.
Atlas: `haynsworth-inertia-additivity`.
-/

noncomputable section
open Matrix Module

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Diagonalizing each block independently gives a congruence of their
direct sum to the sum-indexed diagonal. Spectral theorem;
helper for `haynsworth-inertia-additivity`. -/
theorem fromBlocks_eq_congruence_diagonal {A : Matrix m m ℝ} {C : Matrix n n ℝ}
    (hA : A.IsHermitian) (hC : C.IsHermitian) :
    fromBlocks A 0 0 C =
      (fromBlocks (hA.eigenvectorUnitary : Matrix m m ℝ)ᵀ 0 0
        (hC.eigenvectorUnitary : Matrix n n ℝ)ᵀ)ᵀ *
      diagonal (Sum.elim hA.eigenvalues hC.eigenvalues) *
      fromBlocks (hA.eigenvectorUnitary : Matrix m m ℝ)ᵀ 0 0
        (hC.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  rw [← fromBlocks_diagonal, fromBlocks_transpose]
  simp only [Matrix.transpose_transpose, Matrix.transpose_zero, fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
  rw [← eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA,
    ← eq_eigenvectorUnitary_mul_diagonal_mul_transpose hC]

/-- Positive inertia adds over a block direct sum. Horn--Johnson (2013),
Exercise 4.5.P21; helper for `haynsworth-inertia-additivity`. -/
theorem inertiaPos_fromBlocks_zero {A : Matrix m m ℝ} {C : Matrix n n ℝ}
    (hA : A.IsHermitian) (hC : C.IsHermitian) :
    inertiaPos (fromBlocks A 0 0 C) = inertiaPos A + inertiaPos C := by
  classical
  rw [fromBlocks_eq_congruence_diagonal hA hC]
  rw [inertiaPos_transpose_mul_mul _ (isUnit_fromBlocks_zero₂₁.mpr
    ⟨isUnit_transpose_eigenvectorUnitary hA, isUnit_transpose_eigenvectorUnitary hC⟩)]
  rw [inertiaPos_diagonal, inertiaPos_eq_card_eigenvalues_pos hA,
    inertiaPos_eq_card_eigenvalues_pos hC]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  congr 1

/-- Negative inertia adds over a block direct sum. Horn--Johnson (2013),
Exercise 4.5.P21; helper for `haynsworth-inertia-additivity`. -/
theorem inertiaNeg_fromBlocks_zero {A : Matrix m m ℝ} {C : Matrix n n ℝ}
    (hA : A.IsHermitian) (hC : C.IsHermitian) :
    inertiaNeg (fromBlocks A 0 0 C) = inertiaNeg A + inertiaNeg C := by
  classical
  rw [fromBlocks_eq_congruence_diagonal hA hC]
  rw [inertiaNeg_transpose_mul_mul _ (isUnit_fromBlocks_zero₂₁.mpr
    ⟨isUnit_transpose_eigenvectorUnitary hA, isUnit_transpose_eigenvectorUnitary hC⟩)]
  rw [inertiaNeg_diagonal, inertiaNeg_eq_card_eigenvalues_neg hA,
    inertiaNeg_eq_card_eigenvalues_neg hC]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  congr 1

/-- Positive and negative inertia together equal the rank of a symmetric
matrix. Sylvester's law and the spectral rank count;
helper for `haynsworth-inertia-additivity`. -/
theorem inertiaPos_add_inertiaNeg_eq_rank {k : Type*} [Fintype k] [DecidableEq k]
    {A : Matrix k k ℝ} (hA : A.IsHermitian) : inertiaPos A + inertiaNeg A = A.rank := by
  classical
  rw [inertiaPos_eq_card_eigenvalues_pos hA, inertiaNeg_eq_card_eigenvalues_neg hA,
    hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hu : (Finset.univ.filter fun i => 0 < hA.eigenvalues i) ∪
      (Finset.univ.filter fun i => hA.eigenvalues i < 0) =
      (Finset.univ.filter fun i => hA.eigenvalues i ≠ 0) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [ne_comm] using
      (ne_iff_lt_or_gt (a := (0 : ℝ)) (b := hA.eigenvalues i)).symm
  have hd : Disjoint (Finset.univ.filter fun i => 0 < hA.eigenvalues i)
      (Finset.univ.filter fun i => hA.eigenvalues i < 0) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    exact (not_lt_of_ge hi'.le) hj'
  rw [← hu, Finset.card_union_of_disjoint hd]

/-- Nullity of a real symmetric matrix counts exactly its zero
eigenvalues. Spectral rank count and rank--nullity;
helper for `haynsworth-inertia-additivity`. -/
theorem finrank_ker_eq_card_eigenvalues_zero {k : Type*} [Fintype k] [DecidableEq k]
    {A : Matrix k k ℝ} (hA : A.IsHermitian) :
    finrank ℝ (LinearMap.ker A.mulVecLin) =
      (Finset.univ.filter fun i => hA.eigenvalues i = 0).card := by
  classical
  have hr : A.rank + finrank ℝ (LinearMap.ker A.mulVecLin) = Fintype.card k := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset k)) (p := fun i => hA.eigenvalues i = 0)
  have hAr : A.rank = (Finset.univ.filter fun i => hA.eigenvalues i ≠ 0).card := by
    rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hFilter : (Finset.univ.filter fun i => ¬ hA.eigenvalues i = 0) =
      (Finset.univ.filter fun i => hA.eigenvalues i ≠ 0) := by
    ext i
    simp only [Finset.mem_filter]
  rw [hFilter] at hc
  simp only [Finset.card_univ] at hc
  omega

/-- Symmetric block elimination is an exact triangular congruence to the
leading block and its Schur complement. Horn--Johnson (2013), Exercise 4.5.P21;
helper for `haynsworth-inertia-additivity`. -/
theorem fromBlocks_eq_transpose_mul_schur_mul {A : Matrix m m ℝ}
    (hA : A.IsHermitian) (hAu : IsUnit A) (B : Matrix m n ℝ) (C : Matrix n n ℝ) :
    fromBlocks A B Bᵀ C =
      (fromBlocks 1 (A⁻¹ * B) 0 1)ᵀ *
      fromBlocks A 0 0 (C - Bᵀ * A⁻¹ * B) *
      fromBlocks 1 (A⁻¹ * B) 0 1 := by
  let : Invertible A := hAu.invertible
  have hAt : (A⁻¹)ᵀ = A⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.inv.eq
  simpa only [Matrix.invOf_eq_nonsing_inv, fromBlocks_transpose,
    Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_mul, hAt] using
    Matrix.fromBlocks_eq_of_invertible₁₁ A B Bᵀ C

omit [Fintype n] [DecidableEq n] in
/-- The Schur complement of a symmetric matrix at an invertible symmetric
leading block is symmetric. Horn--Johnson (2013), Exercise 4.5.P21;
helper for `haynsworth-inertia-additivity`. -/
theorem isHermitian_schur_complement {A : Matrix m m ℝ} {C : Matrix n n ℝ}
    (hA : A.IsHermitian) (hC : C.IsHermitian) (B : Matrix m n ℝ) :
    (C - Bᵀ * A⁻¹ * B).IsHermitian := by
  apply hC.sub
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_mul B hA.inv

/-- Haynsworth's positive inertia additivity at an invertible leading
block. Horn--Johnson (2013), Exercise 4.5.P21.
atlas: haynsworth-inertia-additivity (partial) -/
theorem inertiaPos_fromBlocks_eq_add_schur {A : Matrix m m ℝ} {C : Matrix n n ℝ}
    (hA : A.IsHermitian) (hAu : IsUnit A) (hC : C.IsHermitian) (B : Matrix m n ℝ) :
    inertiaPos (fromBlocks A B Bᵀ C) = inertiaPos A + inertiaPos (C - Bᵀ * A⁻¹ * B) := by
  rw [fromBlocks_eq_transpose_mul_schur_mul hA hAu B C,
    inertiaPos_transpose_mul_mul _ (isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, isUnit_one⟩)]
  exact inertiaPos_fromBlocks_zero hA (isHermitian_schur_complement hA hC B)

/-- Haynsworth's negative inertia additivity at an invertible leading
block. Horn--Johnson (2013), Exercise 4.5.P21.
atlas: haynsworth-inertia-additivity (partial) -/
theorem inertiaNeg_fromBlocks_eq_add_schur {A : Matrix m m ℝ} {C : Matrix n n ℝ}
    (hA : A.IsHermitian) (hAu : IsUnit A) (hC : C.IsHermitian) (B : Matrix m n ℝ) :
    inertiaNeg (fromBlocks A B Bᵀ C) = inertiaNeg A + inertiaNeg (C - Bᵀ * A⁻¹ * B) := by
  rw [fromBlocks_eq_transpose_mul_schur_mul hA hAu B C,
    inertiaNeg_transpose_mul_mul _ (isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, isUnit_one⟩)]
  exact inertiaNeg_fromBlocks_zero hA (isHermitian_schur_complement hA hC B)

/-- A block direct sum is positive definite exactly when both blocks are
positive definite. Horn--Johnson (2013), Exercise 4.5.P21;
helper for `haynsworth-inertia-additivity`. -/
theorem posDef_fromBlocks_zero_iff (A : Matrix m m ℝ) (C : Matrix n n ℝ) :
    (fromBlocks A 0 0 C).PosDef ↔ A.PosDef ∧ C.PosDef := by
  constructor
  · intro h
    exact ⟨h.submatrix Sum.inl_injective, h.submatrix Sum.inr_injective⟩
  · rintro ⟨hA, hC⟩
    let : Invertible A := hA.isUnit.invertible
    have hPSD : (fromBlocks A 0 0 C).PosSemidef := by
      apply (Matrix.PosDef.fromBlocks₁₁ (0 : Matrix m n ℝ) C hA).mpr
      simpa only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, sub_zero]
        using hC.posSemidef
    exact hPSD.posDef_iff_isUnit.mpr
      (isUnit_fromBlocks_zero₂₁.mpr ⟨hA.isUnit, hC.isUnit⟩)

private theorem posDef_fromBlocks_iff_posDef_schur {A : Matrix m m ℝ}
    (hA : A.IsHermitian) (hAu : IsUnit A) (B : Matrix m n ℝ) (C : Matrix n n ℝ) :
    (fromBlocks A B Bᵀ C).PosDef ↔ A.PosDef ∧ (C - Bᵀ * A⁻¹ * B).PosDef := by
  rw [fromBlocks_eq_transpose_mul_schur_mul hA hAu B C]
  have hU : IsUnit (fromBlocks 1 (A⁻¹ * B) 0 1 : Matrix (m ⊕ n) (m ⊕ n) ℝ) :=
    isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, isUnit_one⟩
  rw [show (fromBlocks 1 (A⁻¹ * B) 0 1 : Matrix (m ⊕ n) (m ⊕ n) ℝ)ᵀ =
    star (fromBlocks 1 (A⁻¹ * B) 0 1 : Matrix (m ⊕ n) (m ⊕ n) ℝ) by rfl,
    hU.posDef_star_left_conjugate_iff, posDef_fromBlocks_zero_iff]

/-- A symmetric block matrix `[A B; Bᵀ C]` is positive definite exactly when its leading block
`A` and its Schur complement `C − BᵀA⁻¹B` are both positive definite; no invertibility
hypothesis is needed (the forward implication derives it). Horn--Johnson (2013),
Exercise 4.5.P21 and Theorem 7.7.7.
atlas: haynsworth-inertia-additivity (partial), psd-block-contraction (partial) -/
theorem posDef_fromBlocks_iff_posDef_and_schur
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ) :
    (fromBlocks A B Bᵀ C).PosDef ↔ A.PosDef ∧ (C - Bᵀ * A⁻¹ * B).PosDef := by
  constructor
  · intro hH
    have hA : A.PosDef := hH.submatrix
      (Sum.inl_injective : Function.Injective (Sum.inl : m → m ⊕ n))
    exact (posDef_fromBlocks_iff_posDef_schur hA.isHermitian hA.isUnit B C).mp hH
  · rintro ⟨hA, hS⟩
    exact (posDef_fromBlocks_iff_posDef_schur hA.isHermitian hA.isUnit B C).mpr ⟨hA, hS⟩

/-- An invertible leading block leaves all nullity in its Schur complement.
Horn--Johnson (2013), Exercise 4.5.P21.
atlas: haynsworth-inertia-additivity (partial) -/
theorem finrank_ker_fromBlocks_eq_schur {A : Matrix m m ℝ} {C : Matrix n n ℝ}
    (hA : A.IsHermitian) (hAu : IsUnit A) (hC : C.IsHermitian) (B : Matrix m n ℝ) :
    finrank ℝ (LinearMap.ker (fromBlocks A B Bᵀ C).mulVecLin) =
      finrank ℝ (LinearMap.ker (C - Bᵀ * A⁻¹ * B).mulVecLin) := by
  have hM : (fromBlocks A B Bᵀ C).IsHermitian :=
    hA.fromBlocks (by simp only [Matrix.conjTranspose_eq_transpose_of_trivial]) hC
  have hS := isHermitian_schur_complement hA hC B
  have hP := inertiaPos_fromBlocks_eq_add_schur hA hAu hC B
  have hN := inertiaNeg_fromBlocks_eq_add_schur hA hAu hC B
  have hrM : (fromBlocks A B Bᵀ C).rank +
      finrank ℝ (LinearMap.ker (fromBlocks A B Bᵀ C).mulVecLin) =
        Fintype.card m + Fintype.card n := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card, Fintype.card_sum] using
      LinearMap.finrank_range_add_finrank_ker (fromBlocks A B Bᵀ C).mulVecLin
  have hrS : (C - Bᵀ * A⁻¹ * B).rank +
      finrank ℝ (LinearMap.ker (C - Bᵀ * A⁻¹ * B).mulVecLin) = Fintype.card n := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker (C - Bᵀ * A⁻¹ * B).mulVecLin
  have hrA := Matrix.rank_of_isUnit A hAu
  have hPA := inertiaPos_add_inertiaNeg_eq_rank hA
  have hPM := inertiaPos_add_inertiaNeg_eq_rank hM
  have hPS := inertiaPos_add_inertiaNeg_eq_rank hS
  omega

/-- Haynsworth inertia additivity gives the positive and negative counts,
the nullity identity, and the positive-definite Schur criterion.
Horn--Johnson (2013), Exercise 4.5.P21. Nullity is stated as kernel dimension,
which counts zero eigenvalues for a real symmetric matrix.
atlas: haynsworth-inertia-additivity -/
theorem haynsworth_inertia_additivity {A : Matrix m m ℝ} {C : Matrix n n ℝ}
    (hA : A.IsHermitian) (hAu : IsUnit A) (hC : C.IsHermitian) (B : Matrix m n ℝ) :
    inertiaPos (fromBlocks A B Bᵀ C) = inertiaPos A + inertiaPos (C - Bᵀ * A⁻¹ * B) ∧
    inertiaNeg (fromBlocks A B Bᵀ C) = inertiaNeg A + inertiaNeg (C - Bᵀ * A⁻¹ * B) ∧
    finrank ℝ (LinearMap.ker (fromBlocks A B Bᵀ C).mulVecLin) =
      finrank ℝ (LinearMap.ker (C - Bᵀ * A⁻¹ * B).mulVecLin) ∧
    ((fromBlocks A B Bᵀ C).PosDef ↔ A.PosDef ∧ (C - Bᵀ * A⁻¹ * B).PosDef) :=
  ⟨inertiaPos_fromBlocks_eq_add_schur hA hAu hC B,
    inertiaNeg_fromBlocks_eq_add_schur hA hAu hC B,
    finrank_ker_fromBlocks_eq_schur hA hAu hC B,
    posDef_fromBlocks_iff_posDef_schur hA hAu B C⟩

end NLAlib
