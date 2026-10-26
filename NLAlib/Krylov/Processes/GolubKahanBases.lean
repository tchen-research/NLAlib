import NLAlib.Krylov.Processes.GolubKahanLanczos

/-!
# Graded bases produced by Golub--Kahan bidiagonalization

Krylov membership follows directly from the two recurrence equations. Orthonormality
follows by restricting the Lanczos basis of the symmetric dilation to its even and odd
columns. This uses the existing native recurrences, including their initialization.
Source: Golub--Van Loan (2013), Section 10.4.1; Paige--Saunders (1982), Section 3.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Both vectors of every Golub--Kahan state lie in their respective Krylov spaces.
This is true without a success hypothesis, including zero vectors after breakdown. -/
theorem golubKahanRecurrence_mem (A : Matrix m n ℝ) (b : m → ℝ) (j : ℕ) :
    (golubKahanRecurrence A b j).u ∈ krylovSpace (A * Aᵀ) b (j + 1) ∧
      (golubKahanRecurrence A b j).v ∈ krylovSpace (Aᵀ * A) (Aᵀ *ᵥ b) (j + 1) := by
  induction j with
  | zero =>
    have hu : (golubKahanInit A b).u ∈ krylovSpace (A * Aᵀ) b 1 :=
      Submodule.smul_mem _ _ (self_mem_krylovSpace_succ _ _ 0)
    exact ⟨hu, Submodule.smul_mem _ _ (transpose_mulVec_mem_krylovSpace A b hu)⟩
  | succ j ih =>
    have hu : (golubKahanStep A (golubKahanRecurrence A b j)).u ∈
        krylovSpace (A * Aᵀ) b (j + 1 + 1) := by
      apply Submodule.smul_mem
      exact Submodule.sub_mem _ (mulVec_mem_krylovSpace_mul_transpose A b ih.2)
        (Submodule.smul_mem _ _ (krylovSpace_mono _ _ (Nat.le_succ _) ih.1))
    have hv : (golubKahanStep A (golubKahanRecurrence A b j)).v ∈
        krylovSpace (Aᵀ * A) (Aᵀ *ᵥ b) (j + 1 + 1) := by
      apply Submodule.smul_mem
      exact Submodule.sub_mem _ (transpose_mulVec_mem_krylovSpace A b hu)
        (Submodule.smul_mem _ _ (krylovSpace_mono _ _ (Nat.le_succ _) ih.2))
    simpa only [golubKahanRecurrence, Function.iterate_succ_apply'] using And.intro hu hv

/-- A dilation Krylov grade of at least `2q` gives both graded Golub--Kahan bases of
width `q`. The case `q = 0` includes two empty frames. -/
theorem isGradedKrylovBasis_golubKahan_of_dilationGrade {A : Matrix m n ℝ} {b : m → ℝ}
    {q : ℕ} (hq : 2 * q ≤ krylovGrade (dilation A) (Sum.elim b (0 : n → ℝ))) :
    IsGradedKrylovBasis (A * Aᵀ) b (golubKahanU A b q) ∧
      IsGradedKrylovBasis (Aᵀ * A) (Aᵀ *ᵥ b) (golubKahanV A b q) := by
  constructor
  · apply IsGradedKrylovBasis.of_mem
    · change (golubKahanU A b q)ᴴ * golubKahanU A b q = 1
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j
      rw [transpose_mul_self_apply, Matrix.one_apply]
      have h := arnoldiBasis_dotProduct (dilation A) (Sum.elim b (0 : n → ℝ))
        (i := 2 * (i : ℕ)) (j := 2 * (j : ℕ)) (by omega) (by omega)
      rw [← lanczosRecurrence_eq_arnoldiBasis (isHermitian_dilation A),
        ← lanczosRecurrence_eq_arnoldiBasis (isHermitian_dilation A),
        lanczosRecurrence_dilation_even, lanczosRecurrence_dilation_even] at h
      have he : (2 * (i : ℕ) = 2 * (j : ℕ)) ↔ i = j := by
        constructor
        · intro hij; apply Fin.ext; omega
        · rintro rfl; rfl
      simpa only [golubKahanU, Matrix.col, Matrix.transpose_apply, Matrix.of_apply, dotProduct,
        Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
        mul_zero, Finset.sum_const_zero, add_zero, he] using h
    · intro j
      exact (golubKahanRecurrence_mem A b j).1
  · apply IsGradedKrylovBasis.of_mem
    · change (golubKahanV A b q)ᴴ * golubKahanV A b q = 1
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j
      rw [transpose_mul_self_apply, Matrix.one_apply]
      have h := arnoldiBasis_dotProduct (dilation A) (Sum.elim b (0 : n → ℝ))
        (i := 2 * (i : ℕ) + 1) (j := 2 * (j : ℕ) + 1) (by omega) (by omega)
      rw [← lanczosRecurrence_eq_arnoldiBasis (isHermitian_dilation A),
        ← lanczosRecurrence_eq_arnoldiBasis (isHermitian_dilation A),
        lanczosRecurrence_dilation_odd, lanczosRecurrence_dilation_odd] at h
      have he : (2 * (i : ℕ) + 1 = 2 * (j : ℕ) + 1) ↔ i = j := by
        constructor
        · intro hij; apply Fin.ext; omega
        · rintro rfl; rfl
      simpa only [golubKahanV, Matrix.col, Matrix.transpose_apply, Matrix.of_apply, dotProduct,
        Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
        zero_mul, Finset.sum_const_zero, zero_add, he] using h
    · intro j
      exact (golubKahanRecurrence_mem A b j).2

/-- A successful Golub--Kahan state forces the dilation grade past its last odd link. -/
theorem two_mul_le_dilationGrade_of_golubKahanSucceeds {A : Matrix m n ℝ} {b : m → ℝ} {k : ℕ}
    (h : GolubKahanSucceeds A b k) :
    2 * (k + 1) ≤ krylovGrade (dilation A) (Sum.elim b (0 : n → ℝ)) := by
  have hn := (h k le_rfl).1
  rw [← lanczosBeta_dilation_odd] at hn
  have hg := (lanczosBeta_eq_zero_iff (isHermitian_dilation A)
    (Sum.elim b (0 : n → ℝ)) (j := 2 * k + 1) (by omega)).not.mp hn
  omega

end NLAlib
