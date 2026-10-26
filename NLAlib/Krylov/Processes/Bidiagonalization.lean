import NLAlib.Krylov.Processes.GolubKahanBases
import NLAlib.Krylov.Spaces.Dilation

/-!
# Realization and breakdown of Golub--Kahan bidiagonalization

The structures, recurrence and decomposition facts are in `BidiagonalizationBasic`.
This file connects the actual recurrence to its graded bases and proves its exact
breakdown criterion. The proof alternates the two coordinate blocks of the native
Lanczos recurrence on the symmetric dilation.
Source: Golub--Van Loan (2013), Section 10.4.1; Paige--Saunders (1982), Section 3.
-/

noncomputable section
open scoped Matrix
open Matrix
namespace NLAlib
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- If the recursion succeeds through state `k`, its left and right vectors are
respective graded orthonormal Krylov bases. This follows by restricting the Lanczos
basis of the symmetric dilation to the even and odd vectors.
Source: Golub--Van Loan (2013) [`gvl13`], Section 10.4.1; Paige--Saunders (1982), Section 3.
atlas: golub-kahan-recurrence (partial)
atlas: golub-kahan-bidiagonalization (partial) -/
theorem isGradedKrylovBasis_golubKahanU_V {A : Matrix m n ℝ} {b : m → ℝ} {k : ℕ}
    (h : GolubKahanSucceeds A b k) :
    IsGradedKrylovBasis (A * Aᵀ) b (golubKahanU A b (k + 1)) ∧
      IsGradedKrylovBasis (Aᵀ * A) (Aᵀ *ᵥ b) (golubKahanV A b (k + 1)) :=
  isGradedKrylovBasis_golubKahan_of_dilationGrade
    (two_mul_le_dilationGrade_of_golubKahanSucceeds h)

/-- The recursion succeeds through state `k` exactly when both normal-matrix
Krylov grades are at least `k + 1`. In particular, `b = 0` and `Aᵀb = 0` fail at
initialization. The converse uses the two independent power families in the disjoint
coordinate blocks of the dilation, followed by native Lanczos breakdown.
Source: Golub--Van Loan (2013) [`gvl13`], Section 10.4.1; Paige--Saunders (1982), Section 3.
atlas: golub-kahan-recurrence (partial) -/
theorem golubKahanSucceeds_iff (A : Matrix m n ℝ) (b : m → ℝ) (k : ℕ) :
    GolubKahanSucceeds A b k ↔
      k + 1 ≤ krylovGrade (A * Aᵀ) b ∧ k + 1 ≤ krylovGrade (Aᵀ * A) (Aᵀ *ᵥ b) := by
  constructor
  · intro h
    exact ⟨(isGradedKrylovBasis_golubKahanU_V h).1.le_krylovGrade,
      (isGradedKrylovBasis_golubKahanU_V h).2.le_krylovGrade⟩
  · rintro ⟨hu, hv⟩ j hj
    have hg := two_mul_le_krylovGrade_dilation hu hv
    constructor
    · rw [← lanczosBeta_dilation_odd]
      exact (lanczosBeta_pos (isHermitian_dilation A) _ (by omega) (by omega)).ne'
    · cases j with
      | zero =>
        have hb : b ≠ 0 := by
          intro hb
          have hz := (krylovGrade_eq_zero_iff (A * Aᵀ) b).2 hb
          omega
        change √(b ⬝ᵥ b) ≠ 0
        rw [← norm_toLp_eq_sqrt_dotProduct_self]
        exact norm_ne_zero_iff.mpr (by simpa using hb)
      | succ j =>
        rw [← lanczosBeta_dilation_even_succ]
        exact (lanczosBeta_pos (isHermitian_dilation A) _ (by omega) (by omega)).ne'

omit [DecidableEq m] [DecidableEq n] in
/-- The compression has the recurrence's `alpha` on the diagonal and `beta` on
its first subdiagonal. The underlying identities also hold after breakdown.
Source: Golub--Van Loan (2013) [`gvl13`], Algorithm 10.4.1 and equation (10.4.4).
atlas: golub-kahan-recurrence (partial) -/
theorem dotProduct_golubKahan_eq {A : Matrix m n ℝ} {b : m → ℝ} {k : ℕ}
    (_h : GolubKahanSucceeds A b k) :
    (∀ j ≤ k, (golubKahanRecurrence A b j).u ⬝ᵥ (A *ᵥ (golubKahanRecurrence A b j).v) =
      (golubKahanRecurrence A b j).alpha) ∧
    (∀ j < k, (golubKahanRecurrence A b (j + 1)).u ⬝ᵥ (A *ᵥ (golubKahanRecurrence A b j).v) =
      (golubKahanRecurrence A b (j + 1)).beta) :=
  ⟨fun j _ => dotProduct_golubKahan_eq_alpha A b j,
    fun j _ => dotProduct_golubKahan_eq_beta A b j⟩

end NLAlib
