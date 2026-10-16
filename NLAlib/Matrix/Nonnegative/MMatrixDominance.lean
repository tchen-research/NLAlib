import NLAlib.Matrix.Nonnegative.MMatrixBasic
import NLAlib.Matrix.Spectral.GershgorinBasic

/-! # Positive diagonal scalings of Z-matrices

A positive-vector certificate is exactly strict row diagonal dominance,
with positive diagonal, after right scaling by that vector.
Source: Berman–Plemmons, Nonnegative Matrices, Chapter 6.
-/
noncomputable section
open Matrix Finset
open scoped Matrix
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Z-matrix has positive image of a positive vector exactly when its
right diagonal scaling has positive diagonal and strict absolute row dominance.
Source: Berman–Plemmons, Chapter 6.
atlas: nonsingular-m-matrix-characterizations (partial) -/
theorem IsZMatrix.mulVec_pos_iff_right_diagonal_strict_dominance
    {A : Matrix ι ι ℝ} (hA : A.IsZMatrix) {x : ι → ℝ} (hx : ∀ i, 0 < x i) :
    (∀ i, 0 < (A *ᵥ x) i) ↔
      ∀ i, 0 < (A * Matrix.diagonal x) i i ∧
        NLAlib.gershgorinRowRadius (A * Matrix.diagonal x) i < (A * Matrix.diagonal x) i i := by
  have he (i : ι) : (A *ᵥ x) i = (A * Matrix.diagonal x) i i -
      NLAlib.gershgorinRowRadius (A * Matrix.diagonal x) i := by
    have hsum : (∑ j ∈ Finset.univ.erase i, A i j * x j) + A i i * x i = (A *ᵥ x) i :=
      Finset.sum_erase_add _ _ (mem_univ i)
    have habs : NLAlib.gershgorinRowRadius (A * Matrix.diagonal x) i =
        -(∑ j ∈ Finset.univ.erase i, A i j * x j) := by
      unfold NLAlib.gershgorinRowRadius
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Matrix.mul_diagonal, Real.norm_eq_abs,
        abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg
          (hA i j (Finset.mem_erase.mp hj).1.symm) (hx j).le)]
    rw [habs, Matrix.mul_diagonal]
    linarith
  constructor
  · intro hpos i
    have hr := NLAlib.gershgorinRowRadius_nonneg (A * Matrix.diagonal x) i
    have hpi := hpos i
    rw [he i] at hpi
    exact ⟨by linarith, by linarith⟩
  · intro hdom i
    rw [he i]
    exact sub_pos.mpr (hdom i).2

end Matrix
