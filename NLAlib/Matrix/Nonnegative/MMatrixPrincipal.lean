import NLAlib.Matrix.Nonnegative.MMatrixBasic

/-! # Principal closure of nonsingular M-matrices

Deleting off-diagonal nonpositive terms improves a positive-vector certificate.
This gives every principal submatrix, including empty selections, without an
irreducibility assumption. Source: Berman–Plemmons, Chapter 6.
-/

noncomputable section
open Matrix Finset
namespace Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Principal reindexing preserves the Z-matrix sign pattern. -/
theorem IsZMatrix.submatrix {A : Matrix ι ι ℝ} (hA : A.IsZMatrix)
    (e : κ → ι) (he : Function.Injective e) : (A.submatrix e e).IsZMatrix := by
  intro i j hij
  exact hA (e i) (e j) (fun h => hij (he h))

omit [DecidableEq κ] in
/-- A positive-vector certificate restricts to every principal submatrix.
The omitted nonpositive off-diagonal entries can only increase its image. -/
theorem IsZMatrix.positive_certificate_submatrix {A : Matrix ι ι ℝ} (hA : A.IsZMatrix)
    {x : ι → ℝ} (hx : ∀ i, 0 < x i) (hAx : ∀ i, 0 < (A *ᵥ x) i)
    (e : κ → ι) (he : Function.Injective e) :
    ∀ i, 0 < (A.submatrix e e *ᵥ (x ∘ e)) i := by
  classical
  intro i
  have hsum : (A *ᵥ x) (e i) ≤ (A.submatrix e e *ᵥ (x ∘ e)) i := by
    change (∑ j : ι, A (e i) j * x j) ≤ ∑ j : κ, A (e i) (e j) * x (e j)
    have himg : (∑ j ∈ Finset.univ.image e, A (e i) j * x j) =
        ∑ j : κ, A (e i) (e j) * x (e j) :=
      Finset.sum_image (fun j _ k _ h => he h)
    rw [← himg]
    have hh : (∑ j ∈ Finset.univ.image e, -(A (e i) j * x j)) ≤
        ∑ j : ι, -(A (e i) j * x j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j _ hj
      apply neg_nonneg.mpr
      apply mul_nonpos_of_nonpos_of_nonneg
      · apply hA
        intro hij
        exact hj (Finset.mem_image.mpr ⟨i, mem_univ i, hij⟩)
      · exact (hx j).le
    simpa only [Finset.sum_neg_distrib, neg_le_neg_iff] using hh
  exact (hAx (e i)).trans_le hsum

/-- Every principal submatrix of a nonsingular M-matrix is a nonsingular M-matrix.
The result includes arbitrary injective coordinate selections and empty selections.
Source: Berman–Plemmons, Chapter 6.
atlas: m-matrix-schur-complement (partial) -/
theorem IsNonsingularMMatrix.submatrix {A : Matrix ι ι ℝ} (hA : A.IsNonsingularMMatrix)
    (e : κ → ι) (he : Function.Injective e) :
    (A.submatrix e e).IsNonsingularMMatrix := by
  obtain ⟨x, hx, hAx⟩ := hA.exists_positive_certificate
  exact (hA.1.submatrix e he).isNonsingularMMatrix_of_positive_certificate
    (fun i => hx (e i)) (hA.1.positive_certificate_submatrix hx hAx e he)

end Matrix
