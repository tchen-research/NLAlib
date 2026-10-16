import NLAlib.Probability.Gaussian.Moments.HermiteExpansion
import NLAlib.Probability.Gaussian.Moments.HermiteRecurrence
import NLAlib.Matrix.Structured.HermiteLadders

/-! # Coordinate multiplication in the finite Hermite model

The literal finite creation-plus-annihilation matrix represents multiplication
by a Gaussian coordinate on vectors supported strictly below the cutoff.
The degree support is tracked explicitly before taking finite powers.
Supports `gaussian-series-partial-transpose-norm`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Finset
open scoped Matrix
namespace NLAlib
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

private theorem coordinate_hermite_column (i : ι) (b : HermiteIndex ι p)
    (hb : b.degree < p) (x : ι → ℝ) :
    (∑ a, (hermiteCreation p i + (hermiteCreation p i)ᴴ) a b *
      (productHermite a.val x : ℂ)) =
        (x i : ℂ) * (productHermite b.val x : ℂ) := by
  simp only [Matrix.add_apply, Matrix.conjTranspose_apply]
  simp_rw [hermiteCreation_apply_of_lt i _ b hb]
  simp_rw [hermiteCreation_apply i b]
  simp only [add_mul, Finset.sum_add_distrib]
  have hh := congrArg Complex.ofReal (coordinate_mul_productHermite b i hb x)
  by_cases hbi : 0 < b.val i
  · simp only [hbi, true_and, ↓reduceIte] at *
    simpa [apply_ite, mul_ite, ite_mul, eq_comm] using hh.symm
  · simp only [hbi, false_and, ↓reduceIte, star_zero, zero_mul,
      Finset.sum_const_zero, add_zero] at *
    simpa [ite_mul] using hh.symm

/-- The finite Hermite coordinate operator realizes actual coordinate
multiplication for every vector supported below the cutoff. -/
theorem hermiteExpansion_creation_add_conjTranspose_mulVec
    (i : ι) (z : HermiteIndex ι p → ℂ)
    (hz : ∀ a, ¬ a.degree < p → z a = 0) (x : ι → ℝ) :
    hermiteExpansion ((hermiteCreation p i + (hermiteCreation p i)ᴴ) *ᵥ z) x =
      (x i : ℂ) * hermiteExpansion z x := by
  simp only [hermiteExpansion, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ b, z b * ∑ a,
        (hermiteCreation p i + (hermiteCreation p i)ᴴ) a b *
          (productHermite a.val x : ℂ) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ b, z b * ((x i : ℂ) * (productHermite b.val x : ℂ)) := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : b.degree < p
      · rw [coordinate_hermite_column _ _ hb]
      · rw [hz b hb, zero_mul, zero_mul]
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

/-- Creation-plus-annihilation raises total degree support by at most one.
This is a statement about the literal finite matrices, including the cutoff. -/
theorem hermiteCreation_add_conjTranspose_mulVec_support (i : ι)
    (z : HermiteIndex ι p → ℂ) (k : ℕ)
    (hz : ∀ a, k < a.degree → z a = 0)
    (a : HermiteIndex ι p) (ha : k + 1 < a.degree) :
    ((hermiteCreation p i + (hermiteCreation p i)ᴴ) *ᵥ z) a = 0 := by
  simp only [Matrix.add_mulVec, Pi.add_apply, hermiteCreation_mulVec,
    hermiteCreation_conjTranspose_mulVec]
  have h₁ : (if 0 < a.val i then (Real.sqrt (a.val i) : ℂ) * z (a.lower i) else 0) = 0 := by
    split_ifs with hi
    · rw [hz _ (by have hd := a.degree_lower i hi; omega), mul_zero]
    · rfl
  have h₂ : (if h : a.degree < p then
      (Real.sqrt (a.val i + 1) : ℂ) * z (a.raise i h) else 0) = 0 := by
    split_ifs with hi
    · rw [hz _ (by rw [HermiteIndex.degree_raise]; omega), mul_zero]
    · rfl
  rw [h₁, h₂, add_zero]

end NLAlib
