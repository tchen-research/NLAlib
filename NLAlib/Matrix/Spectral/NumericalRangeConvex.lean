import NLAlib.Matrix.Spectral.NumericalRangeTwo
import NLAlib.Matrix.Spectral.NumericalRangeNormal
import NLAlib.Matrix.Subspaces.OrthonormalBasisMatrix

/-!
# Toeplitz–Hausdorff convexity

The span of two unit vectors has complex dimension at most two. Compressing
to an orthonormal basis of that span reduces every proposed numerical-range
segment to the two-dimensional convexity theorem. Empty matrices are included.
Source: Horn–Johnson (1991), Chapter 1; operator derivations, Section 8.
Atlas: `field-of-values-def`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

private theorem convex_numericalRange_fin_le_two {d : ℕ} (hd : d ≤ 2)
    (B : Matrix (Fin d) (Fin d) ℂ) : Convex ℝ (numericalRange B) := by
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · have hnormal : B * Bᴴ = Bᴴ * B := Subsingleton.elim _ _
    rw [numericalRange_eq_convexHull_spectrum_of_normal B hnormal]
    exact convex_convexHull _ _
  · have hnormal : B * Bᴴ = Bᴴ * B := by
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply]
      ring
    rw [numericalRange_eq_convexHull_spectrum_of_normal B hnormal]
    exact convex_convexHull _ _
  · exact convex_numericalRange_two B

/-- The numerical range of every finite complex matrix is convex
(Toeplitz–Hausdorff), including empty matrices. The proof compresses any two
unit-vector witnesses to their span and invokes the two-dimensional theorem.
Source: Horn–Johnson (1991), Chapter 1; operator derivations, Section 8.
atlas: field-of-values-def (partial) -/
theorem convex_numericalRange {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : Convex ℝ (numericalRange A) := by
  classical
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  obtain ⟨x, hx, hqx⟩ := hz₁
  obtain ⟨y, hy, hqy⟩ := hz₂
  let S := Submodule.span ℂ ({x, y} : Set (n → ℂ))
  let : Fintype ({x, y} : Set (n → ℂ)) := Fintype.ofFinite _
  have hd : Module.finrank ℂ S ≤ 2 := by
    have h := finrank_span_le_card (R := ℂ) ({x, y} : Set (n → ℂ))
    have hcard : ({x, y} : Set (n → ℂ)).toFinset.card ≤ 2 := by
      simp only [Set.toFinset_insert, Set.toFinset_singleton]
      exact (Finset.card_insert_le _ _).trans (by simp)
    exact h.trans hcard
  let Q := orthonormalBasisMatrix S
  have hQ : HasOrthonormalCols Q := hasOrthonormalCols_orthonormalBasisMatrix S
  have hQS : LinearMap.range Q.mulVecLin = S := range_orthonormalBasisMatrix S
  have hxS : x ∈ S := Submodule.subset_span (by simp)
  have hyS : y ∈ S := Submodule.subset_span (by simp)
  rw [← hQS] at hxS hyS
  obtain ⟨u, hu⟩ := hxS
  obtain ⟨v, hv⟩ := hyS
  change Q *ᵥ u = x at hu
  change Q *ᵥ v = y at hv
  have huNorm : ‖WithLp.toLp 2 u‖ = 1 := by
    rw [← norm_toLp_mulVec_of_hasOrthonormalCols hQ, hu, hx]
  have hvNorm : ‖WithLp.toLp 2 v‖ = 1 := by
    rw [← norm_toLp_mulVec_of_hasOrthonormalCols hQ, hv, hy]
  have hzu : z₁ ∈ numericalRange (Qᴴ * A * Q) := by
    refine ⟨u, huNorm, ?_⟩
    rw [quadForm_conjTranspose_mul_mul, hu, hqx]
  have hzv : z₂ ∈ numericalRange (Qᴴ * A * Q) := by
    refine ⟨v, hvNorm, ?_⟩
    rw [quadForm_conjTranspose_mul_mul, hv, hqy]
  have hC := (convex_numericalRange_fin_le_two hd (Qᴴ * A * Q)) hzu hzv ha hb hab
  exact numericalRange_conjTranspose_mul_mul_subset hQ A hC

end NLAlib
