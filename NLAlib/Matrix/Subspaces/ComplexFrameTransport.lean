import NLAlib.Matrix.Spectral.ComplexSingularTransport
import NLAlib.Matrix.Subspaces.ObliqueFrameInverse
import NLAlib.Matrix.Subspaces.PrincipalAngles
/-!
# Complexifying real range frames and applying unitary similarities

Exact range identities and frame overlaps are preserved by complexification
and common unitary coordinate changes, without changing frame dimensions.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- Equality of real Euclidean column ranges implies equality of the
ordinary coordinate column ranges. Horn–Johnson 2013, Section 2.1;
inverse direction of the existing range-frame bridge. -/
theorem range_mulVecLin_eq_of_range_toEuclideanLin_eq {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℝ) (B : Matrix m p ℝ)
    (h : LinearMap.range A.toEuclideanLin = LinearMap.range B.toEuclideanLin) :
    LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := h.le (show A.toEuclideanLin (WithLp.toLp 2 v) ∈
      LinearMap.range A.toEuclideanLin from ⟨_, rfl⟩)
    exact ⟨w.ofLp, congrArg WithLp.ofLp hw⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := h.ge (show B.toEuclideanLin (WithLp.toLp 2 v) ∈
      LinearMap.range B.toEuclideanLin from ⟨_, rfl⟩)
    exact ⟨w.ofLp, congrArg WithLp.ofLp hw⟩

/-- The range of a complex matrix product is contained in the left
matrix's range. Horn–Johnson 2013, Section 1.1; frame transport helper. -/
theorem range_toEuclideanLin_mul_le_complex {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    LinearMap.range (A * B).toEuclideanLin ≤ LinearMap.range A.toEuclideanLin := by
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
  exact LinearMap.range_comp_le_range _ _

/-- Equal real frame ranges remain equal after complexification. The
complex span gains no unintended directions relative to the complexified
target range. Horn–Johnson 2013, Section 2.1; complex oblique frame helper. -/
theorem range_toEuclideanLin_map_ofReal_eq {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℝ) (B : Matrix m p ℝ)
    (h : LinearMap.range A.toEuclideanLin = LinearMap.range B.toEuclideanLin) :
    LinearMap.range (A.map Complex.ofReal).toEuclideanLin =
      LinearMap.range (B.map Complex.ofReal).toEuclideanLin := by
  have hr := range_mulVecLin_eq_of_range_toEuclideanLin_eq A B h
  obtain ⟨F, hF⟩ := exists_eq_mul_of_range_le hr.le
  obtain ⟨G, hG⟩ := exists_eq_mul_of_range_le hr.ge
  apply le_antisymm
  · rw [hF, map_ofReal_mul]
    exact range_toEuclideanLin_mul_le_complex _ _
  · rw [hG, map_ofReal_mul]
    exact range_toEuclideanLin_mul_le_complex _ _

/-- A unitary similarity carries any exact range frame to an exact range
frame of the conjugated matrix. Horn–Johnson 2013, Section 2.1;
complex oblique projection helper. -/
theorem range_unitary_mul_eq_of_similarity {n r : Type*}
    [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]
    (U : Matrix.unitaryGroup n ℂ) (P R : Matrix n n ℂ) (Q : Matrix n r ℂ)
    (hP : P = (U : Matrix n n ℂ) * R * (U : Matrix n n ℂ)ᴴ)
    (hQ : LinearMap.range Q.toEuclideanLin = LinearMap.range R.toEuclideanLin) :
    LinearMap.range ((U : Matrix n n ℂ) * Q).toEuclideanLin = LinearMap.range P.toEuclideanLin := by
  have hU : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  have hsurj : Function.Surjective (U : Matrix n n ℂ)ᴴ.toEuclideanLin := by
    intro x
    refine ⟨(U : Matrix n n ℂ).toEuclideanLin x, ?_⟩
    have h := congrArg (fun M : Matrix n n ℂ => M.toEuclideanLin x) hU
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, Matrix.toLpLin_one,
      LinearMap.comp_apply, LinearMap.id_apply] using h
  have hright : LinearMap.range (((U : Matrix n n ℂ) * R) * (U : Matrix n n ℂ)ᴴ).toEuclideanLin =
      LinearMap.range ((U : Matrix n n ℂ) * R).toEuclideanLin := by
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
    exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)
  rw [hP, hright]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.range_comp] at hQ ⊢
  rw [hQ]

end NLAlib
