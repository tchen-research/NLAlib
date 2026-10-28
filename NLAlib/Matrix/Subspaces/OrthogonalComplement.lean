import NLAlib.Matrix.Subspaces.OrthogonalProducts

/-!
# A unitary complement with all block identities

The existing native unitary complement supplies a projector decomposition.
Multiplication by the two frame factors also gives their mutual orthogonality.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Every orthonormal frame has an orthonormal, mutually orthogonal complement
whose projector completes the identity. Empty complements are included. -/
theorem exists_unitary_complement_orthogonal
    {𝕜 m q : Type*} [RCLike 𝕜] [Fintype m] [Fintype q] [DecidableEq m] [DecidableEq q]
    (E : Matrix m q 𝕜) (hE : HasOrthonormalCols E) :
    ∃ V : Matrix m (Fin (Fintype.card m-Fintype.card q)) 𝕜,
      HasOrthonormalCols V ∧ Eᴴ*V=0 ∧ E*Eᴴ+V*Vᴴ=1 := by
  obtain ⟨V,hV,hcomp⟩ := exists_unitary_complement E hE
  have hVV : V*Vᴴ=1-E*Eᴴ := by rw [← hcomp]; abel
  refine ⟨V,hV,?_,hcomp⟩
  calc
    Eᴴ*V = Eᴴ*(V*Vᴴ)*V := by
      simp only [Matrix.mul_assoc]
      rw [hV.conjTranspose_mul_self,Matrix.mul_one]
    _ = Eᴴ*(1-E*Eᴴ)*V := by rw [hVV]
    _ = 0 := by
      rw [Matrix.mul_sub,Matrix.mul_one,← Matrix.mul_assoc Eᴴ E Eᴴ,
        hE.conjTranspose_mul_self,Matrix.one_mul,sub_self,Matrix.zero_mul]

end NLAlib
