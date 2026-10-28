import NLAlib.Matrix.Subspaces.Projections

/-!
# Unitary actions on an orthogonal complementary block

An arbitrary unitary on the complementary coordinates lifts to a genuine
ambient unitary fixing the retained coordinates pointwise.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {K n r q : Type*} [RCLike K] [Fintype n] [Fintype r] [Fintype q]
  [DecidableEq n] [DecidableEq r] [DecidableEq q]

/-- The ambient lift of the adjoint complementary-coordinate action. -/
def blockUnitaryAction (U : Matrix n r K) (V : Matrix n q K) (W : Matrix.unitaryGroup q K) :
    Matrix n n K := U*Uᴴ+V*(W : Matrix q q K)ᴴ*Vᴴ

omit [Fintype r] [Fintype q] [DecidableEq n] [DecidableEq r] [DecidableEq q] in
private theorem orthogonal_complement_conjTranspose {U : Matrix n r K} {V : Matrix n q K}
    (hUV : Uᴴ*V=0) : Vᴴ*U=0 := by
  have h := congrArg Matrix.conjTranspose hUV
  simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.conjTranspose_zero] using h

/-- The lifted action is a genuine ambient unitary. -/
theorem hasOrthonormalCols_blockUnitaryAction
    (U : Matrix n r K) (V : Matrix n q K) (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) (hUV : Uᴴ*V=0) (hcomp : U*Uᴴ+V*Vᴴ=1)
    (W : Matrix.unitaryGroup q K) : HasOrthonormalCols (blockUnitaryAction U V W) := by
  have hVU := orthogonal_complement_conjTranspose hUV
  have hWW : (W : Matrix q q K)*(W : Matrix q q K)ᴴ=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self W
  have h₁ : (U*Uᴴ)*(U*Uᴴ)=U*Uᴴ := by
    calc
      _ = U*(Uᴴ*U)*Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU,Matrix.mul_one]
  have h₂ : (U*Uᴴ)*(V*(W : Matrix q q K)ᴴ*Vᴴ)=0 := by
    calc
      _ = U*(Uᴴ*V)*(W : Matrix q q K)ᴴ*Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUV];simp
  have h₃ : (V*(W : Matrix q q K)*Vᴴ)*(U*Uᴴ)=0 := by
    calc
      _ = V*(W : Matrix q q K)*(Vᴴ*U)*Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hVU];simp
  have h₄ : (V*(W : Matrix q q K)*Vᴴ)*(V*(W : Matrix q q K)ᴴ*Vᴴ)=V*Vᴴ := by
    calc
      _ = V*(W : Matrix q q K)*(Vᴴ*V)*(W : Matrix q q K)ᴴ*Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hV,Matrix.mul_one]
        rw [Matrix.mul_assoc V,hWW,Matrix.mul_one]
  have hstar : (blockUnitaryAction U V W)ᴴ = U*Uᴴ+V*(W : Matrix q q K)*Vᴴ := by
    simp only [blockUnitaryAction,Matrix.conjTranspose_add,Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  unfold HasOrthonormalCols
  rw [hstar,blockUnitaryAction,Matrix.add_mul,Matrix.mul_add,Matrix.mul_add,
    h₁,h₂,h₃,h₄,add_zero,zero_add,hcomp]

omit [DecidableEq n] in
/-- The adjoint ambient action fixes every retained frame vector. -/
theorem blockUnitaryAction_conjTranspose_mul_left
    (U : Matrix n r K) (V : Matrix n q K) (hU : HasOrthonormalCols U) (hUV : Uᴴ*V=0)
    (W : Matrix.unitaryGroup q K) : (blockUnitaryAction U V W)ᴴ*U=U := by
  have hVU := orthogonal_complement_conjTranspose hUV
  unfold blockUnitaryAction
  simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.add_mul]
  calc
    _ = U*(Uᴴ*U)+V*(W : Matrix q q K)*(Vᴴ*U) := by simp only [Matrix.mul_assoc]
    _ = U := by rw [hU,hVU];simp

omit [DecidableEq n] [DecidableEq r] in
/-- On the complementary frame, the adjoint action is the requested right unitary. -/
theorem blockUnitaryAction_conjTranspose_mul_right
    (U : Matrix n r K) (V : Matrix n q K) (hV : HasOrthonormalCols V) (hUV : Uᴴ*V=0)
    (W : Matrix.unitaryGroup q K) : (blockUnitaryAction U V W)ᴴ*V=V*(W : Matrix q q K) := by
  unfold blockUnitaryAction
  simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.add_mul]
  calc
    _ = U*(Uᴴ*V)+V*(W : Matrix q q K)*(Vᴴ*V) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hUV,hV];simp

end NLAlib
