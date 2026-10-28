import NLAlib.Matrix.Spectral.NormalSpectral

/-! # Real scalar multiplication preserves matrix normality -/

namespace NLAlib
open scoped Matrix
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/-- A real multiple of a normal matrix commutes with its adjoint. -/
theorem normal_real_smul {A : Matrix n n 𝕜} (hA : A*Aᴴ=Aᴴ*A) (c : ℝ) :
    (c•A)*(c•A)ᴴ=(c•A)ᴴ*(c•A) := by
  simp only [Matrix.conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, hA]

end NLAlib
