import NLAlib.RandomMatrix.Haar.UnitaryFrameTransform
import NLAlib.Matrix.Subspaces.UnitaryCanonicalQR
import NLAlib.Matrix.Basic.InverseGramConjugation

/-!
# The actual leading Haar Gram inverse through canonical Gaussian QR

The inverse trace is exactly the dimension plus an independent-block squared
Frobenius term. The identity proves invertibility of the normalized leading
Gram from native full rank of the original Gaussian block.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable (𝕜 : Type*) [RCLike 𝕜]

/-- The actual QR frame's leading Gram inverse has the exact source block
representation, with no matrix-Beta distribution premise. -/
theorem re_trace_inv_leadingGram_unitaryQRFrame_eq {n r ell s : ℕ}
    (hrn : r ≤ n) (helln : ell ≤ n) (V : Matrix (Fin n) (Fin s) 𝕜)
    (hcomp : (coordinateUnitaryStiefel 𝕜 n ell helln).val*
      (coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ+V*Vᴴ=1)
    (G : Matrix (Fin n) (Fin r) 𝕜)
    (hG : LinearIndependent 𝕜 (unitaryQRColumnFamily 𝕜 G))
    (hY : IsUnit (((coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ*G)ᴴ*
      ((coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ*G))) :
    RCLike.re (Matrix.trace (unitaryFrameLeadingGram 𝕜 helln
      (unitaryQRFrame 𝕜 n r hrn G))⁻¹) =
      (r:ℝ)+frobSq ((Vᴴ*G)*(pinvR (((coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ*G)ᴴ))ᴴ) ∧
    IsUnit (unitaryFrameLeadingGram 𝕜 helln (unitaryQRFrame 𝕜 n r hrn G)) := by
  let E := (coordinateUnitaryStiefel 𝕜 n ell helln).val
  let Q := (unitaryQRFrame 𝕜 n r hrn G).val
  let R := unitaryQRUpper 𝕜 hrn G
  let Y := Eᴴ*G
  let Z := Vᴴ*G
  let T := Eᴴ*Q
  have hR : IsUnit R := isUnit_unitaryQRUpper 𝕜 hrn G hG
  have hQR : Q*R=G := unitaryQRFrame_mul_unitaryQRUpper 𝕜 hrn G hG
  have hTY : T*R=Y := by
    change (Eᴴ*Q)*R=Eᴴ*G
    rw [Matrix.mul_assoc,hQR]
  have hGram : Rᴴ*R=Yᴴ*Y+Zᴴ*Z := by
    rw [conjTranspose_unitaryQRUpper_mul_self 𝕜 hrn G hG]
    calc
      Gᴴ*G = Gᴴ*(E*Eᴴ+V*Vᴴ)*G := by rw [hcomp,Matrix.mul_one]
      _ = Yᴴ*Y+Zᴴ*Z := by
        dsimp only [Y,Z]
        rw [Matrix.mul_add,Matrix.add_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose,Matrix.conjTranspose_conjTranspose]
        simp only [Matrix.mul_assoc]
  have htrace := trace_inv_gram_of_mul_right_eq T Y Z R hR hY hTY hGram
  have hcross := frobSq_mul_pinvR_adjoint_eq_re_trace Yᴴ Z
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hY)
  simp only [Matrix.conjTranspose_conjTranspose] at hcross
  constructor
  · change RCLike.re (Matrix.trace (Tᴴ*T)⁻¹) = _
    rw [htrace,map_add]
    simp only [Fintype.card_fin,RCLike.natCast_re]
    rw [← hcross]
  · exact (inv_gram_of_mul_right_eq T Y R hR hY hTY).2

end NLAlib
