import NLAlib.RandomMatrix.Haar.UnitaryFrameMeasure

/-!
# Adjoint-frame transport of the actual Haar top-block Gram law

A top block of an `ell`-frame and a leading-row block of an `r`-frame have
the same Hermitian Gram distribution. This is an exact pushforward statement
for actual compact Haar probability, proved by inversion invariance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Measure
open scoped Matrix
namespace NLAlib
variable (𝕜 : Type*) [RCLike 𝕜]

/-- Normalized compact unitary Haar probability is inversion-invariant. -/
instance unitaryHaar_isInvInvariant (n : ℕ) : IsInvInvariant (unitaryHaar 𝕜 n) where
  inv_eq_self := by
    have : IsProbabilityMeasure ((unitaryHaar 𝕜 n).inv) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    have : IsHaarMeasure ((unitaryHaar 𝕜 n).inv) :=
      isHaarMeasure_of_isCompact_nonempty_interior _ Set.univ isCompact_univ
        (by simp) (by simp) (by simp)
    exact isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- Acting on any fixed frame by the Haar adjoint gives the actual frame law. -/
theorem unitaryHaar_map_inv_smul_eq_frameLaw {n k : ℕ} (hkn : k ≤ n)
    (Q : UnitaryStiefel 𝕜 n k) :
    (unitaryHaar 𝕜 n).map (fun O => O⁻¹ • Q) = unitaryHaarFrameLaw 𝕜 n k hkn := by
  have heq : (fun O : Matrix.unitaryGroup (Fin n) 𝕜 => O⁻¹ • Q) =
      (fun O => O • Q) ∘ Inv.inv := rfl
  rw [heq,← Measure.map_map (by fun_prop) (by fun_prop),map_inv_eq_self]
  exact unitaryHaar_map_smul_eq_frameLaw 𝕜 hkn Q

/-- The top `r`-row Gram matrix relative to an arbitrary fixed orthonormal frame. -/
def unitaryFrameTopGram {n r ell : ℕ} (U : Matrix (Fin n) (Fin r) 𝕜)
    (Q : UnitaryStiefel 𝕜 n ell) : Matrix (Fin r) (Fin r) 𝕜 :=
  (Uᴴ*Q.val)*(Uᴴ*Q.val)ᴴ

/-- The leading `ell` rows of an `r`-frame, expressed by the coordinate selector. -/
def unitaryFrameLeadingGram {n r ell : ℕ} (helln : ell ≤ n)
    (Q : UnitaryStiefel 𝕜 n r) : Matrix (Fin r) (Fin r) 𝕜 :=
  ((coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ*Q.val)ᴴ*
    ((coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ*Q.val)

/-- The actual Haar top-block Gram distribution equals the leading-row Gram
distribution of the complementary rectangular frame. No matrix-Beta law is
postulated and all `ell≤n`, including `ell=n`, are retained.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem unitaryHaarFrameLaw_map_topGram_eq {n r ell : ℕ} (hrn : r ≤ n) (helln : ell ≤ n)
    (U : Matrix (Fin n) (Fin r) 𝕜) (hU : HasOrthonormalCols U) :
    (unitaryHaarFrameLaw 𝕜 n ell helln).map (unitaryFrameTopGram 𝕜 U) =
      (unitaryHaarFrameLaw 𝕜 n r hrn).map (unitaryFrameLeadingGram 𝕜 helln) := by
  rw [← unitaryHaar_map_inv_smul_eq_frameLaw 𝕜 hrn (⟨U,hU⟩ : UnitaryStiefel 𝕜 n r)]
  unfold unitaryHaarFrameLaw
  rw [Measure.map_map (by unfold unitaryFrameTopGram; fun_prop) (by fun_prop),
    Measure.map_map (by unfold unitaryFrameLeadingGram; fun_prop) (by fun_prop)]
  congr 1
  funext O
  have hinv : (O⁻¹).val = O.valᴴ := rfl
  change (Uᴴ*(O.val*(coordinateUnitaryStiefel 𝕜 n ell helln).val))*
      (Uᴴ*(O.val*(coordinateUnitaryStiefel 𝕜 n ell helln).val))ᴴ =
    ((coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ*((O⁻¹).val*U))ᴴ*
      ((coordinateUnitaryStiefel 𝕜 n ell helln).valᴴ*((O⁻¹).val*U))
  rw [hinv]
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]

end NLAlib
