import NLAlib.Matrix.Functions.KTransformCalculus

/-! # Native inverse-sandwich identities for the K kernel

Every matrix inverse below is justified by an actual unit. No
Hermitian or positivity assumption is needed for these algebraic
identities, so they also apply at nonnormal half-plane parameters.
-/

noncomputable section
set_option autoImplicit false
open Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- A genuine K denominator and a genuine matrix unit give the actual
inverse-variable denominator unit, without a positivity premise. -/
theorem isUnit_inverse_add_of_isUnit_matrixKDenominator
    (S T : M) (hS : IsUnit S) (hD : IsUnit (1+S*T)) : IsUnit (S⁻¹+T) := by
  have he : S⁻¹*(1+S*T)=S⁻¹+T := by
    rw [Matrix.mul_add,Matrix.mul_one,← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hS),Matrix.one_mul]
  rw [← he]
  exact (Matrix.isUnit_nonsing_inv_iff.mpr hS).mul hD

/-- The actual native K defect is exactly the inverse-variable
resolvent sandwich. Singular and indefinite samples are included;
only the genuinely used denominators must be units. -/
theorem matrixKResolvent_defect_eq_inverse_sandwich
    (S T : M) (hS : IsUnit S) (hD : IsUnit (1+S*T)) :
    T-matrixKResolvent S T=T*(S⁻¹+T)⁻¹*T := by
  have hleft : S⁻¹*(1+S*T)=S⁻¹+T := by
    rw [Matrix.mul_add,Matrix.mul_one,← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hS),Matrix.one_mul]
  have hInv : (S⁻¹+T)⁻¹=(1+S*T)⁻¹*S := by
    apply Matrix.inv_eq_right_inv
    calc
      _ = S⁻¹*(((1+S*T)*(1+S*T)⁻¹)*S) := by rw [← hleft]; noncomm_ring
      _ = 1 := by
        rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hD),Matrix.one_mul,
          Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hS)]
  have hcan : (1+S*T)⁻¹*(1+S*T)=1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  have he : T*(1+S*T)⁻¹*(S*T)=T-T*(1+S*T)⁻¹ := by
    have hh := congrArg (fun X : M => T*X) hcan
    exact eq_sub_iff_add_eq.mpr (by
      simpa only [Matrix.mul_add,Matrix.mul_one,Matrix.mul_assoc,add_comm] using hh)
  simpa only [matrixKResolvent,hInv,Matrix.mul_assoc] using he.symm

end NLAlib
