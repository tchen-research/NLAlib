import NLAlib.Matrix.Structured.CoefficientBlock

/-! # Genuine coefficient-frame bounds for matrix trace probes

The full entry covariance controls the sum of squared trace probes by the
actual Frobenius norm of the probe matrix. This deterministic frame estimate
is the coordinate-gradient step behind normalized GUE partial-trace decay.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- The squared coordinate-gradient frame is controlled by the true
unnormalized entry covariance and the squared Frobenius norm of its trace
probe. The coefficients need not be Hermitian. Empty families are included. -/
theorem sum_norm_trace_mul_sq_le_coefficientCovariance_mul_frobSq
    (A : ι → Matrix n n ℂ) (U : Matrix n n ℂ) :
    (∑ i, ‖(U*A i).trace‖^2) ≤ specNorm (coefficientCovariance A)*frobSq U := by
  let V : Matrix (n×n) ι ℂ := coefficientVectorization A
  let P : Matrix Unit (n×n) ℂ := fun _ ab => U ab.2 ab.1
  have he (i : ι) : (P*V) () i=(U*A i).trace := by
    change (∑ ab : n×n, U ab.2 ab.1*A i ab.1 ab.2)=_
    simp only [Fintype.sum_prod_type,Matrix.trace,Matrix.diag]
    exact Finset.sum_comm
  have hp : frobSq P=frobSq U := by
    rw [frobSq_eq_sum_norm_sq P,frobSq_eq_sum_norm_sq U]
    simp only [P,Fintype.sum_prod_type,Fintype.sum_unique]
    exact Finset.sum_comm
  have hprod : frobSq (P*V)=∑ i, ‖(U*A i).trace‖^2 := by
    simp only [frobSq_eq_sum_norm_sq,Fintype.sum_unique,he]
  have hv : specNorm V^2=specNorm (coefficientCovariance A) :=
    (specNorm_mul_conjTranspose_self V).symm
  have hh := frobSq_mul_le_frobSq_mul_specNorm_sq P V
  rw [hprod,hp,hv,mul_comm] at hh
  exact hh

end NLAlib
