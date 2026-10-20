import NLAlib.Matrix.Spectral.HermitianExtremaNorm

/-! # Spectral norm bounded by the real trace for complex PSD matrices

Nonnegative spectral coordinates give the bound, including empty dimension.
-/

noncomputable section
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- A complex positive semidefinite matrix has spectral norm at most its
ordinary real trace. No nonempty-dimension assumption is needed. -/
theorem PosSemidef.specNorm_le_re_trace {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    NLAlib.specNorm A ≤ A.trace.re := by
  have he : A.trace.re=∑ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    simp
  rw [hA.isHermitian.specNorm_eq_norm_eigenvalues,he]
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => hA.eigenvalues_nonneg i)).mpr
  intro i
  rw [Real.norm_eq_abs,abs_of_nonneg (hA.eigenvalues_nonneg i)]
  exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)

end Matrix
