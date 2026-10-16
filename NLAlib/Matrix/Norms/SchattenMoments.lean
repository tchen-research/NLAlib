import NLAlib.Matrix.Norms.Schatten
import NLAlib.Matrix.Spectral.GramSpectralSums
import NLAlib.Matrix.Functions.CFCTrace

/-!
# Finite Schatten moments and absolute functional calculus

Every positive integer Schatten moment is the trace of the corresponding
absolute matrix power. In particular the third moment used by matrix
universality agrees with the native singular-value definition.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib
variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Every positive integer Schatten moment is a spectral trace of the
column Gram matrix. Zero singular values and empty shapes are included. -/
theorem schattenNormReal_pow_nat_eq_re_trace_cfc_gram (A : Matrix m n 𝕜)
    {k : ℕ} (hk : 0 < k) :
    schattenNormReal A (k : ℝ)^k =
      RCLike.re (cfc (fun x : ℝ => (Real.sqrt x)^k) (Aᴴ*A)).trace := by
  have hp : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : 0 ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      singularValues A i ^ (k : ℝ) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValues_nonneg A i) _
  rw [schattenNormReal,←Real.rpow_natCast,one_div,Real.rpow_inv_rpow hsum hp.ne',
    re_trace_cfc_eq_sum_eigenvalues (Matrix.isHermitian_conjTranspose_mul_self A),
    sum_eigenvalues_gram_eq_sum_singularValues A (fun x : ℝ => (Real.sqrt x)^k)]
  simp only [Real.sqrt_sq (singularValues_nonneg _ _),Real.rpow_natCast]
  symm
  exact sum_range_singularValues_map_eq_of_min_le A (fun x => x^k)
    (by simp [hk.ne']) (min_le_right _ _)

open scoped Matrix.Norms.L2Operator in
omit [Fintype m] [DecidableEq m] in
/-- For a Hermitian matrix, a positive integer Schatten moment is the trace
of its absolute-power functional calculus, over either real or complex scalars. -/
theorem schattenNormReal_pow_nat_eq_re_trace_cfc_abs {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : 0 < k) :
    schattenNormReal A (k : ℝ)^k =
      RCLike.re (cfc (fun x : ℝ => |x|^k) A).trace := by
  rw [schattenNormReal_pow_nat_eq_re_trace_cfc_gram A hk,hA.eq,←pow_two]
  have heq : cfc (fun x : ℝ => (Real.sqrt (x^2))^k) A =
      cfc (fun x : ℝ => (Real.sqrt x)^k) (A^2) :=
    cfc_comp_pow (fun x : ℝ => (Real.sqrt x)^k) 2 A (by fun_prop) hA
  calc
    _ = RCLike.re (cfc (fun x : ℝ => (Real.sqrt (x^2))^k) A).trace :=
      congrArg (fun B : Matrix n n 𝕜 => RCLike.re B.trace) heq.symm
    _ = _ := by simp only [Real.sqrt_sq_eq_abs]

end NLAlib
