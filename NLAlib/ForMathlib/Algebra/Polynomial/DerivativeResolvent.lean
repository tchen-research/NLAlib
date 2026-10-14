import Mathlib.Algebra.Polynomial.SumIteratedDerivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Finite polynomial derivative resolvents

For a nonzero scalar `a`, the inverse of `a I-D` on polynomials is a finite
weighted sum of derivatives. The coefficient support makes this a linear map.
Source: nilpotent finite geometric series; focused reciprocal exponential reroute.
-/

noncomputable section
open Finset
namespace Polynomial
variable {𝕜 : Type*} [Field 𝕜]

/-- The finite inverse of `a I-D`, expressed through the finite derivative
coefficient support. At zero scalar it is the total zero map. -/
def derivativeResolvent (a : 𝕜) : 𝕜[X] →ₗ[𝕜] 𝕜[X] :=
  Finsupp.lsum ℕ (fun k => (a⁻¹)^(k+1) • LinearMap.id) ∘ₗ derivativeFinsupp

/-- A degree bound turns the polynomial derivative resolvent into its finite sum. -/
theorem derivativeResolvent_apply_of_le {p : 𝕜[X]} {n : ℕ} (hn : p.natDegree ≤ n) (a : 𝕜) :
    derivativeResolvent a p = ∑ r ∈ range (n+1), (a⁻¹)^(r+1) • derivative^[r] p := by
  dsimp [derivativeResolvent]
  exact Finsupp.sum_of_support_subset _ (by simp [hn]) _ (by simp)

/-- The polynomial derivative resolvent is a finite sum through the actual degree. -/
theorem derivativeResolvent_apply (a : 𝕜) (p : 𝕜[X]) :
    derivativeResolvent a p =
      ∑ r ∈ range (p.natDegree+1), (a⁻¹)^(r+1) • derivative^[r] p :=
  derivativeResolvent_apply_of_le le_rfl a

/-- The polynomial derivative resolvent preserves every degree bound. -/
theorem natDegree_derivativeResolvent_le (a : 𝕜) (p : 𝕜[X]) :
    (derivativeResolvent a p).natDegree ≤ p.natDegree := by
  rw [derivativeResolvent_apply]
  apply (natDegree_sum_le _ _).trans
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun i _ => ?_⟩
  exact (natDegree_smul_le _ _).trans ((natDegree_iterate_derivative p i).trans (Nat.sub_le _ _))

/-- The finite resolvent is an exact right inverse of `a I-D`.
No characteristic-zero or infinite-series assumption is needed. -/
theorem sub_derivative_derivativeResolvent {a : 𝕜} (ha : a ≠ 0) (p : 𝕜[X]) :
    a • derivativeResolvent a p - (derivativeResolvent a p).derivative = p := by
  rw [derivativeResolvent_apply, smul_sum, derivative_sum]
  simp_rw [derivative_smul, ← Function.iterate_succ_apply']
  have hcoeff (r : ℕ) : a * (a⁻¹)^(r+1) = (a⁻¹)^r := by
    rw [pow_succ]
    calc
      a * ((a⁻¹)^r * a⁻¹) = (a⁻¹)^r * (a*a⁻¹) := by ring
      _ = (a⁻¹)^r := by rw [mul_inv_cancel₀ ha, mul_one]
  simp_rw [smul_smul, hcoeff]
  rw [sum_range_succ' (f := fun r => (a⁻¹)^r • derivative^[r] p)]
  simp only [pow_zero, Function.iterate_zero_apply, one_smul]
  rw [sum_range_succ]
  rw [iterate_derivative_eq_zero (Nat.lt_succ_self p.natDegree), smul_zero, add_zero]
  abel

/-- The derivative of the resolvent satisfies its exact polynomial ODE. -/
theorem derivative_derivativeResolvent {a : 𝕜} (ha : a ≠ 0) (p : 𝕜[X]) :
    (derivativeResolvent a p).derivative = a • derivativeResolvent a p - p := by
  have h := sub_derivative_derivativeResolvent ha p
  apply eq_sub_of_add_eq
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm

/-- At any upper degree bound, the coefficient of the resolvent is the
corresponding original coefficient divided by the resolvent scalar. -/
theorem coeff_derivativeResolvent_of_natDegree_le {a : 𝕜} (ha : a ≠ 0)
    {p : 𝕜[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    (derivativeResolvent a p).coeff n = p.coeff n / a := by
  have h := congrArg (fun q : 𝕜[X] => q.coeff n) (derivative_derivativeResolvent ha p)
  rw [coeff_derivative, coeff_sub, coeff_smul] at h
  rw [coeff_eq_zero_of_natDegree_lt
    ((natDegree_derivativeResolvent_le a p).trans_lt (hp.trans_lt (Nat.lt_succ_self n))),
    zero_mul, smul_eq_mul] at h
  apply (eq_div_iff ha).mpr
  rw [mul_comm]
  exact (sub_eq_zero.mp h.symm)

end Polynomial
