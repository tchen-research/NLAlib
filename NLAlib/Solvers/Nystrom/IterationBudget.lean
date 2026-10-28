import NLAlib.Solvers.Nystrom.Convergence

/-!
# Logarithmic iteration budget for Nyström PCG

All constants below are independent of the input matrix. On the native
constant-probability residual event, the stated number of PCG iterations
reduces squared energy error by the requested squared relative tolerance.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- The universal FTU factor is nonnegative. -/
theorem nystromPCGRate_nonneg : 0 ≤ nystromPCGRate := by
  have h : 1 ≤ Real.sqrt 56 := by
    have hh := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 56 by norm_num)
    rw [Real.sqrt_one] at hh
    exact hh
  unfold nystromPCGRate
  exact div_nonneg (sub_nonneg.mpr h) (by positivity)

/-- The explicit universal factor is strictly below `0.77`. -/
theorem nystromPCGRate_lt_seventySeven_div_hundred : nystromPCGRate < 77/100 := by
  unfold nystromPCGRate
  apply (div_lt_iff₀ (by positivity : 0 < Real.sqrt 56+1)).mpr
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 56)
  have h0 := Real.sqrt_nonneg (56:ℝ)
  nlinarith

/-- A matrix-independent iteration count for relative energy tolerance `ε`. -/
def nystromPCGIterations (ε : ℝ) : ℕ :=
  ⌈Real.log (2/ε) / Real.log (100/77)⌉₊

/-- The rounded logarithmic count meets its real budget. -/
theorem log_div_le_nystromPCGIterations (ε : ℝ) :
    Real.log (2/ε) / Real.log (100/77) ≤ nystromPCGIterations ε := Nat.le_ceil _

/-- The iteration count is at most its logarithmic budget plus one for
relative tolerances at most one. -/
theorem nystromPCGIterations_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (nystromPCGIterations ε : ℝ) ≤ Real.log (2/ε) / Real.log (100/77) + 1 := by
  unfold nystromPCGIterations
  apply (Nat.ceil_lt_add_one _).le
  apply div_nonneg
  · apply Real.log_nonneg
    exact (le_div_iff₀ hε).mpr (by linarith)
  · exact (Real.log_pos (by norm_num : (1:ℝ) < 100/77)).le

/-- The universal PCG energy factor meets the requested squared tolerance
after the stated logarithmic number of steps. -/
theorem nystromPCGRate_pow_le_sq {ε : ℝ} (hε : 0 < ε) {q : ℕ}
    (hq : nystromPCGIterations ε ≤ q) : (2*nystromPCGRate^q)^2 ≤ ε^2 := by
  have hc : 0 < Real.log (100/77) := Real.log_pos (by norm_num)
  have hlog : Real.log (2/ε) ≤ (q:ℝ)*Real.log (100/77) := by
    apply (div_le_iff₀ hc).mp
    exact (log_div_le_nystromPCGIterations ε).trans (by exact_mod_cast hq)
  have heq : (77/100:ℝ)^q = Real.exp (-((q:ℝ)*Real.log (100/77))) := by
    rw [show -((q:ℝ)*Real.log (100/77)) = (q:ℝ)*(-Real.log (100/77)) by ring,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 100/77)]
    norm_num
  have hex := Real.exp_le_exp.mpr (neg_le_neg hlog)
  rw [← heq, Real.exp_neg, Real.exp_log (div_pos (by norm_num) hε)] at hex
  have hinv : (2/ε)⁻¹ = ε/2 := by field_simp
  rw [hinv] at hex
  have hp := pow_le_pow_left₀ nystromPCGRate_nonneg
    nystromPCGRate_lt_seventySeven_div_hundred.le q
  have hu : 2*nystromPCGRate^q ≤ ε := by linarith
  exact pow_le_pow_left₀ (mul_nonneg (by norm_num) (pow_nonneg nystromPCGRate_nonneg q)) hu 2

open scoped Matrix.Norms.L2Operator in
/-- The native FTU-preconditioned PCG iterate meets relative energy tolerance
after a number of steps logarithmic in its reciprocal, on the previously
proved constant-probability residual event.
atlas: nystrom-pcg -/
theorem quadForm_sub_le_sq_mul_of_isPCGIterate_nystrom_rounded
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {μ : ℝ} (hμ : 0 < μ)
    (Ω : Matrix (Fin n) (Fin (nystromSketchWidth A μ)) ℝ)
    (hE : specNorm (A-nystrom A Ω) ≤ 54*μ)
    {ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : nystromPCGIterations ε ≤ q)
    {c x₀ xs x : Fin n → ℝ} (hxs : (A+μ•1)*ᵥxs=c)
    (hx : IsPCGIterate (A+μ•1)
      (nystromPreconditioner (nystrom A Ω) (nystromFloor A Ω) μ) c x₀ q x) :
    quadForm (A+μ•1) (x-xs) ≤ ε^2 * quadForm (A+μ•1) (x₀-xs) := by
  have h := quadForm_sub_le_of_isPCGIterate_nystrom_rounded hA hμ Ω hE hxs hx
  exact h.trans (mul_le_mul_of_nonneg_right (nystromPCGRate_pow_le_sq hε hq)
    ((hA.add (Matrix.PosSemidef.one.smul hμ.le)).quadForm_nonneg (x₀-xs)))

end NLAlib
