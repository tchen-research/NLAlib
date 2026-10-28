/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Solvers.Nystrom.Preconditioner
import NLAlib.Matrix.Functions.GeometricMean
import NLAlib.Matrix.Functions.LoewnerHeinz
import NLAlib.Matrix.Perturbation.ConditionNumber
import NLAlib.Krylov.Solvers.Preconditioned

/-!
# Deterministic condition and PCG bounds for the FTU preconditioner

The actual symmetrically preconditioned matrix uses the positive inverse square root.
The Loewner sandwich for the spectral-floor preconditioner bounds its ordinary finite
condition number, including singular low-rank approximations.
Source: Frangella–Tropp–Udell 2023, Theorem 5.1; the PCG consumer is the native
Saad–Greenbaum energy-minimization theorem.
Atlas: `nystrom-pcg` (deterministic condition and iteration bounds).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix MatrixOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- The actual symmetric matrix `P^(-1/2)(A+μI)P^(-1/2)` for the FTU preconditioner. -/
def nystromPreconditionedMatrix (A B : Matrix n n ℝ) (a μ : ℝ) : Matrix n n ℝ :=
  let R := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) (nystromPreconditioner B a μ)
  R * (A + μ • 1) * R

open scoped Matrix.Norms.L2Operator in
private theorem conditionNumber_toReal_le_of_sandwich {M : Matrix n n ℝ} {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (hl : α • 1 ≤ M) (hu : M ≤ β • 1) :
    (conditionNumber M).toReal ≤ β / α := by
  have hM : M.PosDef := posDef_of_posDef_le (Matrix.PosDef.one.smul hα) hl
  have hn := (hM.posSemidef.specNorm_le_iff (hα.le.trans hαβ)).mpr hu
  have hi := inv_le_inv_of_posDef (Matrix.PosDef.one.smul hα) hl
  have hid : (α • (1 : Matrix n n ℝ))⁻¹ = α⁻¹ • 1 := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hα), one_smul]
  rw [hid] at hi
  have hni := (hM.inv.posSemidef.specNorm_le_iff (inv_nonneg.mpr hα.le)).mpr hi
  rw [conditionNumber_toReal_of_isUnit hM.isUnit, div_eq_mul_inv]
  exact mul_le_mul hn hni (specNorm_nonneg _) (hα.le.trans hαβ)

open scoped Matrix.Norms.L2Operator in
/-- **The FTU deterministic condition bound for the actual symmetric preconditioned matrix.**
No invertibility of the low-rank approximation is assumed. The preconditioner itself is SPD.
Source: Frangella–Tropp–Udell 2023, Theorem 5.1 proof.
atlas: nystrom-pcg (partial) -/
theorem conditionNumber_nystromPreconditionedMatrix_toReal_le {A B : Matrix n n ℝ}
    (hB : B.PosSemidef) (hBA : B ≤ A) {a μ : ℝ} (ha : 0 ≤ a) (hμ : 0 < μ) :
    (conditionNumber (nystromPreconditionedMatrix A B a μ)).toReal ≤
      1 + (a + specNorm (A - B)) / μ := by
  let P := nystromPreconditioner B a μ
  let R := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) P
  have hP : P.PosDef := nystromPreconditioner_posDef hB ha hμ
  have hR : R.IsHermitian := cfc_predicate _ _
  have hRPR : R * nystromPreconditioner B a μ * R = 1 := cfc_inv_sqrt_mul_self_mul_inv_sqrt hP
  have hs := nystromPreconditioner_sandwich hB hBA ha hμ
  have hl : μ • 1 ≤ R * (A + μ • 1) * R := by
    have h := (Matrix.le_iff.mp hs.1).mul_mul_conjTranspose_same R
    apply Matrix.le_iff.mpr
    simpa only [hR.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, hRPR] using h
  have hu : R * (A + μ • 1) * R ≤ (a + μ + specNorm (A - B)) • 1 := by
    have h := (Matrix.le_iff.mp hs.2).mul_mul_conjTranspose_same R
    apply Matrix.le_iff.mpr
    simpa only [hR.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, hRPR] using h
  have hh : μ ≤ a + μ + specNorm (A - B) := by linarith [specNorm_nonneg (A - B)]
  exact (conditionNumber_toReal_le_of_sandwich hμ hh hl hu).trans_eq (by
    field_simp [ne_of_gt hμ]
    ring)

open scoped Matrix.Norms.L2Operator in
/-- The same actual symmetric preconditioned matrix is SPD, so its condition number is
finite; the real-valued condition bound does not hide a singular matrix's `toReal` value. -/
theorem nystromPreconditionedMatrix_posDef {A B : Matrix n n ℝ}
    (hB : B.PosSemidef) (hBA : B ≤ A) {a μ : ℝ} (ha : 0 ≤ a) (hμ : 0 < μ) :
    (nystromPreconditionedMatrix A B a μ).PosDef := by
  let P := nystromPreconditioner B a μ
  let R := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) P
  have hP : P.PosDef := nystromPreconditioner_posDef hB ha hμ
  have hR : R.IsHermitian := cfc_predicate _ _
  have hRPR : R * nystromPreconditioner B a μ * R = 1 := cfc_inv_sqrt_mul_self_mul_inv_sqrt hP
  apply posDef_of_posDef_le (Matrix.PosDef.one.smul hμ)
  have h := (Matrix.le_iff.mp (nystromPreconditioner_sandwich hB hBA ha hμ).1)
    |>.mul_mul_conjTranspose_same R
  apply Matrix.le_iff.mpr
  change (R * (A + μ • 1) * R - μ • 1).PosSemidef
  simpa only [hR.eq, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, hRPR] using h

/-- **PCG with the actual FTU preconditioner.** The residual-dependent Loewner enclosure
gives the standard energy error bound for every native PCG iterate. -/
theorem quadForm_sub_le_of_isPCGIterate_nystromPreconditioner {A B : Matrix n n ℝ}
    (hB : B.PosSemidef) (hBA : B ≤ A) {a μ : ℝ} (ha : 0 ≤ a) (hμ : 0 < μ)
    {c x₀ xs x : n → ℝ} (hxs : (A + μ • 1) *ᵥ xs = c) {q : ℕ}
    (hx : IsPCGIterate (A + μ • 1) (nystromPreconditioner B a μ) c x₀ q x) :
    quadForm (A + μ • 1) (x - xs) ≤
      (2 * ((Real.sqrt (a + μ + specNorm (A - B)) - Real.sqrt μ) /
        (Real.sqrt (a + μ + specNorm (A - B)) + Real.sqrt μ)) ^ q) ^ 2 *
          quadForm (A + μ • 1) (x₀ - xs) := by
  have hs := nystromPreconditioner_sandwich hB hBA ha hμ
  exact quadForm_sub_le_of_isPCGIterate (nystromPreconditioner_posDef hB ha hμ)
    hμ (by linarith [specNorm_nonneg (A - B)]) hs.1 hs.2 hxs hx

end NLAlib
