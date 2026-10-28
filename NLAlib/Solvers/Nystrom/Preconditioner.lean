/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Matrix.Norms.LoewnerBounds

/-!
# The spectral-floor Nyström preconditioner

For a PSD approximation `B`, a floor `a≥0`, and regularization `μ>0`, the FTU
preconditioner applies `(max λ a + μ)/(a+μ)` to the eigenvalues of `B`. Choosing `a`
as the smallest retained eigenvalue gives the usual low-rank formula, with eigenvalue
one on the orthogonal complement. This functional-calculus representation avoids choosing
random eigenvectors in the probability law.
Source: Frangella–Tropp–Udell 2023, randomized Nyström preconditioning, Theorem 5.1.
Atlas: `nystrom-pcg` (deterministic preconditioner).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- The FTU preconditioner represented as an eigenvalue floor and a positive shift.
Its intended domain is a PSD matrix, `a≥0`, and `μ>0`. -/
def nystromPreconditioner (B : Matrix n n 𝕜) (a μ : ℝ) : Matrix n n 𝕜 :=
  cfc (fun t : ℝ => (max t a + μ) / (a + μ)) B

open scoped Matrix.Norms.L2Operator in
/-- The spectral-floor preconditioner is positive definite, including when the approximation
is singular or zero. -/
theorem nystromPreconditioner_posDef {B : Matrix n n 𝕜} (hB : B.PosSemidef)
    {a μ : ℝ} (ha : 0 ≤ a) (hμ : 0 < μ) : (nystromPreconditioner B a μ).PosDef := by
  apply Matrix.isStrictlyPositive_iff_posDef.mp
  apply (cfc_isStrictlyPositive_iff _ B (by fun_prop) hB.isHermitian).mpr
  intro t _
  exact div_pos (add_pos_of_nonneg_of_pos (ha.trans (le_max_right t a)) hμ)
    (add_pos_of_nonneg_of_pos ha hμ)

open scoped Matrix.Norms.L2Operator in
private theorem cfc_add_shift (B : Matrix n n 𝕜) (hB : B.IsHermitian) (μ : ℝ) :
    cfc (fun t : ℝ => t + μ) B = B + μ • 1 := by
  rw [cfc_add_const μ (fun t : ℝ => t) B (by fun_prop) hB.isSelfAdjoint, cfc_id' ℝ B hB.isSelfAdjoint,
    Algebra.algebraMap_eq_smul_one]

open scoped Matrix.Norms.L2Operator in
/-- The spectral-floor preconditioner is bounded below by the identity. -/
theorem one_le_nystromPreconditioner {B : Matrix n n 𝕜} (hB : B.PosSemidef)
    {a μ : ℝ} (ha : 0 ≤ a) (hμ : 0 < μ) : 1 ≤ nystromPreconditioner B a μ := by
  have hd : 0 < a + μ := add_pos_of_nonneg_of_pos ha hμ
  have h := cfc_mono (a := B) (f := fun _ : ℝ => 1)
    (g := fun t : ℝ => (max t a + μ) / (a + μ))
    (fun t _ => (one_le_div hd).mpr (by linarith [le_max_right t a]))
    continuousOn_const (by fun_prop)
  simpa only [cfc_const (1 : ℝ) B hB.isHermitian.isSelfAdjoint, map_one, nystromPreconditioner] using h

open scoped Matrix.Norms.L2Operator in
/-- The shifted approximation lies below the scaled FTU preconditioner. -/
theorem add_smul_one_le_smul_nystromPreconditioner {B : Matrix n n 𝕜}
    (hB : B.PosSemidef) {a μ : ℝ} (ha : 0 ≤ a) (hμ : 0 < μ) :
    B + μ • 1 ≤ (a + μ) • nystromPreconditioner B a μ := by
  have hd : a + μ ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos ha hμ)
  rw [← cfc_add_shift B hB.isHermitian μ, nystromPreconditioner,
    ← cfc_const_mul (a + μ) (fun t : ℝ => (max t a + μ) / (a + μ)) B (by fun_prop)]
  refine cfc_mono ?_ (by fun_prop) (by fun_prop)
  intro t _
  rw [mul_div_cancel₀ _ hd]
  exact add_le_add (le_max_left t a) le_rfl

open scoped Matrix.Norms.L2Operator in
/-- Scaling the FTU preconditioner by the regularization is below the shifted approximation. -/
theorem smul_nystromPreconditioner_le_add_smul_one {B : Matrix n n 𝕜}
    (hB : B.PosSemidef) {a μ : ℝ} (ha : 0 ≤ a) (hμ : 0 < μ) :
    μ • nystromPreconditioner B a μ ≤ B + μ • 1 := by
  have hd : 0 < a + μ := add_pos_of_nonneg_of_pos ha hμ
  rw [← cfc_add_shift B hB.isHermitian μ, nystromPreconditioner,
    ← cfc_const_mul μ (fun t : ℝ => (max t a + μ) / (a + μ)) B (by fun_prop)]
  refine cfc_mono ?_ (by fun_prop) (by fun_prop)
  intro t ht
  have ht0 : 0 ≤ t := (spectrum_nonneg_of_nonneg hB.nonneg) ht
  rw [← mul_div_assoc, div_le_iff₀ hd]
  rcases le_total t a with hta | hat
  · rw [max_eq_right hta]
    nlinarith
  · rw [max_eq_left hat]
    nlinarith

open scoped Matrix.Norms.L2Operator in
/-- **FTU Loewner sandwich.** If `0≤B≤A`, the actual positive-definite floor preconditioner
satisfies `μP≤A+μI≤(a+μ+‖A−B‖₂)P`. Thus its condition bound is
`1+(a+‖A−B‖₂)/μ`. Source: Frangella–Tropp–Udell 2023, Theorem 5.1 proof.
atlas: nystrom-pcg (partial) -/
theorem nystromPreconditioner_sandwich {A B : Matrix n n 𝕜}
    (hB : B.PosSemidef) (hBA : B ≤ A) {a μ : ℝ} (ha : 0 ≤ a) (hμ : 0 < μ) :
    μ • nystromPreconditioner B a μ ≤ A + μ • 1 ∧
      A + μ • 1 ≤ (a + μ + specNorm (A - B)) • nystromPreconditioner B a μ := by
  constructor
  · exact (smul_nystromPreconditioner_le_add_smul_one hB ha hμ).trans
      (add_le_add hBA le_rfl)
  · have hE : (A - B).PosSemidef := Matrix.le_iff.mp hBA
    have hEn : A - B ≤ specNorm (A - B) • (1 : Matrix n n 𝕜) :=
      (hE.specNorm_le_iff (specNorm_nonneg _)).mp le_rfl
    have hEP := smul_le_smul_of_nonneg_left (one_le_nystromPreconditioner hB ha hμ)
      (specNorm_nonneg (A - B))
    have h := add_le_add (add_smul_one_le_smul_nystromPreconditioner hB ha hμ)
      (hEn.trans hEP)
    convert h using 1 <;> module

open scoped Matrix.Norms.L2Operator in
/-- The actual spectral action of the preconditioner in an orthonormal eigenbasis. -/
theorem nystromPreconditioner_eq_eigenvectorUnitary_mul_diagonal
    {B : Matrix n n 𝕜} (hB : B.IsHermitian) (a μ : ℝ) :
    nystromPreconditioner B a μ =
      (hB.eigenvectorUnitary : Matrix n n 𝕜) *
        Matrix.diagonal (fun i => (((max (hB.eigenvalues i) a + μ) / (a + μ) : ℝ) : 𝕜)) *
        (hB.eigenvectorUnitary : Matrix n n 𝕜)ᴴ := by
  rw [nystromPreconditioner, hB.cfc_eq, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- The spectral floor is the original matrix plus a fixed continuous correction
applied to its scalar shift. This identity gives a measurable implementation
without selecting a random eigenbasis. -/
theorem nystromPreconditioner_eq_cfc_shift {B : Matrix n n 𝕜}
    (hB : B.IsHermitian) (a μ : ℝ) :
    nystromPreconditioner B a μ = (a + μ)⁻¹ •
      (B + μ • 1 + cfc (fun t : ℝ => max (-t) 0) (B - a • 1)) := by
  have hshift : cfc (fun t : ℝ => t - a) B = B - a • 1 := by
    rw [cfc_sub (fun t : ℝ => t) (fun _ : ℝ => a) B,
      cfc_id' ℝ B hB.isSelfAdjoint, cfc_const a B hB.isSelfAdjoint,
      Algebra.algebraMap_eq_smul_one]
  have hcomp : cfc (fun t : ℝ => max (-t) 0) (B - a • 1) =
      cfc (fun t : ℝ => max (-(t-a)) 0) B := by
    rw [← hshift, ← cfc_comp (fun t : ℝ => max (-t) 0) (fun t : ℝ => t-a) B
      hB.isSelfAdjoint (by fun_prop) (by fun_prop)]
    rfl
  rw [hcomp, ← cfc_add_shift B hB μ, ← cfc_add B (fun t : ℝ => t+μ)
    (fun t : ℝ => max (-(t-a)) 0) (by fun_prop) (by fun_prop),
    ← cfc_const_mul (a+μ)⁻¹ (fun t : ℝ => t+μ+max (-(t-a)) 0) B (by fun_prop)]
  apply cfc_congr
  intro t _
  dsimp only
  rw [div_eq_mul_inv]
  have he : max t a + μ = t + μ + max (-(t-a)) 0 := by
    rcases le_total t a with h | h
    · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -(t-a))]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith : -(t-a) ≤ 0)]
      ring
  rw [he]
  ring

end NLAlib
