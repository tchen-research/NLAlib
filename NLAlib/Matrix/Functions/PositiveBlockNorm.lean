import NLAlib.Matrix.Functions.PositiveMapSpectral
import NLAlib.Matrix.Functions.HermitianCalculus

/-!
# Norm bounds for equal-diagonal positive blocks

A positive block with equal diagonal blocks `S` has off-diagonal norm at
most `‖S‖`, including singular and zero `S`. Tropp (2022), Theorem 12.22.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The identity-diagonal block criterion holds over complex matrices too. -/
theorem norm_le_one_of_posSemidef_identity_fromBlocks {D : Matrix n n ℂ}
    (h : (fromBlocks 1 D D.conjTranspose 1).PosSemidef) : ‖D‖ ≤ 1 := by
  let : Invertible (1 : Matrix n n ℂ) := invertibleOne
  have hp := (Matrix.PosDef.fromBlocks₁₁ D (1 : Matrix n n ℂ) Matrix.PosDef.one).mp h
  have hle : D.conjTranspose * D ≤ 1 := Matrix.le_iff.mpr
    (by simpa only [inv_one, Matrix.mul_one] using hp)
  have hn : ‖D.conjTranspose * D‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _
      (Matrix.posSemidef_conjTranspose_mul_self D).nonneg).mpr hle
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  nlinarith [norm_nonneg D]

/-- A positive block with equal diagonal blocks has off-diagonal norm
bounded by their norm, with no strict-positivity hypothesis. -/
theorem norm_le_of_posSemidef_equal_fromBlocks {S D : Matrix n n ℂ}
    (hS : S.PosSemidef) (h : (fromBlocks S D D.conjTranspose S).PosSemidef) :
    ‖D‖ ≤ ‖S‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let t : ℝ := ‖S‖ + ε
  have ht : 0 < t := add_pos_of_nonneg_of_pos (norm_nonneg _) hε
  have hSt : S ≤ t • (1 : Matrix n n ℂ) := by
    have hS' := hS.isHermitian.isSelfAdjoint.le_algebraMap_norm_self
    have htt : algebraMap ℝ (Matrix n n ℂ) ‖S‖ ≤ algebraMap ℝ (Matrix n n ℂ) t := by
      simp only [Algebra.algebraMap_eq_smul_one]
      exact smul_le_smul_of_nonneg_right (by dsimp [t]; linarith) zero_le_one
    exact hS'.trans (by simpa only [Algebra.algebraMap_eq_smul_one] using htt)
  have hG : (t • (1 : Matrix n n ℂ) - S).PosSemidef := Matrix.le_iff.mp hSt
  have hp := h.add (posSemidef_fromBlocks_diag hG hG)
  have heq : fromBlocks S D D.conjTranspose S +
      fromBlocks (t • 1 - S) 0 0 (t • 1 - S) =
      fromBlocks (t • 1) D D.conjTranspose (t • 1) := by
    ext i j
    cases i <;> cases j <;> simp [fromBlocks]
  rw [heq] at hp
  have hp' := hp.smul (inv_pos.mpr ht).le
  have heq' : t⁻¹ • fromBlocks (t • (1 : Matrix n n ℂ)) D D.conjTranspose (t • 1) =
      fromBlocks 1 (t⁻¹ • D) (t⁻¹ • D).conjTranspose 1 := by
    ext i j
    cases i <;> cases j <;> simp [fromBlocks, ht.ne', Matrix.conjTranspose_smul]
  rw [heq'] at hp'
  have hn := norm_le_one_of_posSemidef_identity_fromBlocks hp'
  rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr ht).le] at hn
  simpa only [mul_one] using (inv_mul_le_iff₀ ht).mp hn

end NLAlib
