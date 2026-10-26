import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Order

/-!
# Determinant-ratio normalization bridge

A complex positive definite matrix can be rescaled by a positive real scalar to
determinant one; applying an `ℝ`-linear map `T` to such a rescaling realizes the
ratio `(T X).det.re / X.det.re` with the determinant-one matrix `Y`.
This is the normalization bridge used for operator capacity objectives: the set of
attainable real objectives over determinant-one matrices equals the set over the
determinant-ratio formulation, and their infima agree.

The positive determinant-root normalization in
`NLAlib.Matrix.Inequalities.DeterminantRoot` works over `ℝ`; here we work directly
over `ℂ` using the real part of the determinant, which is positive when the matrix
is positive definite (`Matrix.PosDef.det_pos` together with `Complex.pos_iff`).
-/

noncomputable section
open Matrix
open scoped ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive real rescaling factor that normalizes a complex positive definite matrix
to determinant one: the inverse of the `card n`-th determinant root of the real part
of the determinant. -/
noncomputable def detNormalizeScaling (X : Matrix n n ℂ) : ℝ :=
  (X.det.re ^ (1 / (Fintype.card n : ℝ)))⁻¹

/-- The rescaling factor in `detNormalizeScaling` is positive. -/
theorem _root_.Matrix.PosDef.detNormalizeScaling_pos {X : Matrix n n ℂ} (hX : X.PosDef) :
    0 < detNormalizeScaling X := by
  unfold detNormalizeScaling
  exact inv_pos.mpr (Real.rpow_pos_of_pos (Complex.pos_iff.mp hX.det_pos).1 _)

private theorem det_normalize_scaling_pow_card (X : Matrix n n ℂ) (hX : X.PosDef)
    (hN : 0 < Fintype.card n) :
    detNormalizeScaling X ^ Fintype.card n = (X.det.re)⁻¹ := by
  have hre_pos : 0 < X.det.re := (Complex.pos_iff.mp hX.det_pos).1
  have hN_ne : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  unfold detNormalizeScaling
  rw [inv_pow]
  congr 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hre_pos.le]
  rw [one_div_mul_cancel hN_ne, Real.rpow_one]

/-- Rescaling a complex positive definite matrix by `detNormalizeScaling` yields
determinant exactly one. -/
theorem _root_.Matrix.PosDef.det_smul_detNormalizeScaling_eq_one {X : Matrix n n ℂ} (hX : X.PosDef)
    (hN : 0 < Fintype.card n) :
    (detNormalizeScaling X • X).det = 1 := by
  have hre_pos : 0 < X.det.re := (Complex.pos_iff.mp hX.det_pos).1
  have hpow_card : detNormalizeScaling X ^ Fintype.card n = (X.det.re)⁻¹ :=
    det_normalize_scaling_pow_card X hX hN
  have hre_smul (r : ℝ) (z : ℂ) : (r • z).re = r * z.re := by
    rw [Algebra.smul_def]
    exact Complex.re_ofReal_mul r z
  have him_smul (r : ℝ) (z : ℂ) : (r • z).im = r * z.im := by
    rw [Algebra.smul_def]
    exact Complex.im_ofReal_mul r z
  apply Complex.ext
  · rw [Matrix.det_smul_of_tower, hpow_card, hre_smul]
    rw [inv_mul_cancel₀ (ne_of_gt hre_pos)]
    rfl
  · rw [Matrix.det_smul_of_tower, hpow_card, him_smul]
    rw [(Complex.pos_iff.mp hX.det_pos).2.symm]
    simp

/-- Normalization bridge for determinant-ratio objectives: for every positive definite
`X` and every `ℝ`-linear map `T`, there is a determinant-one positive definite matrix
`Y` (namely `detNormalizeScaling X • X`) with
`(T Y).det.re = (T X).det.re / X.det.re`. -/
theorem _root_.Matrix.PosDef.exists_det_eq_one_re_det_map_eq_div {X : Matrix n n ℂ} (hX : X.PosDef)
    (hN : 0 < Fintype.card n) (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) :
    ∃ Y, Y.PosDef ∧ Y.det = 1 ∧ (T Y).det.re = (T X).det.re / X.det.re := by
  refine ⟨detNormalizeScaling X • X, ?_, ?_, ?_⟩
  · exact hX.smul (hX.detNormalizeScaling_pos)
  · exact hX.det_smul_detNormalizeScaling_eq_one hN
  · have hpow_card : detNormalizeScaling X ^ Fintype.card n = (X.det.re)⁻¹ :=
      det_normalize_scaling_pow_card X hX hN
    have hre_smul (r : ℝ) (z : ℂ) : (r • z).re = r * z.re := by
      rw [Algebra.smul_def]
      exact Complex.re_ofReal_mul r z
    rw [T.map_smul]
    rw [Matrix.det_smul_of_tower]
    rw [hpow_card, hre_smul]
    rw [div_eq_inv_mul, mul_comm]

/-- The set of attainable real determinant-ratio objectives over positive definite
matrices equals the set of attainable objectives over determinant-one matrices.
The forward direction reads the ratio off a determinant-one witness; the backward
direction restores determinant one by rescaling. -/
theorem detRatio_attainable_sets_eq (hN : 0 < Fintype.card n)
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) :
    {d : ℝ | ∃ X, X.PosDef ∧ X.det = 1 ∧ d = (T X).det.re} =
      {d : ℝ | ∃ X, X.PosDef ∧ d = (T X).det.re / X.det.re} := by
  ext d
  constructor
  · rintro ⟨X, hX, hXdet, rfl⟩
    refine ⟨X, hX, ?_⟩
    have hXdet_re : X.det.re = 1 := by rw [hXdet]; simp
    rw [hXdet_re]
    simp
  · rintro ⟨X, hX, hd⟩
    rcases hX.exists_det_eq_one_re_det_map_eq_div hN T with ⟨Y, hY, hYdet, hYT⟩
    refine ⟨Y, hY, hYdet, ?_⟩
    rw [hd, hYT]

/-- The infimum of the determinant-one attainable objectives equals the infimum of
the determinant-ratio attainable objectives. -/
theorem detRatio_normalized_sInf_eq (hN : 0 < Fintype.card n)
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) :
    sInf {d : ℝ | ∃ X, X.PosDef ∧ X.det = 1 ∧ d = (T X).det.re} =
      sInf {d : ℝ | ∃ X, X.PosDef ∧ d = (T X).det.re / X.det.re} := by
  rw [detRatio_attainable_sets_eq hN T]

end NLAlib
