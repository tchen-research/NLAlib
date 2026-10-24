import NLAlib.Matrix.Factorizations.RankRevealingTrailing
import NLAlib.Matrix.Norms.BlockNormBounds
import NLAlib.Matrix.Norms.Reindex
import NLAlib.Matrix.Norms.SpectralNormBounds
import NLAlib.Matrix.Factorizations.MaximumVolumeQR

/-!
# Interpolative decomposition

Distinct selected columns and interpolation entries bounded by one give the
sharp maximum-volume factor `sqrt (1 + k (n-k))`. The maximum-volume QR budget
proves the guarantee for the actual normal-equation coefficients of every supplied
maximal embedding. The finite search algorithm is developed separately in the
`InterpolativeDecompositionSearch` leaf. Sources: HMT 2011, §4.2; Gu–Eisenstat 1996,
Theorem 3.2. Atlas: `interpolative-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- The actual normal-equation interpolation coefficients for a selected column
embedding. The formula is total; the maximum-volume theorem guarantees the selected
Gram matrix is invertible, including the valid empty inverse at cutoff zero. -/
def columnInterpolationCoefficients {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) {k : ℕ} (e : Fin k ↪ n) : Matrix (Fin k) n ℝ :=
  ((A.submatrix id e)ᵀ * A.submatrix id e)⁻¹ * (A.submatrix id e)ᵀ * A

/-- Every actual maximum-volume column embedding gives the normal-equation
interpolant with identity selected columns, entries bounded by one, and the sharp
maximum-volume spectral residual. The selected embedding is preserved throughout
the QR budget argument. Source: HMT 2011, §4.2; Gu–Eisenstat 1996, Theorem 3.2. -/
theorem columnInterpolationCoefficients_spec_of_maximum_volume {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ) (hk : k ≤ A.rank) (e : Fin k ↪ n)
    (hpos : 0 < ((A.submatrix id e)ᵀ * A.submatrix id e).det)
    (hmax : ∀ f : Fin k → n, ((A.submatrix id f)ᵀ * A.submatrix id f).det ≤
      ((A.submatrix id e)ᵀ * A.submatrix id e).det) :
    (columnInterpolationCoefficients A e).submatrix id e = 1 ∧
      (∀ i j, |columnInterpolationCoefficients A e i j| ≤ 1) ∧
      specNorm (A - A.submatrix id e * columnInterpolationCoefficients A e) ≤
        Real.sqrt (1 + (k : ℝ) * ((Fintype.card n : ℝ) - k)) * singularValues A k := by
  classical
  obtain ⟨π, Q, R, T₀, D, hπ, hQ, _, hR, _, hFact, hEntry, hBudget⟩ :=
    exists_maximum_volume_qr_blocks_of_embedding A k hk e hpos hmax
  let C := A.submatrix id e
  let T := columnInterpolationCoefficients A e
  have hSel : C = Q * Matrix.fromRows R 0 := by
    ext i j
    have h := congrFun (congrFun hFact i) (Sum.inl j)
    simpa [C, hπ, Matrix.mul_apply] using h
  have hCQ : Cᵀ * Q = Matrix.fromCols Rᵀ 0 := by
    rw [hSel, Matrix.transpose_mul, Matrix.mul_assoc, show Qᵀ * Q = 1 from hQ,
      Matrix.mul_one, Matrix.transpose_fromRows, Matrix.transpose_zero]
  have hGram : Cᵀ * C = Rᵀ * R := by
    calc
      _ = Cᵀ * (Q * Matrix.fromRows R 0) := congrArg (fun X => Cᵀ * X) hSel
      _ = (Cᵀ * Q) * Matrix.fromRows R 0 := (Matrix.mul_assoc _ _ _).symm
      _ = _ := by rw [hCQ, Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero]
  have hNormal : Cᵀ * A.submatrix id π = (Cᵀ * C) * Matrix.fromCols 1 T₀ := by
    rw [hFact, ← Matrix.mul_assoc, hCQ, Matrix.fromCols_mul_fromBlocks,
      hGram, Matrix.mul_fromCols]
    simp only [Matrix.zero_mul, add_zero, Matrix.mul_one, Matrix.mul_assoc]
  have hT : T.submatrix id π = Matrix.fromCols 1 T₀ := by
    change (((Cᵀ * C)⁻¹ * Cᵀ) * A).submatrix id π = _
    rw [Matrix.mul_assoc]
    change (Cᵀ * C)⁻¹ * (Cᵀ * A.submatrix id π) = _
    rw [hNormal, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hpos.ne'), Matrix.one_mul]
  have hProd : (C * T).submatrix id π = Q * Matrix.fromBlocks R (R * T₀) 0 0 := by
    have heq : (C * T).submatrix id π = C * T.submatrix id π := by ext i j; rfl
    rw [heq, hSel, hT, Matrix.mul_assoc, Matrix.fromRows_mul_fromCols,
      Matrix.mul_one, Matrix.zero_mul, Matrix.zero_mul]
  have hErr : (A - C * T).submatrix id π = Q * Matrix.fromBlocks 0 0 0 D := by
    change A.submatrix id π - (C * T).submatrix id π = _
    rw [hFact, hProd, ← Matrix.mul_sub]
    congr 1
    ext (i | i) (j | j) <;> simp
  have hBlock : specNorm (Matrix.fromBlocks (0 : Matrix (Fin k) (Fin k) ℝ)
      (0 : Matrix (Fin k) (Fin (Fintype.card n - k)) ℝ) 0 D) ≤ specNorm D := by
    have hrow := specNorm_fromRows_sq_le
      (0 : Matrix (Fin k) (Fin k ⊕ Fin (Fintype.card n - k)) ℝ)
      (Matrix.fromCols (0 : Matrix (Fin (Fintype.card m - k)) (Fin k) ℝ) D)
    have hcol := specNorm_fromCols_sq_le
      (0 : Matrix (Fin (Fintype.card m - k)) (Fin k) ℝ) D
    simp only [specNorm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at hrow hcol
    have heq : Matrix.fromRows
        (0 : Matrix (Fin k) (Fin k ⊕ Fin (Fintype.card n - k)) ℝ)
        (Matrix.fromCols (0 : Matrix (Fin (Fintype.card m - k)) (Fin k) ℝ) D) =
        Matrix.fromBlocks 0 0 0 D := by ext (i | i) (j | j) <;> rfl
    rw [heq] at hrow
    nlinarith [specNorm_nonneg D, specNorm_nonneg
      (Matrix.fromBlocks (0 : Matrix (Fin k) (Fin k) ℝ)
        (0 : Matrix (Fin k) (Fin (Fintype.card n - k)) ℝ) 0 D)]
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have h := congrArg (fun M => M i (Sum.inl j)) hT
    simpa only [Matrix.submatrix_apply, id_eq, hπ, Matrix.fromCols_apply_inl] using h
  · intro i j
    obtain ⟨j', rfl⟩ := π.surjective j
    cases j' with
    | inl j' =>
      have h := congrArg (fun M => M i (Sum.inl j')) hT
      simp only [Matrix.submatrix_apply, id_eq, Matrix.fromCols_apply_inl] at h
      change |T i (π (Sum.inl j'))| ≤ 1
      rw [h]
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num
    | inr j' =>
      have h := congrArg (fun M => M i (Sum.inr j')) hT
      simp only [Matrix.submatrix_apply, id_eq, Matrix.fromCols_apply_inr] at h
      change |T i (π (Sum.inr j'))| ≤ 1
      rw [h]
      exact hEntry i j'
  · have hReindex := specNorm_reindex (A - C * T) (Equiv.refl m) π.symm
    change specNorm ((A - C * T).submatrix id π) = _ at hReindex
    change specNorm (A - C * T) ≤ _
    rw [← hReindex, hErr, specNorm_mul_left_of_hasOrthonormalCols hQ]
    apply hBlock.trans
    have hkn : k ≤ Fintype.card n := hk.trans A.rank_le_card_width
    have hb : 0 ≤ (k : ℝ) * ((Fintype.card n : ℝ) - k) :=
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (Nat.cast_le.mpr hkn))
    have h := singularValues_trailing_le_sqrt_budget_mul R T₀ D hR
      ((k : ℝ) * ((Fintype.card n : ℝ) - k)) hb hBudget 0
    have hSpec := congrFun (singularValues_reindex A (Equiv.refl m) π.symm) k
    change singularValues (A.submatrix id π) k = _ at hSpec
    rw [hFact, singularValues_isometry_mul hQ] at hSpec
    rw [Nat.add_zero, hSpec, singularValues_zero_eq_specNorm] at h
    exact h

/-- Every matrix admits an interpolative decomposition with distinct selected
columns, identity interpolation on those columns, coefficients bounded by one,
and the maximum-volume spectral error factor. The empty selection is included.
This is an existence theorem, without a cost guarantee for computing the selection.
Source: HMT 2011, §4.2; Gu–Eisenstat 1996, Theorem 3.2.
atlas: interpolative-decomposition (partial)-/
theorem exists_interpolative_decomposition {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ) (hk : k ≤ A.rank) :
    ∃ e : Fin k ↪ n, ∃ T : Matrix (Fin k) n ℝ,
      T.submatrix id e = 1 ∧ (∀ i j, |T i j| ≤ 1) ∧
      specNorm (A - A.submatrix id e * T) ≤
        Real.sqrt (1 + (k : ℝ) * ((Fintype.card n : ℝ) - k)) * singularValues A k := by
  obtain ⟨e, hpos, hmax⟩ := exists_maximum_volume_column_embedding A k hk
  exact ⟨e, columnInterpolationCoefficients A e,
    columnInterpolationCoefficients_spec_of_maximum_volume A k hk e hpos hmax⟩
/-- At the matrix rank the selected columns reconstruct the matrix exactly,
with identity interpolation and coefficients bounded by one. Rank zero and
empty matrices are included. Source: HMT 2011, §4.2.
atlas: interpolative-decomposition (partial)-/
theorem exists_exact_interpolative_decomposition {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) :
    ∃ e : Fin A.rank ↪ n, ∃ T : Matrix (Fin A.rank) n ℝ,
      T.submatrix id e = 1 ∧ (∀ i j, |T i j| ≤ 1) ∧ A = A.submatrix id e * T := by
  obtain ⟨e, T, hId, hEntry, hErr⟩ := exists_interpolative_decomposition A A.rank le_rfl
  rw [singularValues_eq_zero_of_rank_le A le_rfl, mul_zero] at hErr
  have hzero : specNorm (A - A.submatrix id e * T) = 0 :=
    le_antisymm hErr (specNorm_nonneg _)
  have hEq : A - A.submatrix id e * T = 0 := by
    open scoped Matrix.Norms.L2Operator in
    simpa only [specNorm_eq_norm] using norm_eq_zero.mp
      (by simpa only [specNorm_eq_norm] using hzero)
  exact ⟨e, T, hId, hEntry, sub_eq_zero.mp hEq⟩

end NLAlib
