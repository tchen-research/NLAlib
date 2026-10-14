import NLAlib.Matrix.Factorizations.StrongRankRevealingQR
import NLAlib.Matrix.Norms.BlockNormBounds
import NLAlib.Matrix.Norms.Reindex
import NLAlib.Matrix.Norms.SpectralNormBounds

/-!
# Interpolative decomposition

Distinct selected columns and interpolation entries bounded by one give the
sharp maximum-volume existence factor `sqrt (1 + k (n-k))`. The existing strong
RRQR theorem supplies the same existence guarantee, without a new factorization
object or an algorithmic cost claim. Sources: HMT 2011, §4.2; Gu–Eisenstat 1996,
Theorem 3.2. Atlas: `interpolative-decomposition`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Every matrix admits an interpolative decomposition with distinct selected
columns, identity interpolation on those columns, coefficients bounded by one,
and the maximum-volume spectral error factor. The empty selection is included.
This is an existence theorem, without a cost guarantee for computing the selection.
Source: HMT 2011, §4.2; Gu–Eisenstat 1996, Theorem 3.2.
atlas: interpolative-decomposition (partial) -/
theorem exists_interpolative_decomposition {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ) (hk : k ≤ A.rank) :
    ∃ e : Fin k ↪ n, ∃ T : Matrix (Fin k) n ℝ,
      T.submatrix id e = 1 ∧ (∀ i j, |T i j| ≤ 1) ∧
      specNorm (A - A.submatrix id e * T) ≤
        Real.sqrt (1 + (k : ℝ) * ((Fintype.card n : ℝ) - k)) * singularValues A k := by
  classical
  obtain ⟨π, Q, R, B, D, hQ, _, hR, _, _, hFact, _, hTail, hEntry, _⟩ :=
    exists_strong_rank_revealing_qr A k hk 1 le_rfl
  let e : Fin k ↪ n := ⟨fun i => π (Sum.inl i), π.injective.comp Sum.inl_injective⟩
  let T₀ := R⁻¹ * B
  let T : Matrix (Fin k) n ℝ := (Matrix.fromCols 1 T₀).submatrix id π.symm
  have hRT : R * T₀ = B := by
    change R * (R⁻¹ * B) = B
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv R
      ((Matrix.isUnit_iff_isUnit_det _).mp hR), Matrix.one_mul]
  have hSel : A.submatrix id e = Q * Matrix.fromRows R 0 := by
    ext i j
    have h := congrFun (congrFun hFact i) (Sum.inl j)
    simpa [e, Matrix.mul_apply] using h
  have hT : T.submatrix id π = Matrix.fromCols 1 T₀ := by
    ext i j
    simp [T]
  have hProd : (A.submatrix id e * T).submatrix id π =
      Q * Matrix.fromBlocks R B 0 0 := by
    have heq : (A.submatrix id e * T).submatrix id π =
        A.submatrix id e * T.submatrix id π := by
      ext i j
      rfl
    rw [heq, hSel, hT, Matrix.mul_assoc, Matrix.fromRows_mul_fromCols,
      Matrix.mul_one, Matrix.zero_mul, hRT, Matrix.zero_mul]
  have hErr : (A - A.submatrix id e * T).submatrix id π =
      Q * Matrix.fromBlocks 0 0 0 D := by
    change A.submatrix id π - (A.submatrix id e * T).submatrix id π = _
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
        Matrix.fromBlocks 0 0 0 D := by
      ext (i | i) (j | j) <;> rfl
    rw [heq] at hrow
    have hnonneg := specNorm_nonneg D
    have hnonneg' := specNorm_nonneg (Matrix.fromBlocks
      (0 : Matrix (Fin k) (Fin k) ℝ)
      (0 : Matrix (Fin k) (Fin (Fintype.card n - k)) ℝ) 0 D)
    nlinarith
  refine ⟨e, T, ?_, ?_, ?_⟩
  · ext i j
    simp [T, e]
  · intro i j
    obtain ⟨j', rfl⟩ := π.surjective j
    cases j' with
    | inl j' => simp [T, Matrix.one_apply]; split_ifs <;> norm_num
    | inr j' => simpa [T, T₀] using hEntry i j'
  · have hReindex := specNorm_reindex (A - A.submatrix id e * T) (Equiv.refl m) π.symm
    change specNorm ((A - A.submatrix id e * T).submatrix id π) = _ at hReindex
    rw [← hReindex, hErr, specNorm_mul_left_of_hasOrthonormalCols hQ]
    apply hBlock.trans
    have h := hTail 0
    rw [singularValues_zero_eq_specNorm] at h
    norm_num only [one_pow, one_mul, add_zero] at h
    simpa only [mul_comm] using h

/-- At the matrix rank the selected columns reconstruct the matrix exactly,
with identity interpolation and coefficients bounded by one. Rank zero and
empty matrices are included. Source: HMT 2011, §4.2.
atlas: interpolative-decomposition (partial) -/
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
