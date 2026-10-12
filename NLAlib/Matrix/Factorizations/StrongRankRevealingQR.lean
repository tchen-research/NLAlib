import NLAlib.Matrix.Factorizations.RankRevealingTrailing
import NLAlib.Matrix.Factorizations.MaximumVolumeRankAdapted
import NLAlib.Matrix.Spectral.SingularValueInvariance
import NLAlib.Matrix.Inequalities.KyFanNorms
/-!
# Strong rank-revealing QR with the exact Gu–Eisenstat constants

A finite maximum-volume selection proves all three strong RRQR guarantees.
The leading inverse is genuine under `k ≤ rank A`. Setting `k = rank A`
gives the rank-adapted branch with exactly zero residual, including rank zero.
Gu–Eisenstat 1996, Theorem 3.2; derivations §alg:rrqr.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Strong rank-revealing QR exists with the exact constants
`sqrt(1 + f² k(n-k))` and interpolation bound `f`, for every `f ≥ 1`.
The column equivalence is an actual reordering of all input columns; the
full orthogonal factor has both Gram identities; the leading block is
invertible and upper triangular and the trailing block is upper trapezoidal.
Every leading and every zero-padded trailing singular value is controlled.

The necessary source repair is `k ≤ rank A`, since an ordinary leading
inverse is required. This theorem allows all such `k`, so applying it with
`k = rank A` proves the rank-adapted replacement when a requested rank is
too large; its last clause gives an exactly zero residual. At rank zero the
leading inverse is the valid empty inverse and the factorization reconstructs
the zero matrix. Gu–Eisenstat 1996, Theorem 3.2; Martinsson–Tropp 2020,
Section 13.2; derivations §alg:rrqr, maximum-volume proof.
atlas: rank-revealing-qr -/
theorem exists_strong_rank_revealing_qr {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (k : ℕ) (hk : k ≤ A.rank) (f : ℝ) (hf : 1 ≤ f) :
    ∃ π : (Fin k ⊕ Fin (Fintype.card n - k)) ≃ n,
    ∃ Q : Matrix m (Fin k ⊕ Fin (Fintype.card m - k)) ℝ,
    ∃ R₁₁ : Matrix (Fin k) (Fin k) ℝ,
    ∃ R₁₂ : Matrix (Fin k) (Fin (Fintype.card n - k)) ℝ,
    ∃ R₂₂ : Matrix (Fin (Fintype.card m - k)) (Fin (Fintype.card n - k)) ℝ,
      HasOrthonormalCols Q ∧ Q * Qᵀ = 1 ∧ IsUnit R₁₁ ∧ R₁₁.IsUpperTriangular ∧
      IsUpperTrapezoidal R₂₂ ∧ A.submatrix id π = Q * Matrix.fromBlocks R₁₁ R₁₂ 0 R₂₂ ∧
      (∀ i < k, singularValues A i /
        Real.sqrt (1 + f ^ 2 * k * ((Fintype.card n : ℝ) - k)) ≤ singularValues R₁₁ i) ∧
      (∀ j, singularValues R₂₂ j ≤ singularValues A (k + j) *
        Real.sqrt (1 + f ^ 2 * k * ((Fintype.card n : ℝ) - k))) ∧
      (∀ i j, |(R₁₁⁻¹ * R₁₂) i j| ≤ f) ∧
      (k = A.rank → R₂₂ = 0) := by
  obtain ⟨π, Q, R, T, D, hQ, hQt, hR, hUpper, hDUpper, hFact, hEntry, hBudget⟩ :=
    exists_maximum_volume_triangular_qr_blocks A k hk
  let b : ℝ := (k : ℝ) * ((Fintype.card n : ℝ) - k)
  let c := Real.sqrt (1 + f ^ 2 * k * ((Fintype.card n : ℝ) - k))
  have hkn : k ≤ Fintype.card n := hk.trans A.rank_le_card_width
  have hnk : 0 ≤ (Fintype.card n : ℝ) - k := sub_nonneg.mpr (Nat.cast_le.mpr hkn)
  have hb : 0 ≤ b := mul_nonneg (Nat.cast_nonneg k) hnk
  have hf2 : 1 ≤ f ^ 2 := by nlinarith
  have hConst : 1 + b ≤ 1 + f ^ 2 * k * ((Fintype.card n : ℝ) - k) := by
    have hh := mul_le_mul_of_nonneg_right hf2 hb
    dsimp only [b] at hh ⊢
    nlinarith
  have hc : 0 < c := Real.sqrt_pos.mpr (lt_of_lt_of_le (by linarith : 0 < 1 + b) hConst)
  have hSmall : Real.sqrt (1 + b) ≤ c := Real.sqrt_le_sqrt hConst
  have hSpec (i : ℕ) : singularValues (Matrix.fromBlocks R (R * T) 0 D) i =
      singularValues A i := by
    have hh := congrFun (singularValues_reindex A (Equiv.refl m) π.symm) i
    change singularValues (A.submatrix id π) i = _ at hh
    rw [hFact, singularValues_isometry_mul hQ] at hh
    exact hh
  refine ⟨π, Q, R, R * T, D, hQ, hQt, hR, hUpper, hDUpper, hFact, ?_, ?_, ?_, ?_⟩
  · intro i hi
    apply (div_le_iff₀ hc).mpr
    calc
      _ = singularValues (Matrix.fromBlocks R (R * T) 0 D) i := (hSpec i).symm
      _ ≤ Real.sqrt (1 + b) * singularValues R i :=
        singularValues_upper_block_le_sqrt_budget_mul R T D hR b hb hBudget hi
      _ ≤ c * singularValues R i :=
        mul_le_mul_of_nonneg_right hSmall (singularValues_nonneg R i)
      _ = _ := mul_comm _ _
  · intro j
    have hh := singularValues_trailing_le_sqrt_budget_mul R T D hR b hb hBudget j
    rw [hSpec] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_right hSmall
      (singularValues_nonneg _ _)).trans_eq (mul_comm _ _))
  · intro i j
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det _).mp hR),
      Matrix.one_mul]
    exact (hEntry i j).trans hf
  · intro hr
    have hRankA : (A.submatrix id π).rank = A.rank := by
      simpa only [Equiv.coe_refl] using Matrix.rank_submatrix A (Equiv.refl m) π
    rw [hFact, rank_isometry_mul_eq hQ] at hRankA
    have hAdd := rank_fromBlocks_eq_rank_add_rank_schur R (R * T)
      (0 : Matrix (Fin (Fintype.card m - k)) (Fin k) ℝ) D
      ((Matrix.isUnit_iff_isUnit_det _).mp hR)
    simp only [Matrix.zero_mul, sub_zero, Matrix.rank_of_isUnit R hR, Fintype.card_fin] at hAdd
    have hRankD : D.rank = 0 := by omega
    apply (frobSq_eq_zero_iff D).mp
    apply le_antisymm _ (frobSq_nonneg D)
    simpa only [hRankD, Nat.cast_zero, zero_mul] using frobSq_le_rank_mul_specNorm_sq D

end NLAlib
