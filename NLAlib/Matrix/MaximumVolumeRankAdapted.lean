import NLAlib.Matrix.MaximumVolumeTriangularQR
import NLAlib.Matrix.SchurRank

/-!
# Rank-adapted maximum-volume QR

Choosing the actual rank as the leading size makes the trailing residual
exactly zero, including rank zero. This is the necessary deficient-rank branch
of strong RRQR; no singular leading block is assigned an ordinary inverse.
Gu–Eisenstat 1996, maximum-volume argument; derivations §alg:rrqr.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false

/-- A column isometry preserves matrix rank, including rectangular and empty
isometries. Horn–Johnson 2013, Section 0.4; RRQR transport helper. -/
theorem rank_isometry_mul_eq {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    {Q : Matrix m p ℝ} (hQ : HasOrthonormalCols Q) (A : Matrix p n ℝ) :
    (Q * A).rank = A.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  have hBack : Qᵀ * (Q * A) = A := by
    rw [← Matrix.mul_assoc, show Qᵀ * Q = 1 from hQ, Matrix.one_mul]
  calc
    A.rank = (Qᵀ * (Q * A)).rank := congrArg Matrix.rank hBack.symm
    _ ≤ (Q * A).rank := Matrix.rank_mul_le_right _ _

/-- At the actual rank, maximum-volume QR has an invertible triangular
leading block and an exactly zero trailing residual. Its interpolation
entries are bounded by one and their Frobenius square by `r(n-r)`, including
`r=0`, where the empty basis reconstructs the zero matrix. This is the
rank-adapted replacement required when a requested `k` exceeds `rank A`.
Gu–Eisenstat 1996, maximum-volume proof; derivations §alg:rrqr.
atlas: rank-revealing-qr (partial) -/
theorem exists_rank_adapted_maximum_volume_qr {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    ∃ π : (Fin A.rank ⊕ Fin (Fintype.card n - A.rank)) ≃ n,
    ∃ Q : Matrix m (Fin A.rank ⊕ Fin (Fintype.card m - A.rank)) ℝ,
    ∃ R : Matrix (Fin A.rank) (Fin A.rank) ℝ,
    ∃ T : Matrix (Fin A.rank) (Fin (Fintype.card n - A.rank)) ℝ,
      HasOrthonormalCols Q ∧ Q * Qᵀ = 1 ∧ IsUnit R ∧ R.IsUpperTriangular ∧
      A.submatrix id π = Q * Matrix.fromBlocks R (R * T) 0 0 ∧
      (∀ i j, |T i j| ≤ 1) ∧
      frobSq T ≤ (A.rank : ℝ) * (Fintype.card n - A.rank) := by
  obtain ⟨π, Q, R, T, D, hQ, hQt, hR, hUpper, _, hFact, hEntry, hBudget⟩ :=
    exists_maximum_volume_triangular_qr_blocks A A.rank le_rfl
  have hRankA : (A.submatrix id π).rank = A.rank := by
    simpa only [Equiv.coe_refl] using Matrix.rank_submatrix A (Equiv.refl m) π
  have hRankBlock : A.rank = (Matrix.fromBlocks R (R * T) 0 D).rank := by
    exact hRankA.symm.trans ((congrArg Matrix.rank hFact).trans (rank_isometry_mul_eq hQ _))
  have hRankD : D.rank = 0 := by
    have hAdd := rank_fromBlocks_eq_rank_add_rank_schur R (R * T)
      (0 : Matrix (Fin (Fintype.card m - A.rank)) (Fin A.rank) ℝ) D
      ((Matrix.isUnit_iff_isUnit_det _).mp hR)
    simp only [Matrix.zero_mul, sub_zero, Matrix.rank_of_isUnit R hR, Fintype.card_fin] at hAdd
    omega
  have hD : D = 0 := by
    apply (frobSq_eq_zero_iff D).mp
    apply le_antisymm _ (frobSq_nonneg D)
    have hh := frobSq_le_rank_mul_specNorm_sq D
    simpa only [hRankD, Nat.cast_zero, zero_mul] using hh
  refine ⟨π, Q, R, T, hQ, hQt, hR, hUpper, ?_, hEntry, ?_⟩
  · simpa only [hD] using hFact
  · simpa only [hD, frobSq_zero, mul_zero, add_zero] using hBudget

end NLAlib
