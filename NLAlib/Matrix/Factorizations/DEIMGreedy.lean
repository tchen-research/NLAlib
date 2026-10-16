import NLAlib.Matrix.Subspaces.OrthogonalProducts
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Fin.Tuple.Basic
/-!
# Greedy discrete empirical interpolation

The DEIM recursion uses the actual largest-coordinate residual at each step.
Its previous interpolation matrices are nonsingular, so the process never
breaks down and always selects a new coordinate.

Source: Brunton–Kutz (2022), §13.4; matrix-toolkit re-derivation, §66.
Atlas: `deim-greedy-interpolation`.
-/
noncomputable section
open Matrix Finset
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
variable {r : ℕ}

/-- The first `k` columns of the ordered DEIM basis. -/
def deimPrefix (U : Matrix n (Fin r) 𝕜) (k : ℕ) (hk : k ≤ r) :
    Matrix n (Fin k) 𝕜 := U.submatrix id (Fin.castLE hk)

/-- The sampled first `k` columns at the coordinates selected so far. -/
def deimSampleMatrix (U : Matrix n (Fin r) 𝕜) (k : ℕ) (hk : k ≤ r)
    (indices : Fin k → n) : Matrix (Fin k) (Fin k) 𝕜 :=
  U.submatrix indices (Fin.castLE hk)

/-- The residual used to choose the next DEIM coordinate. The inverse is
total; nonsingularity at every reached stage is proved below. -/
def deimResidual (U : Matrix n (Fin r) 𝕜) (k : ℕ) (hk : k < r)
    (indices : Fin k → n) : n → 𝕜 :=
  U.col ⟨k, hk⟩ - deimPrefix U k hk.le *ᵥ
    ((deimSampleMatrix U k hk.le indices)⁻¹ *ᵥ (fun i => U (indices i) ⟨k, hk⟩))

/-- A largest-modulus coordinate, with arbitrary but fixed tie resolution. -/
def deimPivot [Nonempty n] (v : n → 𝕜) : n :=
  (Finset.exists_max_image univ (fun i => ‖v i‖) univ_nonempty).choose

/-- The chosen coordinate maximizes residual magnitude. -/
theorem norm_le_norm_deimPivot [Nonempty n] (v : n → 𝕜) (i : n) :
    ‖v i‖ ≤ ‖v (deimPivot v)‖ :=
  (Finset.exists_max_image univ (fun i => ‖v i‖) univ_nonempty).choose_spec.2 i (mem_univ i)

/-- A nonzero residual has a nonzero pivot. -/
theorem deimPivot_ne_zero [Nonempty n] {v : n → 𝕜} (hv : v ≠ 0) :
    v (deimPivot v) ≠ 0 := by
  intro hz
  apply hv
  funext i
  have hi := norm_le_norm_deimPivot v i
  rw [hz, norm_zero] at hi
  exact norm_eq_zero.mp (le_antisymm hi (norm_nonneg _))

/-- DEIM's residual vanishes at all earlier sampled coordinates. -/
theorem deimResidual_apply_indices {U : Matrix n (Fin r) 𝕜} {k : ℕ} (hk : k < r)
    (indices : Fin k → n) (hM : IsUnit (deimSampleMatrix U k hk.le indices)) (i : Fin k) :
    deimResidual U k hk indices (indices i) = 0 := by
  have hright : deimSampleMatrix U k hk.le indices *
      (deimSampleMatrix U k hk.le indices)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM)
  have he := congr_fun (congrArg (fun M => M *ᵥ (fun j => U (indices j) ⟨k, hk⟩)) hright) i
  simp only [Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at he
  change U (indices i) ⟨k, hk⟩ - _ = 0
  exact sub_eq_zero.mpr he.symm

/-- Orthonormal columns prevent the next residual from being zero. -/
theorem deimResidual_ne_zero {U : Matrix n (Fin r) 𝕜} (hU : HasOrthonormalCols U)
    {k : ℕ} (hk : k < r) (indices : Fin k → n) : deimResidual U k hk indices ≠ 0 := by
  intro hz
  have he : U.col ⟨k, hk⟩ = deimPrefix U k hk.le *ᵥ
      ((deimSampleMatrix U k hk.le indices)⁻¹ *ᵥ (fun i => U (indices i) ⟨k, hk⟩)) :=
    sub_eq_zero.mp hz
  apply hU.linearIndependent_col.notMem_span ⟨k, hk⟩
  rw [he, mulVec_eq_sum_smul_col]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨Fin.castLE hk.le i, ?_, rfl⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro heq
  have hv := congrArg Fin.val heq
  simp only [Fin.val_castLE] at hv
  have := i.isLt
  omega

/-- Extending the selected rows by a nonzero DEIM residual preserves
nonsingularity. The scalar Schur complement is precisely that residual. -/
theorem isUnit_deimSampleMatrix_snoc {U : Matrix n (Fin r) 𝕜}
    {k : ℕ} (hk : k < r) (indices : Fin k → n)
    (hM : IsUnit (deimSampleMatrix U k hk.le indices)) (pivot : n)
    (hp : deimResidual U k hk indices pivot ≠ 0) :
    IsUnit (deimSampleMatrix U (k + 1) (by omega) (Fin.snoc indices pivot)) := by
  let M := deimSampleMatrix U k hk.le indices
  let B : Matrix (Fin k) (Fin 1) 𝕜 := fun i _ => U (indices i) ⟨k, hk⟩
  let C : Matrix (Fin 1) (Fin k) 𝕜 := fun _ j => U pivot (Fin.castLE hk.le j)
  let D : Matrix (Fin 1) (Fin 1) 𝕜 := fun _ _ => U pivot ⟨k, hk⟩
  let S₁ : Matrix (Fin 1) (Fin 1) 𝕜 := Matrix.of fun _ _ => deimResidual U k hk indices pivot
  let e : Fin k ⊕ Fin 1 ≃ Fin (k + 1) := finSumFinEquiv
  have hcast (i : Fin k) : Fin.castAdd 1 i = i.castSucc := rfl
  have hlast : Fin.natAdd k (0 : Fin 1) = Fin.last k := rfl
  have hcolLast : Fin.castLE (by omega : k + 1 ≤ r) (Fin.last k) = (⟨k, hk⟩ : Fin r) :=
    Fin.ext rfl
  have hblock : (deimSampleMatrix U (k + 1) (by omega) (Fin.snoc indices pivot)).submatrix e e =
      Matrix.fromBlocks M B C D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [deimSampleMatrix, M, e, finSumFinEquiv, hcast]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [deimSampleMatrix, B, e, finSumFinEquiv, hcast, hlast, hcolLast]
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [deimSampleMatrix, C, e, finSumFinEquiv, hcast, hlast]
    · have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i j
      simp [deimSampleMatrix, D, e, finSumFinEquiv, hcast, hlast, hcolLast]
  letI : Invertible M := hM.invertible
  have hschur : D - C * ⅟M * B = S₁ := by
    ext i j
    rw [Matrix.mul_assoc, Matrix.invOf_eq_nonsing_inv]
    simp only [D, C, B, deimResidual, deimPrefix, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.submatrix_apply, id_eq, Pi.sub_apply, Matrix.col, Matrix.mulVec, dotProduct]
    rfl
  have hscalar : IsUnit S₁ := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simpa [S₁, Matrix.det_unique] using (isUnit_iff_ne_zero.mpr hp)
  have hbig : IsUnit (Matrix.fromBlocks M B C D) :=
    Matrix.isUnit_fromBlocks_iff_of_invertible₁₁.mpr (hschur ▸ hscalar)
  rw [← hblock] at hbig
  exact (Matrix.isUnit_submatrix_equiv e e).mp hbig

/-- The actual sequential DEIM choice, starting with no selected rows. -/
def deimIndices [Nonempty n] (U : Matrix n (Fin r) 𝕜) :
    (k : ℕ) → k ≤ r → Fin k → n
  | 0, _ => Fin.elim0
  | k + 1, hk =>
    let previous := deimIndices U k (by omega)
    Fin.snoc previous (deimPivot (deimResidual U k (by omega) previous))

/-- The actual greedy DEIM recursion never breaks down; every reached
sampled leading basis is nonsingular.
atlas: deim-greedy-interpolation (partial) -/
theorem isUnit_deimSampleMatrix_deimIndices [Nonempty n]
    {U : Matrix n (Fin r) 𝕜} (hU : HasOrthonormalCols U) (k : ℕ) (hk : k ≤ r) :
    IsUnit (deimSampleMatrix U k hk (deimIndices U k hk)) := by
  induction k with
  | zero =>
    have he : deimSampleMatrix U 0 hk (deimIndices U 0 hk) = 1 := by
      ext i; exact i.elim0
    rw [he]
    exact isUnit_one
  | succ k ih =>
    apply isUnit_deimSampleMatrix_snoc (by omega) _ (ih (by omega))
    exact deimPivot_ne_zero (deimResidual_ne_zero hU (by omega) _)

/-- DEIM chooses distinct coordinates at every stage, since the current
residual is zero on all previous choices and nonzero at its new pivot.
atlas: deim-greedy-interpolation (partial) -/
theorem deimIndices_injective [Nonempty n] {U : Matrix n (Fin r) 𝕜}
    (hU : HasOrthonormalCols U) (k : ℕ) (hk : k ≤ r) :
    Function.Injective (deimIndices U k hk) := by
  induction k with
  | zero => exact fun i => i.elim0
  | succ k ih =>
    let previous := deimIndices U k (by omega)
    let residual := deimResidual U k (by omega) previous
    have hp : residual (deimPivot residual) ≠ 0 :=
      deimPivot_ne_zero (deimResidual_ne_zero hU (by omega) previous)
    have hnew : ∀ i, previous i ≠ deimPivot residual := by
      intro i hi
      apply hp
      rw [← hi]
      exact deimResidual_apply_indices (by omega) previous
        (isUnit_deimSampleMatrix_deimIndices hU k (by omega)) i
    change Function.Injective (Fin.snoc previous (deimPivot residual))
    apply Fin.snoc_injective_iff.mpr
    refine ⟨ih (by omega), ?_⟩
    rintro ⟨i, hi⟩
    exact hnew i hi

end NLAlib
