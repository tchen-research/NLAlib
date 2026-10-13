import NLAlib.Matrix.Perturbation.SpectralFrameWeights
import NLAlib.Matrix.Perturbation.SpectralWeightGap

/-!
# The invariant top/complement spectral decomposition

The named sorted frames satisfy exact invariant equations and their projectors
sum to the identity. These identities retain zero and full prefix endpoints.
Source: Horn–Johnson (2013), §4.3; supports `davis-kahan-sin-theta`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- The complete sorted spectral frame satisfies its diagonal invariant
equation. Horn–Johnson (2013), §4.3. -/
theorem mul_sortedEigenframe_eq_mul_diagonal (hA : A.IsHermitian) :
    A*sortedEigenframe hA=sortedEigenframe hA*Matrix.diagonal hA.eigenvalues₀ := by
  calc
    _ = (sortedEigenframe hA*Matrix.diagonal hA.eigenvalues₀*(sortedEigenframe hA)ᵀ)*sortedEigenframe hA :=
      congrArg (fun T => T*sortedEigenframe hA) (eq_sortedEigenframe_mul_diagonal_mul_transpose hA)
    _ = _ := by rw [Matrix.mul_assoc, (hasOrthonormalCols_sortedEigenframe hA).transpose_mul_self,
      Matrix.mul_one]

omit [DecidableEq n] in
/-- Selecting any columns from an invariant diagonal frame gives the actual
selected diagonal invariant equation. Horn–Johnson (2013), §4.3. -/
theorem mul_submatrix_cols_eq_mul_diagonal {N r : Type*} [Fintype N] [Fintype r]
    [DecidableEq N] [DecidableEq r] (U : Matrix n N ℝ) (d : N → ℝ)
    (e : r → N) (hU : A*U=U*Matrix.diagonal d) :
    A*U.submatrix id e=U.submatrix id e*Matrix.diagonal (d ∘ e) := by
  have hmul : A*U.submatrix id e=(A*U).submatrix id e := by
    simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
      Matrix.submatrix_mul_equiv A U id (Equiv.refl n) e
  rw [hmul, hU]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Function.comp_apply, id_eq]

/-- Top eigenframes satisfy the invariant equation with their actual sorted
prefix eigenvalues. Horn–Johnson (2013), §4.3. -/
theorem mul_topEigenframe_eq_mul_diagonal (hA : A.IsHermitian) {k : ℕ}
    (hk : k ≤ Fintype.card n) :
    A*topEigenframe hA hk=topEigenframe hA hk*
      Matrix.diagonal (fun i : Fin k => hA.eigenvalues₀ (Fin.castLE hk i)) := by
  exact mul_submatrix_cols_eq_mul_diagonal (sortedEigenframe hA) hA.eigenvalues₀
    (Fin.castLEEmb hk) (mul_sortedEigenframe_eq_mul_diagonal hA)

/-- Complementary eigenframes satisfy the invariant equation with the actual
remaining sorted eigenvalues. Horn–Johnson (2013), §4.3. -/
theorem mul_complementaryEigenframe_eq_mul_diagonal (hA : A.IsHermitian) {k : ℕ}
    (hk : k ≤ Fintype.card n) :
    A*complementaryEigenframe hA hk=complementaryEigenframe hA hk*
      Matrix.diagonal (fun i : Fin (Fintype.card n-k) =>
        hA.eigenvalues₀ ⟨i.val+k, by omega⟩) := by
  have hh := mul_submatrix_cols_eq_mul_diagonal (sortedEigenframe hA) hA.eigenvalues₀
    (Fin.natAdd_castLEEmb (Nat.sub_le (Fintype.card n) k)) (mul_sortedEigenframe_eq_mul_diagonal hA)
  change A*complementaryEigenframe hA hk=complementaryEigenframe hA hk*Matrix.diagonal _ at hh
  have heq : (hA.eigenvalues₀ ∘ (Fin.natAdd_castLEEmb (Nat.sub_le (Fintype.card n) k)))=
      (fun i : Fin (Fintype.card n-k) => hA.eigenvalues₀ ⟨i.val+k, by omega⟩) := by
    funext i
    apply congrArg hA.eigenvalues₀
    apply Fin.ext
    simp [Fin.natAdd_castLEEmb, Nat.sub_sub_self hk]
  rw [heq] at hh
  exact hh

/-- A finite suffix indicator sum equals the sum over its actual suffix
coordinates. Finite spectral-frame bookkeeping, including empty suffixes. -/
theorem sum_fin_ite_ge_eq_sum_suffix {N k : ℕ} (hk : k ≤ N) (f : Fin N → ℝ) :
    (∑ i : Fin N, if k ≤ i.val then f i else 0)=
      ∑ j : Fin (N-k), f ⟨j.val+k, by omega⟩ := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun j _ => (⟨j.val+k, by omega⟩ : Fin N))
  · intro j _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro i _ j _ hij
    apply Fin.ext
    have hh := congrArg Fin.val hij
    change i.val+k=j.val+k at hh
    omega
  · intro i hi
    have hik : k ≤ i.val := (Finset.mem_filter.mp hi).2
    refine ⟨⟨i.val-k, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change i.val-k+k=i.val
    omega
  · intro j _
    rfl

/-- Top and complementary eigenframe projectors sum to the identity, at every
admissible width including zero and the entire ambient space.
Horn–Johnson (2013), §4.3. -/
theorem topEigenframe_projector_add_complementary_eq_one (hA : A.IsHermitian)
    {k : ℕ} (hk : k ≤ Fintype.card n) :
    topEigenframe hA hk*(topEigenframe hA hk)ᵀ+
      complementaryEigenframe hA hk*(complementaryEigenframe hA hk)ᵀ=1 := by
  rw [← sortedEigenframe_mul_transpose_eq_one hA]
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, topEigenframe,
    complementaryEigenframe, Matrix.submatrix_apply, id_eq]
  have heq : (fun a : Fin (Fintype.card n-k) =>
      (Fin.natAdd_castLEEmb (Nat.sub_le (Fintype.card n) k)) a)=
      (fun a => (⟨a.val+k, by omega⟩ : Fin (Fintype.card n))) := by
    funext a
    apply Fin.ext
    simp [Fin.natAdd_castLEEmb, Nat.sub_sub_self hk]
  simp_rw [heq]
  change (∑ a : Fin k, sortedEigenframe hA i (Fin.castLE hk a)*sortedEigenframe hA j (Fin.castLE hk a))+
    (∑ a : Fin (Fintype.card n-k), sortedEigenframe hA i ⟨a.val+k, by omega⟩*
      sortedEigenframe hA j ⟨a.val+k, by omega⟩)=_
  have hp := sum_fin_ite_lt_eq_sum_prefix hk (fun a => sortedEigenframe hA i a*sortedEigenframe hA j a)
  have hs := sum_fin_ite_ge_eq_sum_suffix hk (fun a => sortedEigenframe hA i a*sortedEigenframe hA j a)
  rw [← hp, ← hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a.val<k
  · have hnot : ¬ k ≤ a.val := by omega
    simp [ha, hnot]
  · have hge : k ≤ a.val := by omega
    simp [ha, hge]

/-- Each eigenvalue of a real diagonal matrix is an actual diagonal entry.
Mathlib's diagonal spectrum theorem; supports spectral interval bounds. -/
theorem exists_eq_eigenvalues_diagonal {r : Type*} [Fintype r] [DecidableEq r]
    (d : r → ℝ) (i : r) :
    ∃ j, d j=(Matrix.isHermitian_diagonal d).eigenvalues i := by
  have hh := (Matrix.isHermitian_diagonal d).eigenvalues_mem_spectrum_real i
  rwa [spectrum_diagonal] at hh

end NLAlib
