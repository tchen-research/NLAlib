import NLAlib.Matrix.Spectral.GershgorinBasic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# Irreducible weak diagonal dominance

Equality at a largest nullvector coordinate propagates along every nonzero
entry to a strictly dominant row. Source: Horn–Johnson (2013), Theorem 6.2.27
(Taussky), with the necessary hypothesis that at least one row is strict.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {K n : Type*} [NormedField K] [Fintype n] [DecidableEq n]

/-- At a nullvector coordinate, the diagonal contribution is bounded by the
weighted off-diagonal sum. This is the row estimate in the Taussky proof
for `gershgorin-diagonal-dominance`. -/
theorem norm_diagonal_mul_le_of_mulVec_eq_zero {A : Matrix n n K} {v : n → K}
    (hv : A *ᵥ v = 0) (i : n) :
    ‖A i i‖ * ‖v i‖ ≤ ∑ j ∈ Finset.univ.erase i, ‖A i j‖ * ‖v j‖ := by
  have hsum : ∑ j ∈ Finset.univ.erase i, A i j * v j = -(A i i * v i) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    have hrow := congrFun hv i
    change (∑ j, A i j * v j) = 0 at hrow
    rw [hrow, zero_sub]
  calc
    ‖A i i‖ * ‖v i‖ = ‖-(A i i * v i)‖ := by rw [norm_neg, norm_mul]
    _ = ‖∑ j ∈ Finset.univ.erase i, A i j * v j‖ := congrArg norm hsum.symm
    _ ≤ ∑ j ∈ Finset.univ.erase i, ‖A i j * v j‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul]

/-- A maximal nullvector coordinate propagates along every nonzero matrix
entry under weak row diagonal dominance. This is the equality-propagation
step in Horn–Johnson (2013), Theorem 6.2.27. -/
theorem norm_eq_max_of_mulVec_eq_zero_of_entry_ne_zero
    {A : Matrix n n K} {v : n → K} {M : ℝ} (hv : A *ᵥ v = 0)
    (hweak : ∀ i, gershgorinRowRadius A i ≤ ‖A i i‖)
    (hmax : ∀ i, ‖v i‖ ≤ M) {i j : n} (hi : ‖v i‖ = M) (hij : A i j ≠ 0) :
    ‖v j‖ = M := by
  by_cases heq : j = i
  · simpa only [heq] using hi
  have hM : 0 ≤ M := hi ▸ norm_nonneg (v i)
  have hbound := norm_diagonal_mul_le_of_mulVec_eq_zero hv i
  rw [hi] at hbound
  have hsum : ∑ k ∈ Finset.univ.erase i, ‖A i k‖ * ‖v k‖ =
      ∑ k ∈ Finset.univ.erase i, ‖A i k‖ * M := by
    apply le_antisymm
    · exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hmax k) (norm_nonneg _))
    · rw [← Finset.sum_mul]
      exact (mul_le_mul_of_nonneg_right (hweak i) hM).trans hbound
  have hzero : ∑ k ∈ Finset.univ.erase i, ‖A i k‖ * (M - ‖v k‖) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← hsum, sub_self]
  have hterm : ‖A i j‖ * (M - ‖v j‖) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      mul_nonneg (norm_nonneg _) (sub_nonneg.mpr (hmax k)))).mp hzero j
        (Finset.mem_erase.mpr ⟨heq, Finset.mem_univ _⟩)
  have := (mul_eq_zero.mp hterm).resolve_left (norm_ne_zero_iff.mpr hij)
  linarith

/-- An irreducible weakly row diagonally dominant matrix with at least one
strict row is nonsingular. Source: Horn–Johnson (2013), Theorem 6.2.27
(Taussky); irreducibility uses Mathlib's strongly connected graph of the
entrywise norms, so no sign condition is imposed on the original matrix.
atlas: gershgorin-diagonal-dominance -/
theorem det_ne_zero_of_irreducible_weak_diagonal_dominance
    (A : Matrix n n K) (hIrred : (A.map norm).IsIrreducible)
    (hweak : ∀ i, gershgorinRowRadius A i ≤ ‖A i i‖)
    (hstrict : ∃ i, gershgorinRowRadius A i < ‖A i i‖) : A.det ≠ 0 := by
  intro hdet
  have heig : Module.End.HasEigenvalue (Matrix.toLin' A) 0 := by
    rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_zero, ne_comm]
    exact ne_of_lt (LinearMap.bot_lt_ker_of_det_eq_zero (by rwa [LinearMap.det_toLin']))
  obtain ⟨v, hv, hvne⟩ := heig.exists_hasEigenvector
  have hAv : A *ᵥ v = 0 := by
    simpa only [Matrix.toLin'_apply, zero_smul] using Module.End.mem_eigenspace_iff.mp hv
  obtain ⟨s, hs⟩ := hstrict
  let : Nonempty n := ⟨s⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => ‖v i‖)
  have hmax (j : n) : ‖v j‖ ≤ ‖v i‖ := hi ▸ Finset.le_sup' (fun i => ‖v i‖) (Finset.mem_univ j)
  have hpos : 0 < ‖v i‖ := by
    by_contra! h
    apply hvne
    ext j
    exact norm_eq_zero.mp (le_antisymm ((hmax j).trans h) (norm_nonneg _))
  let : Quiver n := Matrix.toQuiver (A.map norm)
  obtain ⟨p, _⟩ := hIrred.connected i s
  have hpath : ∀ {j : n} (q : Quiver.Path i j), ‖v j‖ = ‖v i‖ := by
    intro j q
    induction q with
    | nil => rfl
    | @cons b c q e ih =>
      exact norm_eq_max_of_mulVec_eq_zero_of_entry_ne_zero hAv hweak hmax ih
        (norm_pos_iff.mp e.down)
  have hprop := hpath p
  have hbound := norm_diagonal_mul_le_of_mulVec_eq_zero hAv s
  rw [hprop] at hbound
  have hsum : (∑ j ∈ Finset.univ.erase s, ‖A s j‖ * ‖v j‖) ≤
      gershgorinRowRadius A s * ‖v i‖ := by
    rw [gershgorinRowRadius, Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hmax j) (norm_nonneg _))
  exact (not_lt_of_ge (hbound.trans hsum)) (mul_lt_mul_of_pos_right hs hpos)

end NLAlib
