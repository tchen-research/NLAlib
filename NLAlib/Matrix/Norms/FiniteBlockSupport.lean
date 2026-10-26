import NLAlib.Matrix.Norms.DependentBlockDiagonal
import Mathlib.Logic.Equiv.Sum

/-!
# Spectral norm bounds from finite block support

A matrix supported on equal fibers of a finite labeling is a dependent block
diagonal matrix after a coordinate permutation. This provides spectral-norm
bounds for disjointly supported blocks without requiring equal block sizes.
-/

noncomputable section

namespace NLAlib

/-- The spectral norm satisfies the three-term triangle inequality. -/
theorem specNorm_add_add_le {𝕜 m n : Type*} [RCLike 𝕜]
    [Fintype m] [Fintype n] [DecidableEq n] (A B C : Matrix m n 𝕜) :
    specNorm (A + B + C) ≤ specNorm A + specNorm B + specNorm C :=
  (specNorm_add_le (A + B) C).trans (add_le_add (specNorm_add_le A B) le_rfl)

/-- A finite labeling with no cross-label entries gives a spectral norm bound
from the corresponding fiber compressions. Empty fibers are allowed. -/
theorem specNorm_le_of_fiber_compressions_le
    {𝕜 ι κ : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι ι 𝕜) (label : ι → κ)
    (hzero : ∀ i j, label i ≠ label j → A i j = 0) {c : ℝ} (hc : 0 ≤ c)
    (hblock : ∀ k, specNorm (A.submatrix
      (fun i : {i // label i = k} => i.val)
      (fun j : {j // label j = k} => j.val)) ≤ c) :
    specNorm A ≤ c := by
  classical
  let e := Equiv.sigmaFiberEquiv label
  let B (k : κ) : Matrix {i // label i = k} {j // label j = k} 𝕜 :=
    A.submatrix Subtype.val Subtype.val
  have hrep : A.reindex e.symm e.symm = Matrix.blockDiagonal' B := by
    ext ⟨k, i⟩ ⟨l, j⟩
    by_cases h : k = l
    · subst l
      simp [Matrix.reindex_apply, e, Equiv.sigmaFiberEquiv, B]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
      change A i.val j.val = 0
      apply hzero
      intro hlabel
      exact h (i.property.symm.trans (hlabel.trans j.property))
  calc
    specNorm A = specNorm (A.reindex e.symm e.symm) := (specNorm_reindex _ _ _).symm
    _ = specNorm (Matrix.blockDiagonal' B) := congrArg specNorm hrep
    _ ≤ c := specNorm_blockDiagonal'_le B hc hblock

/-- If every fiber compression agrees with a compression of a bounded block,
the whole matrix is bounded by the same constant. -/
theorem specNorm_le_of_fiber_block_bounds
    {𝕜 ι κ : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι ι 𝕜) (label : ι → κ)
    (hzero : ∀ i j, label i ≠ label j → A i j = 0)
    (B : κ → Matrix ι ι 𝕜)
    (heq : ∀ k i j, label i = k → label j = k → A i j = B k i j)
    {c : ℝ} (hc : 0 ≤ c) (hB : ∀ k, specNorm (B k) ≤ c) :
    specNorm A ≤ c := by
  apply specNorm_le_of_fiber_compressions_le A label hzero hc
  intro k
  have hrep : A.submatrix (fun i : {i // label i = k} => i.val)
      (fun j : {j // label j = k} => j.val) =
      (B k).submatrix Subtype.val Subtype.val := by
    ext i j
    exact heq k i.val j.val i.property j.property
  rw [hrep]
  exact (specNorm_submatrix_le (B k) Subtype.val Subtype.val
    Subtype.val_injective Subtype.val_injective).trans (hB k)

/-- A matrix supported on disjoint coordinate blocks is bounded by any common
bound on its blocks, even if some coordinates lie outside every block. -/
theorem specNorm_le_of_disjoint_block_bounds
    {𝕜 ι κ : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι ι 𝕜) (P : κ → ι → Prop)
    (hunique : ∀ i k l, P k i → P l i → k = l)
    (hsupport : ∀ i j, A i j ≠ 0 → ∃ k, P k i ∧ P k j)
    (B : κ → Matrix ι ι 𝕜)
    (heq : ∀ k i j, P k i → P k j → A i j = B k i j)
    {c : ℝ} (hc : 0 ≤ c) (hB : ∀ k, specNorm (B k) ≤ c) :
    specNorm A ≤ c := by
  classical
  let label (i : ι) : Option κ := if h : ∃ k, P k i then some (Classical.choose h) else none
  have hsome {i : ι} {k : κ} (hi : P k i) : label i = some k := by
    have hex : ∃ l, P l i := ⟨k, hi⟩
    simp only [label, dif_pos hex]
    exact congrArg some (hunique i _ k (Classical.choose_spec hex) hi)
  have hmem {i : ι} {k : κ} (hi : label i = some k) : P k i := by
    dsimp [label] at hi
    split_ifs at hi with h
    exact (Option.some.inj hi) ▸ Classical.choose_spec h
  let B' : Option κ → Matrix ι ι 𝕜 := fun k => k.elim 0 B
  refine specNorm_le_of_fiber_block_bounds A label ?_ B' ?_ hc ?_
  · intro i j hne
    by_contra hij
    obtain ⟨k, hi, hj⟩ := hsupport i j hij
    exact hne ((hsome hi).trans (hsome hj).symm)
  · intro k i j hi hj
    cases k with
    | none =>
        change A i j = 0
        by_contra hij
        obtain ⟨l, hil, _⟩ := hsupport i j hij
        have h := (hsome hil).symm.trans hi
        cases h
    | some k => exact heq k i j (hmem hi) (hmem hj)
  · intro k
    cases k with
    | none => simpa [B', specNorm_zero] using hc
    | some k => exact hB k

end NLAlib
