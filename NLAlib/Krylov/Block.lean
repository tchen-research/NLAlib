import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.Span
import NLAlib.Krylov.Polynomial
import NLAlib.Matrix.Projections

/-!
# Block Krylov subspaces and subspace iteration

For `A : Matrix n n ℝ` and a starting block `Ω : Matrix n s ℝ`,

* `NLAlib.blockKrylovSpace A Ω q = span {(A^i Ω) e_j : i < q, j ∈ s}
  = range [Ω, AΩ, …, A^(q−1)Ω]`, with
  `blockKrylovSpace_eq_iSup` (the sum of the single-vector spaces `K_q(A, Ω e_j)`),
  `mem_blockKrylovSpace_iff` (the matrix-polynomial characterisation
  `x = ∑_j p_j(A) Ω e_j`, `deg p_j < q`), `range_aeval_mul_le_blockKrylovSpace`
  (`range (p(A) Ω) ⊆ K_q(A, Ω)` for `deg p < q`, the form Musco–Musco use),
  `krylovSpace_col_le_blockKrylovSpace`, monotonicity, `A K_q ⊆ K_{q+1}` and `dim K_q ≤ q s`;
* `NLAlib.subspaceIterate A Ω k = range (A^k Ω)`, the `k`-th subspace (orthogonal) iterate, with
  `subspaceIterate_le_blockKrylovSpace` (`S_k ⊆ K_{k+1}(A, Ω)`), `subspaceIterate_succ`
  (`S_{k+1} = A S_k`), `range_mul_eq_subspaceIterate_succ` (orthonormalising does not change the
  next iterate: any basis of `S_k` is a witness), invariance under `Ω ↦ Ω R` for invertible `R`,
  and basis independence of the compression `Qᵀ A Q` up to orthogonal similarity
  (`transpose_mul_mul_eq_of_range_le`).

The rectangular block space of low-rank approximation, `K_q(AAᵀ, AΩ)`, is
`blockKrylovSpace (A * Aᵀ) (A * Ω) q`; no separate definition is needed.

Source: Musco–Musco (2015) [`mm15`], Alg. 2; Tropp–Webber (2023) [`tw23`], §7; Saad (2011)
[`saad11`], §5.1 and §6.3; Golub–Van Loan (2013) [`gvl13`], §8.2.4.
Atlas: `block-krylov-subspace`, `subspace-iteration-def`.
-/

noncomputable section

open scoped Matrix Polynomial
open Polynomial

namespace NLAlib

variable {n s : Type*} [Fintype n] [DecidableEq n] [Fintype s]

/-! ### Block Krylov spaces -/

/-- The block Krylov subspace `K_q(A, Ω) = span {(A^i Ω) e_j : i < q, j ∈ s}`, the range of
`[Ω, AΩ, …, A^(q−1)Ω]`. Source: Musco–Musco (2015) [`mm15`], Alg. 2; Saad (2011) [`saad11`],
§6.3.
atlas: block-krylov-subspace -/
def blockKrylovSpace (A : Matrix n n ℝ) (Ω : Matrix n s ℝ) (q : ℕ) : Submodule ℝ (n → ℝ) :=
  Submodule.span ℝ (Set.range fun ij : Fin q × s => ((A ^ (ij.1 : ℕ)) * Ω).col ij.2)

omit [DecidableEq n] [Fintype s] in
/-- Column `j` of a product is the matrix applied to column `j`: `(M Ω) e_j = M (Ω e_j)`.
Helper for `block-krylov-subspace`. -/
theorem col_mul_eq_mulVec_col {m : Type*} (M : Matrix m n ℝ) (Ω : Matrix n s ℝ) (j : s) :
    (M * Ω).col j = M *ᵥ Ω.col j := by
  ext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

omit [Fintype s] in
/-- The generators `(A^i Ω) e_j` (`i < q`) lie in `K_q(A, Ω)`. Helper for
`block-krylov-subspace`. -/
theorem pow_mulVec_col_mem_blockKrylovSpace (A : Matrix n n ℝ) (Ω : Matrix n s ℝ) {q i : ℕ}
    (hi : i < q) (j : s) : (A ^ i) *ᵥ Ω.col j ∈ blockKrylovSpace A Ω q := by
  rw [← col_mul_eq_mulVec_col]
  exact Submodule.subset_span ⟨(⟨i, hi⟩, j), rfl⟩

omit [Fintype s] in
/-- The Krylov space of a single column is contained in the block space:
`K_q(A, Ω e_j) ⊆ K_q(A, Ω)`. Source: Saad (2011) [`saad11`], §6.3.
atlas: block-krylov-subspace -/
theorem krylovSpace_col_le_blockKrylovSpace (A : Matrix n n ℝ) (Ω : Matrix n s ℝ) (q : ℕ)
    (j : s) : krylovSpace A (Ω.col j) q ≤ blockKrylovSpace A Ω q :=
  Submodule.span_le.2 <| by
    rintro _ ⟨i, rfl⟩
    exact pow_mulVec_col_mem_blockKrylovSpace A Ω i.isLt j

omit [Fintype s] in
/-- The block Krylov space is the sum of the single-vector Krylov spaces of the columns:
`K_q(A, Ω) = ∑_j K_q(A, Ω e_j)`. Source: Saad (2011) [`saad11`], §6.3.
atlas: block-krylov-subspace -/
theorem blockKrylovSpace_eq_iSup (A : Matrix n n ℝ) (Ω : Matrix n s ℝ) (q : ℕ) :
    blockKrylovSpace A Ω q = ⨆ j, krylovSpace A (Ω.col j) q := by
  refine le_antisymm (Submodule.span_le.2 ?_) (iSup_le (krylovSpace_col_le_blockKrylovSpace A Ω q))
  rintro _ ⟨⟨i, j⟩, rfl⟩
  refine Submodule.mem_iSup_of_mem j ?_
  change ((A ^ (i : ℕ)) * Ω).col j ∈ _
  rw [col_mul_eq_mulVec_col]
  exact pow_mulVec_mem_krylovSpace A _ i.isLt

/-- Matrix-polynomial characterisation of the block Krylov space (valid for every `q`):
`x ∈ K_q(A, Ω) ↔ x = ∑_j p_j(A) Ω e_j` for polynomials `p_j` of degree `< q`. Equivalently
`x = ∑_{i<q} A^i Ω c_i`. Source: Saad (2011) [`saad11`], §6.3; Tropp–Webber (2023) [`tw23`], §7.
atlas: block-krylov-subspace -/
theorem mem_blockKrylovSpace_iff (A : Matrix n n ℝ) (Ω : Matrix n s ℝ) (q : ℕ) (x : n → ℝ) :
    x ∈ blockKrylovSpace A Ω q ↔
      ∃ p : s → ℝ[X], (∀ j, (p j).degree < q) ∧ x = ∑ j, aeval A (p j) *ᵥ Ω.col j := by
  classical
  rw [blockKrylovSpace_eq_iSup]
  constructor
  · intro hx
    obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).1 hx
    have h : ∀ j, ∃ p : ℝ[X], p.degree < q ∧ f j = aeval A p *ᵥ Ω.col j := fun j =>
      (mem_krylovSpace_iff_degree A _ q _).1 (hf j)
    choose p hpdeg hp using h
    refine ⟨p, hpdeg, ?_⟩
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact Finset.sum_congr rfl fun j _ => hp j
  · rintro ⟨p, hp, rfl⟩
    refine Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ?_
    exact (mem_krylovSpace_iff_degree A _ q _).2 ⟨p j, hp j, rfl⟩

/-- `range (p(A) Ω) ⊆ K_q(A, Ω)` for every scalar polynomial `p` with `deg p < q`: the form used
by block Krylov low-rank approximation. Source: Musco–Musco (2015) [`mm15`], proof of Thm 1;
Tropp–Webber (2023) [`tw23`], §7.
atlas: block-krylov-subspace -/
theorem range_aeval_mul_le_blockKrylovSpace (A : Matrix n n ℝ) (Ω : Matrix n s ℝ) {q : ℕ}
    {p : ℝ[X]} (hp : p.degree < q) :
    LinearMap.range (aeval A p * Ω).mulVecLin ≤ blockKrylovSpace A Ω q := by
  rw [Matrix.range_mulVecLin, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [col_mul_eq_mulVec_col]
  exact krylovSpace_col_le_blockKrylovSpace A Ω q j
    ((mem_krylovSpace_iff_degree A _ q _).2 ⟨p, hp, rfl⟩)

omit [Fintype s] in
/-- Block Krylov spaces are nested: `q ≤ q' → K_q(A, Ω) ⊆ K_{q'}(A, Ω)`.
Source: Saad (2011) [`saad11`], §6.3.
atlas: block-krylov-subspace -/
theorem blockKrylovSpace_mono (A : Matrix n n ℝ) (Ω : Matrix n s ℝ) {q q' : ℕ} (h : q ≤ q') :
    blockKrylovSpace A Ω q ≤ blockKrylovSpace A Ω q' :=
  Submodule.span_le.2 <| by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    change ((A ^ (i : ℕ)) * Ω).col j ∈ _
    rw [col_mul_eq_mulVec_col]
    exact pow_mulVec_col_mem_blockKrylovSpace A Ω (lt_of_lt_of_le i.isLt h) j

omit [Fintype s] in
/-- `A K_q(A, Ω) ⊆ K_{q+1}(A, Ω)`. Source: Saad (2011) [`saad11`], §6.3.
atlas: block-krylov-subspace -/
theorem mulVec_mem_blockKrylovSpace_succ (A : Matrix n n ℝ) (Ω : Matrix n s ℝ) {q : ℕ}
    {x : n → ℝ} (hx : x ∈ blockKrylovSpace A Ω q) : A *ᵥ x ∈ blockKrylovSpace A Ω (q + 1) := by
  have hle : blockKrylovSpace A Ω q ≤
      (blockKrylovSpace A Ω (q + 1)).comap (Matrix.mulVecLin A) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨i, j⟩, rfl⟩
    change A *ᵥ ((A ^ (i : ℕ)) * Ω).col j ∈ blockKrylovSpace A Ω (q + 1)
    rw [col_mul_eq_mulVec_col, Matrix.mulVec_mulVec, ← pow_succ']
    exact pow_mulVec_col_mem_blockKrylovSpace A Ω (Nat.succ_lt_succ i.isLt) j
  exact hle hx

/-- `dim K_q(A, Ω) ≤ q s` for `Ω` with `s` columns. Source: Saad (2011) [`saad11`], §6.3.
atlas: block-krylov-subspace -/
theorem finrank_blockKrylovSpace_le (A : Matrix n n ℝ) (Ω : Matrix n s ℝ) (q : ℕ) :
    Module.finrank ℝ (blockKrylovSpace A Ω q) ≤ q * Fintype.card s :=
  (finrank_range_le_card (R := ℝ) _).trans (by simp)

/-! ### Subspace iteration -/

/-- The `k`-th subspace iterate `S_k = range (A^k Ω)` of subspace (orthogonal, simultaneous)
iteration started from the block `Ω`. Orthonormalisation is bookkeeping: any `Q` with
`range Q = S_k` is a basis the algorithm may carry (`range_mul_eq_subspaceIterate_succ`).
Source: Saad (2011) [`saad11`], §5.1; Golub–Van Loan (2013) [`gvl13`], §8.2.4.
atlas: subspace-iteration-def -/
def subspaceIterate (A : Matrix n n ℝ) (Ω : Matrix n s ℝ) (k : ℕ) : Submodule ℝ (n → ℝ) :=
  LinearMap.range (A ^ k * Ω).mulVecLin

/-- `S_0 = range Ω`. Helper for `subspace-iteration-def`. -/
@[simp]
theorem subspaceIterate_zero (A : Matrix n n ℝ) (Ω : Matrix n s ℝ) :
    subspaceIterate A Ω 0 = LinearMap.range Ω.mulVecLin := by
  simp [subspaceIterate]

/-- One step of subspace iteration: `S_{k+1} = A S_k`. Source: Saad (2011) [`saad11`], §5.1.
atlas: subspace-iteration-def -/
theorem subspaceIterate_succ (A : Matrix n n ℝ) (Ω : Matrix n s ℝ) (k : ℕ) :
    subspaceIterate A Ω (k + 1) = (subspaceIterate A Ω k).map A.mulVecLin := by
  rw [subspaceIterate, subspaceIterate, pow_succ', Matrix.mul_assoc, Matrix.mulVecLin_mul,
    LinearMap.range_comp]

/-- Orthonormalisation does not change the iteration: if the columns of `Q` span `S_k` (for
instance `Q` is an orthonormal basis of `S_k`), then `range (A Q) = S_{k+1}`. Source: Saad (2011)
[`saad11`], §5.1, Alg. 5.1.
atlas: subspace-iteration-def -/
theorem range_mul_eq_subspaceIterate_succ {k' : Type*} [Fintype k'] (A : Matrix n n ℝ)
    (Ω : Matrix n s ℝ) {k : ℕ} {Q : Matrix n k' ℝ}
    (hQ : LinearMap.range Q.mulVecLin = subspaceIterate A Ω k) :
    LinearMap.range (A * Q).mulVecLin = subspaceIterate A Ω (k + 1) := by
  rw [subspaceIterate_succ, ← hQ, Matrix.mulVecLin_mul, LinearMap.range_comp]

/-- Subspace iteration is block Krylov with the fixed polynomial `x^k`:
`S_k = range (A^k Ω) ⊆ K_{k+1}(A, Ω)`. Source: Saad (2011) [`saad11`], §5.1 and §6.3;
Musco–Musco (2015) [`mm15`], §4.
atlas: subspace-iteration-def -/
theorem subspaceIterate_le_blockKrylovSpace (A : Matrix n n ℝ) (Ω : Matrix n s ℝ) (k : ℕ) :
    subspaceIterate A Ω k ≤ blockKrylovSpace A Ω (k + 1) := by
  have h := range_aeval_mul_le_blockKrylovSpace A Ω (q := k + 1) (p := X ^ k)
    (by rw [degree_X_pow]; exact_mod_cast Nat.lt_succ_self k)
  simpa [subspaceIterate] using h

/-- Right multiplication of the starting block can only shrink the iterates:
`range (A^k Ω R) ⊆ range (A^k Ω)`. Helper for `subspace-iteration-def`. -/
theorem subspaceIterate_mul_le {s' : Type*} [Fintype s'] (A : Matrix n n ℝ) (Ω : Matrix n s ℝ)
    (R : Matrix s s' ℝ) (k : ℕ) : subspaceIterate A (Ω * R) k ≤ subspaceIterate A Ω k := by
  rw [subspaceIterate, subspaceIterate, ← Matrix.mul_assoc, Matrix.mulVecLin_mul,
    LinearMap.range_comp]
  exact LinearMap.map_le_range

/-- Subspace iteration depends only on `range Ω`: `S_k(A, Ω R) = S_k(A, Ω)` for invertible `R`.
Source: Saad (2011) [`saad11`], §5.1.
atlas: subspace-iteration-def -/
theorem subspaceIterate_mul_of_isUnit [DecidableEq s] (A : Matrix n n ℝ) (Ω : Matrix n s ℝ)
    {R : Matrix s s ℝ} (hR : IsUnit R) (k : ℕ) :
    subspaceIterate A (Ω * R) k = subspaceIterate A Ω k := by
  refine le_antisymm (subspaceIterate_mul_le A Ω R k) ?_
  have h := subspaceIterate_mul_le A (Ω * R) R⁻¹ k
  rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).1 hR),
    Matrix.mul_one] at h

omit [Fintype s] [DecidableEq n] in
/-- Basis independence of the Rayleigh–Ritz compression: if `Q` and `Q'` have orthonormal
columns and `range Q' ⊆ range Q`, then `U = Qᵀ Q'` has orthonormal columns and
`Q'ᵀ A Q' = Uᵀ (Qᵀ A Q) U`. When the ranges are equal and `Q, Q'` have the same number of
columns, `U` is orthogonal, so the compression of `A` to `S_k` (and its Ritz values) does not
depend on the orthonormal basis chosen. Source: Saad (2011) [`saad11`], §4.3 and §5.1.
atlas: subspace-iteration-def (partial) -/
theorem transpose_mul_mul_eq_of_range_le {k₁ k₂ : Type*} [Fintype k₁] [DecidableEq k₁]
    [Fintype k₂] [DecidableEq k₂] {Q : Matrix n k₁ ℝ} {Q' : Matrix n k₂ ℝ}
    (hQ : HasOrthonormalCols Q) (hQ' : HasOrthonormalCols Q')
    (hle : LinearMap.range Q'.mulVecLin ≤ LinearMap.range Q.mulVecLin) (A : Matrix n n ℝ) :
    HasOrthonormalCols (Qᵀ * Q') ∧
      Q'ᵀ * A * Q' = (Qᵀ * Q')ᵀ * (Qᵀ * A * Q) * (Qᵀ * Q') := by
  have hQQ : Qᵀ * Q = 1 := hQ
  -- `Q Qᵀ Q' = Q'`, column by column
  have hcol : ∀ j, (Q * (Qᵀ * Q')).col j = Q'.col j := by
    intro j
    obtain ⟨z, hz⟩ := hle (show Q'.col j ∈ LinearMap.range Q'.mulVecLin from by
      rw [Matrix.range_mulVecLin]; exact Submodule.subset_span ⟨j, rfl⟩)
    simp only [Matrix.mulVecLin_apply] at hz
    rw [col_mul_eq_mulVec_col, col_mul_eq_mulVec_col, ← hz, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have hproj : Q * (Qᵀ * Q') = Q' := by
    ext i j
    exact congrFun (hcol j) i
  have hproj' : Q'ᵀ * Q * Qᵀ = Q'ᵀ := by
    have h := congrArg Matrix.transpose hproj
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using h
  refine ⟨?_, ?_⟩
  · change (Qᵀ * Q')ᵀ * (Qᵀ * Q') = 1
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [show Q'ᵀ * Q * (Qᵀ * Q') = Q'ᵀ * (Q * (Qᵀ * Q')) by simp only [Matrix.mul_assoc],
      hproj]
    exact hQ'
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc Q'ᵀ * A * Q' = (Q'ᵀ * Q * Qᵀ) * A * (Q * (Qᵀ * Q')) := by rw [hproj, hproj']
      _ = Q'ᵀ * Q * (Qᵀ * A * Q) * (Qᵀ * Q') := by simp only [Matrix.mul_assoc]

end NLAlib
