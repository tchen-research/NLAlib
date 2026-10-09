import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Rank
import NLAlib.Matrix.Norms

/-!
# Singular value decomposition

Every real matrix `A : Matrix (Fin m) (Fin n) ℝ` factors as `A = U Σ Vᵀ` with `U`, `V`
orthogonal and `Σ = rectDiag (singularValues A)` rectangular diagonal with nonnegative,
non-increasing diagonal (Horn–Johnson 2013, Thm 2.6.3; HMT 2011, §2.1).

## Conventions

* `NLAlib.singularValues A : ℕ → ℝ` is Mathlib's `LinearMap.singularValues` of the Euclidean
  linear map of `A`: **zero-indexed** (`σ 0` is the largest), nonnegative, antitone, and
  `σ k ≠ 0 ↔ k < A.rank`; in particular `σ k = 0` for `k ≥ min m n`. Indexing by `ℕ` (rather
  than `Fin (min m n)`) means the singular values of matrices of different shapes are compared
  without casts, a rank-`k` split is `k < ·` vs `k ≤ ·`, and the truncated SVD is
  `rectDiag (fun i => if i < k then σ i else 0)`.
* The singular values are a *function of `A`*, not an existential witness: `exists_isSVD` only
  chooses the singular vectors `U`, `V`.
* `NLAlib.rectDiag σ : Matrix (Fin m) (Fin n) ℝ` has entry `σ i` at `(i, i)` and `0` elsewhere.

## Main results

* `NLAlib.exists_isSVD`: `∃ U V, IsSVD A U V` (atlas `svd`).
* `NLAlib.IsSVD.transpose_mul_self`, `NLAlib.IsSVD.mul_transpose_self`: `AᵀA = V Σ² Vᵀ`,
  `AAᵀ = U Σ² Uᵀ`.
* `NLAlib.IsSVD.apply`: the entrywise outer-product expansion
  `A i j = ∑_{k < min m n} σ_k U_{ik} V_{jk}`.
* `NLAlib.frobSq_eq_sum_sq_singularValues`: `‖A‖_F² = ∑_{k < min m n} σ_k²`.
* `NLAlib.singularValues_ne_zero_iff`, `NLAlib.rank_eq_card_singularValues_ne_zero`: rank.
* `NLAlib.sq_singularValues_eq_eigenvalues₀`: `σ_k²` is the `k`-th largest eigenvalue of `AᵀA`.
* `NLAlib.IsSVD.eq_head_add_tail`: block split `A = U Σ_{<k} Vᵀ + U Σ_{≥k} Vᵀ`.
* `NLAlib.singularValues_eq_of_eq_mul_rectDiag_mul`: uniqueness of the singular values, hence
  `singularValues_transpose`, `singularValues_orthogonal_mul`, `singularValues_mul_orthogonal`.

The orthonormal completion of `{A vⱼ / σⱼ : σⱼ ≠ 0}` (atlas `orthonormal-completion`) is
Mathlib's `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`.

Atlas: `svd`.
-/

noncomputable section

open scoped Matrix
open Module Polynomial

namespace NLAlib

variable {m n : ℕ}

/-! ### Singular values -/

/-- The singular values `σ₀ ≥ σ₁ ≥ ⋯ ≥ 0` of a real matrix, zero-indexed, padded with zeros:
`σ k = √(λ_k(AᵀA))` for `k < n` and `σ k = 0` for `k ≥ n`. Defined as Mathlib's
`LinearMap.singularValues` of `Matrix.toEuclideanLin A`. Atlas `svd`
(Horn–Johnson 2013, §2.6; HMT 2011, §2.1). Deviation: zero-indexed, indexed by `ℕ`. -/
def singularValues (A : Matrix (Fin m) (Fin n) ℝ) : ℕ → ℝ :=
  fun k => (Matrix.toEuclideanLin A).singularValues k

/-- Bridge to Mathlib's `LinearMap.singularValues`. Atlas `svd`. -/
theorem singularValues_eq_linearMap (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    singularValues A k = (Matrix.toEuclideanLin A).singularValues k := rfl

/-- Singular values are nonnegative. Atlas `svd`. -/
theorem singularValues_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    0 ≤ singularValues A k :=
  LinearMap.singularValues_nonneg _ _

/-- Singular values are listed in non-increasing order. Atlas `svd`. -/
theorem singularValues_antitone (A : Matrix (Fin m) (Fin n) ℝ) :
    Antitone (singularValues A) :=
  fun _ _ h => LinearMap.singularValues_antitone _ h

/-- The nonzero singular values are exactly the first `rank A` ones
(Horn–Johnson 2013, Thm 2.6.3 / §2.6.1). Atlas `svd`. -/
theorem singularValues_ne_zero_iff (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    singularValues A k ≠ 0 ↔ k < A.rank := by
  unfold singularValues
  rw [← LinearMap.singularValues_pos_iff_ne_zero,
    LinearMap.singularValues_pos_iff_lt_finrank_range,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, ← Matrix.rank_eq_finrank_range_toLin]

/-- The positive singular values are exactly the first `rank A` ones. Atlas `svd`. -/
theorem singularValues_pos_iff (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    0 < singularValues A k ↔ k < A.rank := by
  rw [← singularValues_ne_zero_iff, (singularValues_nonneg A k).lt_iff_ne', ne_comm]

/-- `σ k = 0` once `k ≥ rank A`. Atlas `svd`. -/
theorem singularValues_eq_zero_of_rank_le (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ}
    (hk : A.rank ≤ k) : singularValues A k = 0 := by
  by_contra h
  exact absurd ((singularValues_ne_zero_iff A k).1 h) (not_lt.2 hk)

/-- `σ k = 0` once `k ≥ m` (number of rows). Atlas `svd`. -/
theorem singularValues_eq_zero_of_height_le (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ}
    (hk : m ≤ k) : singularValues A k = 0 :=
  singularValues_eq_zero_of_rank_le A (A.rank_le_height.trans hk)

/-- `σ k = 0` once `k ≥ n` (number of columns). Atlas `svd`. -/
theorem singularValues_eq_zero_of_width_le (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ}
    (hk : n ≤ k) : singularValues A k = 0 :=
  singularValues_eq_zero_of_rank_le A (A.rank_le_width.trans hk)

/-- `σ k = 0` once `k ≥ min m n`. Atlas `svd`. -/
theorem singularValues_eq_zero_of_min_le (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ}
    (hk : min m n ≤ k) : singularValues A k = 0 := by
  rcases le_total m n with h | h
  · exact singularValues_eq_zero_of_height_le A (by simpa [min_eq_left h] using hk)
  · exact singularValues_eq_zero_of_width_le A (by simpa [min_eq_right h] using hk)

/-- The rank is the number of nonzero singular values (Horn–Johnson 2013, §2.6.1).
Atlas `svd`. -/
theorem rank_eq_card_singularValues_ne_zero (A : Matrix (Fin m) (Fin n) ℝ) :
    A.rank = ((Finset.range (min m n)).filter fun k => singularValues A k ≠ 0).card := by
  have hr : A.rank ≤ min m n := le_min A.rank_le_height A.rank_le_width
  have : ((Finset.range (min m n)).filter fun k => singularValues A k ≠ 0) =
      Finset.range A.rank := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, singularValues_ne_zero_iff]
    exact ⟨fun h => h.2, fun h => ⟨h.trans_le hr, h⟩⟩
  rw [this, Finset.card_range]

/-- `σ k² = λ_k(AᵀA)` for `k < n`, in terms of Mathlib's sorted eigenvalues of the
self-adjoint operator `T† T`, `T = toEuclideanLin A`. Atlas `svd`. -/
theorem sq_singularValues_eq_eigenvalues_adjoint_comp_self (A : Matrix (Fin m) (Fin n) ℝ)
    (k : Fin n) :
    singularValues A k ^ 2 =
      (Matrix.toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvalues
        finrank_euclideanSpace_fin k :=
  (Matrix.toEuclideanLin A).sq_singularValues_fin finrank_euclideanSpace_fin k

/-- Sorted eigenvalues of a symmetric operator do not depend on how it or the dimension is
spelled. -/
private lemma eigenvalues_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T₁ T₂ : E →ₗ[ℝ] E} (h : T₁ = T₂) (h₁ : T₁.IsSymmetric)
    (h₂ : T₂.IsSymmetric) {n₁ n₂ : ℕ} (hn₁ : finrank ℝ E = n₁) (hn₂ : finrank ℝ E = n₂)
    (i : Fin n₁) :
    h₁.eigenvalues hn₁ i = h₂.eigenvalues hn₂ (Fin.cast (hn₁.symm.trans hn₂) i) := by
  subst h; subst hn₁; subst hn₂
  rfl

/-- The squared singular values are the eigenvalues of the Gram matrix `AᵀA`, in decreasing
order: `σ_k² = λ_k(AᵀA)`, with Mathlib's sorted `Matrix.IsHermitian.eigenvalues₀`
(Horn–Johnson 2013, §2.6). Atlas `svd`. -/
theorem sq_singularValues_eq_eigenvalues₀ (A : Matrix (Fin m) (Fin n) ℝ)
    (hAA : (Aᵀ * A).IsHermitian) (k : Fin n) :
    singularValues A k ^ 2 = hAA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm k) := by
  rw [sq_singularValues_eq_eigenvalues_adjoint_comp_self, Matrix.IsHermitian.eigenvalues₀]
  apply eigenvalues_congr
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]

/-! ### Rectangular diagonal matrices -/

/-- The `m × n` rectangular diagonal matrix with diagonal `σ 0, σ 1, …, σ (min m n - 1)`.
Atlas `svd`. -/
def rectDiag (σ : ℕ → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = j then σ i else 0

/-- Entries of `rectDiag`. Atlas `svd`. -/
theorem rectDiag_apply (σ : ℕ → ℝ) (i : Fin m) (j : Fin n) :
    (rectDiag σ : Matrix (Fin m) (Fin n) ℝ) i j = if (i : ℕ) = j then σ i else 0 := rfl

/-- The transpose of a rectangular diagonal matrix is rectangular diagonal. Atlas `svd`. -/
theorem transpose_rectDiag (σ : ℕ → ℝ) :
    (rectDiag σ : Matrix (Fin m) (Fin n) ℝ)ᵀ = rectDiag σ := by
  ext i j
  simp only [Matrix.transpose_apply, rectDiag_apply]
  split_ifs with h₁ h₂ h₂
  · rw [h₁]
  · exact absurd h₁.symm h₂
  · exact absurd h₂.symm h₁
  · rfl

/-- `Σᵀ Σ` is diagonal with entries `σ_j²` for `j < m` and `0` beyond. Atlas `svd`. -/
theorem transpose_rectDiag_mul_rectDiag (σ : ℕ → ℝ) :
    (rectDiag σ : Matrix (Fin m) (Fin n) ℝ)ᵀ * rectDiag σ =
      Matrix.diagonal fun j : Fin n => if (j : ℕ) < m then σ j ^ 2 else 0 := by
  ext j l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rectDiag_apply, Matrix.diagonal_apply]
  by_cases hjm : (j : ℕ) < m
  · rw [Finset.sum_eq_single ⟨j, hjm⟩]
    · by_cases hjl : j = l
      · subst hjl; simp [hjm, sq]
      · have : (j : ℕ) ≠ l := fun h => hjl (Fin.ext h)
        simp [hjl, this]
    · intro i _ hi
      rw [if_neg (fun h => hi (Fin.ext h)), zero_mul]
    · simp
  · rw [Finset.sum_eq_zero]
    · split_ifs <;> simp_all
    · intro i _
      rw [if_neg (fun (h : (i : ℕ) = j) => hjm (h ▸ i.isLt)), zero_mul]

/-- `Σ Σᵀ` is diagonal with entries `σ_i²` for `i < n` and `0` beyond. Atlas `svd`. -/
theorem rectDiag_mul_transpose_rectDiag (σ : ℕ → ℝ) :
    (rectDiag σ : Matrix (Fin m) (Fin n) ℝ) * (rectDiag σ)ᵀ =
      Matrix.diagonal fun i : Fin m => if (i : ℕ) < n then σ i ^ 2 else 0 := by
  rw [← transpose_rectDiag (m := n) (n := m) σ, Matrix.transpose_transpose,
    transpose_rectDiag_mul_rectDiag]

/-- `rectDiag` is additive. Atlas `svd`. -/
theorem rectDiag_add (σ τ : ℕ → ℝ) :
    (rectDiag (σ + τ) : Matrix (Fin m) (Fin n) ℝ) = rectDiag σ + rectDiag τ := by
  ext i j
  simp only [rectDiag_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

/-! ### Orthogonal matrices from orthonormal bases -/

/-- The matrix whose columns are an orthonormal basis of `ℝᵏ` is orthogonal: `CᵀC = I`.
Atlas `svd` (helper; belongs in a `Basic.lean`). -/
theorem transpose_mul_self_of_orthonormalBasis {k : ℕ}
    (c : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k))) :
    (Matrix.of fun i j => c j i)ᵀ * (Matrix.of fun i j => c j i) = 1 := by
  ext i j
  rw [Matrix.one_apply, ← c.inner_eq_ite]
  simp [Matrix.mul_apply, PiLp.inner_apply, mul_comm]

/-! ### The decomposition -/

/-- `IsSVD A U V`: `U`, `V` are orthogonal and `A = U Σ Vᵀ` with `Σ = rectDiag (singularValues A)`
(Horn–Johnson 2013, Thm 2.6.3; HMT 2011, §2.1). The `k`-th columns of `U` and `V` are the
left/right singular vectors for `σ_k`. Atlas `svd`. -/
structure IsSVD (A : Matrix (Fin m) (Fin n) ℝ) (U : Matrix (Fin m) (Fin m) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) : Prop where
  /-- `U` is orthogonal. -/
  transpose_mul_left : Uᵀ * U = 1
  /-- `V` is orthogonal. -/
  transpose_mul_right : Vᵀ * V = 1
  /-- The factorization `A = U Σ Vᵀ`. -/
  eq : A = U * (rectDiag (singularValues A) : Matrix (Fin m) (Fin n) ℝ) * Vᵀ

/-- **Singular value decomposition** (Horn–Johnson 2013, Thm 2.6.3; HMT 2011, §2.1): every real
`m × n` matrix is `A = U Σ Vᵀ` with `U`, `V` orthogonal and `Σ = rectDiag (singularValues A)`,
the singular values being nonnegative and non-increasing (`singularValues_nonneg`,
`singularValues_antitone`). Atlas `svd`.

Proof: `V` is an orthonormal eigenbasis of `AᵀA` (Mathlib's spectral theorem, sorted), the
vectors `A vⱼ / σⱼ` with `σⱼ ≠ 0` are orthonormal and are completed to an orthonormal basis of
`ℝᵐ` (atlas `orthonormal-completion`) giving `U`. -/
theorem exists_isSVD (A : Matrix (Fin m) (Fin n) ℝ) : ∃ U V, IsSVD A U V := by
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hT := (Matrix.toEuclideanLin A).isSymmetric_adjoint_comp_self
  have hsq : ∀ j : Fin n, singularValues A j ^ 2 = hT.eigenvalues hn j :=
    (Matrix.toEuclideanLin A).sq_singularValues_fin hn
  -- the images `A vⱼ` are orthogonal with `‖A vⱼ‖² = σⱼ²`
  have key : ∀ i j, inner ℝ (Matrix.toEuclideanLin A (hT.eigenvectorBasis hn i))
      (Matrix.toEuclideanLin A (hT.eigenvectorBasis hn j)) =
      if i = j then singularValues A j ^ 2 else 0 := by
    intro i j
    rw [← LinearMap.adjoint_inner_right]
    have := hT.apply_eigenvectorBasis hn j
    rw [LinearMap.comp_apply] at this
    rw [this, hsq, inner_smul_right, (hT.eigenvectorBasis hn).inner_eq_ite]
    split_ifs <;> simp
  have hlt : ∀ k : ℕ, singularValues A k ≠ 0 → k < m := fun k hk =>
    ((singularValues_ne_zero_iff A k).1 hk).trans_le A.rank_le_height
  have hltn : ∀ k : ℕ, singularValues A k ≠ 0 → k < n := fun k hk =>
    ((singularValues_ne_zero_iff A k).1 hk).trans_le A.rank_le_width
  generalize hσ : singularValues A = σ at hsq key hlt hltn
  generalize hT.eigenvectorBasis hn = b at key
  generalize hTdef : Matrix.toEuclideanLin A = T at key
  -- left singular vectors `uⱼ = A vⱼ / σⱼ`, placed at index `j` of `Fin m`
  let v : Fin m → EuclideanSpace ℝ (Fin m) := fun i =>
    if h : (i : ℕ) < n then (σ i)⁻¹ • T (b ⟨i, h⟩) else 0
  let s : Set (Fin m) := {i | σ i ≠ 0}
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' := hltn _ hi
    have hj' := hltn _ hj
    simp only [Set.domRestrict_apply, v, dif_pos hi', dif_pos hj', inner_smul_left,
      inner_smul_right, key]
    by_cases hij : i = j
    · subst hij
      have : σ i ≠ 0 := hi
      simp
      field_simp
    · have : (⟨i, hi'⟩ : Fin n) ≠ ⟨j, hj'⟩ := fun h => hij (Fin.ext (by simpa using h))
      simp [hij, this]
  -- orthonormal completion (atlas `orthonormal-completion`)
  obtain ⟨c, hc⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  set U : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => c j i
  set V : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => b j i
  have hU : Uᵀ * U = 1 := transpose_mul_self_of_orthonormalBasis c
  have hV : Vᵀ * V = 1 := transpose_mul_self_of_orthonormalBasis b
  have hAV : A * V = U * rectDiag σ := by
    ext i j
    have hl : (A * V) i j = T (b j) i := by
      rw [← hTdef]
      simp [V, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [hl]
    simp only [Matrix.mul_apply, U, rectDiag, Matrix.of_apply, mul_ite, mul_zero]
    by_cases hj : σ j = 0
    · have h0 : T (b j) = 0 := by
        rw [← inner_self_eq_zero (𝕜 := ℝ), key, if_pos rfl, hj]; simp
      rw [h0, Finset.sum_eq_zero]
      · rfl
      intro k _
      split_ifs with hk
      · rw [hk, hj, mul_zero]
      · rfl
    · have hjm := hlt j hj
      rw [Finset.sum_eq_single ⟨j, hjm⟩]
      · rw [if_pos rfl, hc ⟨j, hjm⟩ hj]
        simp only [v, dif_pos j.isLt]
        simp
        field_simp
      · intro k _ hk
        rw [if_neg]
        exact fun h => hk (Fin.ext h)
      · simp
  refine ⟨U, V, hU, hV, ?_⟩
  subst hσ
  rw [← hAV, Matrix.mul_assoc, mul_eq_one_comm.1 hV, Matrix.mul_one]

/-- Sum over `Fin n` of a function vanishing at indices `≥ min m n`. -/
private lemma sum_fin_eq_sum_fin_min {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (hf : ∀ k, min m n ≤ k → f k = 0) :
    ∑ k : Fin n, f k = ∑ k : Fin (min m n), f k := by
  rw [Fin.sum_univ_eq_sum_range f, Fin.sum_univ_eq_sum_range f]
  symm
  apply Finset.sum_subset
  · intro k hk; simp at hk ⊢; omega
  · intro k _ hk; exact hf k (by simp only [Finset.mem_range, min_le_iff] at hk ⊢; omega)

namespace IsSVD

variable {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
  {V : Matrix (Fin n) (Fin n) ℝ}

/-- `U Uᵀ = I`. Atlas `svd`. -/
theorem mul_transpose_left (h : IsSVD A U V) : U * Uᵀ = 1 :=
  mul_eq_one_comm.1 h.transpose_mul_left

/-- `V Vᵀ = I`. Atlas `svd`. -/
theorem mul_transpose_right (h : IsSVD A U V) : V * Vᵀ = 1 :=
  mul_eq_one_comm.1 h.transpose_mul_right

/-- `A V = U Σ`, i.e. `A vₖ = σₖ uₖ`. Atlas `svd`. -/
theorem mul_right (h : IsSVD A U V) : A * V = U * rectDiag (singularValues A) := by
  conv_lhs => rw [h.eq]
  rw [Matrix.mul_assoc, h.transpose_mul_right, Matrix.mul_one]

/-- `Uᵀ A = Σ Vᵀ`, i.e. `Aᵀ uₖ = σₖ vₖ`. Atlas `svd`. -/
theorem transpose_mul (h : IsSVD A U V) : Uᵀ * A = rectDiag (singularValues A) * Vᵀ := by
  conv_lhs => rw [h.eq]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.transpose_mul_left, Matrix.one_mul]

/-- `Uᵀ A V = Σ`. Atlas `svd`. -/
theorem transpose_mul_mul (h : IsSVD A U V) : Uᵀ * A * V = rectDiag (singularValues A) := by
  rw [Matrix.mul_assoc, h.mul_right, ← Matrix.mul_assoc, h.transpose_mul_left, Matrix.one_mul]

/-- `Aᵀ = V Σᵀ Uᵀ`: an SVD of the transpose (the singular values agree by
`singularValues_transpose`). Atlas `svd`. -/
theorem transpose_eq (h : IsSVD A U V) :
    Aᵀ = V * (rectDiag (singularValues A) : Matrix (Fin n) (Fin m) ℝ) * Uᵀ := by
  conv_lhs => rw [h.eq]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, transpose_rectDiag,
    Matrix.mul_assoc]

/-- `AᵀA = V diag(σ₀², …, σₙ₋₁²) Vᵀ`: the right singular vectors diagonalize the Gram matrix
(Horn–Johnson 2013, §2.6). Atlas `svd`. -/
theorem transpose_mul_self (h : IsSVD A U V) :
    Aᵀ * A = V * Matrix.diagonal (fun j : Fin n => singularValues A j ^ 2) * Vᵀ := by
  have hd : (Matrix.diagonal fun j : Fin n => if (j : ℕ) < m then singularValues A j ^ 2 else 0)
      = Matrix.diagonal (fun j : Fin n => singularValues A j ^ 2) := by
    congr 1; funext j
    split_ifs with hj
    · rfl
    · rw [singularValues_eq_zero_of_height_le A (not_lt.1 hj)]; simp
  set S : Matrix (Fin m) (Fin n) ℝ := rectDiag (singularValues A)
  calc Aᵀ * A = (U * S * Vᵀ)ᵀ * (U * S * Vᵀ) := by rw [← h.eq]
    _ = V * (Sᵀ * (Uᵀ * U) * S) * Vᵀ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = _ := by rw [h.transpose_mul_left, Matrix.mul_one, transpose_rectDiag_mul_rectDiag, hd]

/-- `AAᵀ = U diag(σ₀², …, σₘ₋₁²) Uᵀ`: the left singular vectors diagonalize `AAᵀ`.
Atlas `svd`. -/
theorem mul_transpose_self (h : IsSVD A U V) :
    A * Aᵀ = U * Matrix.diagonal (fun i : Fin m => singularValues A i ^ 2) * Uᵀ := by
  have hd : (Matrix.diagonal fun i : Fin m => if (i : ℕ) < n then singularValues A i ^ 2 else 0)
      = Matrix.diagonal (fun i : Fin m => singularValues A i ^ 2) := by
    congr 1; funext i
    split_ifs with hi
    · rfl
    · rw [singularValues_eq_zero_of_width_le A (not_lt.1 hi)]; simp
  set S : Matrix (Fin m) (Fin n) ℝ := rectDiag (singularValues A)
  calc A * Aᵀ = (U * S * Vᵀ) * (U * S * Vᵀ)ᵀ := by rw [← h.eq]
    _ = U * (S * (Vᵀ * V) * Sᵀ) * Uᵀ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = _ := by rw [h.transpose_mul_right, Matrix.mul_one, rectDiag_mul_transpose_rectDiag, hd]

/-- Thin-SVD / outer-product expansion, entrywise:
`A i j = ∑_{k < min m n} σ_k U_{ik} V_{jk}`, i.e. `A = ∑_k σ_k u_k v_kᵀ`
(Horn–Johnson 2013, §2.6; HMT 2011, §2.1). Atlas `svd`. -/
theorem apply (h : IsSVD A U V) (i : Fin m) (j : Fin n) :
    A i j = ∑ k : Fin (min m n), singularValues A k * U i (Fin.castLE (min_le_left m n) k) *
      V j (Fin.castLE (min_le_right m n) k) := by
  let g : ℕ → ℝ := fun k => if h : k < m ∧ k < n then
    singularValues A k * U i ⟨k, h.1⟩ * V j ⟨k, h.2⟩ else 0
  have hg : ∀ k, min m n ≤ k → g k = 0 := fun k hk => by
    simp only [g]; split_ifs
    · rw [singularValues_eq_zero_of_min_le A hk]; simp
    · rfl
  have rhs : ∀ k : Fin (min m n), singularValues A k * U i (Fin.castLE (min_le_left m n) k) *
      V j (Fin.castLE (min_le_right m n) k) = g k := fun k => by
    have h1 : (k : ℕ) < m := lt_of_lt_of_le k.isLt (min_le_left m n)
    have h2 : (k : ℕ) < n := lt_of_lt_of_le k.isLt (min_le_right m n)
    simp only [g, dif_pos (And.intro h1 h2)]; rfl
  simp_rw [rhs]
  rw [← sum_fin_eq_sum_fin_min g hg]
  conv_lhs => rw [h.eq]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rectDiag_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : (k : ℕ) < m
  · rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp only [g, dif_pos (And.intro hk k.isLt), if_true]; ring
    · intro l _ hl; rw [if_neg (fun e => hl (Fin.ext e)), mul_zero]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [g, hk]
    · intro l _; rw [if_neg (fun (e : (l : ℕ) = k) => hk (e ▸ l.isLt)), mul_zero]

/-- Block SVD split at index `k` (HMT 2011, §2.1, `A = U₁Σ₁V₁ᵀ + U₂Σ₂V₂ᵀ`): the head
`U Σ_{<k} Vᵀ` (the truncated SVD) plus the tail `U Σ_{≥k} Vᵀ`. Atlas `svd`. -/
theorem eq_head_add_tail (h : IsSVD A U V) (k : ℕ) :
    A = U * (rectDiag (fun i => if i < k then singularValues A i else 0) :
        Matrix (Fin m) (Fin n) ℝ) * Vᵀ +
      U * (rectDiag (fun i => if i < k then 0 else singularValues A i) :
        Matrix (Fin m) (Fin n) ℝ) * Vᵀ := by
  rw [← Matrix.add_mul, ← Matrix.mul_add, ← rectDiag_add]
  convert h.eq using 4
  funext i
  simp only [Pi.add_apply]; split_ifs <;> simp

end IsSVD

/-- `‖A‖_F² = ∑_{k < min m n} σ_k²` (Horn–Johnson 2013, §2.6 / 5.6; HMT 2011, §2.1).
Atlas `svd`. -/
theorem frobSq_eq_sum_sq_singularValues (A : Matrix (Fin m) (Fin n) ℝ) :
    frobSq A = ∑ k ∈ Finset.range (min m n), singularValues A k ^ 2 := by
  obtain ⟨U, V, h⟩ := exists_isSVD A
  rw [frobSq, frobInner_eq_trace, h.transpose_mul_self, Matrix.trace_mul_cycle,
    h.transpose_mul_right, Matrix.one_mul, Matrix.trace_diagonal,
    Fin.sum_univ_eq_sum_range (fun k => singularValues A k ^ 2)]
  symm
  apply Finset.sum_subset
  · intro k hk; simp at hk ⊢; omega
  · intro k _ hk
    rw [singularValues_eq_zero_of_min_le A
      (by simp only [Finset.mem_range, min_le_iff] at hk ⊢; omega)]; simp


/-- For a real symmetric `S = W diag(μ) Wᵀ` with `W` orthogonal and `μ` non-increasing, `μ` is
Mathlib's sorted eigenvalue list `eigenvalues₀` of `S` (uniqueness of the sorted spectrum, via
the characteristic polynomial). Atlas `svd` (helper; belongs with the spectral API). -/
theorem eigenvalues₀_eq_of_eq_mul_diagonal_mul {S W : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.IsHermitian) {μ : Fin n → ℝ} (hμ : Antitone μ) (hW : Wᵀ * W = 1)
    (hSW : S = W * Matrix.diagonal μ * Wᵀ) (k : Fin n) :
    hS.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm k) = μ k := by
  have hc : S.charpoly = (Matrix.diagonal μ).charpoly := by
    rw [hSW, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hW, Matrix.mul_one]
  have hsort := hS.sort_roots_charpoly_eq_eigenvalues₀
  rw [hc, Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at hsort
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map,
    Function.comp_def, RCLike.re_to_real] at hsort
  have hl : List.ofFn hS.eigenvalues₀ = List.ofFn μ := by
    rw [← hsort]
    simp_rw [Fin.univ_val_map, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hμ.sortedGE_ofFn
  have := congrArg (fun l : List ℝ => l.getD k 0) hl
  simpa using this


/-- **Uniqueness of singular values** (Horn–Johnson 2013, Thm 2.6.3): if `A = U Σ_τ Vᵀ` with
`U`, `V` orthogonal and `τ` nonnegative and non-increasing, then `τ k = σ_k(A)` for every
`k < min m n`. Atlas `svd`. -/
theorem singularValues_eq_of_eq_mul_rectDiag_mul {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ} {τ : ℕ → ℝ}
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hτ0 : ∀ k, 0 ≤ τ k) (hτ : Antitone τ)
    (hA : A = U * (rectDiag τ : Matrix (Fin m) (Fin n) ℝ) * Vᵀ) {k : ℕ} (hk : k < min m n) :
    singularValues A k = τ k := by
  have hkm : k < m := lt_of_lt_of_le hk (min_le_left m n)
  have hkn : k < n := lt_of_lt_of_le hk (min_le_right m n)
  set μ : Fin n → ℝ := fun j => if (j : ℕ) < m then τ j ^ 2 else 0
  have hμ : Antitone μ := by
    intro a b hab
    simp only [μ]
    split_ifs with hb ha ha
    · exact pow_le_pow_left₀ (hτ0 _) (hτ hab) 2
    · exact absurd (lt_of_le_of_lt (Fin.le_def.1 hab) hb) ha
    · exact sq_nonneg _
    · exact le_rfl
  have hAA : Aᵀ * A = V * Matrix.diagonal μ * Vᵀ := by
    set Sg : Matrix (Fin m) (Fin n) ℝ := rectDiag τ
    calc Aᵀ * A = (U * Sg * Vᵀ)ᵀ * (U * Sg * Vᵀ) := by rw [← hA]
      _ = V * (Sgᵀ * (Uᵀ * U) * Sg) * Vᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one, transpose_rectDiag_mul_rectDiag]
  have hH : (Aᵀ * A).IsHermitian := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_self A
  have e1 := sq_singularValues_eq_eigenvalues₀ A hH ⟨k, hkn⟩
  rw [eigenvalues₀_eq_of_eq_mul_diagonal_mul hH hμ hV hAA] at e1
  simp only [μ, if_pos hkm] at e1
  exact (sq_eq_sq₀ (singularValues_nonneg A k) (hτ0 k)).1 e1

/-- `σ(Aᵀ) = σ(A)` (Horn–Johnson 2013, §2.6). Atlas `svd`. -/
theorem singularValues_transpose (A : Matrix (Fin m) (Fin n) ℝ) :
    singularValues Aᵀ = singularValues A := by
  funext k
  by_cases hk : k < min n m
  · obtain ⟨U, V, h⟩ := exists_isSVD A
    exact singularValues_eq_of_eq_mul_rectDiag_mul h.transpose_mul_right h.transpose_mul_left
      (singularValues_nonneg A) (singularValues_antitone A) h.transpose_eq hk
  · rw [singularValues_eq_zero_of_min_le _ (not_lt.1 hk),
      singularValues_eq_zero_of_min_le _ (by rw [min_comm]; exact not_lt.1 hk)]

/-- Singular values are invariant under left multiplication by an orthogonal matrix
(Horn–Johnson 2013, §2.6). Atlas `svd`. -/
theorem singularValues_orthogonal_mul (A : Matrix (Fin m) (Fin n) ℝ) {Q : Matrix (Fin m) (Fin m) ℝ}
    (hQ : Qᵀ * Q = 1) : singularValues (Q * A) = singularValues A := by
  funext k
  by_cases hk : k < min m n
  · obtain ⟨U, V, h⟩ := exists_isSVD A
    refine singularValues_eq_of_eq_mul_rectDiag_mul (U := Q * U) (V := V) ?_ h.transpose_mul_right
      (singularValues_nonneg A) (singularValues_antitone A) ?_ hk
    · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, hQ, Matrix.one_mul,
        h.transpose_mul_left]
    · conv_lhs => rw [h.eq]
      simp only [Matrix.mul_assoc]
  · rw [singularValues_eq_zero_of_min_le _ (not_lt.1 hk),
      singularValues_eq_zero_of_min_le _ (not_lt.1 hk)]

/-- Singular values are invariant under right multiplication by an orthogonal matrix
(Horn–Johnson 2013, §2.6). Atlas `svd`. -/
theorem singularValues_mul_orthogonal (A : Matrix (Fin m) (Fin n) ℝ) {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Qᵀ * Q = 1) : singularValues (A * Q) = singularValues A := by
  have hQ' : Q * Qᵀ = 1 := mul_eq_one_comm.1 hQ
  have hQ'' : (Qᵀ)ᵀ * Qᵀ = 1 := by rwa [Matrix.transpose_transpose]
  rw [← singularValues_transpose, Matrix.transpose_mul, singularValues_orthogonal_mul _ hQ'',
    singularValues_transpose]


end NLAlib
