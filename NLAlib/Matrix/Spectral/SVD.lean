import Mathlib.Analysis.InnerProductSpace.SingularValues
import NLAlib.Matrix.Norms.Core
/-!
# Singular value decomposition

Every matrix `A : Matrix m n 𝕜` over `𝕜 = ℝ` or `ℂ` (any `RCLike` field), with `m`, `n` arbitrary
finite types, factors as `A = U Σ Vᴴ` with `U`, `V` unitary and `Σ = rectDiag (singularValues A)` rectangular
diagonal with nonnegative, non-increasing real diagonal (Horn–Johnson 2013, Thm 2.6.3;
HMT 2011, §2.1). Over `ℝ`, `Vᴴ` is definitionally `Vᵀ` and `U`, `V` are orthogonal.

## Conventions

* `NLAlib.singularValues A : ℕ → ℝ` is Mathlib's `LinearMap.singularValues` of the Euclidean
 linear map of `A`, defined for `A : Matrix m n 𝕜` with `𝕜` `RCLike` and `m`, `n` arbitrary
 finite types: **zero-indexed** (`σ 0` is the largest), nonnegative, antitone, and
 `σ k ≠ 0 ↔ k < A.rank`; in particular `σ k = 0` for `k ≥ min m n`. Indexing by `ℕ` (rather
 than `Fin (min m n)`) means the singular values of matrices of different shapes are compared
 without casts, a rank-`k` split is `k < ·` vs `k ≤ ·`, and the truncated SVD is
 `rectDiag (fun i => if i < k then σ i else 0)`.
* The singular values are a *function of `A`*, not an existential witness: `exists_isSVD` only
 chooses the singular vectors `U`, `V`.
* `NLAlib.rectDiag σ : Matrix (Fin p) (Fin q) 𝕜` has entry `(σ i : 𝕜)` at `(i, i)` and `0`
 elsewhere (`rectDiag_apply_ofReal`); over `ℝ` the entry is `σ i` (`rectDiag_apply`). It is
 *positional*: its rows and columns are the sorted singular directions, like Mathlib's
 `Matrix.IsHermitian.eigenvalues₀ : Fin (card n) → ℝ`.
* Index shapes of `IsSVD A U V` for `A : Matrix m n 𝕜`: `U : Matrix m (Fin p) 𝕜`,
 `V : Matrix n (Fin q) 𝕜`, unitary (`UᴴU = 1`, `UUᴴ = 1`, so `p = card m`, `IsSVD.card_left`),
 the `k`-th column being the `k`-th singular vector. `exists_isSVD A` fills `p = card m`
 automatically; for `A : Matrix (Fin a) (Fin b) 𝕜` it gives `U : Matrix (Fin a) (Fin a) 𝕜`
 (`Fintype.card_fin`), so `Fin` statements need no casts. (`Fintype.equivFin (Fin a)` is an
 unspecified permutation, so a `rectDiag : Matrix m n 𝕜` built from `equivFin` would not be the
 positional diagonal at `Fin`; see `docs/rclike/F1b-alpha.md`.)
* Real matrices. Lemmas are stated once, with `ᴴ` (no `ᵀ` twins, `docs/STANDARDS.md` §2): at `ℝ`
 a term of the general statement elaborates against the `ᵀ` form, and a `rw` on a `ᵀ` goal uses
 `show Uᵀ * U = 1 from h.conjTranspose_mul_left` or
 `simp only [Matrix.conjTranspose_eq_transpose_of_trivial]`. The one real entry lemma kept is
 `rectDiag_apply` (cast-free entries of a real `rectDiag`).

## Main results

* `NLAlib.exists_isSVD`: `∃ U V, IsSVD A U V` (atlas `svd`).
* `NLAlib.IsSVD.conjTranspose_mul_self`, `NLAlib.IsSVD.mul_conjTranspose_self`:
 `AᴴA = V Σ² Vᴴ`, `AAᴴ = U Σ² Uᴴ`.
* `NLAlib.IsSVD.apply`: the entrywise outer-product expansion
 `A i j = ∑_{k < min m n} σ_k U_{ik} conj(V_{jk})`.
* `NLAlib.frobSq_eq_sum_sq_singularValues` (in `SingularValueSpectrum`):
 `‖A‖_F² = ∑_{k < min m n} σ_k²`.
* `NLAlib.singularValues_ne_zero_iff`, `NLAlib.rank_eq_card_singularValues_ne_zero`: rank.
* `NLAlib.sq_singularValues_eq_eigenvalues₀`: `σ_k²` is the `k`-th largest eigenvalue of `AᴴA`.
* `NLAlib.IsSVD.eq_head_add_tail`: block split `A = U Σ_{<k} Vᴴ + U Σ_{≥k} Vᴴ`.
* `NLAlib.singularValues_eq_of_eq_mul_rectDiag_mul`: uniqueness of the singular values (used for
 `singularValues_transpose` and the isometry invariances in `SingularValueInvariance.lean`).

The orthonormal completion of `{A vⱼ / σⱼ : σⱼ ≠ 0}` (atlas `orthonormal-completion`) is
Mathlib's `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`.

Atlas: `svd`.
-/

noncomputable section

open scoped Matrix
open Module Polynomial

namespace NLAlib

/-! ### Singular values -/

section General

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The singular values `σ₀ ≥ σ₁ ≥ ⋯ ≥ 0` of a matrix over `ℝ` or `ℂ` (any `RCLike` field) with
arbitrary finite row and column types, zero-indexed, padded with zeros:
`σ k = √(λ_k(AᴴA))` for `k < card n` and `σ k = 0` for `k ≥ card n`. Defined as Mathlib's
`LinearMap.singularValues` of `Matrix.toEuclideanLin A` (Horn–Johnson 2013, §2.6;
HMT 2011, §2.1). Deviation: zero-indexed, indexed by `ℕ`.
atlas: svd-def -/
def singularValues (A : Matrix m n 𝕜) : ℕ → ℝ :=
  fun k => (Matrix.toEuclideanLin A).singularValues k

/-- Bridge to Mathlib's `LinearMap.singularValues` (definitional). Atlas `svd`. -/
theorem singularValues_eq_linearMap (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k = (Matrix.toEuclideanLin A).singularValues k := rfl

/-- Singular values are nonnegative. Atlas `svd`. -/
theorem singularValues_nonneg (A : Matrix m n 𝕜) (k : ℕ) :
    0 ≤ singularValues A k :=
  LinearMap.singularValues_nonneg _ _

/-- Singular values are listed in non-increasing order. Atlas `svd`. -/
theorem singularValues_antitone (A : Matrix m n 𝕜) :
    Antitone (singularValues A) :=
  fun _ _ h => LinearMap.singularValues_antitone _ h

/-- The nonzero singular values are exactly the first `rank A` ones
(Horn–Johnson 2013, Thm 2.6.3). Atlas `svd`. -/
theorem singularValues_ne_zero_iff (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k ≠ 0 ↔ k < A.rank := by
  unfold singularValues
  rw [← LinearMap.singularValues_pos_iff_ne_zero,
    LinearMap.singularValues_pos_iff_lt_finrank_range,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, ← Matrix.rank_eq_finrank_range_toLin]

/-- The positive singular values are exactly the first `rank A` ones. Atlas `svd`. -/
theorem singularValues_pos_iff (A : Matrix m n 𝕜) (k : ℕ) :
    0 < singularValues A k ↔ k < A.rank := by
  rw [← singularValues_ne_zero_iff, (singularValues_nonneg A k).lt_iff_ne', ne_comm]

/-- `σ k = 0` once `k ≥ rank A`. Atlas `svd`. -/
theorem singularValues_eq_zero_of_rank_le (A : Matrix m n 𝕜) {k : ℕ}
    (hk : A.rank ≤ k) : singularValues A k = 0 := by
  by_contra h
  exact absurd ((singularValues_ne_zero_iff A k).1 h) (not_lt.2 hk)

/-- Sorted eigenvalues of a symmetric operator do not depend on how the operator is
spelled. -/
private lemma eigenvalues_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T₁ T₂ : E →ₗ[𝕜] E} (h : T₁ = T₂) (h₁ : T₁.IsSymmetric)
    (h₂ : T₂.IsSymmetric) {d : ℕ} (hd : Module.finrank 𝕜 E = d) (i : Fin d) :
    h₁.eigenvalues hd i = h₂.eigenvalues hd i := by
  subst h
  rfl

/-- The squared singular values are the eigenvalues of the Gram matrix `AᴴA`, in decreasing
order: `σ_k² = λ_k(AᴴA)` for `k < card n`, with Mathlib's sorted
`Matrix.IsHermitian.eigenvalues₀` (Horn–Johnson 2013, §2.6). For real matrices `Aᴴ = Aᵀ`
(`Matrix.conjTranspose_eq_transpose_of_trivial`). Atlas `svd`. -/
theorem sq_singularValues_eq_eigenvalues₀ (A : Matrix m n 𝕜) (i : Fin (Fintype.card n)) :
    singularValues A i ^ 2 = (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ i := by
  classical
  have heq : LinearMap.adjoint (Matrix.toEuclideanLin A) ∘ₗ Matrix.toEuclideanLin A =
      Matrix.toEuclideanLin (Aᴴ * A) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
  rw [singularValues_eq_linearMap,
    (Matrix.toEuclideanLin A).sq_singularValues_of_lt finrank_euclideanSpace i.isLt]
  exact eigenvalues_congr heq _ _ finrank_euclideanSpace i

/-- `σ k = 0` once `k` is at least the number of rows. Atlas `svd`. -/
theorem singularValues_eq_zero_of_height_le (A : Matrix m n 𝕜) {k : ℕ}
    (hk : Fintype.card m ≤ k) : singularValues A k = 0 :=
  singularValues_eq_zero_of_rank_le A (A.rank_le_card_height.trans hk)

/-- `σ k = 0` once `k` is at least the number of columns. Atlas `svd`. -/
theorem singularValues_eq_zero_of_width_le (A : Matrix m n 𝕜) {k : ℕ}
    (hk : Fintype.card n ≤ k) : singularValues A k = 0 :=
  singularValues_eq_zero_of_rank_le A (A.rank_le_card_width.trans hk)

/-- `σ k = 0` once `k ≥ min (card m) (card n)`. Atlas `svd`. -/
theorem singularValues_eq_zero_of_min_le (A : Matrix m n 𝕜) {k : ℕ}
    (hk : min (Fintype.card m) (Fintype.card n) ≤ k) : singularValues A k = 0 :=
  singularValues_eq_zero_of_rank_le A
    ((le_min A.rank_le_card_height A.rank_le_card_width).trans hk)


/-- The rank is the number of nonzero singular values (Horn–Johnson 2013, Thm 2.6.3).
Atlas `svd`. -/
theorem rank_eq_card_singularValues_ne_zero (A : Matrix m n 𝕜) :
    A.rank = ((Finset.range (min (Fintype.card m) (Fintype.card n))).filter
      fun k => singularValues A k ≠ 0).card := by
  have hr : A.rank ≤ min (Fintype.card m) (Fintype.card n) :=
    le_min A.rank_le_card_height A.rank_le_card_width
  have : ((Finset.range (min (Fintype.card m) (Fintype.card n))).filter
      fun k => singularValues A k ≠ 0) = Finset.range A.rank := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, singularValues_ne_zero_iff]
    exact ⟨fun h => h.2, fun h => ⟨h.trans_le hr, h⟩⟩
  rw [this, Finset.card_range]

/-- Extending a real matrix to `𝕜` (`ℝ` or `ℂ`) entrywise preserves every singular value,
including the padded zeros: no dimension doubling. Horn–Johnson 2013, Section 2.6. -/
theorem singularValues_map_ofReal (A : Matrix m n ℝ) (k : ℕ) :
    singularValues (A.map (algebraMap ℝ 𝕜)) k = singularValues A k := by
  classical
  by_cases hk : k < Fintype.card n
  · have h₁ := sq_singularValues_eq_eigenvalues₀ (A.map (algebraMap ℝ 𝕜)) ⟨k, hk⟩
    have h₂ := sq_singularValues_eq_eigenvalues₀ A ⟨k, hk⟩
    have hB := Matrix.isHermitian_conjTranspose_mul_self A
    have hG : (A.map (algebraMap ℝ 𝕜))ᴴ * A.map (algebraMap ℝ 𝕜) =
        (Aᴴ * A).map (algebraMap ℝ 𝕜) := by
      ext i j
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum]
    have hl : List.ofFn (Matrix.isHermitian_conjTranspose_mul_self
        (A.map (algebraMap ℝ 𝕜))).eigenvalues₀ = List.ofFn hB.eigenvalues₀ := by
      rw [← (Matrix.isHermitian_conjTranspose_mul_self _).sort_roots_charpoly_eq_eigenvalues₀,
        ← hB.sort_roots_charpoly_eq_eigenvalues₀, hG, Matrix.charpoly_map,
        hB.splits_charpoly.roots_map]
      simp only [Multiset.map_map, Function.comp_def, RCLike.re_to_real,
        RCLike.algebraMap_eq_ofReal, RCLike.ofReal_re]
    have he := congrFun (List.ofFn_inj.mp hl) ⟨k, hk⟩
    have hs : singularValues (A.map (algebraMap ℝ 𝕜)) k ^ 2 = singularValues A k ^ 2 :=
      h₁.trans (he.trans h₂.symm)
    exact (sq_eq_sq₀ (singularValues_nonneg _ k) (singularValues_nonneg A k)).1 hs
  · rw [singularValues_eq_zero_of_width_le _ (not_lt.1 hk),
      singularValues_eq_zero_of_width_le _ (not_lt.1 hk)]

end General


section RectDiag

variable {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}

/-! ### Rectangular diagonal matrices -/

/-- The `m × n` rectangular diagonal matrix over `𝕜` (`ℝ` or `ℂ`) with real diagonal
`σ 0, σ 1, …, σ (min m n - 1)`, cast to `𝕜`. Over `ℝ` the entries are `σ i` (definitionally).
Atlas `svd`.
atlas: svd-def -/
def rectDiag (σ : ℕ → ℝ) : Matrix (Fin m) (Fin n) 𝕜 :=
  Matrix.of fun i j => if (i : ℕ) = j then (σ i : 𝕜) else 0

/-- Entries of `rectDiag` over `𝕜`: `(σ i : 𝕜)` on the diagonal, `0` elsewhere. Atlas `svd`. -/
theorem rectDiag_apply_ofReal (σ : ℕ → ℝ) (i : Fin m) (j : Fin n) :
    (rectDiag σ : Matrix (Fin m) (Fin n) 𝕜) i j = if (i : ℕ) = j then (σ i : 𝕜) else 0 := rfl

/-- Entries of a real `rectDiag` (no cast): the real form of `rectDiag_apply_ofReal`.
Atlas `svd`. -/
theorem rectDiag_apply (σ : ℕ → ℝ) (i : Fin m) (j : Fin n) :
    (rectDiag σ : Matrix (Fin m) (Fin n) ℝ) i j = if (i : ℕ) = j then σ i else 0 := rfl

/-- The transpose of a rectangular diagonal matrix is rectangular diagonal. Atlas `svd`. -/
theorem transpose_rectDiag (σ : ℕ → ℝ) :
    (rectDiag σ : Matrix (Fin m) (Fin n) 𝕜)ᵀ = rectDiag σ := by
  ext i j
  simp only [Matrix.transpose_apply, rectDiag_apply_ofReal]
  split_ifs with h₁ h₂ h₂
  · rw [h₁]
  · exact absurd h₁.symm h₂
  · exact absurd h₂.symm h₁
  · rfl

/-- The conjugate transpose of a rectangular diagonal matrix (real diagonal) is rectangular
diagonal. Atlas `svd`. -/
theorem conjTranspose_rectDiag (σ : ℕ → ℝ) :
    (rectDiag σ : Matrix (Fin m) (Fin n) 𝕜)ᴴ = rectDiag σ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, rectDiag_apply_ofReal]
  split_ifs with h₁ h₂ h₂
  · rw [h₁, RCLike.star_def, RCLike.conj_ofReal]
  · exact absurd h₁.symm h₂
  · exact absurd h₂.symm h₁
  · exact star_zero _

/-- `Σᴴ Σ` is diagonal with entries `σ_j²` for `j < m` and `0` beyond. Atlas `svd`. -/
theorem conjTranspose_rectDiag_mul_rectDiag (σ : ℕ → ℝ) :
    (rectDiag σ : Matrix (Fin m) (Fin n) 𝕜)ᴴ * rectDiag σ =
      Matrix.diagonal fun j : Fin n => if (j : ℕ) < m then ((σ j ^ 2 : ℝ) : 𝕜) else 0 := by
  rw [conjTranspose_rectDiag]
  ext j l
  simp only [Matrix.mul_apply, rectDiag_apply_ofReal, Matrix.diagonal_apply]
  by_cases hjm : (j : ℕ) < m
  · rw [Finset.sum_eq_single ⟨j, hjm⟩]
    · by_cases hjl : j = l
      · subst hjl; simp [hjm, sq]
      · have : (j : ℕ) ≠ l := fun h => hjl (Fin.ext h)
        simp [hjl, this]
    · intro i _ hi
      rw [if_neg (fun h => hi (Fin.ext h.symm)), zero_mul]
    · simp
  · rw [Finset.sum_eq_zero]
    · split_ifs <;> simp_all
    · intro i _
      rw [if_neg (fun (h : (j : ℕ) = i) => hjm (h ▸ i.isLt)), zero_mul]

/-- `Σ Σᴴ` is diagonal with entries `σ_i²` for `i < n` and `0` beyond. Atlas `svd`. -/
theorem rectDiag_mul_conjTranspose_rectDiag (σ : ℕ → ℝ) :
    (rectDiag σ : Matrix (Fin m) (Fin n) 𝕜) * (rectDiag σ)ᴴ =
      Matrix.diagonal fun i : Fin m => if (i : ℕ) < n then ((σ i ^ 2 : ℝ) : 𝕜) else 0 := by
  rw [← conjTranspose_rectDiag (𝕜 := 𝕜) (m := n) (n := m) σ, Matrix.conjTranspose_conjTranspose,
    conjTranspose_rectDiag_mul_rectDiag]

/-- `rectDiag` is additive. Atlas `svd`. -/
theorem rectDiag_add (σ τ : ℕ → ℝ) :
    (rectDiag (σ + τ) : Matrix (Fin m) (Fin n) 𝕜) = rectDiag σ + rectDiag τ := by
  ext i j
  simp only [rectDiag_apply_ofReal, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

end RectDiag

/-! ### Unitary matrices from orthonormal bases -/

section Unitary

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
/-- The matrix whose columns are an orthonormal basis of `𝕜ᵐ`, indexed by any finite `ι`, has
orthonormal columns: `CᴴC = I`. Atlas `svd` (helper; belongs in a `Basic.lean`). -/
theorem conjTranspose_mul_self_of_orthonormalBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 m)) :
    (Matrix.of fun i j => c j i : Matrix m ι 𝕜)ᴴ * (Matrix.of fun i j => c j i) = 1 := by
  ext i j
  rw [Matrix.one_apply, ← c.inner_eq_ite, EuclideanSpace.inner_eq_star_dotProduct]
  simp [Matrix.mul_apply, dotProduct, mul_comm]

/-- Orthonormal columns plus a square count make a unitary matrix: if `U : Matrix m (Fin p) 𝕜`
has `UᴴU = I` and `p = card m`, then `UUᴴ = I`. Atlas `svd`. -/
theorem mul_conjTranspose_eq_one_of_conjTranspose_mul_eq_one {p : ℕ} {U : Matrix m (Fin p) 𝕜}
    (hp : Fintype.card m = p) (hU : Uᴴ * U = 1) : U * Uᴴ = 1 := by
  let e : Fin p ≃ m := (finCongr hp.symm).trans (Fintype.equivFin m).symm
  have h1 : (Uᴴ.submatrix e.symm (Equiv.refl m)) * U.submatrix (Equiv.refl m) e.symm = 1 := by
    rw [Matrix.submatrix_mul_equiv, hU, Matrix.submatrix_one_equiv]
  have h2 := mul_eq_one_comm.1 h1
  rw [Matrix.submatrix_mul_equiv, Equiv.coe_refl, Matrix.submatrix_id_id] at h2
  exact h2

/-- A unitary `U : Matrix m (Fin p) 𝕜` (`UᴴU = I` and `UUᴴ = I`) has `p = card m` columns
(compare traces). Atlas `svd`. -/
theorem card_eq_of_conjTranspose_mul_eq_one {p : ℕ} {U : Matrix m (Fin p) 𝕜}
    (h₁ : Uᴴ * U = 1) (h₂ : U * Uᴴ = 1) : Fintype.card m = p := by
  have h := congrArg Matrix.trace h₁
  rw [Matrix.trace_mul_comm, h₂, Matrix.trace_one, Matrix.trace_one, Fintype.card_fin] at h
  exact_mod_cast h

end Unitary

/-! ### The decomposition -/

section Decomposition

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- `IsSVD A U V` for `A : Matrix m n 𝕜`: `U : Matrix m (Fin p) 𝕜` and `V : Matrix n (Fin q) 𝕜`
are unitary (orthogonal over `ℝ`; so `p = card m`, `q = card n`) and `A = U Σ Vᴴ` with
`Σ = rectDiag (singularValues A)` (Horn–Johnson 2013, Thm 2.6.3; HMT 2011, §2.1). The `k`-th
columns of `U` and `V` are the left/right singular vectors for `σ_k`. At `m = Fin a`, `n = Fin b`
the factors are square, `U : Matrix (Fin a) (Fin a) 𝕜`. Over `ℝ`, `Uᴴ` is definitionally `Uᵀ`,
so the fields elaborate against the `ᵀ` forms. Atlas `svd`.
atlas: svd-def -/
structure IsSVD {p q : ℕ} (A : Matrix m n 𝕜) (U : Matrix m (Fin p) 𝕜)
    (V : Matrix n (Fin q) 𝕜) : Prop where
  /-- `U` has orthonormal columns: `UᴴU = I`. -/
  conjTranspose_mul_left : Uᴴ * U = 1
  /-- `V` has orthonormal columns: `VᴴV = I`. -/
  conjTranspose_mul_right : Vᴴ * V = 1
  /-- The factorization `A = U Σ Vᴴ`. -/
  eq : A = U * (rectDiag (singularValues A) : Matrix (Fin p) (Fin q) 𝕜) * Vᴴ
  /-- `U` is unitary: `UUᴴ = I`. -/
  mul_conjTranspose_left : U * Uᴴ = 1
  /-- `V` is unitary: `VVᴴ = I`. -/
  mul_conjTranspose_right : V * Vᴴ = 1

/-- **Singular value decomposition** (Horn–Johnson 2013, Thm 2.6.3; HMT 2011, §2.1): every
matrix `A : Matrix m n 𝕜` over `ℝ` or `ℂ`, with `m`, `n` arbitrary finite types, is
`A = U Σ Vᴴ` with `U : Matrix m (Fin p) 𝕜`, `V : Matrix n (Fin q) 𝕜` unitary and
`Σ = rectDiag (singularValues A)`, the singular values being nonnegative and non-increasing
(`singularValues_nonneg`, `singularValues_antitone`). The sizes `p = card m`, `q = card n` are
discharged automatically; for `Fin a`, `Fin b` this gives square `Fin a`, `Fin b` factors.
Atlas `svd`.

Proof: `V` is an orthonormal eigenbasis of `AᴴA` (Mathlib's spectral theorem, sorted), the
vectors `A vⱼ / σⱼ` with `σⱼ ≠ 0` are orthonormal and are completed to an orthonormal basis of
`𝕜ᵐ` (atlas `orthonormal-completion`) giving `U`.
atlas: svd -/
theorem exists_isSVD (A : Matrix m n 𝕜) {p q : ℕ}
    (hp : Fintype.card m = p := by first | exact Fintype.card_fin _ | rfl)
    (hq : Fintype.card n = q := by first | exact Fintype.card_fin _ | rfl) :
    ∃ (U : Matrix m (Fin p) 𝕜) (V : Matrix n (Fin q) 𝕜), IsSVD A U V := by
  subst hp hq
  have hn : finrank 𝕜 (EuclideanSpace 𝕜 n) = Fintype.card n := finrank_euclideanSpace
  have hT := (Matrix.toEuclideanLin A).isSymmetric_adjoint_comp_self
  have hsq : ∀ j : Fin (Fintype.card n), singularValues A j ^ 2 = hT.eigenvalues hn j :=
    fun j => (Matrix.toEuclideanLin A).sq_singularValues_of_lt hn j.isLt
  -- the images `A vⱼ` are orthogonal with `‖A vⱼ‖² = σⱼ²`
  have key : ∀ i j, inner 𝕜 (Matrix.toEuclideanLin A (hT.eigenvectorBasis hn i))
      (Matrix.toEuclideanLin A (hT.eigenvectorBasis hn j)) =
      if i = j then ((singularValues A j ^ 2 : ℝ) : 𝕜) else 0 := by
    intro i j
    rw [← LinearMap.adjoint_inner_right]
    have := hT.apply_eigenvectorBasis hn j
    rw [LinearMap.comp_apply] at this
    rw [this, hsq, inner_smul_right, (hT.eigenvectorBasis hn).inner_eq_ite]
    split_ifs <;> simp
  have hlt : ∀ k : ℕ, singularValues A k ≠ 0 → k < Fintype.card m := fun k hk =>
    ((singularValues_ne_zero_iff A k).1 hk).trans_le A.rank_le_card_height
  have hltn : ∀ k : ℕ, singularValues A k ≠ 0 → k < Fintype.card n := fun k hk =>
    ((singularValues_ne_zero_iff A k).1 hk).trans_le A.rank_le_card_width
  generalize hσ : singularValues A = σ at hsq key hlt hltn
  generalize hT.eigenvectorBasis hn = b at key
  generalize hTdef : Matrix.toEuclideanLin A = T at key
  -- left singular vectors `uⱼ = A vⱼ / σⱼ`, placed at index `j` of `Fin (card m)`
  let v : Fin (Fintype.card m) → EuclideanSpace 𝕜 m := fun i =>
    if h : (i : ℕ) < Fintype.card n then ((σ i : 𝕜))⁻¹ • T (b ⟨i, h⟩) else 0
  let s : Set (Fin (Fintype.card m)) := {i | σ i ≠ 0}
  have hv : Orthonormal 𝕜 (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' := hltn _ hi
    have hj' := hltn _ hj
    simp only [Set.domRestrict_apply, v, dif_pos hi', dif_pos hj', inner_smul_left,
      inner_smul_right, key]
    by_cases hij : i = j
    · subst hij
      have : (σ i : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hi
      simp
      field_simp
    · have : (⟨i, hi'⟩ : Fin (Fintype.card n)) ≠ ⟨j, hj'⟩ :=
        fun h => hij (Fin.ext (by simpa using h))
      simp [hij, this]
  -- orthonormal completion (atlas `orthonormal-completion`)
  obtain ⟨c, hc⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  set U : Matrix m (Fin (Fintype.card m)) 𝕜 := Matrix.of fun i j => c j i
  set V : Matrix n (Fin (Fintype.card n)) 𝕜 := Matrix.of fun i j => b j i
  have hU : Uᴴ * U = 1 := conjTranspose_mul_self_of_orthonormalBasis c
  have hV : Vᴴ * V = 1 := conjTranspose_mul_self_of_orthonormalBasis b
  have hU' : U * Uᴴ = 1 := mul_conjTranspose_eq_one_of_conjTranspose_mul_eq_one rfl hU
  have hV' : V * Vᴴ = 1 := mul_conjTranspose_eq_one_of_conjTranspose_mul_eq_one rfl hV
  have hAV : A * V = U * rectDiag σ := by
    ext i j
    have hl : (A * V) i j = T (b j) i := by
      rw [← hTdef]
      simp [V, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [hl]
    simp only [Matrix.mul_apply, U, rectDiag_apply_ofReal, Matrix.of_apply, mul_ite, mul_zero]
    by_cases hj : σ j = 0
    · have h0 : T (b j) = 0 := by
        rw [← inner_self_eq_zero (𝕜 := 𝕜), key, if_pos rfl, hj]; simp
      rw [h0, Finset.sum_eq_zero]
      · rfl
      intro k _
      split_ifs with hk
      · rw [hk, hj, RCLike.ofReal_zero, mul_zero]
      · rfl
    · have hjm := hlt j hj
      rw [Finset.sum_eq_single ⟨j, hjm⟩]
      · rw [if_pos rfl, hc ⟨j, hjm⟩ hj]
        simp only [v, dif_pos j.isLt]
        have : (σ j : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 hj
        simp
        field_simp
      · intro k _ hk
        rw [if_neg]
        exact fun h => hk (Fin.ext h)
      · simp
  refine ⟨U, V, hU, hV, ?_, hU', hV'⟩
  subst hσ
  rw [← hAV, Matrix.mul_assoc, hV', Matrix.mul_one]

/-- Sum over `Fin n` of a function vanishing at indices `≥ min m n`. -/
private lemma sum_fin_eq_sum_fin_min {m n : ℕ} {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (hf : ∀ k, min m n ≤ k → f k = 0) :
    ∑ k : Fin n, f k = ∑ k : Fin (min m n), f k := by
  rw [Fin.sum_univ_eq_sum_range f, Fin.sum_univ_eq_sum_range f]
  symm
  apply Finset.sum_subset
  · intro k hk; simp at hk ⊢; omega
  · intro k _ hk; exact hf k (by simp only [Finset.mem_range, min_le_iff] at hk ⊢; omega)

namespace IsSVD

variable {p q : ℕ} {A : Matrix m n 𝕜} {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜}

/-- The left factor of an SVD is square: `p = card m`. Atlas `svd`. -/
theorem card_left (h : IsSVD A U V) : Fintype.card m = p :=
  card_eq_of_conjTranspose_mul_eq_one h.conjTranspose_mul_left h.mul_conjTranspose_left

/-- The right factor of an SVD is square: `q = card n`. Atlas `svd`. -/
theorem card_right (h : IsSVD A U V) : Fintype.card n = q :=
  card_eq_of_conjTranspose_mul_eq_one h.conjTranspose_mul_right h.mul_conjTranspose_right

/-- `A V = U Σ`, i.e. `A vₖ = σₖ uₖ`. Atlas `svd`. -/
theorem mul_right (h : IsSVD A U V) : A * V = U * rectDiag (singularValues A) := by
  conv_lhs => rw [h.eq]
  rw [Matrix.mul_assoc, h.conjTranspose_mul_right, Matrix.mul_one]

/-- `Uᴴ A = Σ Vᴴ`, i.e. `Aᴴ uₖ = σₖ vₖ`. Atlas `svd`. -/
theorem conjTranspose_mul (h : IsSVD A U V) : Uᴴ * A = rectDiag (singularValues A) * Vᴴ := by
  conv_lhs => rw [h.eq]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.conjTranspose_mul_left, Matrix.one_mul]

/-- `Uᴴ A V = Σ`. Atlas `svd`. -/
theorem conjTranspose_mul_mul (h : IsSVD A U V) : Uᴴ * A * V = rectDiag (singularValues A) := by
  rw [Matrix.mul_assoc, h.mul_right, ← Matrix.mul_assoc, h.conjTranspose_mul_left,
    Matrix.one_mul]

/-- `Aᴴ = V Σᴴ Uᴴ`: an SVD of the conjugate transpose. Atlas `svd`. -/
theorem conjTranspose_eq (h : IsSVD A U V) :
    Aᴴ = V * (rectDiag (singularValues A) : Matrix (Fin q) (Fin p) 𝕜) * Uᴴ := by
  conv_lhs => rw [h.eq]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    conjTranspose_rectDiag, Matrix.mul_assoc]

/-- `AᴴA = V diag(σ₀², …, σ_{q-1}²) Vᴴ`: the right singular vectors diagonalize the Gram matrix
(Horn–Johnson 2013, §2.6). Atlas `svd`. -/
theorem conjTranspose_mul_self (h : IsSVD A U V) :
    Aᴴ * A = V * Matrix.diagonal (fun j : Fin q => ((singularValues A j ^ 2 : ℝ) : 𝕜)) * Vᴴ := by
  have hd : (Matrix.diagonal fun j : Fin q =>
        if (j : ℕ) < p then ((singularValues A j ^ 2 : ℝ) : 𝕜) else 0) =
      Matrix.diagonal (fun j : Fin q => ((singularValues A j ^ 2 : ℝ) : 𝕜)) := by
    congr 1; funext j
    split_ifs with hj
    · rfl
    · rw [singularValues_eq_zero_of_height_le A (by rw [h.card_left]; exact not_lt.1 hj)]
      simp
  set S : Matrix (Fin p) (Fin q) 𝕜 := rectDiag (singularValues A)
  calc Aᴴ * A = (U * S * Vᴴ)ᴴ * (U * S * Vᴴ) := by rw [← h.eq]
    _ = V * (Sᴴ * (Uᴴ * U) * S) * Vᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = _ := by
      rw [h.conjTranspose_mul_left, Matrix.mul_one, conjTranspose_rectDiag_mul_rectDiag, hd]

/-- `AAᴴ = U diag(σ₀², …, σ_{p-1}²) Uᴴ`: the left singular vectors diagonalize `AAᴴ`.
Atlas `svd`. -/
theorem mul_conjTranspose_self (h : IsSVD A U V) :
    A * Aᴴ = U * Matrix.diagonal (fun i : Fin p => ((singularValues A i ^ 2 : ℝ) : 𝕜)) * Uᴴ := by
  have hd : (Matrix.diagonal fun i : Fin p =>
        if (i : ℕ) < q then ((singularValues A i ^ 2 : ℝ) : 𝕜) else 0) =
      Matrix.diagonal (fun i : Fin p => ((singularValues A i ^ 2 : ℝ) : 𝕜)) := by
    congr 1; funext i
    split_ifs with hi
    · rfl
    · rw [singularValues_eq_zero_of_width_le A (by rw [h.card_right]; exact not_lt.1 hi)]
      simp
  set S : Matrix (Fin p) (Fin q) 𝕜 := rectDiag (singularValues A)
  calc A * Aᴴ = (U * S * Vᴴ) * (U * S * Vᴴ)ᴴ := by rw [← h.eq]
    _ = U * (S * (Vᴴ * V) * Sᴴ) * Uᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = _ := by
      rw [h.conjTranspose_mul_right, Matrix.mul_one, rectDiag_mul_conjTranspose_rectDiag, hd]

/-- Thin-SVD / outer-product expansion, entrywise:
`A i j = ∑_{k < min p q} σ_k U_{ik} conj(V_{jk})`, i.e. `A = ∑_k σ_k u_k v_kᴴ`
(Horn–Johnson 2013, §2.6; HMT 2011, §2.1). Atlas `svd`. -/
theorem apply (h : IsSVD A U V) (i : m) (j : n) :
    A i j = ∑ k : Fin (min p q), (singularValues A k : 𝕜) *
      U i (Fin.castLE (min_le_left p q) k) * star (V j (Fin.castLE (min_le_right p q) k)) := by
  let g : ℕ → 𝕜 := fun k => if h : k < p ∧ k < q then
    (singularValues A k : 𝕜) * U i ⟨k, h.1⟩ * star (V j ⟨k, h.2⟩) else 0
  have hg : ∀ k, min p q ≤ k → g k = 0 := fun k hk => by
    simp only [g]; split_ifs
    · rw [singularValues_eq_zero_of_min_le A (by rw [h.card_left, h.card_right]; exact hk)]
      simp
    · rfl
  have rhs : ∀ k : Fin (min p q), (singularValues A k : 𝕜) *
      U i (Fin.castLE (min_le_left p q) k) * star (V j (Fin.castLE (min_le_right p q) k)) =
      g k := fun k => by
    have h1 : (k : ℕ) < p := lt_of_lt_of_le k.isLt (min_le_left p q)
    have h2 : (k : ℕ) < q := lt_of_lt_of_le k.isLt (min_le_right p q)
    simp only [g, dif_pos (And.intro h1 h2)]; rfl
  simp_rw [rhs]
  rw [← sum_fin_eq_sum_fin_min g hg]
  conv_lhs => rw [h.eq]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, rectDiag_apply_ofReal]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : (k : ℕ) < p
  · rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp only [g, dif_pos (And.intro hk k.isLt), if_true]; ring
    · intro l _ hl; rw [if_neg (fun e => hl (Fin.ext e)), mul_zero]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [g, hk]
    · intro l _; rw [if_neg (fun (e : (l : ℕ) = k) => hk (e ▸ l.isLt)), mul_zero]

/-- Block SVD split at index `k` (HMT 2011, §2.1, `A = U₁Σ₁V₁ᴴ + U₂Σ₂V₂ᴴ`): the head
`U Σ_{<k} Vᴴ` (the truncated SVD) plus the tail `U Σ_{≥k} Vᴴ`. Atlas `svd`.
atlas: svd -/
theorem eq_head_add_tail (h : IsSVD A U V) (k : ℕ) :
    A = U * (rectDiag (fun i => if i < k then singularValues A i else 0) :
        Matrix (Fin p) (Fin q) 𝕜) * Vᴴ +
      U * (rectDiag (fun i => if i < k then 0 else singularValues A i) :
        Matrix (Fin p) (Fin q) 𝕜) * Vᴴ := by
  rw [← Matrix.add_mul, ← Matrix.mul_add, ← rectDiag_add]
  convert h.eq using 4
  funext i
  simp only [Pi.add_apply]; split_ifs <;> simp


end IsSVD

omit [DecidableEq m] in
/-- For a Hermitian `S = W diag(μ) Wᴴ` with `W : Matrix n (Fin q) 𝕜`, `WᴴW = 1`, `q = card n`
and `μ` real and non-increasing, `μ` is Mathlib's sorted eigenvalue list `eigenvalues₀` of `S`
(uniqueness of the sorted spectrum, via the characteristic polynomial). Atlas `svd` (helper;
belongs with the spectral API). -/
theorem eigenvalues₀_eq_of_eq_mul_diagonal_mul {q : ℕ} {S : Matrix n n 𝕜}
    {W : Matrix n (Fin q) 𝕜} (hS : S.IsHermitian) {μ : Fin q → ℝ} (hμ : Antitone μ)
    (hW : Wᴴ * W = 1) (hq : Fintype.card n = q)
    (hSW : S = W * Matrix.diagonal (fun i => (μ i : 𝕜)) * Wᴴ) (k : Fin q) :
    hS.eigenvalues₀ (Fin.cast hq.symm k) = μ k := by
  have hc : S.charpoly = (Matrix.diagonal fun i => (μ i : 𝕜)).charpoly := by
    rw [hSW, Matrix.mul_assoc, Matrix.charpoly_mul_comm_of_le _ _
      (by rw [Fintype.card_fin, hq]), Fintype.card_fin, hq, Nat.sub_self, pow_zero, one_mul,
      Matrix.mul_assoc, hW, Matrix.mul_one]
  have hsort := hS.sort_roots_charpoly_eq_eigenvalues₀
  rw [hc, Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at hsort
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map,
    Function.comp_def, RCLike.ofReal_re] at hsort
  have hl : List.ofFn hS.eigenvalues₀ = List.ofFn μ := by
    rw [← hsort]
    simp_rw [Fin.univ_val_map, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hμ.sortedGE_ofFn
  have := congrArg (fun l : List ℝ => l.getD k 0) hl
  have hk : (k : ℕ) < Fintype.card n := hq ▸ k.isLt
  simp [hk] at this
  exact this

omit [DecidableEq m] in
/-- **Uniqueness of singular values** (Horn–Johnson 2013, Thm 2.6.3): if `A = U Σ_τ Vᴴ` with
`U`, `V` having orthonormal columns, `V` square (`q = card n`, discharged automatically for
`V : Matrix (Fin b) (Fin b) 𝕜` and `V : Matrix n (Fin (card n)) 𝕜`) and `τ` nonnegative and
non-increasing, then `τ k = σ_k(A)` for every `k < min p q`. Atlas `svd`.
atlas: svd -/
theorem singularValues_eq_of_eq_mul_rectDiag_mul {p q : ℕ} {A : Matrix m n 𝕜}
    {U : Matrix m (Fin p) 𝕜} {V : Matrix n (Fin q) 𝕜} {τ : ℕ → ℝ}
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (hτ0 : ∀ k, 0 ≤ τ k) (hτ : Antitone τ)
    (hA : A = U * (rectDiag τ : Matrix (Fin p) (Fin q) 𝕜) * Vᴴ) {k : ℕ} (hk : k < min p q)
    (hq : Fintype.card n = q := by first | exact Fintype.card_fin _ | rfl) :
    singularValues A k = τ k := by
  have hkm : k < p := lt_of_lt_of_le hk (min_le_left p q)
  have hkn : k < q := lt_of_lt_of_le hk (min_le_right p q)
  set μ : Fin q → ℝ := fun j => if (j : ℕ) < p then τ j ^ 2 else 0
  have hμ : Antitone μ := by
    intro a b hab
    simp only [μ]
    split_ifs with hb ha ha
    · exact pow_le_pow_left₀ (hτ0 _) (hτ hab) 2
    · exact absurd (lt_of_le_of_lt (Fin.le_def.1 hab) hb) ha
    · exact sq_nonneg _
    · exact le_rfl
  have hAA : Aᴴ * A = V * Matrix.diagonal (fun j => (μ j : 𝕜)) * Vᴴ := by
    set Sg : Matrix (Fin p) (Fin q) 𝕜 := rectDiag τ
    calc Aᴴ * A = (U * Sg * Vᴴ)ᴴ * (U * Sg * Vᴴ) := by rw [← hA]
      _ = V * (Sgᴴ * (Uᴴ * U) * Sg) * Vᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by
        rw [hU, Matrix.mul_one, conjTranspose_rectDiag_mul_rectDiag]
        congr 3; funext j
        simp only [μ]; split_ifs <;> simp
  have hH := Matrix.isHermitian_conjTranspose_mul_self A
  have e1 := sq_singularValues_eq_eigenvalues₀ A (Fin.cast hq.symm ⟨k, hkn⟩)
  rw [eigenvalues₀_eq_of_eq_mul_diagonal_mul hH hμ hV hq hAA] at e1
  simp only [μ, if_pos hkm] at e1
  exact (sq_eq_sq₀ (singularValues_nonneg A k) (hτ0 k)).1 e1

end Decomposition

end NLAlib
