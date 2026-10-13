import NLAlib.Matrix.Functions.PolynomialCalculus
import NLAlib.Matrix.Subspaces.Projections
import Mathlib.Analysis.Matrix.Order

/-!
# Courant–Fischer min-max theorem

For a Hermitian matrix `A` over `𝕜` (`ℝ` or `ℂ`, `[RCLike 𝕜]`) with sorted eigenvalues
`λ₀ ≥ λ₁ ≥ ⋯` (Mathlib's `Matrix.IsHermitian.eigenvalues₀`, zero-indexed and non-increasing),
writing `q(x) = re (xᴴAx)` (`RCLike.re (quadForm A x)`) and `‖x‖² = re (xᴴx)`:

* `Matrix.IsHermitian.eigenvalues₀_le_of_forall_mem`: if `q(x) ≤ c ‖x‖²` on a subspace of
  codimension at most `k`, then `λ_k ≤ c` (min-max half);
* `Matrix.IsHermitian.le_eigenvalues₀_of_forall_mem`: if `c ‖x‖² ≤ q(x)` on a subspace of
  dimension at least `k+1`, then `c ≤ λ_k` (max-min half);
* the attaining subspaces (spans of eigenvectors, written as kernels of eigen-coordinates):
  `exists_submodule_eigenvalues₀_mul_le` and `exists_submodule_le_eigenvalues₀_mul`;
* the equational forms `λ_k = ⨆_{dim S ≥ k+1} ⨅_{0 ≠ x ∈ S} ρ(x)` and
  `λ_k = ⨅_{codim W ≤ k} ⨆_{0 ≠ x ∈ W} ρ(x)` with the Rayleigh quotient `ρ = rayleighQuotient A`
  (`eigenvalues₀_eq_iSup_iInf`, `eigenvalues₀_eq_iInf_iSup`);
* the singular-value form for `σ_k(A)² = λ_k(AᴴA)`: `singularValues_le_of_forall_mem`,
  `le_singularValues_of_forall_mem` and their attaining subspaces;
* consequences: Loewner monotonicity of eigenvalues (`A ≤ B` under `open scoped MatrixOrder`),
  the eigenvalue Weyl inequality `λ_{i+j}(A+B) ≤ λ_i(A) + λ_j(B)`, and Cauchy/Poincaré
  interlacing for compressions `QᴴAQ` and for principal submatrices `A.submatrix e e`.

Over `ℝ`, `q(x)` is `xᵀAx` and `re (xᴴx)` is `xᵀx` by definitional unfolding; a real caller
whose goal is stated with `⬝ᵥ` uses `simp only [quadForm_def, star_trivial, RCLike.re_to_real]`.
Lemmas whose first explicit argument is `hA : A.IsHermitian` live in the namespace
`Matrix.IsHermitian` (dot notation `hA.eigenvalues₀_add_le`).

Proof: a dimension count (`LinearMap.ker_ne_bot_of_finrank_lt`, rank–nullity) against the
coordinates `⟨uⱼ, x⟩` in the sorted eigenbasis, and the expansion `q(x) = ∑ⱼ λⱼ |⟨uⱼ, x⟩|²`
from Mathlib's spectral theorem.

Source: Horn–Johnson 2013, Thm 4.2.6 (Courant–Fischer), Cor 4.3.37 (Poincaré separation),
Thm 4.3.17 (principal submatrices), Cor 4.3.12 (monotonicity), Thm 4.3.1 (Weyl);
Horn–Johnson 2013, §7.3 (singular values).
Labels other than Thm 4.2.6 are marked "verify" where they were not checked against the print.
HJ index eigenvalues increasingly from `1`; here they are decreasing and zero-indexed.
Audit G0 A1, B1, B7, B8, C6. Atlas: `courant-fischer`, `cauchy-interlacing`.
-/

noncomputable section

open scoped Matrix MatrixOrder
open Module

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

namespace CourantFischer

omit [DecidableEq n] in
private theorem re_star_dotProduct_self (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ x) = ∑ i, ‖x i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, map_sum, RCLike.star_def, RCLike.conj_mul,
    ← RCLike.ofReal_pow, RCLike.ofReal_re]

omit [DecidableEq n] in
private theorem re_star_dotProduct_self_pos {x : n → 𝕜} (hx : x ≠ 0) :
    0 < RCLike.re (star x ⬝ᵥ x) := by
  rw [re_star_dotProduct_self]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  exact Finset.sum_pos' (fun j _ => sq_nonneg _)
    ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩

private theorem re_star_dotProduct_diagonal_mulVec (d : n → ℝ) (y : n → 𝕜) :
    RCLike.re (star y ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ d) *ᵥ y)) =
      ∑ i, d i * ‖y i‖ ^ 2 := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, map_sum, Function.comp_apply,
    RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
    RCLike.ofReal_re]

variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)

/-- The reindexing `Fin (card n) ≃ n` under which Mathlib sorts the eigenvalues. -/
private def e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)

/-- The coordinate of `x` along the `j`-th sorted eigenvector. -/
private def coord (j : Fin (Fintype.card n)) (x : n → 𝕜) : 𝕜 :=
  star ⇑(hA.eigenvectorBasis (e j)) ⬝ᵥ x

private theorem eigenvalues_e (j : Fin (Fintype.card n)) :
    hA.eigenvalues (e j) = hA.eigenvalues₀ j := by
  simp [Matrix.IsHermitian.eigenvalues, e]

private theorem star_eigenvectorUnitary_mulVec_apply (x : n → 𝕜) (i : n) :
    (star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ x) i =
      star ⇑(hA.eigenvectorBasis i) ⬝ᵥ x := by
  simp only [Matrix.mulVec, dotProduct, Matrix.star_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply, Pi.star_apply]

private theorem re_quadForm_eq_sum (x : n → 𝕜) :
    RCLike.re (quadForm A x) = ∑ j, hA.eigenvalues₀ j * ‖coord hA j x‖ ^ 2 := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜)
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hD : star U * A * U = Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, U] using h
  have hx : x = U *ᵥ (star U *ᵥ x) := by rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  have hq : quadForm A x =
      star (star U *ᵥ x) ⬝ᵥ ((star U * A * U) *ᵥ (star U *ᵥ x)) := by
    set y := star U *ᵥ x
    rw [quadForm_def, hx, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose]
  rw [hq, hD, re_star_dotProduct_diagonal_mulVec, ← (e (n := n)).sum_comp]
  simp only [coord, eigenvalues_e, star_eigenvectorUnitary_mulVec_apply, U]

private theorem re_star_dotProduct_self_eq_sum (x : n → 𝕜) :
    RCLike.re (star x ⬝ᵥ x) = ∑ j, ‖coord hA j x‖ ^ 2 := by
  set U : Matrix n n 𝕜 := (hA.eigenvectorUnitary : Matrix n n 𝕜)
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have h := star_mulVec_dotProduct_mulVec_self (star U) x
  rw [← Matrix.star_eq_conjTranspose, star_star, hUU, Matrix.one_mulVec] at h
  rw [← h, re_star_dotProduct_self, ← (e (n := n)).sum_comp]
  simp only [coord, star_eigenvectorUnitary_mulVec_apply, U]

/-- If the coordinates above `k` vanish, the Rayleigh quotient is at least `λ_k`. -/
private theorem eigenvalues₀_mul_le_of_coord (k : Fin (Fintype.card n)) {x : n → 𝕜}
    (hx : ∀ j, k < j → coord hA j x = 0) :
    hA.eigenvalues₀ k * RCLike.re (star x ⬝ᵥ x) ≤ RCLike.re (quadForm A x) := by
  rw [re_quadForm_eq_sum hA, re_star_dotProduct_self_eq_sum hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases le_or_gt j k with hjk | hjk
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone hjk) (sq_nonneg _)
  · simp [hx j hjk]

/-- If the coordinates below `k` vanish, the Rayleigh quotient is at most `λ_k`. -/
private theorem le_eigenvalues₀_mul_of_coord (k : Fin (Fintype.card n)) {x : n → 𝕜}
    (hx : ∀ j, j < k → coord hA j x = 0) :
    RCLike.re (quadForm A x) ≤ hA.eigenvalues₀ k * RCLike.re (star x ⬝ᵥ x) := by
  rw [re_quadForm_eq_sum hA, re_star_dotProduct_self_eq_sum hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases lt_or_ge j k with hjk | hjk
  · simp [hx j hjk]
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone hjk) (sq_nonneg _)

/-- The coordinates strictly above `k`, as a linear map. -/
private def hiMat (k : Fin (Fintype.card n)) :
    (n → 𝕜) →ₗ[𝕜] (Fin (Fintype.card n - (k + 1)) → 𝕜) :=
  Matrix.mulVecLin (Matrix.of fun t i => star (⇑(hA.eigenvectorBasis (e ⟨k + 1 + t, by omega⟩)) i))

/-- The coordinates strictly below `k`, as a linear map. -/
private def loMat (k : Fin (Fintype.card n)) : (n → 𝕜) →ₗ[𝕜] (Fin k → 𝕜) :=
  Matrix.mulVecLin (Matrix.of fun t i => star (⇑(hA.eigenvectorBasis (e ⟨t, by omega⟩)) i))

private theorem coord_of_hiMat (k : Fin (Fintype.card n)) {x : n → 𝕜}
    (hx : hiMat hA k x = 0) (j : Fin (Fintype.card n)) (hj : k < j) :
    coord hA j x = 0 := by
  have h := congrFun hx ⟨j - (k + 1), by omega⟩
  have hj' : (⟨k + 1 + (j - (k + 1)), by omega⟩ : Fin (Fintype.card n)) = j := by
    ext; simp only; omega
  simpa [hiMat, coord, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hj'] using h

private theorem coord_of_loMat (k : Fin (Fintype.card n)) {x : n → 𝕜}
    (hx : loMat hA k x = 0) (j : Fin (Fintype.card n)) (hj : j < k) :
    coord hA j x = 0 := by
  have h := congrFun hx ⟨j, hj⟩
  simpa [loMat, coord, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using h

omit [DecidableEq n] in
/-- A subspace of dimension larger than `p` meets the kernel of any linear map to `𝕜^p`. -/
private theorem exists_mem_ne_zero_mulVec_eq_zero {p : ℕ} (M : (n → 𝕜) →ₗ[𝕜] (Fin p → 𝕜))
    (W : Submodule 𝕜 (n → 𝕜)) (hW : p < finrank 𝕜 W) :
    ∃ x ∈ W, x ≠ 0 ∧ M x = 0 := by
  have hker : LinearMap.ker (M.domRestrict W) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by rwa [Module.finrank_fin_fun])
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨y, y.2, fun h => hy0 (Subtype.ext h), ?_⟩
  simpa using hy

omit [DecidableEq n] in
/-- The kernel of a linear map to `𝕜^p` has dimension at least `card n - p`. -/
private theorem card_le_finrank_ker_add {p : ℕ} (M : (n → 𝕜) →ₗ[𝕜] (Fin p → 𝕜)) :
    Fintype.card n ≤ finrank 𝕜 (LinearMap.ker M) + p := by
  have h := LinearMap.finrank_range_add_finrank_ker M
  have hr : finrank 𝕜 (LinearMap.range M) ≤ p := by
    simpa using (LinearMap.range M).finrank_le
  rw [Module.finrank_fintype_fun_eq_card] at h
  omega

omit [DecidableEq n] in
/-- A subspace of positive dimension contains a nonzero vector. -/
private theorem nonempty_of_finrank_pos {W : Submodule 𝕜 (n → 𝕜)} (hW : 0 < finrank 𝕜 W) :
    Nonempty {x : n → 𝕜 // x ∈ W ∧ x ≠ 0} := by
  obtain ⟨x, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hW
  exact ⟨⟨x, x.2, fun h => hx0 (Subtype.ext h)⟩⟩

/-- The Rayleigh quotient of a nonzero vector lies between the extreme eigenvalues. -/
private theorem rayleighQuotient_mem (k : Fin (Fintype.card n)) {x : n → 𝕜} (hx : x ≠ 0) :
    hA.eigenvalues₀ ⟨Fintype.card n - 1, by have := k.isLt; omega⟩ ≤ rayleighQuotient A x ∧
      rayleighQuotient A x ≤ hA.eigenvalues₀ ⟨0, by have := k.isLt; omega⟩ := by
  have hpos := re_star_dotProduct_self_pos hx
  rw [rayleighQuotient_def, le_div_iff₀ hpos, div_le_iff₀ hpos]
  refine ⟨eigenvalues₀_mul_le_of_coord hA _ fun j hj => ?_,
    le_eigenvalues₀_mul_of_coord hA _ fun j hj => ?_⟩
  · exact absurd hj (by rw [Fin.lt_def]; dsimp only; have := j.isLt; omega)
  · exact absurd hj (by rw [Fin.lt_def]; dsimp only; omega)

end CourantFischer

open CourantFischer

/-- **Courant–Fischer, min-max half.** For Hermitian `A`, if `re (xᴴAx) ≤ c · re (xᴴx)` on a
subspace `W` of codimension at most `k` (`card n ≤ dim W + k`), then the `k`-th largest
eigenvalue satisfies `λ_k ≤ c`. Horn–Johnson 2013, Thm 4.2.6 (HJ order eigenvalues
increasingly and from `1`; here `eigenvalues₀` is decreasing and zero-indexed). Audit G0 A1;
atlas `courant-fischer`. No sign condition on `c` is needed.
atlas: courant-fischer -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_le_of_forall_mem {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : Fin (Fintype.card n)) (W : Submodule 𝕜 (n → 𝕜))
    (hW : Fintype.card n ≤ finrank 𝕜 W + k) {c : ℝ}
    (hAW : ∀ x ∈ W, RCLike.re (quadForm A x) ≤ c * RCLike.re (star x ⬝ᵥ x)) :
    hA.eigenvalues₀ k ≤ c := by
  obtain ⟨x, hxW, hx0, hx⟩ :=
    exists_mem_ne_zero_mulVec_eq_zero (hiMat hA k) W (by omega)
  have h1 := eigenvalues₀_mul_le_of_coord hA k (coord_of_hiMat hA k hx)
  have h2 := hAW x hxW
  exact le_of_mul_le_mul_right (h1.trans h2) (re_star_dotProduct_self_pos hx0)

/-- **Courant–Fischer, max-min half.** For Hermitian `A`, if `c · re (xᴴx) ≤ re (xᴴAx)` on a
subspace `S` of dimension at least `k + 1`, then `c ≤ λ_k`. Horn–Johnson 2013, Thm 4.2.6
(decreasing, zero-indexed convention). Audit G0 A1; atlas `courant-fischer`.
atlas: courant-fischer -/
theorem _root_.Matrix.IsHermitian.le_eigenvalues₀_of_forall_mem {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : Fin (Fintype.card n)) (S : Submodule 𝕜 (n → 𝕜))
    (hS : (k : ℕ) + 1 ≤ finrank 𝕜 S) {c : ℝ}
    (hAS : ∀ x ∈ S, c * RCLike.re (star x ⬝ᵥ x) ≤ RCLike.re (quadForm A x)) :
    c ≤ hA.eigenvalues₀ k := by
  obtain ⟨x, hxS, hx0, hx⟩ :=
    exists_mem_ne_zero_mulVec_eq_zero (loMat hA k) S (by omega)
  have h1 := le_eigenvalues₀_mul_of_coord hA k (coord_of_loMat hA k hx)
  have h2 := hAS x hxS
  exact le_of_mul_le_mul_right (h2.trans h1) (re_star_dotProduct_self_pos hx0)

/-- **Courant–Fischer, attaining subspace for the max-min half**: there is a subspace of
dimension at least `k + 1` (the span of the top `k + 1` eigenvectors) on which
`λ_k · re (xᴴx) ≤ re (xᴴAx)`. Horn–Johnson 2013, proof of Thm 4.2.6. Audit G0 C6;
atlas `courant-fischer`. Deviation: the dimension is stated as a lower bound.
atlas: courant-fischer -/
theorem _root_.Matrix.IsHermitian.exists_submodule_eigenvalues₀_mul_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    ∃ S : Submodule 𝕜 (n → 𝕜), (k : ℕ) + 1 ≤ finrank 𝕜 S ∧
      ∀ x ∈ S, hA.eigenvalues₀ k * RCLike.re (star x ⬝ᵥ x) ≤ RCLike.re (quadForm A x) := by
  refine ⟨LinearMap.ker (hiMat hA k), ?_, fun x hx => ?_⟩
  · have := card_le_finrank_ker_add (hiMat hA k)
    omega
  · exact eigenvalues₀_mul_le_of_coord hA k (coord_of_hiMat hA k (LinearMap.mem_ker.mp hx))

/-- **Courant–Fischer, attaining subspace for the min-max half**: there is a subspace of
codimension at most `k` (the span of the eigenvectors `k, k+1, …`) on which
`re (xᴴAx) ≤ λ_k · re (xᴴx)`. Horn–Johnson 2013, proof of Thm 4.2.6. Audit G0 C6;
atlas `courant-fischer`.
atlas: courant-fischer -/
theorem _root_.Matrix.IsHermitian.exists_submodule_le_eigenvalues₀_mul {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    ∃ W : Submodule 𝕜 (n → 𝕜), Fintype.card n ≤ finrank 𝕜 W + k ∧
      ∀ x ∈ W, RCLike.re (quadForm A x) ≤ hA.eigenvalues₀ k * RCLike.re (star x ⬝ᵥ x) :=
  ⟨LinearMap.ker (loMat hA k), card_le_finrank_ker_add (loMat hA k),
    fun _ hx => le_eigenvalues₀_mul_of_coord hA k (coord_of_loMat hA k (LinearMap.mem_ker.mp hx))⟩

/-- **Courant–Fischer, max-min formula.** For Hermitian `A`,
`λ_k = max_{dim S ≥ k+1} min_{0 ≠ x ∈ S} ρ(x)`, written with `⨆`/`⨅` (both attained) and the
Rayleigh quotient `ρ = rayleighQuotient A`. Horn–Johnson 2013, Thm 4.2.6 (decreasing,
zero-indexed convention). Audit G0 A1; atlas `courant-fischer`.
atlas: courant-fischer -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_eq_iSup_iInf {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k =
      ⨆ S : {S : Submodule 𝕜 (n → 𝕜) // (k : ℕ) + 1 ≤ finrank 𝕜 S},
        ⨅ x : {x : n → 𝕜 // x ∈ S.1 ∧ x ≠ 0}, rayleighQuotient A x.1 := by
  have hinner : ∀ S : {S : Submodule 𝕜 (n → 𝕜) // (k : ℕ) + 1 ≤ finrank 𝕜 S},
      (⨅ x : {x : n → 𝕜 // x ∈ S.1 ∧ x ≠ 0}, rayleighQuotient A x.1) ≤ hA.eigenvalues₀ k := by
    intro S
    obtain ⟨x, hxS, hx0, hx⟩ :=
      exists_mem_ne_zero_mulVec_eq_zero (loMat hA k) S.1 (by have := S.2; omega)
    have h1 := le_eigenvalues₀_mul_of_coord hA k (coord_of_loMat hA k hx)
    refine (ciInf_le ⟨hA.eigenvalues₀ ⟨Fintype.card n - 1, by have := k.isLt; omega⟩, ?_⟩
      ⟨x, hxS, hx0⟩).trans ?_
    · rintro _ ⟨y, rfl⟩
      exact (rayleighQuotient_mem hA k y.2.2).1
    · rw [rayleighQuotient_def, div_le_iff₀ (re_star_dotProduct_self_pos hx0)]
      exact h1
  refine le_antisymm ?_ ?_
  · obtain ⟨S, hS, hAS⟩ := hA.exists_submodule_eigenvalues₀_mul_le k
    have := nonempty_of_finrank_pos (W := S) (by omega)
    refine le_ciSup_of_le ⟨hA.eigenvalues₀ k, ?_⟩ ⟨S, hS⟩ (le_ciInf fun x => ?_)
    · rintro _ ⟨S, rfl⟩
      exact hinner S
    · rw [rayleighQuotient_def, le_div_iff₀ (re_star_dotProduct_self_pos x.2.2)]
      exact hAS x.1 x.2.1
  · have : Nonempty {S : Submodule 𝕜 (n → 𝕜) // (k : ℕ) + 1 ≤ finrank 𝕜 S} :=
      ⟨⟨⊤, by rw [finrank_top, Module.finrank_fintype_fun_eq_card]; omega⟩⟩
    exact ciSup_le hinner

/-- **Courant–Fischer, min-max formula.** For Hermitian `A`,
`λ_k = min_{codim W ≤ k} max_{0 ≠ x ∈ W} ρ(x)`, written with `⨅`/`⨆` (both attained) and the
Rayleigh quotient `ρ = rayleighQuotient A`; codimension at most `k` is
`card n ≤ dim W + k`. Horn–Johnson 2013, Thm 4.2.6. Audit G0 A1; atlas `courant-fischer`.
atlas: courant-fischer -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_eq_iInf_iSup {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k =
      ⨅ W : {W : Submodule 𝕜 (n → 𝕜) // Fintype.card n ≤ finrank 𝕜 W + k},
        ⨆ x : {x : n → 𝕜 // x ∈ W.1 ∧ x ≠ 0}, rayleighQuotient A x.1 := by
  have hinner : ∀ W : {W : Submodule 𝕜 (n → 𝕜) // Fintype.card n ≤ finrank 𝕜 W + k},
      hA.eigenvalues₀ k ≤ ⨆ x : {x : n → 𝕜 // x ∈ W.1 ∧ x ≠ 0}, rayleighQuotient A x.1 := by
    intro W
    obtain ⟨x, hxW, hx0, hx⟩ :=
      exists_mem_ne_zero_mulVec_eq_zero (hiMat hA k) W.1 (by have := W.2; omega)
    have h1 := eigenvalues₀_mul_le_of_coord hA k (coord_of_hiMat hA k hx)
    refine le_trans ?_ (le_ciSup ⟨hA.eigenvalues₀ ⟨0, by have := k.isLt; omega⟩, ?_⟩ ⟨x, hxW, hx0⟩)
    · rw [rayleighQuotient_def, le_div_iff₀ (re_star_dotProduct_self_pos hx0)]
      exact h1
    · rintro _ ⟨y, rfl⟩
      exact (rayleighQuotient_mem hA k y.2.2).2
  refine le_antisymm ?_ ?_
  · have : Nonempty {W : Submodule 𝕜 (n → 𝕜) // Fintype.card n ≤ finrank 𝕜 W + k} :=
      ⟨⟨⊤, by rw [finrank_top, Module.finrank_fintype_fun_eq_card]; omega⟩⟩
    exact le_ciInf hinner
  · obtain ⟨W, hW, hAW⟩ := hA.exists_submodule_le_eigenvalues₀_mul k
    have := nonempty_of_finrank_pos (W := W) (by omega)
    refine ciInf_le_of_le ⟨hA.eigenvalues₀ k, ?_⟩ ⟨W, hW⟩ (ciSup_le fun x => ?_)
    · rintro _ ⟨W, rfl⟩
      exact hinner W
    · rw [rayleighQuotient_def, div_le_iff₀ (re_star_dotProduct_self_pos x.2.2)]
      exact hAW x.1 x.2.1

/-! ### Dimension count for intersections -/

omit [DecidableEq n] in
/-- Codimensions add under intersection: if `card n ≤ dim W₁ + a` and `card n ≤ dim W₂ + b`
then `card n ≤ dim (W₁ ⊓ W₂) + (a + b)`. Helper for the Weyl inequalities;
atlas `courant-fischer`. -/
theorem card_le_finrank_inf_add {W₁ W₂ : Submodule 𝕜 (n → 𝕜)} {a b : ℕ}
    (h₁ : Fintype.card n ≤ finrank 𝕜 W₁ + a) (h₂ : Fintype.card n ≤ finrank 𝕜 W₂ + b) :
    Fintype.card n ≤ finrank 𝕜 (W₁ ⊓ W₂ : Submodule 𝕜 (n → 𝕜)) + (a + b) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₂
  have hs : finrank 𝕜 (W₁ ⊔ W₂ : Submodule 𝕜 (n → 𝕜)) ≤ Fintype.card n := by
    simpa [Module.finrank_fintype_fun_eq_card] using (W₁ ⊔ W₂).finrank_le
  omega

/-! ### Consequences for eigenvalues -/

/-- **Loewner monotonicity of eigenvalues.** If `A ≤ B` in the Loewner order (`B − A` positive
semidefinite; `open scoped MatrixOrder`) then `λ_k(A) ≤ λ_k(B)` for every `k`. Horn–Johnson
2013, Cor 4.3.12. Audit G0 B7; atlas `courant-fischer`.
atlas: weyl-mirsky -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_of_le {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A ≤ B)
    (k : Fin (Fintype.card n)) : hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  obtain ⟨S, hS, hAS⟩ := hA.exists_submodule_eigenvalues₀_mul_le k
  refine hB.le_eigenvalues₀_of_forall_mem k S hS fun x hx => (hAS x hx).trans ?_
  have h0 := (Matrix.le_iff.mp h).re_quadForm_nonneg x
  simp only [quadForm_def, Matrix.sub_mulVec, dotProduct_sub, map_sub] at h0 ⊢
  linarith

/-- **Weyl's inequality for eigenvalues.** For Hermitian `A`, `B`,
`λ_{i+j}(A + B) ≤ λ_i(A) + λ_j(B)` whenever `i + j < card n`. Horn–Johnson 2013, Thm 4.3.1
(stated there increasingly; this is the decreasing, zero-indexed form). Audit G0 B7;
atlas `courant-fischer`, `weyl-mirsky`.
atlas: weyl-mirsky -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_add_le {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (A + B).IsHermitian) (i j : Fin (Fintype.card n))
    (hij : (i : ℕ) + j < Fintype.card n) :
    hAB.eigenvalues₀ ⟨i + j, hij⟩ ≤ hA.eigenvalues₀ i + hB.eigenvalues₀ j := by
  obtain ⟨W₁, h₁, hA₁⟩ := hA.exists_submodule_le_eigenvalues₀_mul i
  obtain ⟨W₂, h₂, hB₂⟩ := hB.exists_submodule_le_eigenvalues₀_mul j
  refine hAB.eigenvalues₀_le_of_forall_mem _ (W₁ ⊓ W₂) (card_le_finrank_inf_add h₁ h₂)
    fun x hx => ?_
  have ha := hA₁ x hx.1
  have hb := hB₂ x hx.2
  simp only [quadForm_def, Matrix.add_mulVec, dotProduct_add, map_add] at ha hb ⊢
  linarith

/-! ### Interlacing for compressions and principal submatrices -/

omit [DecidableEq n] in
/-- Pushing a subspace forward by a matrix with orthonormal columns preserves its dimension. -/
private theorem finrank_map_mulVecLin_of_hasOrthonormalCols {r : Type*} [Fintype r]
    [DecidableEq r] {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q) (S : Submodule 𝕜 (r → 𝕜)) :
    finrank 𝕜 (S.map Q.mulVecLin) = finrank 𝕜 S := by
  have hinj : Function.Injective Q.mulVecLin := by
    intro x y hxy
    have h := congrArg (fun v => Qᴴ *ᵥ v) hxy
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] at h
    rwa [hQ.conjTranspose_mul_self, Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact (Submodule.equivMapOfInjective _ hinj S).finrank_eq.symm

omit [DecidableEq n] in
private theorem rayleigh_compression {r : Type*} [Fintype r] [DecidableEq r] {A : Matrix n n 𝕜}
    {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q) (y : r → 𝕜) :
    quadForm A (Q *ᵥ y) = quadForm (Qᴴ * A * Q) y ∧
      star (Q *ᵥ y) ⬝ᵥ (Q *ᵥ y) = star y ⬝ᵥ y := by
  refine ⟨?_, star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ y⟩
  rw [quadForm_def, quadForm_def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (star y) Qᴴ, Matrix.star_mulVec]

/-- **Cauchy interlacing / Poincaré separation, upper bound.** For Hermitian `A` and `Q` with
orthonormal columns, the eigenvalues of the compression `B = QᴴAQ` satisfy
`λ_i(B) ≤ λ_i(A)`. Horn–Johnson 2013, Cor 4.3.37 (Poincaré separation theorem, label to
verify; the principal-submatrix case is `eigenvalues₀_submatrix_le`). Audit G0 B8;
atlas `cauchy-interlacing`.
Deviation from the audit statement: the index of `λ(A)` is `Fin.castLE` of `i`, so no side
condition `i < card n` is needed (`card r ≤ card n` is `card_le_card_of_hasOrthonormalCols`).
atlas: cauchy-interlacing -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_compression_le {r : Type*} [Fintype r]
    [DecidableEq r] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    (hB : (Qᴴ * A * Q).IsHermitian) (i : Fin (Fintype.card r)) :
    hB.eigenvalues₀ i ≤ hA.eigenvalues₀ (Fin.castLE (card_le_card_of_hasOrthonormalCols hQ) i) := by
  obtain ⟨S, hS, hBS⟩ := hB.exists_submodule_eigenvalues₀_mul_le i
  refine hA.le_eigenvalues₀_of_forall_mem _ (S.map Q.mulVecLin)
    (by rw [finrank_map_mulVecLin_of_hasOrthonormalCols hQ]; simpa using hS) fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
  obtain ⟨h1, h2⟩ := rayleigh_compression (A := A) hQ y
  simp only [Matrix.mulVecLin_apply]
  rw [h1, h2]
  exact hBS y hy

/-- **Cauchy interlacing / Poincaré separation, lower bound.** For Hermitian `A` and
`Q : n × r` with orthonormal columns, `λ_{i + (card n − card r)}(A) ≤ λ_i(QᴴAQ)`.
Horn–Johnson 2013, Cor 4.3.37 (label to verify). Audit G0 B8; atlas `cauchy-interlacing`.
The index bound is discharged inside the statement from `card r ≤ card n`.
atlas: cauchy-interlacing -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_compression {r : Type*}
    [Fintype r] [DecidableEq r]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    (hB : (Qᴴ * A * Q).IsHermitian) (i : Fin (Fintype.card r)) :
    hA.eigenvalues₀ ⟨i + (Fintype.card n - Fintype.card r),
      by have := card_le_card_of_hasOrthonormalCols hQ; omega⟩ ≤ hB.eigenvalues₀ i := by
  obtain ⟨W, hW, hBW⟩ := hB.exists_submodule_le_eigenvalues₀_mul i
  have hcard := card_le_card_of_hasOrthonormalCols hQ
  refine hA.eigenvalues₀_le_of_forall_mem _ (W.map Q.mulVecLin)
    (by rw [finrank_map_mulVecLin_of_hasOrthonormalCols hQ]; simp only; omega) fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
  obtain ⟨h1, h2⟩ := rayleigh_compression (A := A) hQ y
  simp only [Matrix.mulVecLin_apply]
  rw [h1, h2]
  exact hBW y hy

/-- The selection matrix of an embedding `e : r ↪ n` has orthonormal columns, and compressing
by it is taking the principal submatrix. -/
private theorem submatrix_eq_compression {r : Type*} [Fintype r] [DecidableEq r]
    (A : Matrix n n 𝕜) (e : r ↪ n) :
    HasOrthonormalCols ((1 : Matrix n n 𝕜).submatrix id e) ∧
      ((1 : Matrix n n 𝕜).submatrix id e)ᴴ * A * (1 : Matrix n n 𝕜).submatrix id e =
        A.submatrix e e := by
  have hQ : ((1 : Matrix n n 𝕜).submatrix id e)ᴴ = (1 : Matrix n n 𝕜).submatrix e id := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  refine ⟨?_, ?_⟩
  · change ((1 : Matrix n n 𝕜).submatrix id e)ᴴ * (1 : Matrix n n 𝕜).submatrix id e = 1
    rw [hQ, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul,
      Matrix.submatrix_one_embedding]
  · rw [hQ, ← Matrix.submatrix_id_id A, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul, Matrix.mul_one]
    rfl

/-- **Cauchy interlacing for principal submatrices, upper bound.** For Hermitian `A` and an
embedding `e : r ↪ n`, `λ_i(A[e, e]) ≤ λ_i(A)`. Horn–Johnson 2013, Thm 4.3.17 (label to
verify); the special case of `eigenvalues₀_compression_le` with the selection matrix.
Audit G0 B8; atlas `cauchy-interlacing`.
atlas: cauchy-interlacing -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_submatrix_le {r : Type*} [Fintype r]
    [DecidableEq r] {A : Matrix n n 𝕜} (hA : A.IsHermitian) (e : r ↪ n)
    (i : Fin (Fintype.card r)) :
    (hA.submatrix e).eigenvalues₀ i ≤
      hA.eigenvalues₀ (Fin.castLE (Fintype.card_le_of_embedding e) i) := by
  obtain ⟨hQ, hB⟩ := submatrix_eq_compression A e
  have hB' : (((1 : Matrix n n 𝕜).submatrix id e)ᴴ * A *
      (1 : Matrix n n 𝕜).submatrix id e).IsHermitian := hB ▸ hA.submatrix e
  have h := hA.eigenvalues₀_compression_le hQ hB' i
  convert h using 2
  exact hB.symm

/-- **Cauchy interlacing for principal submatrices, lower bound.** For Hermitian `A` and an
embedding `e : r ↪ n`, `λ_{i + (card n − card r)}(A) ≤ λ_i(A[e, e])`. Horn–Johnson 2013,
Thm 4.3.17 (label to verify). Audit G0 B8; atlas `cauchy-interlacing`.
atlas: cauchy-interlacing -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_le_eigenvalues₀_submatrix {r : Type*}
    [Fintype r] [DecidableEq r] {A : Matrix n n 𝕜} (hA : A.IsHermitian) (e : r ↪ n)
    (i : Fin (Fintype.card r)) :
    hA.eigenvalues₀ ⟨i + (Fintype.card n - Fintype.card r),
      by have := Fintype.card_le_of_embedding e; omega⟩ ≤
      (hA.submatrix e).eigenvalues₀ i := by
  obtain ⟨hQ, hB⟩ := submatrix_eq_compression A e
  have hB' : (((1 : Matrix n n 𝕜).submatrix id e)ᴴ * A *
      (1 : Matrix n n 𝕜).submatrix id e).IsHermitian := hB ▸ hA.submatrix e
  have h := hA.eigenvalues₀_le_eigenvalues₀_compression hQ hB' i
  convert h using 2
  exact hB.symm

/-! ### Singular-value form -/

private theorem sq_singularValues_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) {k : ℕ} (hk : k < Fintype.card n) :
    singularValues A k ^ 2 = (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀ ⟨k, hk⟩ :=
  sq_singularValues_eq_eigenvalues₀ A ⟨k, hk⟩

private theorem re_star_mulVec_dotProduct_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n 𝕜) (x : n → 𝕜) :
    RCLike.re (star (A *ᵥ x) ⬝ᵥ (A *ᵥ x)) = RCLike.re (quadForm (Aᴴ * A) x) := by
  rw [quadForm_def, star_mulVec_dotProduct_mulVec_self]

/-- **Courant–Fischer for singular values, min-max half.** If `‖Ax‖² ≤ c² ‖x‖²` on a subspace
`W ⊆ 𝕜ⁿ` of codimension at most `k`, then `σ_k(A) ≤ c` (zero-indexed), on arbitrary finite
index types. Horn–Johnson 2013, §7.3 (Thm 7.3.8, label to verify). Audit G0 B1; atlas
`courant-fischer`. The hypothesis `0 ≤ c` covers `k ≥ card n`, where `σ_k = 0`.
atlas: courant-fischer -/
theorem singularValues_le_of_forall_mem {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) (k : ℕ) (W : Submodule 𝕜 (n → 𝕜))
    (hW : Fintype.card n ≤ finrank 𝕜 W + k) {c : ℝ} (hc : 0 ≤ c)
    (hAW : ∀ x ∈ W, RCLike.re (star (A *ᵥ x) ⬝ᵥ (A *ᵥ x)) ≤
      c ^ 2 * RCLike.re (star x ⬝ᵥ x)) :
    singularValues A k ≤ c := by
  by_cases hk : k < Fintype.card n
  · have h := (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀_le_of_forall_mem
      ⟨k, hk⟩ W hW (c := c ^ 2)
      fun x hx => by
        rw [← re_star_mulVec_dotProduct_mulVec]
        exact hAW x hx
    rw [← sq_singularValues_eq A hk] at h
    exact (pow_le_pow_iff_left₀ (singularValues_nonneg A k) hc two_ne_zero).1 h
  · rw [singularValues_eq_zero_of_width_le A (not_lt.1 hk)]
    exact hc

/-- **Courant–Fischer for singular values, max-min half.** If `c² ‖x‖² ≤ ‖Ax‖²` on a subspace
of dimension at least `k + 1`, then `c ≤ σ_k(A)`, on arbitrary finite index types.
Horn–Johnson 2013, §7.3 (Thm 7.3.8). Audit G0 B1; atlas `courant-fischer`.
atlas: courant-fischer -/
theorem le_singularValues_of_forall_mem {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) (k : ℕ) (S : Submodule 𝕜 (n → 𝕜)) (hS : k + 1 ≤ finrank 𝕜 S) {c : ℝ}
    (hAS : ∀ x ∈ S, c ^ 2 * RCLike.re (star x ⬝ᵥ x) ≤
      RCLike.re (star (A *ᵥ x) ⬝ᵥ (A *ᵥ x))) :
    c ≤ singularValues A k := by
  have hSn : finrank 𝕜 S ≤ Fintype.card n := by
    simpa [Module.finrank_fintype_fun_eq_card] using S.finrank_le
  have hk : k < Fintype.card n := by omega
  rcases le_or_gt c 0 with hc | hc
  · exact hc.trans (singularValues_nonneg A k)
  have h := (Matrix.isHermitian_conjTranspose_mul_self A).le_eigenvalues₀_of_forall_mem
    ⟨k, hk⟩ S hS (c := c ^ 2)
    fun x hx => by
      rw [← re_star_mulVec_dotProduct_mulVec]
      exact hAS x hx
  rw [← sq_singularValues_eq A hk] at h
  exact (pow_le_pow_iff_left₀ hc.le (singularValues_nonneg A k) two_ne_zero).1 h

/-- **Attaining subspace, min-max half (singular values)**: there is a subspace of codimension
at most `k` (spanned by the right singular vectors `k, k+1, …`) on which `‖Ax‖² ≤ σ_k² ‖x‖²`.
Horn–Johnson 2013, §7.3. Audit G0 B1/C6; atlas `courant-fischer`. -/
theorem exists_submodule_mulVec_dotProduct_le_sq_singularValues_mul {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] (A : Matrix m n 𝕜) (k : ℕ) :
    ∃ W : Submodule 𝕜 (n → 𝕜), Fintype.card n ≤ finrank 𝕜 W + k ∧
      ∀ x ∈ W, RCLike.re (star (A *ᵥ x) ⬝ᵥ (A *ᵥ x)) ≤
        singularValues A k ^ 2 * RCLike.re (star x ⬝ᵥ x) := by
  by_cases hk : k < Fintype.card n
  · obtain ⟨W, hW, hAW⟩ :=
      (Matrix.isHermitian_conjTranspose_mul_self A).exists_submodule_le_eigenvalues₀_mul ⟨k, hk⟩
    refine ⟨W, hW, fun x hx => ?_⟩
    rw [sq_singularValues_eq A hk, re_star_mulVec_dotProduct_mulVec]
    exact hAW x hx
  · refine ⟨⊥, by simp; omega, fun x hx => ?_⟩
    rw [(Submodule.mem_bot 𝕜).1 hx]
    simp

/-- **Attaining subspace, max-min half (singular values)**: for `k < card n` there is a
subspace of dimension at least `k + 1` (spanned by the top `k + 1` right singular vectors) on
which `σ_k² ‖x‖² ≤ ‖Ax‖²`. Horn–Johnson 2013, §7.3. Audit G0 B1/C6;
atlas `courant-fischer`. -/
theorem exists_submodule_sq_singularValues_mul_le_mulVec_dotProduct {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] (A : Matrix m n 𝕜) {k : ℕ} (hk : k < Fintype.card n) :
    ∃ S : Submodule 𝕜 (n → 𝕜), k + 1 ≤ finrank 𝕜 S ∧
      ∀ x ∈ S, singularValues A k ^ 2 * RCLike.re (star x ⬝ᵥ x) ≤
        RCLike.re (star (A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by
  obtain ⟨S, hS, hAS⟩ :=
    (Matrix.isHermitian_conjTranspose_mul_self A).exists_submodule_eigenvalues₀_mul_le ⟨k, hk⟩
  refine ⟨S, hS, fun x hx => ?_⟩
  rw [sq_singularValues_eq A hk, re_star_mulVec_dotProduct_mulVec]
  exact hAS x hx

end NLAlib
