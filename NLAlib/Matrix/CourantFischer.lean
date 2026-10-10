import NLAlib.Matrix.PolynomialCalculus
import NLAlib.Matrix.SVD
import NLAlib.Matrix.Spectral
import NLAlib.Matrix.Projections
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Courant–Fischer min-max theorem

For a real symmetric matrix `A` with sorted eigenvalues `λ₀ ≥ λ₁ ≥ ⋯` (Mathlib's
`Matrix.IsHermitian.eigenvalues₀`, zero-indexed and non-increasing):

* `eigenvalues₀_le_of_forall_mem`: if `xᵀAx ≤ c xᵀx` on a subspace of codimension at most `k`,
  then `λ_k ≤ c` (min-max half);
* `le_eigenvalues₀_of_forall_mem`: if `c xᵀx ≤ xᵀAx` on a subspace of dimension at least `k+1`,
  then `c ≤ λ_k` (max-min half);
* the attaining subspaces (spans of eigenvectors, written as kernels of eigen-coordinates):
  `exists_submodule_eigenvalues₀_mul_le` and `exists_submodule_le_eigenvalues₀_mul`;
* the singular-value form for `σ_k(A)² = λ_k(AᵀA)`: `singularValues_le_of_forall_mem`,
  `le_singularValues_of_forall_mem` and their attaining subspaces;
* consequences: Loewner monotonicity of eigenvalues, the eigenvalue Weyl inequality
  `λ_{i+j}(A+B) ≤ λ_i(A) + λ_j(B)` and Cauchy/Poincaré interlacing for compressions `QᵀAQ`.

Proof: a dimension count (`LinearMap.ker_ne_bot_of_finrank_lt`, rank–nullity) against the
coordinates `⟨uⱼ, x⟩` in the sorted eigenbasis, and the expansion `xᵀAx = ∑ⱼ λⱼ ⟨uⱼ, x⟩²`
(`quadForm_eq_sum_eigenvalues`).

Source: Horn–Johnson 2013, Thm 4.2.6 (Courant–Fischer), Cor 4.3.37 (Poincaré separation),
Cor 4.3.12 (monotonicity), Thm 4.3.1 (Weyl); Horn–Johnson 2013, §7.3 (singular values).
Labels other than Thm 4.2.6 are marked "verify" where they were not checked against the print.
HJ index eigenvalues increasingly from `1`; here they are decreasing and zero-indexed.
Audit G0 A1, B1, B7, B8, C6. Atlas: `courant-fischer`, `cauchy-interlacing`.
-/

noncomputable section

open scoped Matrix
open Module

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace CourantFischer

variable {A : Matrix n n ℝ} (hA : A.IsHermitian)

/-- The reindexing `Fin (card n) ≃ n` under which Mathlib sorts the eigenvalues. -/
private def e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)

/-- The coordinate of `x` along the `j`-th sorted eigenvector. -/
private def coord (j : Fin (Fintype.card n)) (x : n → ℝ) : ℝ :=
  ⇑(hA.eigenvectorBasis (e j)) ⬝ᵥ x

private theorem eigenvalues_e (j : Fin (Fintype.card n)) :
    hA.eigenvalues (e j) = hA.eigenvalues₀ j := by
  simp [Matrix.IsHermitian.eigenvalues, e]

private theorem dotProduct_mulVec_eq_sum (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ j, hA.eigenvalues₀ j * coord hA j x ^ 2 := by
  have h := quadForm_eq_sum_eigenvalues hA x
  rw [quadForm] at h
  rw [h, ← (e (n := n)).sum_comp]
  simp only [coord, eigenvalues_e]

private theorem dotProduct_self_eq_sum (x : n → ℝ) :
    x ⬝ᵥ x = ∑ j, coord hA j x ^ 2 := by
  rw [← sum_sq_eigenvectorBasis_dotProduct hA x, ← (e (n := n)).sum_comp]
  rfl

/-- If the coordinates above `k` vanish, the Rayleigh quotient is at least `λ_k`. -/
private theorem eigenvalues₀_mul_le_of_coord (k : Fin (Fintype.card n)) {x : n → ℝ}
    (hx : ∀ j, k < j → coord hA j x = 0) :
    hA.eigenvalues₀ k * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  rw [dotProduct_mulVec_eq_sum hA, dotProduct_self_eq_sum hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases le_or_gt j k with hjk | hjk
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone hjk) (sq_nonneg _)
  · simp [hx j hjk]

/-- If the coordinates below `k` vanish, the Rayleigh quotient is at most `λ_k`. -/
private theorem le_eigenvalues₀_mul_of_coord (k : Fin (Fintype.card n)) {x : n → ℝ}
    (hx : ∀ j, j < k → coord hA j x = 0) :
    x ⬝ᵥ (A *ᵥ x) ≤ hA.eigenvalues₀ k * (x ⬝ᵥ x) := by
  rw [dotProduct_mulVec_eq_sum hA, dotProduct_self_eq_sum hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases lt_or_ge j k with hjk | hjk
  · simp [hx j hjk]
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone hjk) (sq_nonneg _)

/-- The coordinates strictly above `k`, as a matrix. -/
private def hiMat (k : Fin (Fintype.card n)) :
    Matrix (Fin (Fintype.card n - (k + 1))) n ℝ :=
  Matrix.of fun t i => ⇑(hA.eigenvectorBasis (e ⟨k + 1 + t, by omega⟩)) i

/-- The coordinates strictly below `k`, as a matrix. -/
private def loMat (k : Fin (Fintype.card n)) : Matrix (Fin k) n ℝ :=
  Matrix.of fun t i => ⇑(hA.eigenvectorBasis (e ⟨t, by omega⟩)) i

private theorem coord_of_hiMat (k : Fin (Fintype.card n)) {x : n → ℝ}
    (hx : hiMat hA k *ᵥ x = 0) (j : Fin (Fintype.card n)) (hj : k < j) :
    coord hA j x = 0 := by
  have h := congrFun hx ⟨j - (k + 1), by omega⟩
  have hj' : (⟨k + 1 + (j - (k + 1)), by omega⟩ : Fin (Fintype.card n)) = j := by
    ext; simp only; omega
  simpa [hiMat, coord, Matrix.mulVec, hj'] using h

private theorem coord_of_loMat (k : Fin (Fintype.card n)) {x : n → ℝ}
    (hx : loMat hA k *ᵥ x = 0) (j : Fin (Fintype.card n)) (hj : j < k) :
    coord hA j x = 0 := by
  have h := congrFun hx ⟨j, hj⟩
  simpa [loMat, coord, Matrix.mulVec] using h

omit [DecidableEq n] in
/-- A subspace of dimension larger than `p` meets the kernel of any `p × n` matrix. -/
private theorem exists_mem_ne_zero_mulVec_eq_zero {p : ℕ} (M : Matrix (Fin p) n ℝ)
    (W : Submodule ℝ (n → ℝ)) (hW : p < finrank ℝ W) :
    ∃ x ∈ W, x ≠ 0 ∧ M *ᵥ x = 0 := by
  have hker : LinearMap.ker (M.mulVecLin.domRestrict W) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by rwa [Module.finrank_fin_fun])
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨y, y.2, fun h => hy0 (Subtype.ext h), ?_⟩
  simpa using hy

omit [DecidableEq n] in
/-- The kernel of a `p × n` matrix has dimension at least `card n - p`. -/
private theorem card_le_finrank_ker_add {p : ℕ} (M : Matrix (Fin p) n ℝ) :
    Fintype.card n ≤ finrank ℝ (LinearMap.ker M.mulVecLin) + p := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hr : finrank ℝ (LinearMap.range M.mulVecLin) ≤ p := by
    simpa using (LinearMap.range M.mulVecLin).finrank_le
  rw [Module.finrank_fintype_fun_eq_card] at h
  omega

omit [DecidableEq n] in
private theorem dotProduct_self_pos {x : n → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x :=
  lt_of_le_of_ne (dotProduct_self_nonneg x) (fun h => hx (dotProduct_self_eq_zero.1 h.symm))

end CourantFischer

open CourantFischer

/-- **Courant–Fischer, min-max half.** For real symmetric `A`, if the Rayleigh quotient is at
most `c` on a subspace `W` of codimension at most `k` (`card n ≤ dim W + k`), then the `k`-th
largest eigenvalue satisfies `λ_k ≤ c`. Horn–Johnson 2013, Thm 4.2.6 (HJ order eigenvalues
increasingly and from `1`; here `eigenvalues₀` is decreasing and zero-indexed). Audit G0 A1;
atlas `courant-fischer`. No sign condition on `c` is needed. -/
theorem eigenvalues₀_le_of_forall_mem {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) (W : Submodule ℝ (n → ℝ))
    (hW : Fintype.card n ≤ finrank ℝ W + k) {c : ℝ}
    (hAW : ∀ x ∈ W, x ⬝ᵥ (A *ᵥ x) ≤ c * (x ⬝ᵥ x)) :
    hA.eigenvalues₀ k ≤ c := by
  obtain ⟨x, hxW, hx0, hx⟩ :=
    exists_mem_ne_zero_mulVec_eq_zero (hiMat hA k) W (by omega)
  have h1 := eigenvalues₀_mul_le_of_coord hA k (coord_of_hiMat hA k hx)
  have h2 := hAW x hxW
  exact le_of_mul_le_mul_right (h1.trans h2) (dotProduct_self_pos hx0)

/-- **Courant–Fischer, max-min half.** For real symmetric `A`, if the Rayleigh quotient is at
least `c` on a subspace `S` of dimension at least `k + 1`, then `c ≤ λ_k`. Horn–Johnson 2013,
Thm 4.2.6 (decreasing, zero-indexed convention). Audit G0 A1; atlas `courant-fischer`. -/
theorem le_eigenvalues₀_of_forall_mem {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) (S : Submodule ℝ (n → ℝ))
    (hS : (k : ℕ) + 1 ≤ finrank ℝ S) {c : ℝ}
    (hAS : ∀ x ∈ S, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) :
    c ≤ hA.eigenvalues₀ k := by
  obtain ⟨x, hxS, hx0, hx⟩ :=
    exists_mem_ne_zero_mulVec_eq_zero (loMat hA k) S (by omega)
  have h1 := le_eigenvalues₀_mul_of_coord hA k (coord_of_loMat hA k hx)
  have h2 := hAS x hxS
  exact le_of_mul_le_mul_right (h2.trans h1) (dotProduct_self_pos hx0)

/-- **Courant–Fischer, attaining subspace for the max-min half**: there is a subspace of
dimension at least `k + 1` (the span of the top `k + 1` eigenvectors) on which
`λ_k xᵀx ≤ xᵀAx`. Horn–Johnson 2013, proof of Thm 4.2.6. Audit G0 C6; atlas `courant-fischer`.
Deviation: the dimension is stated as a lower bound. -/
theorem exists_submodule_eigenvalues₀_mul_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    ∃ S : Submodule ℝ (n → ℝ), (k : ℕ) + 1 ≤ finrank ℝ S ∧
      ∀ x ∈ S, hA.eigenvalues₀ k * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  refine ⟨LinearMap.ker (hiMat hA k).mulVecLin, ?_, fun x hx => ?_⟩
  · have := card_le_finrank_ker_add (hiMat hA k)
    omega
  · exact eigenvalues₀_mul_le_of_coord hA k (coord_of_hiMat hA k (by simpa using hx))

/-- **Courant–Fischer, attaining subspace for the min-max half**: there is a subspace of
codimension at most `k` (the span of the eigenvectors `k, k+1, …`) on which `xᵀAx ≤ λ_k xᵀx`.
Horn–Johnson 2013, proof of Thm 4.2.6. Audit G0 C6; atlas `courant-fischer`. -/
theorem exists_submodule_le_eigenvalues₀_mul {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    ∃ W : Submodule ℝ (n → ℝ), Fintype.card n ≤ finrank ℝ W + k ∧
      ∀ x ∈ W, x ⬝ᵥ (A *ᵥ x) ≤ hA.eigenvalues₀ k * (x ⬝ᵥ x) :=
  ⟨LinearMap.ker (loMat hA k).mulVecLin, card_le_finrank_ker_add (loMat hA k),
    fun x hx => le_eigenvalues₀_mul_of_coord hA k (coord_of_loMat hA k (by simpa using hx))⟩

/-! ### Dimension count for intersections -/

omit [DecidableEq n] in
/-- Codimensions add under intersection: if `card n ≤ dim W₁ + a` and `card n ≤ dim W₂ + b`
then `card n ≤ dim (W₁ ⊓ W₂) + (a + b)`. Helper for the Weyl inequalities;
atlas `courant-fischer`. -/
theorem card_le_finrank_inf_add {W₁ W₂ : Submodule ℝ (n → ℝ)} {a b : ℕ}
    (h₁ : Fintype.card n ≤ finrank ℝ W₁ + a) (h₂ : Fintype.card n ≤ finrank ℝ W₂ + b) :
    Fintype.card n ≤ finrank ℝ (W₁ ⊓ W₂ : Submodule ℝ (n → ℝ)) + (a + b) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₂
  have hs : finrank ℝ (W₁ ⊔ W₂ : Submodule ℝ (n → ℝ)) ≤ Fintype.card n := by
    simpa [Module.finrank_fintype_fun_eq_card] using (W₁ ⊔ W₂).finrank_le
  omega

/-! ### Consequences for eigenvalues -/

/-- **Loewner monotonicity of eigenvalues.** If `B − A` is positive semidefinite then
`λ_k(A) ≤ λ_k(B)` for every `k`. Horn–Johnson 2013, Cor 4.3.12. Audit G0 B7;
atlas `courant-fischer`. -/
theorem eigenvalues₀_le_eigenvalues₀_of_posSemidef_sub {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : (B - A).PosSemidef)
    (k : Fin (Fintype.card n)) : hA.eigenvalues₀ k ≤ hB.eigenvalues₀ k := by
  obtain ⟨S, hS, hAS⟩ := exists_submodule_eigenvalues₀_mul_le hA k
  refine le_eigenvalues₀_of_forall_mem hB k S hS fun x hx => (hAS x hx).trans ?_
  have h0 := h.dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at h0
  linarith

/-- **Weyl's inequality for eigenvalues.** For real symmetric `A`, `B`,
`λ_{i+j}(A + B) ≤ λ_i(A) + λ_j(B)` whenever `i + j < card n`. Horn–Johnson 2013, Thm 4.3.1
(stated there increasingly; this is the decreasing, zero-indexed form). Audit G0 B7;
atlas `courant-fischer`, `weyl-mirsky`. -/
theorem eigenvalues₀_add_le {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (A + B).IsHermitian) (i j : Fin (Fintype.card n))
    (hij : (i : ℕ) + j < Fintype.card n) :
    hAB.eigenvalues₀ ⟨i + j, hij⟩ ≤ hA.eigenvalues₀ i + hB.eigenvalues₀ j := by
  obtain ⟨W₁, h₁, hA₁⟩ := exists_submodule_le_eigenvalues₀_mul hA i
  obtain ⟨W₂, h₂, hB₂⟩ := exists_submodule_le_eigenvalues₀_mul hB j
  refine eigenvalues₀_le_of_forall_mem hAB _ (W₁ ⊓ W₂) (card_le_finrank_inf_add h₁ h₂)
    fun x hx => ?_
  have ha := hA₁ x hx.1
  have hb := hB₂ x hx.2
  rw [Matrix.add_mulVec, dotProduct_add]
  linarith

/-! ### Interlacing for compressions -/

omit [DecidableEq n] in
/-- A real matrix with orthonormal columns has at most as many columns as rows (general finite
index types). Helper for interlacing; atlas `orthonormal-completion`. -/
theorem card_le_card_of_hasOrthonormalCols {r : Type*} [Fintype r] [DecidableEq r]
    {Q : Matrix n r ℝ} (hQ : HasOrthonormalCols Q) : Fintype.card r ≤ Fintype.card n := by
  have hinj : Function.Injective Q.mulVecLin := by
    intro x y hxy
    have h := congrArg (fun v => Qᵀ *ᵥ v) hxy
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] at h
    rwa [show Qᵀ * Q = 1 from hQ, Matrix.one_mulVec, Matrix.one_mulVec] at h
  simpa [Module.finrank_fintype_fun_eq_card] using
    LinearMap.finrank_le_finrank_of_injective hinj

omit [DecidableEq n] in
/-- Pushing a subspace forward by a matrix with orthonormal columns preserves its dimension. -/
private theorem finrank_map_mulVecLin_of_hasOrthonormalCols {r : Type*} [Fintype r]
    [DecidableEq r] {Q : Matrix n r ℝ} (hQ : HasOrthonormalCols Q) (S : Submodule ℝ (r → ℝ)) :
    finrank ℝ (S.map Q.mulVecLin) = finrank ℝ S := by
  have hinj : Function.Injective Q.mulVecLin := by
    intro x y hxy
    have h := congrArg (fun v => Qᵀ *ᵥ v) hxy
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] at h
    rwa [show Qᵀ * Q = 1 from hQ, Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact (Submodule.equivMapOfInjective _ hinj S).finrank_eq.symm

omit [DecidableEq n] in
private theorem rayleigh_compression {r : Type*} [Fintype r] [DecidableEq r] {A : Matrix n n ℝ}
    {Q : Matrix n r ℝ} (hQ : HasOrthonormalCols Q) (y : r → ℝ) :
    (Q *ᵥ y) ⬝ᵥ (A *ᵥ (Q *ᵥ y)) = y ⬝ᵥ ((Qᵀ * A * Q) *ᵥ y) ∧
      (Q *ᵥ y) ⬝ᵥ (Q *ᵥ y) = y ⬝ᵥ y := by
  constructor
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec y Qᵀ,
      Matrix.vecMul_transpose]
  · exact mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ y

/-- **Cauchy interlacing / Poincaré separation, upper bound.** For real symmetric `A` and `Q`
with orthonormal columns, the eigenvalues of the compression `B = QᵀAQ` satisfy
`λ_i(B) ≤ λ_i(A)`. Horn–Johnson 2013, Cor 4.3.37 (Poincaré separation theorem, label to verify; the
bordered / principal-submatrix case is Thm 4.3.17). Audit G0 B8; atlas `cauchy-interlacing`.
Deviation from the audit statement: the index of `λ(A)` is `Fin.castLE` of `i`, so no side
condition `i < card n` is needed (`card r ≤ card n` is `card_le_card_of_hasOrthonormalCols`). -/
theorem eigenvalues₀_compression_le {r : Type*} [Fintype r] [DecidableEq r] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {Q : Matrix n r ℝ} (hQ : HasOrthonormalCols Q)
    (hB : (Qᵀ * A * Q).IsHermitian) (i : Fin (Fintype.card r)) :
    hB.eigenvalues₀ i ≤ hA.eigenvalues₀ (Fin.castLE (card_le_card_of_hasOrthonormalCols hQ) i) := by
  obtain ⟨S, hS, hBS⟩ := exists_submodule_eigenvalues₀_mul_le hB i
  refine le_eigenvalues₀_of_forall_mem hA _ (S.map Q.mulVecLin)
    (by rw [finrank_map_mulVecLin_of_hasOrthonormalCols hQ]; simpa using hS) fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
  obtain ⟨h1, h2⟩ := rayleigh_compression (A := A) hQ y
  simp only [Matrix.mulVecLin_apply]
  rw [h1, h2]
  exact hBS y hy

/-- **Cauchy interlacing / Poincaré separation, lower bound.** For real symmetric `A` and
`Q : n × r` with orthonormal columns, `λ_{i + (card n − card r)}(A) ≤ λ_i(QᵀAQ)`.
Horn–Johnson 2013, Cor 4.3.37 (label to verify). Audit G0 B8; atlas `cauchy-interlacing`.
The index bound is discharged inside the statement from `card r ≤ card n`. -/
theorem eigenvalues₀_le_eigenvalues₀_compression {r : Type*} [Fintype r] [DecidableEq r]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {Q : Matrix n r ℝ} (hQ : HasOrthonormalCols Q)
    (hB : (Qᵀ * A * Q).IsHermitian) (i : Fin (Fintype.card r)) :
    hA.eigenvalues₀ ⟨i + (Fintype.card n - Fintype.card r),
      by have := card_le_card_of_hasOrthonormalCols hQ; omega⟩ ≤ hB.eigenvalues₀ i := by
  obtain ⟨W, hW, hBW⟩ := exists_submodule_le_eigenvalues₀_mul hB i
  have hcard := card_le_card_of_hasOrthonormalCols hQ
  refine eigenvalues₀_le_of_forall_mem hA _ (W.map Q.mulVecLin)
    (by rw [finrank_map_mulVecLin_of_hasOrthonormalCols hQ]; simp only; omega) fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
  obtain ⟨h1, h2⟩ := rayleigh_compression (A := A) hQ y
  simp only [Matrix.mulVecLin_apply]
  rw [h1, h2]
  exact hBW y hy

/-! ### Singular-value form -/

/-- The Gram matrix `AᵀA` of a real matrix is symmetric (real form of Mathlib's
`Matrix.isHermitian_conjTranspose_mul_self`). Atlas `courant-fischer` (helper). -/
theorem isHermitian_transpose_mul_self {m p : Type*} [Fintype m] (A : Matrix m p ℝ) :
    (Aᵀ * A).IsHermitian := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_conjTranspose_mul_self A

private theorem sq_singularValues_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ}
    (hk : k < n) :
    singularValues A k ^ 2 = (isHermitian_transpose_mul_self A).eigenvalues₀
      (Fin.cast (Fintype.card_fin n).symm ⟨k, hk⟩) :=
  sq_singularValues_eq_eigenvalues₀ A _ ⟨k, hk⟩

/-- **Courant–Fischer for singular values, min-max half.** If `‖Ax‖² ≤ c² ‖x‖²` on a subspace
`W ⊆ ℝⁿ` of codimension at most `k`, then `σ_k(A) ≤ c` (zero-indexed). Horn–Johnson 2013,
§7.3 (Thm 7.3.8, label to verify). Audit G0 B1; atlas `courant-fischer`. The hypothesis
`0 ≤ c` covers `k ≥ n`, where `σ_k = 0`. -/
theorem singularValues_le_of_forall_mem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ)
    (W : Submodule ℝ (Fin n → ℝ)) (hW : n ≤ finrank ℝ W + k) {c : ℝ} (hc : 0 ≤ c)
    (hAW : ∀ x ∈ W, (A *ᵥ x) ⬝ᵥ (A *ᵥ x) ≤ c ^ 2 * (x ⬝ᵥ x)) :
    singularValues A k ≤ c := by
  by_cases hk : k < n
  · have h := eigenvalues₀_le_of_forall_mem (isHermitian_transpose_mul_self A)
      (Fin.cast (Fintype.card_fin n).symm ⟨k, hk⟩) W (by simpa using hW) (c := c ^ 2)
      fun x hx => by rw [dotProduct_transpose_mul_mulVec]; exact hAW x hx
    rw [← sq_singularValues_eq A hk] at h
    exact (pow_le_pow_iff_left₀ (singularValues_nonneg A k) hc two_ne_zero).1 h
  · rw [singularValues_eq_zero_of_width_le A (not_lt.1 hk)]
    exact hc

/-- **Courant–Fischer for singular values, max-min half.** If `c² ‖x‖² ≤ ‖Ax‖²` on a subspace
of dimension at least `k + 1`, then `c ≤ σ_k(A)`. Horn–Johnson 2013, §7.3. Audit G0 B1;
atlas `courant-fischer`. -/
theorem le_singularValues_of_forall_mem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ)
    (S : Submodule ℝ (Fin n → ℝ)) (hS : k + 1 ≤ finrank ℝ S) {c : ℝ}
    (hAS : ∀ x ∈ S, c ^ 2 * (x ⬝ᵥ x) ≤ (A *ᵥ x) ⬝ᵥ (A *ᵥ x)) :
    c ≤ singularValues A k := by
  have hSn : finrank ℝ S ≤ n := by simpa using S.finrank_le
  have hk : k < n := by omega
  rcases le_or_gt c 0 with hc | hc
  · exact hc.trans (singularValues_nonneg A k)
  have h := le_eigenvalues₀_of_forall_mem (isHermitian_transpose_mul_self A)
    (Fin.cast (Fintype.card_fin n).symm ⟨k, hk⟩) S (by simpa using hS) (c := c ^ 2)
    fun x hx => by rw [dotProduct_transpose_mul_mulVec]; exact hAS x hx
  rw [← sq_singularValues_eq A hk] at h
  exact (pow_le_pow_iff_left₀ hc.le (singularValues_nonneg A k) two_ne_zero).1 h

/-- **Attaining subspace, min-max half (singular values)**: there is a subspace of codimension
at most `k` (spanned by the right singular vectors `k, k+1, …`) on which `‖Ax‖² ≤ σ_k² ‖x‖²`.
Horn–Johnson 2013, §7.3. Audit G0 B1/C6; atlas `courant-fischer`. -/
theorem exists_submodule_mulVec_dotProduct_le_sq_singularValues_mul {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    ∃ W : Submodule ℝ (Fin n → ℝ), n ≤ finrank ℝ W + k ∧
      ∀ x ∈ W, (A *ᵥ x) ⬝ᵥ (A *ᵥ x) ≤ singularValues A k ^ 2 * (x ⬝ᵥ x) := by
  by_cases hk : k < n
  · obtain ⟨W, hW, hAW⟩ := exists_submodule_le_eigenvalues₀_mul
      (isHermitian_transpose_mul_self A) (Fin.cast (Fintype.card_fin n).symm ⟨k, hk⟩)
    refine ⟨W, by simpa using hW, fun x hx => ?_⟩
    rw [sq_singularValues_eq A hk, ← dotProduct_transpose_mul_mulVec]
    exact hAW x hx
  · refine ⟨⊥, by simp; omega, fun x hx => ?_⟩
    rw [(Submodule.mem_bot ℝ).1 hx]
    simp

/-- **Attaining subspace, max-min half (singular values)**: for `k < n` there is a subspace of
dimension at least `k + 1` (spanned by the top `k + 1` right singular vectors) on which
`σ_k² ‖x‖² ≤ ‖Ax‖²`. Horn–Johnson 2013, §7.3. Audit G0 B1/C6;
atlas `courant-fischer`. -/
theorem exists_submodule_sq_singularValues_mul_le_mulVec_dotProduct {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {k : ℕ} (hk : k < n) :
    ∃ S : Submodule ℝ (Fin n → ℝ), k + 1 ≤ finrank ℝ S ∧
      ∀ x ∈ S, singularValues A k ^ 2 * (x ⬝ᵥ x) ≤ (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
  obtain ⟨S, hS, hAS⟩ := exists_submodule_eigenvalues₀_mul_le
    (isHermitian_transpose_mul_self A) (Fin.cast (Fintype.card_fin n).symm ⟨k, hk⟩)
  refine ⟨S, by simpa using hS, fun x hx => ?_⟩
  rw [sq_singularValues_eq A hk, ← dotProduct_transpose_mul_mulVec]
  exact hAS x hx

end NLAlib
