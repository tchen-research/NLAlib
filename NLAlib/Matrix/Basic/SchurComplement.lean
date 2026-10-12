import NLAlib.Matrix.Basic.GramVanishing
import NLAlib.Matrix.Factorizations.Triangular
/-!
# Schur complements: the elimination step

* `pivotSchur A`: the Schur complement `C − c rᵀ / a` of the leading pivot `a` of a matrix on
  `Fin (n + 1)` written as `[[a, rᵀ], [c, C]]` (`borderedMatrix`). One step of Gaussian
  elimination (`eq_borderedMatrix_mul_borderedMatrix_pivotSchur`) and of Cholesky
  (`posDef_iff_pivotSchur`, `posSemidef_pivotSchur`) is a passage to `pivotSchur A`;
  `det A = a · det (pivotSchur A)` (`det_eq_mul_det_pivotSchur`). With Lean's `x / 0 = 0` the
  definition is total: a zero pivot gives the trailing block.
* `borderedMatrix_eq_reindex_fromBlocks`: the bridge from the `Fin.cons` splitting to Mathlib's
  `Matrix.fromBlocks` over `Fin 1 ⊕ Fin n`, so that Mathlib's block lemmas
  (`Matrix.PosSemidef.fromBlocks₁₁`, `Matrix.det_fromBlocks₁₁`) apply.

The generalized Schur complement `schurComplement A B C = C − Bᵀ A⁺ B` and Albert's criterion
live in `Matrix/Basic/GeneralizedSchurComplement.lean`.

Sources: Trefethen–Bau 1997, Lect. 20 and 23; Golub–Van Loan 2013, §3.2.10 and §4.2.
Helpers for `lu-decomposition`, `cholesky-decomposition` and (special case)
`generalized-schur-complement-psd`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

section Pivot

variable {n : ℕ}

/-- The **Schur complement of the leading pivot**: for `A = [[a, rᵀ], [c, C]]` on `Fin (n + 1)`,
`pivotSchur A = C − a⁻¹ c rᵀ`. This is the trailing matrix after one step of Gaussian
elimination (Trefethen–Bau 1997, Lect. 20; Golub–Van Loan 2013, §3.2.10) and of the Cholesky
recursion (Trefethen–Bau 1997, Lect. 23). Total: for `a = 0` it is the trailing block `C`. -/
def pivotSchur (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A.submatrix Fin.succ Fin.succ - (A 0 0)⁻¹ • vecMulVec (fun i => A i.succ 0) fun j => A 0 j.succ

/-- Entrywise form of the pivot Schur complement: `Cᵢⱼ − cᵢ rⱼ / a`. -/
@[simp]
theorem pivotSchur_apply (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin n) :
    pivotSchur A i j = A i.succ j.succ - (A 0 0)⁻¹ * (A i.succ 0 * A 0 j.succ) := by
  simp [pivotSchur, vecMulVec_apply]

/-- The equivalence `Fin 1 ⊕ Fin n ≃ Fin (n + 1)` sending `inl 0 ↦ 0` and `inr i ↦ i.succ`,
used to transport Mathlib's `fromBlocks` lemmas to the bordered splitting. -/
def finOneSumEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))

/-- `finOneSumEquiv` sends the `Fin 1` block to the pivot index `0`. -/
@[simp]
theorem finOneSumEquiv_inl (i : Fin 1) : finOneSumEquiv n (Sum.inl i) = 0 := by
  ext; simp [finOneSumEquiv]

/-- `finOneSumEquiv` sends `inr i` to `i.succ`. -/
@[simp]
theorem finOneSumEquiv_inr (i : Fin n) : finOneSumEquiv n (Sum.inr i) = i.succ := by
  ext; simp [finOneSumEquiv]

/-- Bridge from the bordered (`Fin.cons`) splitting to Mathlib's `Matrix.fromBlocks` over
`Fin 1 ⊕ Fin n`: `[[a, rᵀ], [c, M]]` is the reindexed block matrix. -/
theorem borderedMatrix_eq_reindex_fromBlocks (a : ℝ) (r c : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    borderedMatrix a r c M =
      reindex (finOneSumEquiv n) (finOneSumEquiv n)
        (fromBlocks (of fun _ _ => a) (of fun _ j => r j) (of fun i _ => c i) M) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · have h : (finOneSumEquiv n).symm 0 = Sum.inl 0 := by
      rw [Equiv.symm_apply_eq]; simp
    simp [h]
  · have h : (finOneSumEquiv n).symm 0 = Sum.inl 0 := by
      rw [Equiv.symm_apply_eq]; simp
    have h' : (finOneSumEquiv n).symm j.succ = Sum.inr j := by
      rw [Equiv.symm_apply_eq]; simp
    simp [h, h']
  · have h : (finOneSumEquiv n).symm 0 = Sum.inl 0 := by
      rw [Equiv.symm_apply_eq]; simp
    have h' : (finOneSumEquiv n).symm i.succ = Sum.inr i := by
      rw [Equiv.symm_apply_eq]; simp
    simp [h, h']
  · have h : (finOneSumEquiv n).symm i.succ = Sum.inr i := by
      rw [Equiv.symm_apply_eq]; simp
    have h' : (finOneSumEquiv n).symm j.succ = Sum.inr j := by
      rw [Equiv.symm_apply_eq]; simp
    simp [h, h']

/-- **One step of Gaussian elimination**: for a nonzero pivot `a = A₀₀`,
`A = [[1, 0], [c/a, I]] · [[a, rᵀ], [0, pivotSchur A]]`.
Trefethen–Bau 1997, Lect. 20 (eq. (20.4)–(20.5)); Golub–Van Loan 2013, §3.2.10. -/
theorem eq_borderedMatrix_mul_borderedMatrix_pivotSchur
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (ha : A 0 0 ≠ 0) :
    A = borderedMatrix 1 0 ((A 0 0)⁻¹ • fun i => A i.succ 0) 1 *
      borderedMatrix (A 0 0) (fun j => A 0 j.succ) 0 (pivotSchur A) := by
  rw [borderedMatrix_mul_borderedMatrix]
  conv_lhs => rw [← borderedMatrix_eta A]
  congr 1
  · simp
  · ext j; simp
  · ext i; simp [ha]
  · ext i j; simp [pivotSchur, vecMulVec_apply]

/-- The determinant factors through the pivot: `det A = A₀₀ · det (pivotSchur A)` for a nonzero
pivot. Golub–Van Loan 2013, §3.2.10; Horn–Johnson 2013, §0.8.5. -/
theorem det_eq_mul_det_pivotSchur (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (ha : A 0 0 ≠ 0) :
    A.det = A 0 0 * (pivotSchur A).det := by
  conv_lhs => rw [eq_borderedMatrix_mul_borderedMatrix_pivotSchur A ha]
  rw [det_mul, det_borderedMatrix_of_top_eq_zero, det_borderedMatrix_of_left_eq_zero]
  simp

/-- The pivot Schur complement of a symmetric matrix is symmetric. -/
theorem isSymm_pivotSchur {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsSymm) :
    (pivotSchur A).IsSymm := by
  ext i j
  have h1 : A i.succ j.succ = A j.succ i.succ := hA.apply j.succ i.succ
  have h2 : A i.succ 0 = A 0 i.succ := hA.apply 0 i.succ
  have h3 : A j.succ 0 = A 0 j.succ := hA.apply 0 j.succ
  simp only [transpose_apply, pivotSchur_apply, h1, h2, h3]
  ring

/-- The quadratic form of a matrix on `Fin (n + 1)` at `(x₀, y)`, expanded over the bordered
splitting. -/
theorem dotProduct_mulVec_vecCons (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x₀ : ℝ)
    (y : Fin n → ℝ) :
    vecCons x₀ y ⬝ᵥ A *ᵥ vecCons x₀ y =
      A 0 0 * x₀ ^ 2 + x₀ * (∑ j, A 0 j.succ * y j) + x₀ * (∑ i, y i * A i.succ 0) +
        y ⬝ᵥ A.submatrix Fin.succ Fin.succ *ᵥ y := by
  simp only [dotProduct, mulVec, Fin.sum_univ_succ, cons_val_zero, cons_val_succ,
    submatrix_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf

/-- The quadratic form of the pivot Schur complement:
`yᵀ (C − c rᵀ / a) y = yᵀ C y − (yᵀ c)(rᵀ y) / a`. -/
theorem dotProduct_pivotSchur_mulVec (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (y : Fin n → ℝ) :
    y ⬝ᵥ pivotSchur A *ᵥ y = y ⬝ᵥ A.submatrix Fin.succ Fin.succ *ᵥ y -
      (A 0 0)⁻¹ * ((∑ i, y i * A i.succ 0) * (∑ j, A 0 j.succ * y j)) := by
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  simp only [dotProduct, mulVec, pivotSchur_apply, submatrix_apply, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Positive definiteness through the pivot**: a symmetric `A` on `Fin (n + 1)` is positive
definite iff its pivot is positive and its pivot Schur complement is positive definite.
Proof: complete the square, `xᵀAx = a (x₀ + cᵀy / a)² + yᵀ (pivotSchur A) y` for
`x = (x₀, y)`. Golub–Van Loan 2013, §4.2.5 (proof of Thm 4.2.7); Trefethen–Bau 1997,
Lect. 23 (proof of Thm 23.1); Horn–Johnson 2013, Thm 7.7.7. This is the step of the Cholesky
recursion (atlas `cholesky-algorithm`); special case of `generalized-schur-complement-psd`. -/
theorem posDef_iff_pivotSchur {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsSymm) :
    A.PosDef ↔ 0 < A 0 0 ∧ (pivotSchur A).PosDef := by
  have hsym : ∀ y : Fin n → ℝ, ∑ i, y i * A i.succ 0 = ∑ j, A 0 j.succ * y j := fun y =>
    Finset.sum_congr rfl fun i _ => by rw [hA.apply 0 i.succ, mul_comm]
  have hSh := Matrix.isHermitian_iff_isSymm.mpr (isSymm_pivotSchur hA)
  constructor
  · intro hPD
    refine ⟨hPD.diag_pos, posDef_iff_dotProduct_mulVec.2 ⟨hSh, fun y hy => ?_⟩⟩
    have hx0 : vecCons (-((A 0 0)⁻¹ * ∑ j, A 0 j.succ * y j)) y ≠ 0 := by
      intro h; apply hy; ext i; simpa using congrFun h i.succ
    have hx := (posDef_iff_dotProduct_mulVec.1 hPD).2 hx0
    simp only [star_trivial] at hx ⊢
    rw [dotProduct_mulVec_vecCons, hsym] at hx
    rw [dotProduct_pivotSchur_mulVec, hsym]
    have ha := hPD.diag_pos (i := 0)
    have key : A 0 0 * ((A 0 0)⁻¹ * ∑ j, A 0 j.succ * y j) ^ 2 =
        (A 0 0)⁻¹ * ((∑ j, A 0 j.succ * y j) * ∑ j, A 0 j.succ * y j) := by
      field_simp
    nlinarith [key]
  · rintro ⟨ha, hS⟩
    refine posDef_iff_dotProduct_mulVec.2 ⟨Matrix.isHermitian_iff_isSymm.mpr hA, fun x hx => ?_⟩
    have hxe : x = vecCons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
    simp only [star_trivial]
    rw [hxe, dotProduct_mulVec_vecCons, hsym]
    set y := Fin.tail x
    set t := ∑ j, A 0 j.succ * y j
    by_cases hy : y = 0
    · have hx0 : x 0 ≠ 0 := by
        intro h0; apply hx; rw [hxe, h0, hy]; ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
      have ht : t = 0 := by simp [t, hy]
      rw [ht, hy]
      simp only [mul_zero, add_zero, zero_dotProduct]
      positivity
    · have hq := (posDef_iff_dotProduct_mulVec.1 hS).2 hy
      simp only [star_trivial] at hq
      rw [dotProduct_pivotSchur_mulVec, hsym] at hq
      have key : A 0 0 * (x 0 + (A 0 0)⁻¹ * t) ^ 2 =
          A 0 0 * x 0 ^ 2 + 2 * x 0 * t + (A 0 0)⁻¹ * (t * t) := by
        field_simp; ring
      nlinarith [key, mul_nonneg ha.le (sq_nonneg (x 0 + (A 0 0)⁻¹ * t))]

/-- The pivot Schur complement of a positive semidefinite matrix is positive semidefinite, with
no condition on the pivot (for `A₀₀ = 0` the first column vanishes and `pivotSchur A` is the
trailing block). Proof: `yᵀ (pivotSchur A) y = xᵀ A x` at `x = (−cᵀy / a, y)` (valid also for
`a = 0` with `0⁻¹ = 0`). Golub–Van Loan 2013, §4.2.8 (semidefinite case); special case of
Albert 1969, Thm 1 (atlas `generalized-schur-complement-psd`). -/
theorem posSemidef_pivotSchur {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : A.PosSemidef) : (pivotSchur A).PosSemidef := by
  have hAs := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have hsym : ∀ y : Fin n → ℝ, ∑ i, y i * A i.succ 0 = ∑ j, A 0 j.succ * y j := fun y =>
    Finset.sum_congr rfl fun i _ => by rw [hAs.apply 0 i.succ, mul_comm]
  refine posSemidef_iff_dotProduct_mulVec.2
    ⟨Matrix.isHermitian_iff_isSymm.mpr (isSymm_pivotSchur hAs), fun y => ?_⟩
  have hx := (posSemidef_iff_dotProduct_mulVec.1 hA).2
    (vecCons (-((A 0 0)⁻¹ * ∑ j, A 0 j.succ * y j)) y)
  simp only [star_trivial] at hx ⊢
  rw [dotProduct_mulVec_vecCons, hsym] at hx
  rw [dotProduct_pivotSchur_mulVec, hsym]
  have key : A 0 0 * ((A 0 0)⁻¹ * ∑ j, A 0 j.succ * y j) ^ 2 =
      (A 0 0)⁻¹ * ((∑ j, A 0 j.succ * y j) * ∑ j, A 0 j.succ * y j) := by
    by_cases ha : A 0 0 = 0
    · simp [ha]
    · field_simp
  nlinarith [key]

end Pivot

end NLAlib
