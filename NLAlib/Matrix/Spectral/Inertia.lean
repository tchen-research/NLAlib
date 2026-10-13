import Mathlib.LinearAlgebra.QuadraticForm.Signature
import NLAlib.Matrix.Functions.PolynomialCalculus
/-!
# Sylvester's law of inertia and eigenvalue counts

The inertia of a real square matrix `A` is read off its quadratic form `x ↦ xᵀAx`
(`Matrix.toQuadraticForm'`): `inertiaPos A` and `inertiaNeg A` are Mathlib's signature
`QuadraticForm.sigPos`/`sigNeg` (the largest dimension of a subspace on which the form is
positive/negative definite). Basis-free, so no symmetry hypothesis is needed to state them.

* `inertiaPos_transpose_mul_mul`, `inertiaNeg_transpose_mul_mul`: **Sylvester's law of
  inertia**, `In(XᵀAX) = In(A)` for invertible `X` (from Mathlib's
  `QuadraticMap.Equivalent.sigPos_eq`).
* `inertiaPos_diagonal`, `inertiaNeg_diagonal`: for a diagonal matrix, the number of positive
  (negative) diagonal entries (Mathlib's `sigPos_weightedSumSquares`).
* `inertiaPos_eq_card_eigenvalues_pos`, `inertiaNeg_eq_card_eigenvalues_neg`: for symmetric
  `A`, the numbers of positive and negative eigenvalues.
* `card_eigenvalues_lt_eq_card_neg_of_eq_mul_diagonal_mul`: the `LDLᵀ` count, if
  `A − xI = L D Lᵀ` with `L` invertible then `#{i : λᵢ < x} = #{i : dᵢ < 0}` (spectrum slicing).
* `card_eigenvalues_lt_eq_card_sign_changes` (scaffold): the leading-principal-minor (Sturm)
  count, `#{λᵢ < x}` = number of sign changes in `1, det(A − xI)_{1:1}, …, det(A − xI)`, when
  every leading minor is nonzero; for symmetric tridiagonal `A` these minors satisfy the
  three-term Sturm recurrence used by bisection.

Source: Horn–Johnson (2013) [`hj13`], Thm 4.5.8; Golub–Van Loan (2013) [`gvl13`], §8.4.1,
§8.5.2 (Thm 8.5.1); Parlett (1998) [`parlett98`], Ch. 3.
Atlas: `sylvester-inertia`.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Definitions -/

/-- The **positive index of inertia** of `A`: the largest dimension of a subspace on which
`x ↦ xᵀAx` is positive definite (Mathlib's `QuadraticForm.sigPos` of `A.toQuadraticForm'`).
For symmetric `A` it is the number of positive eigenvalues
(`inertiaPos_eq_card_eigenvalues_pos`). Source: Horn–Johnson (2013) [`hj13`], §4.5.
atlas: sylvester-inertia -/
def inertiaPos (A : Matrix n n ℝ) : ℕ := sigPos A.toQuadraticForm'

/-- The **negative index of inertia** of `A`: the largest dimension of a subspace on which
`x ↦ xᵀAx` is negative definite. For symmetric `A` it is the number of negative eigenvalues
(`inertiaNeg_eq_card_eigenvalues_neg`). Source: Horn–Johnson (2013) [`hj13`], §4.5.
atlas: sylvester-inertia -/
def inertiaNeg (A : Matrix n n ℝ) : ℕ := sigNeg A.toQuadraticForm'

/-- The quadratic form of a matrix: `A.toQuadraticForm' x = xᵀAx`. Helper for
`sylvester-inertia`. -/
theorem toQuadraticForm'_apply (A : Matrix n n ℝ) (x : n → ℝ) :
    A.toQuadraticForm' x = quadForm A x := by
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply', quadForm]

/-- Congruent matrices have equivalent quadratic forms: for invertible `X`,
`x ↦ xᵀ(XᵀAX)x` and `x ↦ xᵀAx` are related by the change of variables `x ↦ Xx`. Helper for
`sylvester-inertia`. -/
theorem equivalent_toQuadraticForm'_transpose_mul_mul (A : Matrix n n ℝ) {X : Matrix n n ℝ}
    (hX : IsUnit X) :
    QuadraticMap.Equivalent (Xᵀ * A * X).toQuadraticForm' A.toQuadraticForm' := by
  have hdet : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).1 hX
  let hXi := X.invertibleOfIsUnitDet hdet
  refine ⟨{ X.toLinearEquiv' hXi with map_app' := fun x => ?_ }⟩
  change A.toQuadraticForm' (X *ᵥ x) = (Xᵀ * A * X).toQuadraticForm' x
  rw [toQuadraticForm'_apply, toQuadraticForm'_apply, quadForm_eq_dotProduct, quadForm_eq_dotProduct,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Xᵀ,
    Matrix.vecMul_transpose]

/-! ### Sylvester's law of inertia -/

/-- **Sylvester's law of inertia (positive index).** `inertiaPos (XᵀAX) = inertiaPos A` for
invertible `X`. Source: Horn–Johnson (2013) [`hj13`], Thm 4.5.8; Golub–Van Loan (2013)
[`gvl13`], Thm 8.1.17. Uniqueness of the signature is Mathlib's
`QuadraticMap.Equivalent.sigPos_eq`.
atlas: sylvester-inertia -/
theorem inertiaPos_transpose_mul_mul (A : Matrix n n ℝ) {X : Matrix n n ℝ} (hX : IsUnit X) :
    inertiaPos (Xᵀ * A * X) = inertiaPos A :=
  (equivalent_toQuadraticForm'_transpose_mul_mul A hX).sigPos_eq

/-- **Sylvester's law of inertia (negative index).** `inertiaNeg (XᵀAX) = inertiaNeg A` for
invertible `X`. Source: Horn–Johnson (2013) [`hj13`], Thm 4.5.8.
atlas: sylvester-inertia -/
theorem inertiaNeg_transpose_mul_mul (A : Matrix n n ℝ) {X : Matrix n n ℝ} (hX : IsUnit X) :
    inertiaNeg (Xᵀ * A * X) = inertiaNeg A :=
  (equivalent_toQuadraticForm'_transpose_mul_mul A hX).sigNeg_eq

/-- The quadratic form of `diag(d)` is the weighted sum of squares with weights `d`. Helper for
`sylvester-inertia`. -/
theorem toQuadraticForm'_diagonal (d : n → ℝ) :
    (diagonal d).toQuadraticForm' = QuadraticMap.weightedSumSquares ℝ d := by
  ext x
  rw [toQuadraticForm'_apply, QuadraticMap.weightedSumSquares_apply, quadForm_eq_dotProduct]
  simp only [dotProduct, Matrix.mulVec_diagonal, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The positive index of a diagonal matrix is the number of positive diagonal entries. Source:
Horn–Johnson (2013) [`hj13`], §4.5.
atlas: sylvester-inertia -/
theorem inertiaPos_diagonal (d : n → ℝ) :
    inertiaPos (diagonal d) = (Finset.univ.filter fun i => 0 < d i).card := by
  rw [inertiaPos, toQuadraticForm'_diagonal, QuadraticForm.sigPos_weightedSumSquares,
    Set.ncard_eq_toFinset_card']
  congr 1
  ext i
  simp

/-- The negative index of a diagonal matrix is the number of negative diagonal entries. Source:
Horn–Johnson (2013) [`hj13`], §4.5.
atlas: sylvester-inertia -/
theorem inertiaNeg_diagonal (d : n → ℝ) :
    inertiaNeg (diagonal d) = (Finset.univ.filter fun i => d i < 0).card := by
  rw [inertiaNeg, toQuadraticForm'_diagonal, QuadraticForm.sigNeg_weightedSumSquares,
    Set.ncard_eq_toFinset_card']
  congr 1
  ext i
  simp

/-- A real symmetric matrix shifted by `x` is congruent to a diagonal matrix:
`A − xI = (Uᵀ)ᵀ diag(λ − x) Uᵀ` with `U = hA.eigenvectorUnitary`. Helper for
`sylvester-inertia`. -/
theorem sub_smul_one_eq_transpose_mul_diagonal_mul {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (x : ℝ) :
    A - x • (1 : Matrix n n ℝ) =
      ((hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ)ᵀ *
        diagonal (fun i => hA.eigenvalues i - x) * (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  set U : Matrix n n ℝ := (hA.eigenvectorUnitary : Matrix n n ℝ)
  have hUU : U * Uᵀ = 1 := eigenvectorUnitary_mul_transpose_self hA
  rw [Matrix.transpose_transpose,
    show (diagonal fun i => hA.eigenvalues i - x) = diagonal hA.eigenvalues - x • 1 by
      ext i j; by_cases h : i = j <;> simp [h],
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU,
    ← eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA]

/-- The transposed eigenvector matrix is invertible. Helper for `sylvester-inertia`. -/
theorem isUnit_transpose_eigenvectorUnitary {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    IsUnit ((hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ) :=
  (Matrix.isUnit_iff_isUnit_det _).2
    (Matrix.isUnit_det_of_right_inverse (transpose_eigenvectorUnitary_mul_self hA))

/-- **Inertia from the spectrum (positive index).** For real symmetric `A` and any `x`,
`inertiaPos (A − xI) = #{i : λᵢ > x}`; with `x = 0`, the number of positive eigenvalues.
Source: Horn–Johnson (2013) [`hj13`], Thm 4.5.8 (with the spectral theorem).
atlas: sylvester-inertia -/
theorem inertiaPos_sub_smul_one_eq_card {A : Matrix n n ℝ} (hA : A.IsHermitian) (x : ℝ) :
    inertiaPos (A - x • (1 : Matrix n n ℝ)) =
      (Finset.univ.filter fun i => x < hA.eigenvalues i).card := by
  rw [sub_smul_one_eq_transpose_mul_diagonal_mul hA x,
    inertiaPos_transpose_mul_mul _ (isUnit_transpose_eigenvectorUnitary hA), inertiaPos_diagonal]
  simp_rw [sub_pos]

/-- **Inertia from the spectrum (negative index).** For real symmetric `A` and any `x`,
`inertiaNeg (A − xI) = #{i : λᵢ < x}`. Source: Horn–Johnson (2013) [`hj13`], Thm 4.5.8;
Golub–Van Loan (2013) [`gvl13`], §8.4.1.
atlas: sylvester-inertia -/
theorem inertiaNeg_sub_smul_one_eq_card {A : Matrix n n ℝ} (hA : A.IsHermitian) (x : ℝ) :
    inertiaNeg (A - x • (1 : Matrix n n ℝ)) =
      (Finset.univ.filter fun i => hA.eigenvalues i < x).card := by
  rw [sub_smul_one_eq_transpose_mul_diagonal_mul hA x,
    inertiaNeg_transpose_mul_mul _ (isUnit_transpose_eigenvectorUnitary hA), inertiaNeg_diagonal]
  simp_rw [sub_neg]

/-- For real symmetric `A`, `inertiaPos A` is the number of positive eigenvalues. Source:
Horn–Johnson (2013) [`hj13`], §4.5.
atlas: sylvester-inertia -/
theorem inertiaPos_eq_card_eigenvalues_pos {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    inertiaPos A = (Finset.univ.filter fun i => 0 < hA.eigenvalues i).card := by
  simpa using inertiaPos_sub_smul_one_eq_card hA 0

/-- For real symmetric `A`, `inertiaNeg A` is the number of negative eigenvalues. Source:
Horn–Johnson (2013) [`hj13`], §4.5.
atlas: sylvester-inertia -/
theorem inertiaNeg_eq_card_eigenvalues_neg {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    inertiaNeg A = (Finset.univ.filter fun i => hA.eigenvalues i < 0).card := by
  simpa using inertiaNeg_sub_smul_one_eq_card hA 0

/-! ### Eigenvalue counts from `LDLᵀ` and from leading minors -/

/-- **Spectrum slicing by `LDLᵀ`.** If `A` is real symmetric and `A − xI = L D Lᵀ` with `L`
invertible (e.g. unit lower triangular, from symmetric Gaussian elimination) and
`D = diag(d)`, then the number of eigenvalues of `A` below `x` is the number of negative `dᵢ`.
Source: Golub–Van Loan (2013) [`gvl13`], §8.4.1 (Sylvester's law and `LDLᵀ`); Parlett (1998)
[`parlett98`], Ch. 3. Deviation: any invertible `L`.
atlas: sylvester-inertia -/
theorem card_eigenvalues_lt_eq_card_neg_of_eq_mul_diagonal_mul {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {x : ℝ} {L : Matrix n n ℝ} (hL : IsUnit L) {d : n → ℝ}
    (h : A - x • (1 : Matrix n n ℝ) = L * diagonal d * Lᵀ) :
    (Finset.univ.filter fun i => hA.eigenvalues i < x).card =
      (Finset.univ.filter fun i => d i < 0).card := by
  have hLt : IsUnit Lᵀ := (Matrix.isUnit_transpose L).2 hL
  rw [← inertiaNeg_sub_smul_one_eq_card hA x, h, ← inertiaNeg_diagonal,
    ← inertiaNeg_transpose_mul_mul (diagonal d) hLt, Matrix.transpose_transpose]

/-- The `k`-th leading principal minor `det M_{1:k, 1:k}` of `M : Fin n × Fin n` (`1` for
`k = 0`, `0` for `k > n`). Source: Golub–Van Loan (2013) [`gvl13`], §8.4.1. Helper for
`sylvester-inertia`. -/
def leadingMinor {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (k : ℕ) : ℝ :=
  if h : k ≤ m then (M.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

/-- SCAFFOLD: sylvester-inertia
**Eigenvalue count from the leading principal minors (Sturm / Jacobi).** Let `A : Fin m × Fin m`
be real symmetric and `p_k = det (A − xI)_{1:k, 1:k}` (`p_0 = 1`). If every `p_k` (`1 ≤ k ≤ m`)
is nonzero, then the number of eigenvalues of `A` below `x` equals the number of sign changes
in `p_0, p_1, …, p_m`, i.e. `#{k < m : p_k p_{k+1} < 0}`. For an unreduced symmetric
tridiagonal `A` the `p_k` obey the Sturm three-term recurrence
`p_{k+1} = (a_{k+1} − x) p_k − b_k² p_{k−1}`, and this count drives bisection. Source:
Golub–Van Loan (2013) [`gvl13`], Thm 8.5.1 and §8.4.1; Parlett (1998) [`parlett98`], Ch. 3;
Horn–Johnson (2013) [`hj13`], §4.5. Proof sketch: nonzero leading minors give `LU` of `A − xI`
(`luSucceeds_iff_forall_det_ne_zero`, D-A's `Matrix/Factorizations/LU.lean`), symmetric so
`A − xI = L D Lᵀ` with `d_{k+1} = p_{k+1}/p_k` (`IsLU.det_leadingSubmatrix`); then
`card_eigenvalues_lt_eq_card_neg_of_eq_mul_diagonal_mul` and `p_{k+1}/p_k < 0 ↔ p_k p_{k+1} < 0`.
Difficulty 3.
atlas: sylvester-inertia -/
theorem card_eigenvalues_lt_eq_card_sign_changes {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) {x : ℝ}
    (hp : ∀ k, 1 ≤ k → k ≤ m → leadingMinor (A - x • (1 : Matrix (Fin m) (Fin m) ℝ)) k ≠ 0) :
    (Finset.univ.filter fun i => hA.eigenvalues i < x).card =
      (Finset.univ.filter fun k : Fin m =>
        leadingMinor (A - x • (1 : Matrix (Fin m) (Fin m) ℝ)) (k : ℕ) *
          leadingMinor (A - x • (1 : Matrix (Fin m) (Fin m) ℝ)) ((k : ℕ) + 1) < 0).card := by
  sorry

end NLAlib
