import NLAlib.Matrix.SpectralBounds
import NLAlib.Matrix.QuadForm
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Polynomial calculus of real symmetric matrices

For a real symmetric matrix `A = U diag(λ) Uᵀ` (Mathlib's `Matrix.IsHermitian.spectral_theorem`,
with `U = hA.eigenvectorUnitary` and `λ = hA.eigenvalues`) and a real polynomial `p`,

* `aeval_eq_mul_diagonal_mul`: `p(A) = U diag(p(λ)) Uᵀ`;
* `aeval_mulVec_eq_sum`: `p(A) v = ∑ᵢ p(λᵢ) ⟨uᵢ, v⟩ uᵢ`;
* `dotProduct_aeval_mulVec_eq_sum`: `vᵀ p(A) v = ∑ᵢ p(λᵢ) ⟨uᵢ, v⟩²` (the spectral-measure
  identity);
* `specNorm_aeval_le`: `‖p(A)‖₂ ≤ M` when `|p(λᵢ)| ≤ M` for every eigenvalue;
* `dotProduct_aeval_mulVec_self_le`: `‖p(A) v‖² ≤ M² ‖v‖²` when `|p| ≤ M` on a set containing
  the spectrum;
* `quadForm_aeval_mulVec_le`: the energy-norm form `‖p(A) v‖_A² ≤ M² ‖v‖_A²` for positive
  semidefinite `A` (spectrum in `S ⊆ [0, ∞)`).

Mathlib's isometric `norm_cfc_le` needs a complex C⋆-algebra and does not apply to real
matrices, so the bounds are proved directly from the eigendecomposition.

These are the polynomial spectral bounds consumed by the Krylov layer (`cg-convergence`,
`lanczos-gauss-quadrature`, `spectral-measure`) together with the Chebyshev bounds of
`NLAlib.Polynomial`.

Source: Golub–Van Loan, 4th ed., §9.1 / §11.3; Saad 2003, §6.11; Trefethen–Bau 1997, Lecture 38.
Audit G0 C5, G3 C1. Atlas: `polynomial-spectral-bound` (new).
-/

noncomputable section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenvector matrix of a real symmetric matrix is orthogonal: `UᵀU = I`, with
`U = hA.eigenvectorUnitary` (columns `hA.eigenvectorBasis`). Real specialisation of Mathlib's
`Unitary.coe_star_mul_self`. Atlas `polynomial-spectral-bound` (helper). -/
theorem transpose_eigenvectorUnitary_mul_self {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ * (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 := by
  have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  simpa [Matrix.star_eq_conjTranspose] using this

/-- The eigenvector matrix of a real symmetric matrix is orthogonal: `UUᵀ = I`.
Atlas `polynomial-spectral-bound` (helper). -/
theorem eigenvectorUnitary_mul_transpose_self {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℝ) * (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ = 1 :=
  mul_eq_one_comm.1 (transpose_eigenvectorUnitary_mul_self hA)

/-- Real spectral theorem in transpose form: `A = U diag(λ) Uᵀ` with `U = hA.eigenvectorUnitary`
and `λ = hA.eigenvalues`. Real specialisation of Mathlib's `Matrix.IsHermitian.spectral_theorem`
(Horn–Johnson 2013, Thm 4.1.5). Atlas `polynomial-spectral-bound` (helper). -/
theorem eq_eigenvectorUnitary_mul_diagonal_mul_transpose {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℝ) * Matrix.diagonal hA.eigenvalues *
      (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]

/-- A polynomial of a diagonal matrix is the diagonal matrix of the polynomial values:
`p(diag d) = diag(p ∘ d)`. Atlas `polynomial-spectral-bound` (helper). -/
theorem aeval_diagonal (d : n → ℝ) (p : ℝ[X]) :
    aeval (Matrix.diagonal d) p = Matrix.diagonal fun i => p.eval (d i) := by
  have := Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom ℝ (n := n) (α := ℝ)) d p
  simp only [Matrix.diagonalAlgHom_apply] at this
  rw [this]
  congr 1
  funext i
  rw [aeval_pi_apply₂, coe_aeval_eq_eval]

/-- **Polynomial calculus, matrix form.** For real symmetric `A = U diag(λ) Uᵀ`,
`p(A) = U diag(p(λ)) Uᵀ`. Standard (Golub–Van Loan, 4th ed., §9.1.1; Horn–Johnson 2013, §1.3);
audit G0 C5; atlas `polynomial-spectral-bound`. -/
theorem aeval_eq_mul_diagonal_mul {A : Matrix n n ℝ} (hA : A.IsHermitian) (p : ℝ[X]) :
    aeval A p = (hA.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => p.eval (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  set U : Matrix n n ℝ := ↑hA.eigenvectorUnitary
  have hU : Uᵀ * U = 1 := transpose_eigenvectorUnitary_mul_self hA
  have hU' : U * Uᵀ = 1 := eigenvectorUnitary_mul_transpose_self hA
  -- conjugation by `U` as an algebra homomorphism
  let f : Matrix n n ℝ →ₐ[ℝ] Matrix n n ℝ :=
    { toFun := fun M => U * M * Uᵀ
      map_one' := by simp [hU']
      map_mul' := fun M N => by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
      map_zero' := by simp
      map_add' := fun M N => by simp [Matrix.mul_add, Matrix.add_mul]
      commutes' := fun r => by
        simp [Algebra.algebraMap_eq_smul_one, hU'] }
  have hA' : aeval A p = aeval (f (Matrix.diagonal hA.eigenvalues)) p :=
    congrArg (fun M => aeval M p) (eq_eigenvectorUnitary_mul_diagonal_mul_transpose hA)
  rw [hA', Polynomial.aeval_algHom_apply, aeval_diagonal]
  rfl

/-- The coordinates of `v` in the eigenbasis: `(Uᵀ v)ᵢ = ⟨uᵢ, v⟩`, `uᵢ = hA.eigenvectorBasis i`.
Atlas `polynomial-spectral-bound` (helper). -/
theorem transpose_eigenvectorUnitary_mulVec_apply {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (v : n → ℝ) (i : n) :
    ((hA.eigenvectorUnitary : Matrix n n ℝ)ᵀ *ᵥ v) i = ⇑(hA.eigenvectorBasis i) ⬝ᵥ v :=
  rfl

/-- **Polynomial calculus, vector form.** `p(A) v = ∑ᵢ p(λᵢ) ⟨uᵢ, v⟩ uᵢ` for real symmetric `A`
with orthonormal eigenvectors `uᵢ = hA.eigenvectorBasis i`. Standard (Saad 2003, §6.11);
audit G3 C1; atlas `polynomial-spectral-bound`.
atlas: polynomial-spectral-bound -/
theorem aeval_mulVec_eq_sum {A : Matrix n n ℝ} (hA : A.IsHermitian) (p : ℝ[X]) (v : n → ℝ) :
    aeval A p *ᵥ v =
      ∑ i, (p.eval (hA.eigenvalues i) * (⇑(hA.eigenvectorBasis i) ⬝ᵥ v)) •
        ⇑(hA.eigenvectorBasis i) := by
  rw [aeval_eq_mul_diagonal_mul hA p, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  ext j
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
  simp only [if_true]
  ring

/-- Squared coordinates in the eigenbasis sum to the squared norm (Parseval):
`∑ᵢ ⟨uᵢ, v⟩² = v ⬝ v`. Atlas `polynomial-spectral-bound` (helper). -/
theorem sum_sq_eigenvectorBasis_dotProduct {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (v : n → ℝ) : ∑ i, (⇑(hA.eigenvectorBasis i) ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := by
  set U : Matrix n n ℝ := ↑hA.eigenvectorUnitary
  have h := mulVec_dotProduct_mulVec_self Uᵀ v
  rw [Matrix.transpose_transpose, eigenvectorUnitary_mul_transpose_self hA,
    Matrix.one_mulVec] at h
  rw [← h, mulVec_dotProduct_mulVec_eq_sum_sq]
  rfl

/-- **Spectral-measure identity.** `vᵀ p(A) v = ∑ᵢ p(λᵢ) ⟨uᵢ, v⟩²` for real symmetric `A`.
Standard (Golub–Meurant 2010, §7.1); audit G3 C1/C2; atlas `polynomial-spectral-bound`,
`spectral-measure`.
atlas: polynomial-spectral-bound -/
theorem dotProduct_aeval_mulVec_eq_sum {A : Matrix n n ℝ} (hA : A.IsHermitian) (p : ℝ[X])
    (v : n → ℝ) :
    v ⬝ᵥ (aeval A p *ᵥ v) =
      ∑ i, p.eval (hA.eigenvalues i) * (⇑(hA.eigenvectorBasis i) ⬝ᵥ v) ^ 2 := by
  rw [aeval_mulVec_eq_sum hA p v, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm v]
  ring

/-- The quadratic form in the eigenbasis: `vᵀ A v = ∑ᵢ λᵢ ⟨uᵢ, v⟩²`. Standard;
atlas `polynomial-spectral-bound`, `spectral-measure`.
atlas: polynomial-spectral-bound -/
theorem quadForm_eq_sum_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian) (v : n → ℝ) :
    quadForm A v = ∑ i, hA.eigenvalues i * (⇑(hA.eigenvectorBasis i) ⬝ᵥ v) ^ 2 := by
  have h := dotProduct_aeval_mulVec_eq_sum hA X v
  simp only [aeval_X, eval_X] at h
  exact h

/-- A polynomial of a symmetric matrix is symmetric: `p(A)ᵀ = p(A)`.
Atlas `polynomial-spectral-bound` (helper). -/
theorem transpose_aeval {A : Matrix n n ℝ} (hA : A.IsHermitian) (p : ℝ[X]) :
    (aeval A p)ᵀ = aeval A p := by
  rw [aeval_eq_mul_diagonal_mul hA p]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

/-- `‖p(A) v‖² = ∑ᵢ p(λᵢ)² ⟨uᵢ, v⟩²` for real symmetric `A`. Audit G3 C1;
atlas `polynomial-spectral-bound`. -/
theorem dotProduct_aeval_mulVec_self_eq_sum {A : Matrix n n ℝ} (hA : A.IsHermitian) (p : ℝ[X])
    (v : n → ℝ) :
    (aeval A p *ᵥ v) ⬝ᵥ (aeval A p *ᵥ v) =
      ∑ i, p.eval (hA.eigenvalues i) ^ 2 * (⇑(hA.eigenvectorBasis i) ⬝ᵥ v) ^ 2 := by
  rw [mulVec_dotProduct_mulVec_self, transpose_aeval hA, ← map_mul,
    dotProduct_aeval_mulVec_eq_sum hA]
  simp [sq]

/-- `(p(A)v)ᵀ A (p(A)v) = ∑ᵢ λᵢ p(λᵢ)² ⟨uᵢ, v⟩²` for real symmetric `A`. Audit G3 C1;
atlas `polynomial-spectral-bound`. -/
theorem quadForm_aeval_mulVec_eq_sum {A : Matrix n n ℝ} (hA : A.IsHermitian) (p : ℝ[X])
    (v : n → ℝ) :
    quadForm A (aeval A p *ᵥ v) =
      ∑ i, hA.eigenvalues i * p.eval (hA.eigenvalues i) ^ 2 *
        (⇑(hA.eigenvectorBasis i) ⬝ᵥ v) ^ 2 := by
  have hP : quadForm A (aeval A p *ᵥ v) = v ⬝ᵥ (aeval A (p * X * p) *ᵥ v) := by
    rw [quadForm, map_mul, map_mul, aeval_X, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec v (aeval A p), ← Matrix.mulVec_transpose, transpose_aeval hA p]
  rw [hP, dotProduct_aeval_mulVec_eq_sum hA]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [eval_mul, eval_X]
  ring

/-- **Polynomial spectral-norm bound.** For real symmetric `A`, if `|p(λᵢ)| ≤ M` at every
eigenvalue then `‖p(A)‖₂ ≤ M`. Standard (Golub–Van Loan, 4th ed., §11.3.4, used for the CG
bound); audit G0 C5; atlas `polynomial-spectral-bound`. The hypothesis `0 ≤ M` covers the empty
index type.
atlas: polynomial-spectral-bound -/
theorem specNorm_aeval_le {A : Matrix n n ℝ} (hA : A.IsHermitian) (p : ℝ[X]) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i, |p.eval (hA.eigenvalues i)| ≤ M) : specNorm (aeval A p) ≤ M := by
  have hU := transpose_eigenvectorUnitary_mul_self hA
  rw [aeval_eq_mul_diagonal_mul hA p, specNorm_mul_transpose_right_of_hasOrthonormalCols hU,
    specNorm_mul_left_of_hasOrthonormalCols hU, specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hM).2 fun i => by simpa [Real.norm_eq_abs] using h i

/-- **Polynomial bound, vector form.** If every eigenvalue of the real symmetric `A` lies in `S`
and `|p| ≤ M` on `S`, then `‖p(A) v‖² ≤ M² ‖v‖²`. Standard (Saad 2003, §6.11); audit G3 C1;
atlas `polynomial-spectral-bound`.
atlas: polynomial-spectral-bound -/
theorem dotProduct_aeval_mulVec_self_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {p : ℝ[X]}
    {S : Set ℝ} {M : ℝ} (hspec : ∀ i, hA.eigenvalues i ∈ S) (hp : ∀ x ∈ S, |p.eval x| ≤ M)
    (v : n → ℝ) :
    (aeval A p *ᵥ v) ⬝ᵥ (aeval A p *ᵥ v) ≤ M ^ 2 * (v ⬝ᵥ v) := by
  rw [dotProduct_aeval_mulVec_self_eq_sum hA, ← sum_sq_eigenvectorBasis_dotProduct hA v,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have h := hp _ (hspec i)
  exact sq_le_sq' (by linarith [neg_abs_le (p.eval (hA.eigenvalues i))])
    ((le_abs_self _).trans h)

/-- **Polynomial bound, energy form.** If every eigenvalue of the real symmetric `A` lies in
`S ⊆ [0, ∞)` (so `A` is positive semidefinite) and `|p| ≤ M` on `S`, then
`(p(A)v)ᵀ A (p(A)v) ≤ M² vᵀ A v`, i.e. `‖p(A) v‖_A ≤ M ‖v‖_A`. This is the form used for the
CG error (Greenbaum 1997, §3.1; Saad 2003, Thm 6.29); audit G3 C1;
atlas `polynomial-spectral-bound`.
atlas: polynomial-spectral-bound -/
theorem quadForm_aeval_mulVec_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {p : ℝ[X]}
    {S : Set ℝ} {M : ℝ} (hS : S ⊆ Set.Ici 0) (hspec : ∀ i, hA.eigenvalues i ∈ S)
    (hp : ∀ x ∈ S, |p.eval x| ≤ M) (v : n → ℝ) :
    quadForm A (aeval A p *ᵥ v) ≤ M ^ 2 * quadForm A v := by
  rw [quadForm_aeval_mulVec_eq_sum hA, quadForm_eq_sum_eigenvalues hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hlam : 0 ≤ hA.eigenvalues i := hS (hspec i)
  have h := hp _ (hspec i)
  have hsq : p.eval (hA.eigenvalues i) ^ 2 ≤ M ^ 2 :=
    sq_le_sq' (by linarith [neg_abs_le (p.eval (hA.eigenvalues i))]) ((le_abs_self _).trans h)
  have hc := sq_nonneg (⇑(hA.eigenvectorBasis i) ⬝ᵥ v)
  calc hA.eigenvalues i * p.eval (hA.eigenvalues i) ^ 2 * (⇑(hA.eigenvectorBasis i) ⬝ᵥ v) ^ 2
      ≤ hA.eigenvalues i * M ^ 2 * (⇑(hA.eigenvectorBasis i) ⬝ᵥ v) ^ 2 := by gcongr
    _ = M ^ 2 * (hA.eigenvalues i * (⇑(hA.eigenvectorBasis i) ⬝ᵥ v) ^ 2) := by ring

end NLAlib
