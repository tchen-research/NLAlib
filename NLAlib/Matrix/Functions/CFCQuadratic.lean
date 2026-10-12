import NLAlib.Matrix.Functions.PolynomialCalculus
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Lagrange

/-!
# Quadratic forms of matrix functions of a real symmetric matrix

For a real symmetric `A` with eigenpairs `(λᵢ, uᵢ)` (Mathlib's `hA.eigenvalues`,
`hA.eigenvectorBasis`) and `f(A) = cfc f A`:

* `eigenvectorBasis_dotProduct_eigenvectorBasis`: `uᵢ ⬝ uⱼ = δᵢⱼ`;
  `eigenvectorBasis_dotProduct_aeval_mulVec`: `uᵢ ⬝ p(A) v = p(λᵢ) (uᵢ ⬝ v)`;
  `eigenvalues_eq_dotProduct_mulVec`: `λᵢ = uᵢᵀ A uᵢ`;
* `dotProduct_cfc_mulVec_eq_sum`: the eigen-expansion `vᵀ f(A) v = ∑ᵢ f(λᵢ) (uᵢ ⬝ v)²`;
* `mul_dotProduct_le_dotProduct_mulVec_of_eigenvalues`,
  `dotProduct_mulVec_le_mul_dotProduct_of_eigenvalues`: Rayleigh bounds from an eigenvalue
  enclosure; `abs_dotProduct_cfc_mulVec_le`: `|vᵀ g(A) v| ≤ E ‖v‖²` when `|g(λᵢ)| ≤ E`;
* `cfc_eq_aeval_of_forall_eval_eq`, `cfc_eq_aeval_interpolate`: `f(A) = p(A)` for any `p`
  agreeing with `f` on the eigenvalues (e.g. the Lagrange interpolant);
  `dotProduct_cfc_mulVec_self_le`: `‖g(A) v‖² ≤ M² ‖v‖²` when `|g| ≤ M` on the spectrum (the
  `cfc` form of `polynomial-spectral-bound`).

These are the matrix-function helpers of the Krylov layer (`spectral-measure`,
`lanczos-gauss-quadrature`, `lanczos-fa-error`, `krylov-eigenvector-angle`).

Source: Horn–Johnson (2013), Thm 4.2.2; Golub–Meurant (2010) [`gm10`], Ch. 7; Higham (2008)
[`higham08`], Def. 1.4 and Thm 1.12.
-/

noncomputable section

open scoped Matrix Polynomial
open Matrix Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Orthonormality of the eigenvector basis -/

/-- The eigenvector basis is orthonormal in dot-product form: `uᵢ ⬝ uⱼ = δᵢⱼ`.
Helper for `krylov-eigenvector-angle`. -/
theorem eigenvectorBasis_dotProduct_eigenvectorBasis {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (i j : n) :
    (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ (hA.eigenvectorBasis j : n → ℝ) =
      if i = j then 1 else 0 := by
  have h := orthonormal_iff_ite.1 hA.eigenvectorBasis.orthonormal i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [dotProduct_comm] using h

/-- Eigen-coordinates of `p(A) v`: `uᵢ ⬝ p(A) v = p(λᵢ) (uᵢ ⬝ v)` for real symmetric `A`.
Helper for `krylov-eigenvector-angle`. -/
theorem eigenvectorBasis_dotProduct_aeval_mulVec {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (p : ℝ[X]) (v : n → ℝ) (i : n) :
    (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ (aeval A p *ᵥ v) =
      p.eval (hA.eigenvalues i) * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v) := by
  rw [aeval_mulVec_eq_sum hA p v, dotProduct_sum]
  simp [dotProduct_smul, eigenvectorBasis_dotProduct_eigenvectorBasis hA]

/-- An eigenvalue is the Rayleigh quotient of its unit eigenvector: `λᵢ = uᵢᵀ A uᵢ`.
Atlas: `lanczos-gauss-quadrature` (helper). -/
theorem eigenvalues_eq_dotProduct_mulVec {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    hA.eigenvalues i =
      (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ (A *ᵥ (hA.eigenvectorBasis i : n → ℝ)) := by
  simpa [dotProduct_comm] using hA.eigenvalues_eq i

/-! ### Quadratic forms of matrix functions -/

/-- Eigen-expansion of a quadratic form of a matrix function: for symmetric `A`,
`vᵀ f(A) v = ∑ᵢ f(λᵢ) (uᵢ ⬝ v)²` with `(λᵢ, uᵢ)` the eigenpairs of `A`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 7, eq. (7.1). Atlas: `spectral-measure`
(helper). -/
theorem dotProduct_cfc_mulVec_eq_sum {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (v : n → ℝ) :
    v ⬝ᵥ (cfc f A *ᵥ v) =
      ∑ i, f (hA.eigenvalues i) * ((hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v) ^ 2 := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have h1 : v ᵥ* (hA.eigenvectorUnitary : Matrix n n ℝ) =
      fun i => (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v := by
    ext i; simp [Matrix.vecMul, dotProduct, mul_comm]
  have h2 : (star (hA.eigenvectorUnitary : Matrix n n ℝ)) *ᵥ v =
      fun i => (hA.eigenvectorBasis i : n → ℝ) ⬝ᵥ v := by
    ext i; simp [Matrix.mulVec, dotProduct, Matrix.star_apply]
  rw [h1, h2]
  simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply, RCLike.ofReal_real_eq_id,
    id]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Rayleigh bounds from an eigenvalue enclosure: if every eigenvalue of the symmetric `A` lies
in `[a, c]`, then `a ‖x‖² ≤ xᵀ A x ≤ c ‖x‖²`. Lower half.
Source: Horn–Johnson (2013), Thm 4.2.2 (Rayleigh–Ritz). Atlas: `lanczos-gauss-quadrature`
(helper). -/
theorem mul_dotProduct_le_dotProduct_mulVec_of_eigenvalues {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {a : ℝ} (ha : ∀ i, a ≤ hA.eigenvalues i) (x : n → ℝ) :
    a * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  have h := dotProduct_cfc_mulVec_eq_sum hA id x
  rw [cfc_id ℝ A] at h
  rw [h, ← sum_sq_eigenvectorBasis_dotProduct hA x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ha i) (sq_nonneg _)

/-- Upper Rayleigh bound from an eigenvalue enclosure: `xᵀ A x ≤ c ‖x‖²` if every eigenvalue is
at most `c`. Source: Horn–Johnson (2013), Thm 4.2.2. Atlas: `lanczos-gauss-quadrature`
(helper). -/
theorem dotProduct_mulVec_le_mul_dotProduct_of_eigenvalues {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {c : ℝ} (hc : ∀ i, hA.eigenvalues i ≤ c) (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ c * (x ⬝ᵥ x) := by
  have h := dotProduct_cfc_mulVec_eq_sum hA id x
  rw [cfc_id ℝ A] at h
  rw [h, ← sum_sq_eigenvectorBasis_dotProduct hA x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hc i) (sq_nonneg _)

/-- A function bounded by `E` on the eigenvalues gives a quadratic form bounded by `E ‖v‖²`:
`|vᵀ g(A) v| ≤ E (v ⬝ v)`. Atlas: `lanczos-gauss-quadrature` (helper; the `cfc` form of
`polynomial-spectral-bound`). -/
theorem abs_dotProduct_cfc_mulVec_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {g : ℝ → ℝ}
    {E : ℝ} (hg : ∀ i, |g (hA.eigenvalues i)| ≤ E) (v : n → ℝ) :
    |v ⬝ᵥ (cfc g A *ᵥ v)| ≤ E * (v ⬝ᵥ v) := by
  rw [dotProduct_cfc_mulVec_eq_sum hA g v, ← sum_sq_eigenvectorBasis_dotProduct hA v,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_sq]
  exact mul_le_mul_of_nonneg_right (hg i) (sq_nonneg _)

/-! ### Matrix functions are interpolating polynomials -/

/-- A matrix function of a symmetric `A` equals the polynomial calculus of any polynomial that
agrees with `f` at the eigenvalues: `f(A) = p(A)` when `p(λᵢ) = f(λᵢ)` for all `i`.
Standard (Higham 2008 [`higham08`], Def. 1.4 and Thm 1.12). Atlas: `lanczos-fa-error` (helper). -/
theorem cfc_eq_aeval_of_forall_eval_eq {A : Matrix n n ℝ} (hA : A.IsHermitian) {f : ℝ → ℝ}
    {p : ℝ[X]} (h : ∀ i, p.eval (hA.eigenvalues i) = f (hA.eigenvalues i)) :
    cfc f A = aeval A p := by
  rw [← cfc_polynomial p A hA.isSelfAdjoint]
  refine cfc_congr fun x hx => ?_
  rw [hA.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact (h i).symm

/-- The Lagrange interpolant of `f` at the distinct eigenvalues of the symmetric `A` takes the
value `f(λᵢ)` at `λᵢ`. Helper for `lanczos-fa-error`. -/
theorem eval_interpolate_eigenvalues {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (i : n) :
    (Lagrange.interpolate (Finset.univ.image hA.eigenvalues) id f).eval (hA.eigenvalues i) =
      f (hA.eigenvalues i) :=
  Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _)
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))

/-- `f(A)` is `p(A)` for the Lagrange interpolant `p` of `f` at the (distinct) eigenvalues of the
symmetric `A`. Standard (Higham 2008 [`higham08`], Def. 1.4). Atlas: `lanczos-fa-error`
(helper). -/
theorem cfc_eq_aeval_interpolate {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = aeval A (Lagrange.interpolate (Finset.univ.image hA.eigenvalues) id f) :=
  cfc_eq_aeval_of_forall_eval_eq hA (eval_interpolate_eigenvalues hA f)

/-- **Spectral bound, `cfc` form.** If every eigenvalue of the symmetric `A` lies in `S` and
`|g| ≤ M` on `S`, then `‖g(A) v‖² ≤ M² ‖v‖²`. The `cfc` form of
`dotProduct_aeval_mulVec_self_le` (Saad 2003, §6.11). Atlas: `lanczos-fa-error` (helper; the
`cfc` form of `polynomial-spectral-bound`). -/
theorem dotProduct_cfc_mulVec_self_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {g : ℝ → ℝ}
    {S : Set ℝ} {M : ℝ} (hspec : ∀ i, hA.eigenvalues i ∈ S) (hg : ∀ x ∈ S, |g x| ≤ M)
    (v : n → ℝ) : (cfc g A *ᵥ v) ⬝ᵥ (cfc g A *ᵥ v) ≤ M ^ 2 * (v ⬝ᵥ v) := by
  rw [cfc_eq_aeval_interpolate hA g]
  refine dotProduct_aeval_mulVec_self_le hA (S := Set.range hA.eigenvalues) (fun i => ⟨i, rfl⟩)
    ?_ v
  rintro _ ⟨i, rfl⟩
  rw [eval_interpolate_eigenvalues hA g]
  exact hg _ (hspec i)

end NLAlib
