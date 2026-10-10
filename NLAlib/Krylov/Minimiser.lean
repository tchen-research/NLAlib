import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Order.Filter.Extr
import NLAlib.Krylov.Polynomial
import NLAlib.Matrix.PolynomialCalculus
import NLAlib.Polynomial.Basic

/-!
# Affine minimisers over Krylov spaces and residual polynomials

The generic layer behind every minimising Krylov method (`docs/KRYLOV_DEFINITIONS.md` §3.2):

* `IsAffineMinimiser E x₀ S x`: `x ∈ x₀ + S` minimises `E` over `x₀ + S`;
  `isAffineMinimiser_iff_isMinOn` is the bridge to Mathlib's `IsMinOn` on `AffineSubspace.mk'`.
  CG (`IsCGIterate`) and GMRES/MINRES are instances.
* Residual polynomials (atlas `residual-polynomial`): `x − x₀ ∈ K_q(A, r₀)` gives
  `c − A x = p(A) r₀` and `x − x⋆ = p(A)(x₀ − x⋆)` with `deg p ≤ q`, `p(0) = 1`
  (`exists_sub_mulVec_eq_aeval_mulVec_of_sub_mem_krylovSpace`,
  `exists_sub_eq_aeval_mulVec_of_sub_mem_krylovSpace`); conversely every such `p` is realised
  (`exists_mem_krylovSpace_sub_mulVec_eq_aeval_mulVec`,
  `exists_mem_krylovSpace_add_sub_eq_aeval_mulVec`),
  and for invertible `A` this is an iff (`sub_mem_krylovSpace_iff_exists_sub_mulVec_eq`).
* K1, `IsAffineMinimiser.le_aeval` and `IsAffineMinimiser.le_aeval_residual`: a minimiser over
  `x₀ + K_q` beats every residual polynomial, for any objective, with no spectral hypothesis.
* The class theorem `quadForm_sub_le_of_isAffineMinimiser`: for symmetric `A` and a weight
  `g(A)` with `g ≥ 0` on the spectrum, a minimiser of `‖· − x⋆‖²_{g(A)}` over `x₀ + K_q` has
  `‖x − x⋆‖²_{g(A)} ≤ M² ‖x₀ − x⋆‖²_{g(A)}` for every residual polynomial `p` with `|p| ≤ M`
  on the spectrum. CG is `g = X`, MINRES `g = X²`, the error-minimising method `g = 1`.

Source: Saad (2003) [`saad03`], §6.11 and Thm 6.29; Trefethen–Bau (1997) [`tb97`], Lect. 35,
38; Greenbaum (1997) [`greenbaum97`], Ch. 2–3. Atlas: `residual-polynomial` (the polynomial
characterisation); the class theorem serves `cg-convergence`, `minres-bound`.
-/

noncomputable section

open scoped Matrix Polynomial
open Polynomial

namespace NLAlib

/-! ### The predicate -/

section Predicate

variable {n : Type*}

/-- `x` minimises the objective `E` over the affine space `x₀ + S`: `x − x₀ ∈ S` and
`E x ≤ E (x₀ + y)` for every `y ∈ S`. Minimising Krylov methods (CG, GMRES, MINRES, LSQR,
sketched GMRES) are instances with `S` a Krylov space. Non-uniqueness is harmless: theorems
quantify over every minimiser. Source: Saad (2003) [`saad03`], §5.1 (optimality of projection
methods); KRYLOV_DEFINITIONS §3.2. -/
def IsAffineMinimiser (E : (n → ℝ) → ℝ) (x₀ : n → ℝ) (S : Submodule ℝ (n → ℝ))
    (x : n → ℝ) : Prop :=
  x - x₀ ∈ S ∧ ∀ y ∈ S, E x ≤ E (x₀ + y)

variable {E : (n → ℝ) → ℝ} {x₀ x : n → ℝ} {S : Submodule ℝ (n → ℝ)}

/-- `IsAffineMinimiser` is Mathlib's `IsMinOn` on the affine subspace `x₀ + S`.
Source: KRYLOV_DEFINITIONS §3.2. -/
theorem isAffineMinimiser_iff_isMinOn :
    IsAffineMinimiser E x₀ S x ↔
      x ∈ AffineSubspace.mk' x₀ S ∧ IsMinOn E (AffineSubspace.mk' x₀ S) x := by
  simp only [IsAffineMinimiser, AffineSubspace.mem_mk', vsub_eq_sub, isMinOn_iff,
    SetLike.mem_coe]
  refine and_congr_right fun _ => ⟨fun h z hz => ?_, fun h y hy => h _ (by simpa using hy)⟩
  simpa using h (z - x₀) hz

/-- A minimiser beats every point of the affine space: `z − x₀ ∈ S → E x ≤ E z`.
Source: KRYLOV_DEFINITIONS §3.2. -/
theorem IsAffineMinimiser.le_of_sub_mem (hx : IsAffineMinimiser E x₀ S x) {z : n → ℝ}
    (hz : z - x₀ ∈ S) : E x ≤ E z := by
  simpa using hx.2 (z - x₀) hz

/-- A minimiser beats the starting point: `E x ≤ E x₀`. Source: KRYLOV_DEFINITIONS §3.2. -/
theorem IsAffineMinimiser.le_self (hx : IsAffineMinimiser E x₀ S x) : E x ≤ E x₀ :=
  hx.le_of_sub_mem (by simp)

/-- Two minimisers over the same affine space have the same value.
Source: KRYLOV_DEFINITIONS §3.2. -/
theorem IsAffineMinimiser.apply_eq {x' : n → ℝ} (hx : IsAffineMinimiser E x₀ S x)
    (hx' : IsAffineMinimiser E x₀ S x') : E x = E x' :=
  le_antisymm (hx.le_of_sub_mem hx'.1) (hx'.le_of_sub_mem hx.1)

/-- **Monotonicity.** A minimiser over a larger space is at least as good:
`S ≤ S'` gives `E x' ≤ E x`. With `S = K_q`, `S' = K_{q+1}` this is monotonicity of a
minimising Krylov method in the iteration count. Source: Saad (2003) [`saad03`], §6.5.6
(GMRES residuals are nonincreasing). -/
theorem IsAffineMinimiser.le_of_le {S' : Submodule ℝ (n → ℝ)} {x' : n → ℝ}
    (hx : IsAffineMinimiser E x₀ S x) (hx' : IsAffineMinimiser E x₀ S' x') (h : S ≤ S') :
    E x' ≤ E x :=
  hx'.le_of_sub_mem (h hx.1)

end Predicate

/-! ### Residual polynomials on Krylov spaces -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The residual of `x₀ + s(A) r₀` is `(1 − X s)(A) r₀`. -/
private lemma sub_mulVec_add_aeval (A : Matrix n n ℝ) (c x₀ : n → ℝ) (s : ℝ[X]) :
    c - A *ᵥ (x₀ + aeval A s *ᵥ (c - A *ᵥ x₀)) =
      aeval A (1 - X * s) *ᵥ (c - A *ᵥ x₀) := by
  rw [map_sub, map_one, map_mul, aeval_X, Matrix.sub_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_add]
  abel

/-- **Residual-polynomial form of an affine Krylov iterate.** If `x − x₀ ∈ K_q(A, r₀)`,
`r₀ = c − A x₀`, then `c − A x = p(A) r₀` for a residual polynomial `p` (`deg p ≤ q`,
`p(0) = 1`). No hypothesis on `A`. Source: Saad (2003) [`saad03`], §6.11; Trefethen–Bau (1997)
[`tb97`], Lect. 35. Atlas: `residual-polynomial` (partial: forward direction).
atlas: residual-polynomial (partial) -/
theorem exists_sub_mulVec_eq_aeval_mulVec_of_sub_mem_krylovSpace {A : Matrix n n ℝ}
    {c x₀ x : n → ℝ} {q : ℕ} (hx : x - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) q) :
    ∃ p : ℝ[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧
      c - A *ᵥ x = aeval A p *ᵥ (c - A *ᵥ x₀) := by
  obtain ⟨s, hs, hxs⟩ := (mem_krylovSpace_iff_degree _ _ _ _).1 hx
  refine ⟨1 - X * s, (degree_le_and_eval_zero_eq_one_iff.2 ⟨s, hs, rfl⟩).1,
    (degree_le_and_eval_zero_eq_one_iff.2 ⟨s, hs, rfl⟩).2, ?_⟩
  rw [← sub_mulVec_add_aeval, ← hxs, add_sub_cancel]

/-- **Every residual polynomial is realised in `x₀ + K_q`.** For `deg p ≤ q`, `p(0) = 1` there
is `y ∈ K_q(A, r₀)` with `c − A (x₀ + y) = p(A) r₀`. No hypothesis on `A`.
Source: Saad (2003) [`saad03`], §6.11. Atlas: `residual-polynomial` (partial: converse).
atlas: residual-polynomial (partial) -/
theorem exists_mem_krylovSpace_sub_mulVec_eq_aeval_mulVec (A : Matrix n n ℝ) (c x₀ : n → ℝ)
    {q : ℕ} {p : ℝ[X]} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1) :
    ∃ y ∈ krylovSpace A (c - A *ᵥ x₀) q,
      c - A *ᵥ (x₀ + y) = aeval A p *ᵥ (c - A *ᵥ x₀) := by
  obtain ⟨s, hs, rfl⟩ := degree_le_and_eval_zero_eq_one_iff.1 ⟨hp, hp0⟩
  exact ⟨aeval A s *ᵥ (c - A *ᵥ x₀), (mem_krylovSpace_iff_degree _ _ _ _).2 ⟨s, hs, rfl⟩,
    sub_mulVec_add_aeval A c x₀ s⟩

/-- **Error form of the residual polynomial.** If `A x⋆ = c` and `x − x₀ ∈ K_q(A, r₀)`, then
`x − x⋆ = p(A)(x₀ − x⋆)` for a residual polynomial `p`. Source: Saad (2003) [`saad03`], §6.11;
Trefethen–Bau (1997) [`tb97`], Thm 38.3 (proof). Atlas: `residual-polynomial` (partial).
atlas: residual-polynomial (partial) -/
theorem exists_sub_eq_aeval_mulVec_of_sub_mem_krylovSpace {A : Matrix n n ℝ}
    {c x₀ xs x : n → ℝ} (hxs : A *ᵥ xs = c) {q : ℕ}
    (hx : x - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) q) :
    ∃ p : ℝ[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧ x - xs = aeval A p *ᵥ (x₀ - xs) := by
  obtain ⟨s, hs, hy⟩ := (mem_krylovSpace_iff_degree _ _ _ _).1 hx
  refine ⟨1 - X * s, (degree_le_and_eval_zero_eq_one_iff.2 ⟨s, hs, rfl⟩).1,
    (degree_le_and_eval_zero_eq_one_iff.2 ⟨s, hs, rfl⟩).2, ?_⟩
  have hr : c - A *ᵥ x₀ = -(A *ᵥ (x₀ - xs)) := by
    rw [Matrix.mulVec_sub, hxs]; abel
  have hx' : x = x₀ + aeval A s *ᵥ (c - A *ᵥ x₀) := by rw [← hy]; abel
  rw [hx', mul_comm X s, map_sub, map_one, map_mul, aeval_X, Matrix.sub_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hr, Matrix.mulVec_neg]
  abel

/-- **Error form, converse.** If `A x⋆ = c`, every residual polynomial `p` is realised:
some `y ∈ K_q(A, r₀)` has `x₀ + y − x⋆ = p(A)(x₀ − x⋆)`. No hypothesis on `A`.
Source: Saad (2003) [`saad03`], §6.11. Atlas: `residual-polynomial` (partial).
atlas: residual-polynomial (partial) -/
theorem exists_mem_krylovSpace_add_sub_eq_aeval_mulVec {A : Matrix n n ℝ} {c xs : n → ℝ}
    (hxs : A *ᵥ xs = c) (x₀ : n → ℝ) {q : ℕ} {p : ℝ[X]} (hp : p.degree ≤ q)
    (hp0 : p.eval 0 = 1) :
    ∃ y ∈ krylovSpace A (c - A *ᵥ x₀) q, x₀ + y - xs = aeval A p *ᵥ (x₀ - xs) := by
  obtain ⟨s, hs, rfl⟩ := degree_le_and_eval_zero_eq_one_iff.1 ⟨hp, hp0⟩
  refine ⟨aeval A s *ᵥ (c - A *ᵥ x₀), (mem_krylovSpace_iff_degree _ _ _ _).2 ⟨s, hs, rfl⟩, ?_⟩
  have hr : c - A *ᵥ x₀ = -(A *ᵥ (x₀ - xs)) := by
    rw [Matrix.mulVec_sub, hxs]; abel
  rw [mul_comm X s, map_sub, map_one, map_mul, aeval_X, Matrix.sub_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hr, Matrix.mulVec_neg]
  abel

/-- **Residual-polynomial characterisation of `x₀ + K_q`.** For invertible `A`,
`x − x₀ ∈ K_q(A, r₀) ↔ ∃ p, deg p ≤ q ∧ p(0) = 1 ∧ c − A x = p(A) r₀`.
Source: Saad (2003) [`saad03`], §6.11; Trefethen–Bau (1997) [`tb97`], Lect. 35.
Deviation: the converse direction needs `A` injective (`IsUnit A`); the forward direction
(`exists_sub_mulVec_eq_aeval_mulVec_of_sub_mem_krylovSpace`) holds for every `A`.
atlas: residual-polynomial (partial) -/
theorem sub_mem_krylovSpace_iff_exists_sub_mulVec_eq {A : Matrix n n ℝ} (hA : IsUnit A)
    {c x₀ x : n → ℝ} {q : ℕ} :
    x - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) q ↔
      ∃ p : ℝ[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧ c - A *ᵥ x = aeval A p *ᵥ (c - A *ᵥ x₀) := by
  refine ⟨exists_sub_mulVec_eq_aeval_mulVec_of_sub_mem_krylovSpace, ?_⟩
  rintro ⟨p, hp, hp0, hres⟩
  obtain ⟨y, hy, hy'⟩ := exists_mem_krylovSpace_sub_mulVec_eq_aeval_mulVec A c x₀ hp hp0
  have hinj : Function.Injective (Matrix.mulVec A) := Matrix.mulVec_injective_iff_isUnit.2 hA
  have : x = x₀ + y := hinj (sub_right_injective (hres.trans hy'.symm))
  rw [this, add_sub_cancel_left]
  exact hy

/-! ### K1: a Krylov minimiser beats every residual polynomial -/

/-- **K1, error form.** If `x` minimises any objective `E` over `x₀ + K_q(A, r₀)` and
`A x⋆ = c`, then `E x ≤ E (x⋆ + p(A)(x₀ − x⋆))` for every residual polynomial `p`
(`deg p ≤ q`, `p(0) = 1`). No hypothesis on `A` or `E`. Source: Saad (2003) [`saad03`],
Thm 6.29 (proof); Trefethen–Bau (1997) [`tb97`], Thm 38.3 (proof); KRYLOV_DEFINITIONS §3.2.
Atlas: `residual-polynomial` (consumer: `cg-convergence`, `minres-bound`).
atlas: affine-krylov-minimiser -/
theorem IsAffineMinimiser.le_aeval {E : (n → ℝ) → ℝ} {A : Matrix n n ℝ} {c x₀ xs x : n → ℝ}
    {q : ℕ} (hx : IsAffineMinimiser E x₀ (krylovSpace A (c - A *ᵥ x₀) q) x)
    (hxs : A *ᵥ xs = c) {p : ℝ[X]} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1) :
    E x ≤ E (xs + aeval A p *ᵥ (x₀ - xs)) := by
  obtain ⟨y, hy, hpoly⟩ := exists_mem_krylovSpace_add_sub_eq_aeval_mulVec hxs x₀ hp hp0
  rw [← hpoly, add_sub_cancel]
  exact hx.2 y hy

/-- **K1, residual form.** If `x` minimises an objective of the residual,
`y ↦ F (c − A y)`, over `x₀ + K_q(A, r₀)`, then `F (c − A x) ≤ F (p(A) r₀)` for every
residual polynomial `p`. No solution `x⋆` is needed (GMRES on singular or inconsistent
systems). Source: Saad (2003) [`saad03`], Prop 6.32 (proof); KRYLOV_DEFINITIONS §3.3.
Atlas: `residual-polynomial` (consumer: `gmres-def`).
atlas: affine-krylov-minimiser -/
theorem IsAffineMinimiser.le_aeval_residual {F : (n → ℝ) → ℝ} {A : Matrix n n ℝ}
    {c x₀ x : n → ℝ} {q : ℕ}
    (hx : IsAffineMinimiser (fun y => F (c - A *ᵥ y)) x₀ (krylovSpace A (c - A *ᵥ x₀) q) x)
    {p : ℝ[X]} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1) :
    F (c - A *ᵥ x) ≤ F (aeval A p *ᵥ (c - A *ᵥ x₀)) := by
  obtain ⟨y, hy, hres⟩ := exists_mem_krylovSpace_sub_mulVec_eq_aeval_mulVec A c x₀ hp hp0
  rw [← hres]
  exact hx.2 y hy

/-! ### K2: the class theorem for weighted-norm minimisers -/

/-- **The class theorem.** Let `A` be symmetric, `A x⋆ = c`, and `g` a weight polynomial with
`g(λᵢ) ≥ 0` at every eigenvalue. If `x` minimises `‖· − x⋆‖²_{g(A)} = quadForm (g(A)) (· − x⋆)`
over `x₀ + K_q(A, r₀)`, then for every residual polynomial `p` (`deg p ≤ q`, `p(0) = 1`) with
`|p(λᵢ)| ≤ M` at every eigenvalue, `‖x − x⋆‖²_{g(A)} ≤ M² ‖x₀ − x⋆‖²_{g(A)}`.
CG is `g = X` (via `cgObjective_eq_add_quadForm_sub`), MINRES `g = X²`, the error-minimising
method `g = 1`. Source: Greenbaum (1997) [`greenbaum97`], §3.1 (CG) and §3.2 (MINRES);
Saad (2003) [`saad03`], Thm 6.29; KRYLOV_DEFINITIONS §3.2.
Atlas: `cg-convergence`, `minres-bound` (the shared step; tags are on the instances).
atlas: affine-krylov-minimiser -/
theorem quadForm_sub_le_of_isAffineMinimiser {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {g : ℝ[X]} (hg : ∀ i, 0 ≤ g.eval (hA.eigenvalues i)) {c x₀ xs x : n → ℝ}
    (hxs : A *ᵥ xs = c) {q : ℕ}
    (hx : IsAffineMinimiser (fun y => quadForm (aeval A g) (y - xs)) x₀
      (krylovSpace A (c - A *ᵥ x₀) q) x)
    {p : ℝ[X]} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1) {M : ℝ}
    (hM : ∀ i, |p.eval (hA.eigenvalues i)| ≤ M) :
    quadForm (aeval A g) (x - xs) ≤ M ^ 2 * quadForm (aeval A g) (x₀ - xs) := by
  have h := hx.le_aeval hxs hp hp0
  simp only [add_sub_cancel_left] at h
  refine h.trans ?_
  refine quadForm_aeval_aeval_mulVec_le hA (S := Set.range hA.eigenvalues) (fun i => ⟨i, rfl⟩)
    ?_ ?_ (x₀ - xs)
  · rintro _ ⟨i, rfl⟩; exact hg i
  · rintro _ ⟨i, rfl⟩; exact hM i

end NLAlib
