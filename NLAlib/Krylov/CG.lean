import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import NLAlib.Krylov.Grade
import NLAlib.Krylov.Minimiser
import NLAlib.Matrix.PolynomialCalculus
import NLAlib.Polynomial.Approximation

/-!
# Conjugate gradients, variational form

For a symmetric positive (semi)definite `A`, the `q`-th conjugate-gradient iterate for `A x = c`
started at `x₀` is the minimiser of the quadratic `φ(x) = ½ xᵀ A x − cᵀ x` over the affine Krylov
space `x₀ + K_q(A, r₀)`, `r₀ = c − A x₀`; equivalently it minimises the `A`-norm error
`‖x − x⋆‖_A` there. This file works with that variational characterisation (`IsCGIterate`); the
Hestenes–Stiefel recurrence that computes it is not formalised here. `IsCGIterate` is the
instance `IsAffineMinimiser (cgObjective A c) x₀ K_q` of the generic minimiser of
`NLAlib.Krylov.Minimiser`, and its bounds are corollaries of the class theorem
`quadForm_sub_le_of_isAffineMinimiser` with weight `g = X`.

## Main results

* `NLAlib.cgObjective`, `NLAlib.IsCGIterate`: the objective and the iterate predicate;
  `NLAlib.isCGIterate_iff` unfolds it, `NLAlib.isCGIterate_iff_isAffineMinimiser_quadForm_sub`
  identifies it with `A`-norm error minimisation.
* `NLAlib.cgObjective_add`, `NLAlib.cgObjective_eq_add_quadForm_sub`: `φ(z) = φ(x⋆) + ½‖z − x⋆‖_A²`.
* `NLAlib.isCGIterate_of_forall_dotProduct_eq_zero`: Galerkin orthogonality implies minimality.
* `NLAlib.exists_isCGIterate`: existence for positive definite `A`.
* `NLAlib.eq_of_isCGIterate_of_krylovGrade_le`: finite termination at the grade of `r₀`.
* `NLAlib.quadForm_sub_le_of_isCGIterate_of_poly`: the polynomial bound
  `‖x_q − x⋆‖_A² ≤ (max_i |p(λᵢ)|)² ‖x₀ − x⋆‖_A²` for every `p` with `deg p ≤ q`, `p(0) = 1`.
* `NLAlib.quadForm_sub_le_of_isCGIterate`: the condition-number bound
  `‖x_q − x⋆‖_A ≤ 2((√b − √a)/(√b + √a))^q ‖x₀ − x⋆‖_A` for spectrum in `[a, b]`, `0 < a < b`,
  and `NLAlib.quadForm_sub_le_of_isCGIterate_of_le` for `0 < a ≤ b`.

Source: Trefethen–Bau (1997) [`tb97`], Lecture 38 (Thms 38.1, 38.3, 38.5); Golub–Meurant (2010)
[`gm10`], Ch. 8; Saad (2003), Thm 6.29. Atlas: `cg-convergence`; finite termination uses
`krylov-grade`, the bounds use `residual-polynomial` through `NLAlib.Krylov.Minimiser`.
-/

noncomputable section

open scoped Matrix Polynomial
open Matrix Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The conjugate-gradient objective `φ(x) = ½ xᵀ A x − cᵀ x`. Its minimiser over `ℝⁿ` (for
positive definite `A`) solves `A x = c`. Source: Trefethen–Bau (1997) [`tb97`], eq. (38.6).
Atlas: `cg-convergence`.
atlas: cg-convergence -/
def cgObjective (A : Matrix n n ℝ) (c x : n → ℝ) : ℝ := quadForm A x / 2 - c ⬝ᵥ x

/-- `x` is a `q`-th conjugate-gradient iterate for `A x = c` from `x₀`: `x − x₀` lies in
`K_q(A, c − A x₀)` and `x` minimises `cgObjective A c` over `x₀ + K_q(A, c − A x₀)`, i.e.
`IsAffineMinimiser (cgObjective A c) x₀ (krylovSpace A (c − A x₀) q) x`.
Source: Trefethen–Bau (1997) [`tb97`], Thm 38.2 (variational form). Atlas: `cg-convergence`.
Deviation: a predicate rather than the output of the Hestenes–Stiefel recurrence.
atlas: cg-convergence -/
def IsCGIterate (A : Matrix n n ℝ) (c x₀ : n → ℝ) (q : ℕ) (x : n → ℝ) : Prop :=
  IsAffineMinimiser (cgObjective A c) x₀ (krylovSpace A (c - A *ᵥ x₀) q) x

/-- Unfolding `IsCGIterate`: `x − x₀ ∈ K_q` and `φ(x) ≤ φ(x₀ + y)` for every `y ∈ K_q`.
Source: Trefethen–Bau (1997) [`tb97`], Thm 38.2. -/
theorem isCGIterate_iff {A : Matrix n n ℝ} {c x₀ : n → ℝ} {q : ℕ} {x : n → ℝ} :
    IsCGIterate A c x₀ q x ↔
      x - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) q ∧
        ∀ y ∈ krylovSpace A (c - A *ᵥ x₀) q, cgObjective A c x ≤ cgObjective A c (x₀ + y) :=
  Iff.rfl

omit [DecidableEq n] in
/-- For a real symmetric matrix, `uᵀ A d = dᵀ A u`. -/
private lemma dotProduct_mulVec_comm_of_isHermitian {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (u d : n → ℝ) : u ⬝ᵥ (A *ᵥ d) = d ⬝ᵥ (A *ᵥ u) := by
  have hT : Aᵀ = A := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hA
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]

omit [DecidableEq n] in
/-- Expansion of the CG objective along a direction: for symmetric `A`,
`φ(u + d) = φ(u) + dᵀ (A u − c) + ½ dᵀ A d`. Source: Trefethen–Bau (1997) [`tb97`], proof of
Thm 38.2. Atlas: `cg-convergence`. -/
theorem cgObjective_add {A : Matrix n n ℝ} (hA : A.IsHermitian) (c u d : n → ℝ) :
    cgObjective A c (u + d) =
      cgObjective A c u + d ⬝ᵥ (A *ᵥ u - c) + quadForm A d / 2 := by
  have h := dotProduct_mulVec_comm_of_isHermitian hA u d
  simp only [cgObjective, quadForm, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    dotProduct_sub]
  rw [dotProduct_comm d c]
  linarith

omit [DecidableEq n] in
/-- The CG objective measures the `A`-norm error: if `A x⋆ = c` then
`φ(z) = φ(x⋆) + ½ ‖z − x⋆‖_A²`. Source: Trefethen–Bau (1997) [`tb97`], eq. (38.7).
Atlas: `cg-convergence`. -/
theorem cgObjective_eq_add_quadForm_sub {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {c xs : n → ℝ} (hxs : A *ᵥ xs = c) (z : n → ℝ) :
    cgObjective A c z = cgObjective A c xs + quadForm A (z - xs) / 2 := by
  have h := cgObjective_add hA c xs (z - xs)
  rw [add_sub_cancel, hxs, sub_self, dotProduct_zero, add_zero] at h
  exact h

/-- **CG minimises the `A`-norm error.** For symmetric `A` with `A x⋆ = c`, `x` is a `q`-th CG
iterate iff it minimises `‖· − x⋆‖_A² = quadForm A (· − x⋆)` over `x₀ + K_q(A, r₀)`.
Source: Trefethen–Bau (1997) [`tb97`], Thm 38.2. -/
theorem isCGIterate_iff_isAffineMinimiser_quadForm_sub {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {c x₀ xs x : n → ℝ} (hxs : A *ᵥ xs = c) {q : ℕ} :
    IsCGIterate A c x₀ q x ↔
      IsAffineMinimiser (fun y => quadForm A (y - xs)) x₀ (krylovSpace A (c - A *ᵥ x₀) q) x := by
  rw [isCGIterate_iff, IsAffineMinimiser]
  refine and_congr_right fun _ => forall₂_congr fun y _ => ?_
  rw [cgObjective_eq_add_quadForm_sub hA hxs x, cgObjective_eq_add_quadForm_sub hA hxs (x₀ + y)]
  constructor <;> intro h <;> linarith

/-- **Galerkin orthogonality implies the CG minimality.** For symmetric positive semidefinite
`A`, if `x − x₀ ∈ K_q` and the residual `c − A x` is orthogonal to `K_q`, then `x` is a `q`-th CG
iterate. Source: Trefethen–Bau (1997) [`tb97`], Thm 38.1–38.2; Saad (2003), Prop. 5.2
(Petrov–Galerkin with `L = K`). Atlas: `cg-convergence`. -/
theorem isCGIterate_of_forall_dotProduct_eq_zero {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hpsd : ∀ i, 0 ≤ hA.eigenvalues i) {c x₀ x : n → ℝ} {q : ℕ}
    (hx : x - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) q)
    (horth : ∀ z ∈ krylovSpace A (c - A *ᵥ x₀) q, z ⬝ᵥ (c - A *ᵥ x) = 0) :
    IsCGIterate A c x₀ q x := by
  refine ⟨hx, fun y hy => ?_⟩
  have hd : y - (x - x₀) ∈ krylovSpace A (c - A *ᵥ x₀) q := Submodule.sub_mem _ hy hx
  have h := cgObjective_add hA c x (y - (x - x₀))
  have he : x + (y - (x - x₀)) = x₀ + y := by abel
  rw [he] at h
  have h0 : (y - (x - x₀)) ⬝ᵥ (A *ᵥ x - c) = 0 := by
    rw [← neg_sub c, dotProduct_neg, horth _ hd, neg_zero]
  have hq := quadForm_nonneg_of_eigenvalues_nonneg hA hpsd (y - (x - x₀))
  linarith

/-- **Existence of the CG iterate.** For positive definite `A`, every `c`, `x₀` and `q`, there
is a `q`-th CG iterate. It is the Galerkin solution: the bilinear form `(y, z) ↦ zᵀ A y` on `K_q`
is nondegenerate, hence `y ↦ (z ↦ zᵀ A y)` is a bijection `K_q → K_q*`.
Source: Trefethen–Bau (1997) [`tb97`], Thm 38.2 (uniqueness and existence of the minimiser).
Atlas: `cg-convergence`.
atlas: cg-convergence -/
theorem exists_isCGIterate {A : Matrix n n ℝ} (hA : A.PosDef) (c x₀ : n → ℝ) (q : ℕ) :
    ∃ x, IsCGIterate A c x₀ q x := by
  have hH : A.IsHermitian := hA.isHermitian
  have hpos : ∀ i, 0 < hH.eigenvalues i := hA.eigenvalues_pos
  set r₀ := c - A *ᵥ x₀
  set K := krylovSpace A r₀ q
  let T : K →ₗ[ℝ] Module.Dual ℝ K :=
    LinearMap.mk₂ ℝ (fun y z => (z : n → ℝ) ⬝ᵥ (A *ᵥ (y : n → ℝ)))
      (fun y₁ y₂ z => by simp [Matrix.mulVec_add, dotProduct_add])
      (fun a y z => by simp [Matrix.mulVec_smul, dotProduct_smul])
      (fun y z₁ z₂ => by simp [add_dotProduct])
      (fun a y z => by simp [smul_dotProduct])
  let φ : Module.Dual ℝ K :=
    { toFun := fun z => (z : n → ℝ) ⬝ᵥ r₀
      map_add' := fun z₁ z₂ => by simp [add_dotProduct]
      map_smul' := fun a z => by simp [smul_dotProduct] }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : quadForm A (y : n → ℝ) = 0 := by
      have := LinearMap.congr_fun hy y
      simpa [T, quadForm] using this
    rw [quadForm_eq_sum_eigenvalues hH] at h0
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (hpos i).le (sq_nonneg _)).1 h0
    have hyy : (y : n → ℝ) ⬝ᵥ (y : n → ℝ) = 0 := by
      rw [← sum_sq_eigenvectorBasis_dotProduct hH]
      refine Finset.sum_eq_zero fun i hi => ?_
      rcases mul_eq_zero.1 (hall i hi) with h | h
      · exact absurd h (hpos i).ne'
      · exact h
    exact Subtype.ext (dotProduct_self_eq_zero.1 hyy)
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨y, hy⟩ := hsurj φ
  refine ⟨x₀ + (y : n → ℝ),
    isCGIterate_of_forall_dotProduct_eq_zero hH (fun i => (hpos i).le) ?_ ?_⟩
  · simp
  · intro z hz
    have h := LinearMap.congr_fun hy ⟨z, hz⟩
    simp only [T, φ, LinearMap.mk₂_apply, LinearMap.coe_mk, AddHom.coe_mk] at h
    rw [Matrix.mulVec_add, dotProduct_sub, dotProduct_add, h]
    simp only [r₀, dotProduct_sub]
    ring

/-- **CG error bound, polynomial form.** Let `A` be symmetric positive semidefinite,
`A x⋆ = c`, and `x` a `q`-th CG iterate from `x₀`. For every polynomial `p` with `deg p ≤ q`,
`p(0) = 1` and `|p(λᵢ)| ≤ M` at every eigenvalue,
`‖x − x⋆‖_A² ≤ M² ‖x₀ − x⋆‖_A²` (with `‖v‖_A² = quadForm A v`).
Source: Trefethen–Bau (1997) [`tb97`], Thm 38.3 (and the inequality (38.10)); Saad (2003),
Thm 6.29. Atlas: `cg-convergence`; uses `polynomial-spectral-bound`, `krylov-subspace`,
`residual-polynomial` (the case `g = X` of `quadForm_sub_le_of_isAffineMinimiser`).
atlas: cg-convergence -/
theorem quadForm_sub_le_of_isCGIterate_of_poly {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (hpsd : ∀ i, 0 ≤ hA.eigenvalues i) {c x₀ xs x : n → ℝ} (hxs : A *ᵥ xs = c) {q : ℕ}
    (hx : IsCGIterate A c x₀ q x) {p : ℝ[X]} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1) {M : ℝ}
    (hM : ∀ i, |p.eval (hA.eigenvalues i)| ≤ M) :
    quadForm A (x - xs) ≤ M ^ 2 * quadForm A (x₀ - xs) := by
  have hx' := (isCGIterate_iff_isAffineMinimiser_quadForm_sub hA hxs).1 hx
  have h := quadForm_sub_le_of_isAffineMinimiser hA (g := X) (by simpa using hpsd) hxs
    (by simpa only [aeval_X] using hx') hp hp0 hM
  simpa only [aeval_X] using h

/-- **CG convergence, condition-number form.** Let `A` be symmetric with every eigenvalue in
`[a, b]`, `0 < a < b`, `A x⋆ = c`, and `x` a `q`-th CG iterate from `x₀`. Then
`‖x − x⋆‖_A² ≤ (2 ((√b − √a)/(√b + √a))^q)² ‖x₀ − x⋆‖_A²`; with `κ = b/a`,
`(√b − √a)/(√b + √a) = (√κ − 1)/(√κ + 1)`.
Source: Trefethen–Bau (1997) [`tb97`], Thm 38.5; Golub–Meurant (2010) [`gm10`], Ch. 8.
Atlas: `cg-convergence`; uses `chebyshev-minimax`, `polynomial-spectral-bound`,
`krylov-subspace`. Deviation: squared `A`-norms (the source states the unsquared form).
atlas: cg-convergence -/
theorem quadForm_sub_le_of_isCGIterate {A : Matrix n n ℝ} (hA : A.IsHermitian) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b)
    {c x₀ xs x : n → ℝ} (hxs : A *ᵥ xs = c) {q : ℕ} (hx : IsCGIterate A c x₀ q x) :
    quadForm A (x - xs) ≤ (2 * ((√b - √a) / (√b + √a)) ^ q) ^ 2 * quadForm A (x₀ - xs) :=
  quadForm_sub_le_of_isCGIterate_of_poly hA (fun i => ha.le.trans (hspec i).1) hxs hx
    (degree_chebyshevResidual_le a b q) (eval_chebyshevResidual_zero ha hab)
    (fun i => abs_eval_chebyshevResidual_le_two_mul_pow q ha hab (hspec i))

/-- **CG convergence, condition-number form including `a = b`.** As
`quadForm_sub_le_of_isCGIterate` but for `0 < a ≤ b`. When `a = b` (`A = aI`), CG is exact
after one step and the bound reads `0` for `q ≥ 1` and `4 ‖x₀ − x⋆‖_A²` for `q = 0`.
Source: Trefethen–Bau (1997) [`tb97`], Thm 38.5. Atlas: `cg-convergence`. -/
theorem quadForm_sub_le_of_isCGIterate_of_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b)
    {c x₀ xs x : n → ℝ} (hxs : A *ᵥ xs = c) {q : ℕ} (hx : IsCGIterate A c x₀ q x) :
    quadForm A (x - xs) ≤ (2 * ((√b - √a) / (√b + √a)) ^ q) ^ 2 * quadForm A (x₀ - xs) := by
  rcases hab.lt_or_eq with hlt | rfl
  · exact quadForm_sub_le_of_isCGIterate hA ha hlt hspec hxs hx
  have hpsd : ∀ i, 0 ≤ hA.eigenvalues i := fun i => ha.le.trans (hspec i).1
  have hq0 := quadForm_nonneg_of_eigenvalues_nonneg hA hpsd (x₀ - xs)
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · -- `K_0 = 0`, so `x = x₀`
    have hx0 : x = x₀ := by
      have h := hx.1
      rw [krylovSpace_zero, Submodule.mem_bot] at h
      exact sub_eq_zero.1 h
    subst hx0
    nlinarith
  · -- the degree-one polynomial `1 − X/a` vanishes on the spectrum `{a}`
    have hp : (1 - C (1 / a) * X : ℝ[X]).degree ≤ q := by
      refine (degree_sub_le _ _).trans (max_le ?_ ?_)
      · exact degree_one_le.trans (by exact_mod_cast Nat.zero_le q)
      · exact (degree_C_mul_X_le _).trans (by exact_mod_cast hq)
    have h := quadForm_sub_le_of_isCGIterate_of_poly hA hpsd hxs hx hp (by simp) (M := 0)
      (fun i => by
        have hi : hA.eigenvalues i = a := le_antisymm (hspec i).2 (hspec i).1
        simp [hi, ha.ne'])
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at h
    exact h.trans (by positivity)

/-- **Finite termination of CG.** For positive definite `A` with `A x⋆ = c`, once `q` reaches the
grade `ν(A, r₀)` of the initial residual, every `q`-th CG iterate is the solution `x⋆`. The
proof: `x⋆ − x₀ ∈ K_ν(A, r₀)` (`sub_mem_krylovSpace_krylovGrade`), so the `A`-norm error of the
minimiser is `0`. Source: Saad (2003) [`saad03`], Prop 6.3 and §6.7; Trefethen–Bau (1997)
[`tb97`], Thm 38.1 (CG converges in at most `n` steps). Uses atlas `krylov-grade`.
atlas: cg-finite-termination -/
theorem eq_of_isCGIterate_of_krylovGrade_le {A : Matrix n n ℝ} (hA : A.PosDef)
    {c x₀ xs x : n → ℝ} (hxs : A *ᵥ xs = c) {q : ℕ}
    (hq : krylovGrade A (c - A *ᵥ x₀) ≤ q) (hx : IsCGIterate A c x₀ q x) : x = xs := by
  have hx' := (isCGIterate_iff_isAffineMinimiser_quadForm_sub hA.isHermitian hxs).1 hx
  have hmem : xs - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) q := by
    rw [krylovSpace_eq_of_krylovGrade_le _ _ hq]
    exact sub_mem_krylovSpace_krylovGrade hA.isUnit hxs x₀
  have h := hx'.le_of_sub_mem hmem
  simp only [sub_self, quadForm_zero_right] at h
  by_contra hne
  have hpos := hA.dotProduct_mulVec_pos (x := x - xs) (sub_ne_zero.2 hne)
  simp only [star_trivial] at hpos
  exact absurd h (not_le.2 hpos)

end NLAlib
