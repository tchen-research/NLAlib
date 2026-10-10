import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import NLAlib.Krylov.Grade
import NLAlib.Krylov.Minimiser
import NLAlib.Matrix.Projections
import NLAlib.Polynomial.Approximation

/-!
# GMRES and MINRES: residual minimisation over the Krylov space

`IsGMRESIterate A c x₀ q x` says that `x ∈ x₀ + K_q(A, r₀)`, `r₀ = c − A x₀`, minimises the
residual `‖c − A y‖²` over `x₀ + K_q(A, r₀)` (an instance of `IsAffineMinimiser`,
`docs/KRYLOV_DEFINITIONS.md` §3.3). MINRES is the same predicate for symmetric `A`.

## Main results

* `isGMRESIterate_iff_forall_dotProduct_eq_zero`: the Petrov–Galerkin characterisation
  `r_q ⟂ A K_q`.
* `exists_isGMRESIterate`: an iterate exists for every `A` (least squares, through
  `orthonormalBasisMatrix`); `IsGMRESIterate.sub_mulVec_eq`: the residual is unique;
  `IsGMRESIterate.eq_of_isUnit`: the iterate is unique for invertible `A`.
* `IsGMRESIterate.exists_sub_mulVec_eq_aeval`, `IsGMRESIterate.le_aeval`,
  `IsGMRESIterate.isLeast_dotProduct_aeval`: `‖r_q‖² = min_{p ∈ 𝒫_q⁰} ‖p(A) r₀‖²`.
* `IsGMRESIterate.le_of_le`: residuals are nonincreasing in `q`.
* `IsGMRESIterate.sub_mulVec_eq_zero_of_krylovGrade_le`: finite termination at the grade.
* MINRES: `IsGMRESIterate.dotProduct_le_sq_mul_of_isHermitian`
  (`‖r_q‖² ≤ M² ‖r₀‖²` for any residual polynomial with `|p(λᵢ)| ≤ M`) and the Chebyshev rate
  `IsGMRESIterate.dotProduct_le_of_eigenvalues_mem_Icc`; `isGMRESIterate_iff_isAffineMinimiser`
  identifies MINRES with the class theorem's weighted minimiser for `g = X²`.
* Real diagonalisable `A = V diag(d) V⁻¹`: `IsGMRESIterate.dotProduct_le_of_eq_mul_diagonal_mul`
  (`‖r_q‖ ≤ ‖V‖ ‖V⁻¹‖ max |p(dᵢ)| ‖r₀‖`).

Source: Saad–Schultz (1986) [`ss86`], §2–3; Saad (2003) [`saad03`], §6.5, Prop 6.32;
Trefethen–Bau (1997) [`tb97`], Lect. 35; Greenbaum (1997) [`greenbaum97`], §3.1; Paige–Saunders
(1975) [`ps75`]. Atlas: `gmres-def`, `minres-bound` (partial), `gmres-diagonalizable` (partial,
real case).
-/

noncomputable section

open scoped Matrix Polynomial
open Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `x` is a GMRES iterate: `x − x₀ ∈ K_q(A, r₀)` (`r₀ = c − A x₀`) and `x` minimises
`‖c − A y‖²` over `x₀ + K_q(A, r₀)`. MINRES is this predicate for symmetric `A`.
Source: Saad–Schultz (1986) [`ss86`], §2; Saad (2003) [`saad03`], §6.5;
KRYLOV_DEFINITIONS §3.3.
atlas: gmres-def -/
def IsGMRESIterate (A : Matrix n n ℝ) (c x₀ : n → ℝ) (q : ℕ) (x : n → ℝ) : Prop :=
  IsAffineMinimiser (fun y => (c - A *ᵥ y) ⬝ᵥ (c - A *ᵥ y)) x₀ (krylovSpace A (c - A *ᵥ x₀) q) x

variable {A : Matrix n n ℝ} {c x₀ x : n → ℝ} {q : ℕ}

/-- **Petrov–Galerkin characterisation.** `x` is a GMRES iterate iff `x − x₀ ∈ K_q(A, r₀)` and
the residual is orthogonal to `A K_q(A, r₀)`. Source: Saad (2003) [`saad03`], Prop 5.3 and
§6.5.1; Trefethen–Bau (1997) [`tb97`], Lect. 35.
atlas: gmres-def (partial) -/
theorem isGMRESIterate_iff_forall_dotProduct_eq_zero :
    IsGMRESIterate A c x₀ q x ↔ x - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) q ∧
      ∀ z ∈ krylovSpace A (c - A *ᵥ x₀) q, (A *ᵥ z) ⬝ᵥ (c - A *ᵥ x) = 0 := by
  set K := krylovSpace A (c - A *ᵥ x₀) q
  constructor
  · rintro ⟨hxK, hmin⟩
    refine ⟨hxK, fun z hz => ?_⟩
    set α := (A *ᵥ z) ⬝ᵥ (c - A *ᵥ x)
    set β := (A *ᵥ z) ⬝ᵥ (A *ᵥ z)
    have hβ : 0 ≤ β := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    set t := α / (β + 1)
    have ht : t * (β + 1) = α := div_mul_cancel₀ _ (by linarith)
    have h := hmin (x - x₀ + t • z) (K.add_mem hxK (K.smul_mem t hz))
    have hr : c - A *ᵥ (x₀ + (x - x₀ + t • z)) = (c - A *ᵥ x) - t • (A *ᵥ z) := by
      rw [show x₀ + (x - x₀ + t • z) = x + t • z by abel, Matrix.mulVec_add,
        Matrix.mulVec_smul]
      abel
    have hexp : ((c - A *ᵥ x) - t • (A *ᵥ z)) ⬝ᵥ ((c - A *ᵥ x) - t • (A *ᵥ z)) =
        (c - A *ᵥ x) ⬝ᵥ (c - A *ᵥ x) - 2 * t * α + t ^ 2 * β := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        α, β, dotProduct_comm (c - A *ᵥ x) (A *ᵥ z)]
      ring
    simp only [hr, hexp] at h
    have h1 : 0 ≤ (β + 1) ^ 2 * (t ^ 2 * β - 2 * t * α) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    have h2 : (β + 1) ^ 2 * (t ^ 2 * β - 2 * t * α) = -(α ^ 2 * (β + 2)) := by
      rw [← ht]; ring
    rw [h2] at h1
    have h3 : α ^ 2 ≤ 0 := by nlinarith [sq_nonneg α]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h3 (sq_nonneg α))
  · rintro ⟨hxK, horth⟩
    refine ⟨hxK, fun y hy => ?_⟩
    have hd : y - (x - x₀) ∈ K := K.sub_mem hy hxK
    have hr : c - A *ᵥ (x₀ + y) = (c - A *ᵥ x) - A *ᵥ (y - (x - x₀)) := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_add]; abel
    have h0 := horth _ hd
    have hAd : 0 ≤ (A *ᵥ (y - (x - x₀))) ⬝ᵥ (A *ᵥ (y - (x - x₀))) :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    show (c - A *ᵥ x) ⬝ᵥ (c - A *ᵥ x) ≤ (c - A *ᵥ (x₀ + y)) ⬝ᵥ (c - A *ᵥ (x₀ + y))
    rw [hr]
    generalize c - A *ᵥ x = r at h0 ⊢
    generalize A *ᵥ (y - (x - x₀)) = v at h0 hAd ⊢
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm r v, h0]
    linarith

/-- **Existence.** For every square `A`, right-hand side `c`, start `x₀` and `q` there is a
GMRES iterate (a least-squares problem over `A K_q`; no hypothesis on `A`).
Source: Saad (2003) [`saad03`], §6.5.1; Saad–Schultz (1986) [`ss86`], §2.
atlas: gmres-def (partial) -/
theorem exists_isGMRESIterate (A : Matrix n n ℝ) (c x₀ : n → ℝ) (q : ℕ) :
    ∃ x, IsGMRESIterate A c x₀ q x := by
  set r₀ := c - A *ᵥ x₀
  set K := krylovSpace A r₀ q
  set W := K.map A.mulVecLin
  set U := orthonormalBasisMatrix W
  have hU : HasOrthonormalCols U := hasOrthonormalCols_orthonormalBasisMatrix W
  have hW : U *ᵥ (Uᵀ *ᵥ r₀) ∈ W := by
    have h : U *ᵥ (Uᵀ *ᵥ r₀) ∈ LinearMap.range U.mulVecLin := ⟨Uᵀ *ᵥ r₀, rfl⟩
    rwa [range_orthonormalBasisMatrix] at h
  obtain ⟨s, hs, hAs⟩ := Submodule.mem_map.1 hW
  rw [Matrix.mulVecLin_apply] at hAs
  refine ⟨x₀ + s, isGMRESIterate_iff_forall_dotProduct_eq_zero.2
    ⟨by simpa using hs, fun z hz => ?_⟩⟩
  have hres : c - A *ᵥ (x₀ + s) = r₀ - U *ᵥ (Uᵀ *ᵥ r₀) := by
    rw [Matrix.mulVec_add, hAs, ← sub_sub]
  have hperp : Uᵀ *ᵥ (r₀ - U *ᵥ (Uᵀ *ᵥ r₀)) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, show Uᵀ * U = 1 from hU, Matrix.one_mulVec,
      sub_self]
  have hAz : A *ᵥ z ∈ LinearMap.range U.mulVecLin := by
    rw [range_orthonormalBasisMatrix]; exact Submodule.mem_map_of_mem hz
  obtain ⟨v, hv⟩ := hAz
  rw [Matrix.mulVecLin_apply] at hv
  rw [hres, ← hv, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hperp,
    zero_dotProduct]

/-- **The GMRES residual is unique**: two GMRES iterates for the same data have the same
residual `c − A x`. Source: Saad (2003) [`saad03`], §6.5.1 (the residual is the orthogonal
projection of `r₀` onto `(A K_q)^⟂`).
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.sub_mulVec_eq {x' : n → ℝ} (hx : IsGMRESIterate A c x₀ q x)
    (hx' : IsGMRESIterate A c x₀ q x') : c - A *ᵥ x = c - A *ᵥ x' := by
  obtain ⟨h1, o1⟩ := isGMRESIterate_iff_forall_dotProduct_eq_zero.1 hx
  obtain ⟨h2, o2⟩ := isGMRESIterate_iff_forall_dotProduct_eq_zero.1 hx'
  have hd : x' - x ∈ krylovSpace A (c - A *ᵥ x₀) q := by
    simpa using Submodule.sub_mem _ h2 h1
  have e : (c - A *ᵥ x) - (c - A *ᵥ x') = A *ᵥ (x' - x) := by
    rw [Matrix.mulVec_sub]; abel
  have h0 : (A *ᵥ (x' - x)) ⬝ᵥ (A *ᵥ (x' - x)) = 0 := by
    calc (A *ᵥ (x' - x)) ⬝ᵥ (A *ᵥ (x' - x)) =
        (A *ᵥ (x' - x)) ⬝ᵥ ((c - A *ᵥ x) - (c - A *ᵥ x')) := by rw [e]
      _ = 0 := by rw [dotProduct_sub, o1 _ hd, o2 _ hd, sub_self]
  rw [← sub_eq_zero, e, dotProduct_self_eq_zero.1 h0]

/-- **The GMRES iterate is unique for invertible `A`.** Source: Saad (2003) [`saad03`], §6.5.1.
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.eq_of_isUnit {x' : n → ℝ} (hA : IsUnit A)
    (hx : IsGMRESIterate A c x₀ q x) (hx' : IsGMRESIterate A c x₀ q x') : x = x' :=
  Matrix.mulVec_injective_iff_isUnit.2 hA (sub_right_injective (hx.sub_mulVec_eq hx'))

/-- **Polynomial form of the residual**: `c − A x = p(A) r₀` for a residual polynomial `p`
(`deg p ≤ q`, `p(0) = 1`). Source: Saad (2003) [`saad03`], §6.5.6; Trefethen–Bau (1997)
[`tb97`], Lect. 35.
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.exists_sub_mulVec_eq_aeval (hx : IsGMRESIterate A c x₀ q x) :
    ∃ p : ℝ[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧ c - A *ᵥ x = aeval A p *ᵥ (c - A *ᵥ x₀) :=
  exists_sub_mulVec_eq_aeval_mulVec_of_sub_mem_krylovSpace hx.1

/-- **GMRES beats every residual polynomial**: `‖r_q‖² ≤ ‖p(A) r₀‖²` for every `p` with
`deg p ≤ q` and `p(0) = 1`. No hypothesis on `A`. Source: Saad (2003) [`saad03`], Prop 6.32
(proof); Trefethen–Bau (1997) [`tb97`], Thm 35.2 (proof).
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.le_aeval (hx : IsGMRESIterate A c x₀ q x) {p : ℝ[X]}
    (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1) :
    (c - A *ᵥ x) ⬝ᵥ (c - A *ᵥ x) ≤
      (aeval A p *ᵥ (c - A *ᵥ x₀)) ⬝ᵥ (aeval A p *ᵥ (c - A *ᵥ x₀)) :=
  IsAffineMinimiser.le_aeval_residual (F := fun r => r ⬝ᵥ r) hx hp hp0

/-- **`‖r_q‖² = min_{p ∈ 𝒫_q⁰} ‖p(A) r₀‖²`**: the squared GMRES residual is the least value of
`‖p(A) r₀‖²` over residual polynomials. Source: Saad (2003) [`saad03`], §6.5.6;
Trefethen–Bau (1997) [`tb97`], Lect. 35 (GMRES as a polynomial approximation problem).
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.isLeast_dotProduct_aeval (hx : IsGMRESIterate A c x₀ q x) :
    IsLeast {v | ∃ p : ℝ[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧
        v = (aeval A p *ᵥ (c - A *ᵥ x₀)) ⬝ᵥ (aeval A p *ᵥ (c - A *ᵥ x₀))}
      ((c - A *ᵥ x) ⬝ᵥ (c - A *ᵥ x)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hp, hp0, hr⟩ := hx.exists_sub_mulVec_eq_aeval
    exact ⟨p, hp, hp0, by rw [hr]⟩
  · rintro _ ⟨p, hp, hp0, rfl⟩
    exact hx.le_aeval hp hp0

/-- **GMRES residuals are nonincreasing**: for `q ≤ q'`, `‖r_{q'}‖² ≤ ‖r_q‖²`.
Source: Saad (2003) [`saad03`], §6.5.6; Saad–Schultz (1986) [`ss86`], §3.
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.le_of_le {q' : ℕ} {x' : n → ℝ} (hx : IsGMRESIterate A c x₀ q x)
    (hx' : IsGMRESIterate A c x₀ q' x') (h : q ≤ q') :
    (c - A *ᵥ x') ⬝ᵥ (c - A *ᵥ x') ≤ (c - A *ᵥ x) ⬝ᵥ (c - A *ᵥ x) :=
  IsAffineMinimiser.le_of_le hx hx' (krylovSpace_mono A _ h)

/-- **Finite termination.** For invertible `A`, a GMRES iterate with `q` at least the grade
`ν = krylovGrade A r₀` solves the system: `c − A x = 0`. Source: Saad (2003) [`saad03`],
Prop 6.10 (no breakdown before the solution) and §6.5.6; Saad–Schultz (1986) [`ss86`], §3.
atlas: gmres-def (partial) -/
theorem IsGMRESIterate.sub_mulVec_eq_zero_of_krylovGrade_le (hA : IsUnit A)
    (hx : IsGMRESIterate A c x₀ q x) (hq : krylovGrade A (c - A *ᵥ x₀) ≤ q) :
    c - A *ᵥ x = 0 := by
  obtain ⟨xs, hxs⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hA c
  have hmem := krylovSpace_mono A _ hq (sub_mem_krylovSpace_krylovGrade hA hxs x₀)
  have h := hx.2 _ hmem
  simp only [add_sub_cancel, hxs, sub_self, dotProduct_zero] at h
  exact dotProduct_self_eq_zero.1
    (le_antisymm h (Finset.sum_nonneg fun i _ => mul_self_nonneg _))

/-! ### MINRES: symmetric `A` -/

/-- **MINRES spectral bound.** For symmetric `A` and every residual polynomial `p`
(`deg p ≤ q`, `p(0) = 1`) with `|p(λᵢ)| ≤ M` at every eigenvalue, the GMRES (= MINRES) residual
satisfies `‖r_q‖² ≤ M² ‖r₀‖²`. Source: Greenbaum (1997) [`greenbaum97`], §3.1; Paige–Saunders
(1975) [`ps75`].
Deviation: no invertibility of `A` and no solution `x⋆` needed (the bound is on residuals).
atlas: minres-bound (partial) -/
theorem IsGMRESIterate.dotProduct_le_sq_mul_of_isHermitian (hA : A.IsHermitian)
    (hx : IsGMRESIterate A c x₀ q x) {p : ℝ[X]} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1)
    {M : ℝ} (hM : ∀ i, |p.eval (hA.eigenvalues i)| ≤ M) :
    (c - A *ᵥ x) ⬝ᵥ (c - A *ᵥ x) ≤ M ^ 2 * ((c - A *ᵥ x₀) ⬝ᵥ (c - A *ᵥ x₀)) := by
  refine (hx.le_aeval hp hp0).trans ?_
  refine dotProduct_aeval_mulVec_self_le hA (S := Set.range hA.eigenvalues)
    (fun i => ⟨i, rfl⟩) ?_ _
  rintro _ ⟨i, rfl⟩
  exact hM i

/-- **MINRES, definite case (Chebyshev rate).** If `A` is symmetric with every eigenvalue in
`[a, b]`, `0 < a < b`, then `‖r_q‖ ≤ 2 ((√b − √a)/(√b + √a))^q ‖r₀‖` (squared form).
Source: Greenbaum (1997) [`greenbaum97`], §3.1; Liesen–Strakoš (2013) [`ls13`], §5.6.
atlas: minres-bound (partial) -/
theorem IsGMRESIterate.dotProduct_le_of_eigenvalues_mem_Icc (hA : A.IsHermitian) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b)
    (hx : IsGMRESIterate A c x₀ q x) :
    (c - A *ᵥ x) ⬝ᵥ (c - A *ᵥ x) ≤
      (2 * ((√b - √a) / (√b + √a)) ^ q) ^ 2 * ((c - A *ᵥ x₀) ⬝ᵥ (c - A *ᵥ x₀)) :=
  hx.dotProduct_le_sq_mul_of_isHermitian hA (degree_chebyshevResidual_le a b q)
    (eval_chebyshevResidual_zero ha hab)
    fun i => abs_eval_chebyshevResidual_le_two_mul_pow q ha hab (hspec i)

/-- **MINRES is the class theorem's minimiser with weight `g = X²`.** For symmetric `A` and
`A x⋆ = c`, `x` is a GMRES iterate iff it minimises `‖· − x⋆‖²_{A²} = quadForm (A²) (· − x⋆)`
over `x₀ + K_q(A, r₀)`; so `quadForm_sub_le_of_isAffineMinimiser` with `g = X²` applies.
Source: Greenbaum (1997) [`greenbaum97`], §3.2; KRYLOV_DEFINITIONS §3.2.
Atlas: `minres-bound` (helper). -/
theorem isGMRESIterate_iff_isAffineMinimiser (hA : A.IsHermitian) {xs : n → ℝ}
    (hxs : A *ᵥ xs = c) :
    IsGMRESIterate A c x₀ q x ↔
      IsAffineMinimiser (fun y => quadForm (aeval A (X ^ 2 : ℝ[X])) (y - xs)) x₀
        (krylovSpace A (c - A *ᵥ x₀) q) x := by
  have hAs : Aᵀ = A := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA
  have hE : (fun y => (c - A *ᵥ y) ⬝ᵥ (c - A *ᵥ y)) =
      fun y => quadForm (aeval A (X ^ 2 : ℝ[X])) (y - xs) := by
    funext y
    have hr : c - A *ᵥ y = -(A *ᵥ (y - xs)) := by
      rw [Matrix.mulVec_sub, hxs]; abel
    rw [hr, neg_dotProduct, dotProduct_neg, neg_neg, quadForm, map_pow, aeval_X, sq,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hAs,
      dotProduct_comm]
  rw [IsGMRESIterate, hE]

/-! ### Real diagonalisable `A` -/

/-- `‖M v‖² ≤ ‖M‖₂² ‖v‖²` in dot-product form. -/
private lemma mulVec_dotProduct_self_le_specNorm_sq (M : Matrix n n ℝ) (v : n → ℝ) :
    (M *ᵥ v) ⬝ᵥ (M *ᵥ v) ≤ specNorm M ^ 2 * (v ⬝ᵥ v) := by
  have h := sum_sq_mulVec_le_specNorm_sq M v
  simpa [dotProduct, sq] using h

/-- **GMRES bound for real diagonalisable `A`.** If `A = V diag(d) W` with `V W = 1` (so
`W = V⁻¹` and the `dᵢ` are the eigenvalues), then for every residual polynomial `p` with
`|p(dᵢ)| ≤ M`, `‖r_q‖ ≤ ‖V‖₂ ‖V⁻¹‖₂ M ‖r₀‖` (squared form).
Source: Saad (2003) [`saad03`], Prop 6.32; Trefethen–Bau (1997) [`tb97`], Thm 35.2;
Saad–Schultz (1986) [`ss86`], §3.4.
Deviation: real eigenvalues and a real eigenvector matrix only (the printed statement allows a
complex diagonalisation, which is not available over `ℝ`).
atlas: gmres-diagonalizable (partial) -/
theorem IsGMRESIterate.dotProduct_le_of_eq_mul_diagonal_mul {V W : Matrix n n ℝ}
    {d : n → ℝ} (hVW : V * W = 1) (hAd : A = V * Matrix.diagonal d * W)
    (hx : IsGMRESIterate A c x₀ q x) {p : ℝ[X]} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1)
    {M : ℝ} (hM : ∀ i, |p.eval (d i)| ≤ M) :
    (c - A *ᵥ x) ⬝ᵥ (c - A *ᵥ x) ≤
      (specNorm V * specNorm W * M) ^ 2 * ((c - A *ᵥ x₀) ⬝ᵥ (c - A *ᵥ x₀)) := by
  have hWV : W * V = 1 := mul_eq_one_comm.1 hVW
  have hpow : ∀ j : ℕ, A ^ j = V * Matrix.diagonal d ^ j * W := by
    intro j
    induction j with
    | zero => simp [hVW]
    | succ j ih =>
      rw [pow_succ, ih, hAd, pow_succ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc W V, hWV, Matrix.one_mul]
  have hpA : aeval A p = V * Matrix.diagonal (fun i => p.eval (d i)) * W := by
    rw [aeval_eq_sum_range, ← aeval_diagonal d p, aeval_eq_sum_range, Matrix.mul_sum,
      Matrix.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hpow, Matrix.mul_smul, Matrix.smul_mul]
  set r₀ := c - A *ᵥ x₀
  set D := Matrix.diagonal fun i => p.eval (d i)
  have hD : (D *ᵥ (W *ᵥ r₀)) ⬝ᵥ (D *ᵥ (W *ᵥ r₀)) ≤ M ^ 2 * ((W *ᵥ r₀) ⬝ᵥ (W *ᵥ r₀)) := by
    simp only [D, Matrix.mulVec_diagonal, dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := hM i
    have hsq : p.eval (d i) ^ 2 ≤ M ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (p.eval (d i))]) ((le_abs_self _).trans h)
    nlinarith [mul_self_nonneg ((W *ᵥ r₀) i)]
  refine (hx.le_aeval hp hp0).trans ?_
  rw [hpA, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  calc (V *ᵥ (D *ᵥ (W *ᵥ r₀))) ⬝ᵥ (V *ᵥ (D *ᵥ (W *ᵥ r₀)))
      ≤ specNorm V ^ 2 * ((D *ᵥ (W *ᵥ r₀)) ⬝ᵥ (D *ᵥ (W *ᵥ r₀))) :=
        mulVec_dotProduct_self_le_specNorm_sq V _
    _ ≤ specNorm V ^ 2 * (M ^ 2 * (specNorm W ^ 2 * (r₀ ⬝ᵥ r₀))) := by
        gcongr
        exact hD.trans (by gcongr; exact mulVec_dotProduct_self_le_specNorm_sq W r₀)
    _ = (specNorm V * specNorm W * M) ^ 2 * (r₀ ⬝ᵥ r₀) := by ring

end NLAlib
