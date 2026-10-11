import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.GeomSum
import NLAlib.Krylov.Polynomial
import NLAlib.Matrix.PolynomialCalculus
import NLAlib.Polynomial.Approximation

/-!
# Fixed-polynomial Krylov methods: Richardson and Chebyshev iteration

A *polynomial method* with iteration polynomial `s` produces `x₀ + s(A) r₀`, `r₀ = c − A x₀`;
its residual polynomial is `1 − X s` (`docs/KRYLOV_DEFINITIONS.md` §3.6). For these methods
the polynomial *is* the definition and the recurrence is a theorem.

* `polyIterate A c x₀ s`, with `polyIterate_sub` (error `(1 − X s)(A)(x₀ − x⋆)`),
  `sub_mulVec_polyIterate` (residual `(1 − X s)(A) r₀`), `polyIterate_sub_mem_krylovSpace`, and
  the spectral bounds `quadForm_polyIterate_sub_le` (any weight `g(A)`, `g ≥ 0`) and
  `dotProduct_self_sub_mulVec_polyIterate_le` (residual norm).
* `richardsonIterate ω A c x₀ q` (residual polynomial `(1 − ωX)^q`) with the recurrence
  `richardsonIterate_succ` (`x_{q+1} = x_q + ω (c − A x_q)`) and the contraction bounds
  `quadForm_richardsonIterate_sub_le`, `dotProduct_self_sub_mulVec_richardsonIterate_le` and
  the optimal step `quadForm_richardsonIterate_sub_le_of_optimal`.
* `chebyshevIterate a b A c x₀ q` (residual polynomial `chebyshevResidual a b q`) with the
  rates `quadForm_chebyshevIterate_sub_le`, `dotProduct_self_sub_mulVec_chebyshevIterate_le`,
  and the recurrence of Saad Alg. 12.1: `chebyshevIterate_zero`, `chebyshevIterate_one`
  (`x_1 = x₀ + r₀/θ`) and the three-term step `chebyshevIterate_add_two`.

Source: Saad (2003) [`saad03`], §4.2 (Richardson), §12.3 (Chebyshev, Alg. 12.1); Greenbaum
(1997) [`greenbaum97`], §2.1. Atlas: `richardson-iteration` (unpreconditioned case),
`chebyshev-iteration` (residual polynomial, rates and the three-term recurrence).
-/

noncomputable section

open scoped Matrix Polynomial
open Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Polynomial methods -/

/-- The polynomial method with iteration polynomial `s`: `x₀ + s(A) r₀`, `r₀ = c − A x₀`. Its
residual polynomial is `1 − X s`. Source: Saad (2003) [`saad03`], §12.1 (polynomial
iterations); KRYLOV_DEFINITIONS §3.6.
atlas: polynomial-method-def -/
def polyIterate (A : Matrix n n ℝ) (c x₀ : n → ℝ) (s : ℝ[X]) : n → ℝ :=
  x₀ + aeval A s *ᵥ (c - A *ᵥ x₀)

/-- The residual of a polynomial method is `(1 − X s)(A) r₀`. Source: Saad (2003) [`saad03`],
§12.1.
atlas: polynomial-method-def -/
theorem sub_mulVec_polyIterate (A : Matrix n n ℝ) (c x₀ : n → ℝ) (s : ℝ[X]) :
    c - A *ᵥ polyIterate A c x₀ s = aeval A (1 - X * s) *ᵥ (c - A *ᵥ x₀) := by
  rw [polyIterate, map_sub, map_one, map_mul, aeval_X, Matrix.sub_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_add]
  abel

/-- The error of a polynomial method is `(1 − X s)(A)(x₀ − x⋆)` when `A x⋆ = c`.
Source: Saad (2003) [`saad03`], §12.1.
atlas: polynomial-method-def -/
theorem polyIterate_sub {A : Matrix n n ℝ} {c xs : n → ℝ} (hxs : A *ᵥ xs = c) (x₀ : n → ℝ)
    (s : ℝ[X]) : polyIterate A c x₀ s - xs = aeval A (1 - X * s) *ᵥ (x₀ - xs) := by
  have hr : c - A *ᵥ x₀ = -(A *ᵥ (x₀ - xs)) := by rw [Matrix.mulVec_sub, hxs]; abel
  rw [polyIterate, mul_comm X s, map_sub, map_one, map_mul, aeval_X, Matrix.sub_mulVec,
    Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hr, Matrix.mulVec_neg]
  abel

/-- A polynomial method with `deg s < q` stays in the affine Krylov space `x₀ + K_q(A, r₀)`.
Source: Saad (2003) [`saad03`], §12.1. -/
theorem polyIterate_sub_mem_krylovSpace (A : Matrix n n ℝ) (c x₀ : n → ℝ) {s : ℝ[X]} {q : ℕ}
    (hs : s.degree < q) : polyIterate A c x₀ s - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) q :=
  (mem_krylovSpace_iff_degree _ _ _ _).2 ⟨s, hs, by rw [polyIterate, add_sub_cancel_left]⟩

/-- **Error bound for a polynomial method, weighted norm.** For symmetric `A` with spectrum in
`S`, a weight `g ≥ 0` on `S` and `|1 − x s(x)| ≤ M` on `S`,
`‖x − x⋆‖²_{g(A)} ≤ M² ‖x₀ − x⋆‖²_{g(A)}`. Source: Saad (2003) [`saad03`], §12.1;
Greenbaum (1997) [`greenbaum97`], §2.1. -/
theorem quadForm_polyIterate_sub_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {g s : ℝ[X]}
    {S : Set ℝ} {M : ℝ} (hspec : ∀ i, hA.eigenvalues i ∈ S) (hg : ∀ x ∈ S, 0 ≤ g.eval x)
    (hM : ∀ x ∈ S, |(1 - X * s).eval x| ≤ M) {c xs : n → ℝ} (hxs : A *ᵥ xs = c)
    (x₀ : n → ℝ) :
    quadForm (aeval A g) (polyIterate A c x₀ s - xs) ≤ M ^ 2 * quadForm (aeval A g) (x₀ - xs) := by
  rw [polyIterate_sub hxs]
  exact quadForm_aeval_aeval_mulVec_le hA hspec hg hM _

/-- **Residual bound for a polynomial method.** For symmetric `A` with spectrum in `S` and
`|1 − x s(x)| ≤ M` on `S`, `‖c − A x‖² ≤ M² ‖r₀‖²`. No solution is needed.
Source: Saad (2003) [`saad03`], §12.1. -/
theorem dotProduct_self_sub_mulVec_polyIterate_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {s : ℝ[X]} {S : Set ℝ} {M : ℝ} (hspec : ∀ i, hA.eigenvalues i ∈ S)
    (hM : ∀ x ∈ S, |(1 - X * s).eval x| ≤ M) (c x₀ : n → ℝ) :
    (c - A *ᵥ polyIterate A c x₀ s) ⬝ᵥ (c - A *ᵥ polyIterate A c x₀ s) ≤
      M ^ 2 * ((c - A *ᵥ x₀) ⬝ᵥ (c - A *ᵥ x₀)) := by
  rw [sub_mulVec_polyIterate]
  exact dotProduct_aeval_mulVec_self_le hA hspec hM _

/-! ### Richardson iteration -/

/-- The Richardson iterate with step `ω`: `x_q = x₀ + ω ∑_{j<q} (I − ωA)^j r₀`, the polynomial
method with residual polynomial `(1 − ωX)^q`; it satisfies `x_{q+1} = x_q + ω (c − A x_q)`
(`richardsonIterate_succ`). Source: Saad (2003) [`saad03`], §4.2; Greenbaum (1997)
[`greenbaum97`], §2.1. Deviation: unpreconditioned (`P = I`).
atlas: richardson-iteration (partial) -/
def richardsonIterate (ω : ℝ) (A : Matrix n n ℝ) (c x₀ : n → ℝ) (q : ℕ) : n → ℝ :=
  polyIterate A c x₀ (C ω * ∑ j ∈ Finset.range q, (1 - C ω * X) ^ j)

/-- The residual polynomial of Richardson's method is `(1 − ωX)^q`. -/
private lemma one_sub_X_mul_richardson (ω : ℝ) (q : ℕ) :
    1 - X * (C ω * ∑ j ∈ Finset.range q, (1 - C ω * X) ^ j) = (1 - C ω * X) ^ q := by
  linear_combination geom_sum_mul (1 - C ω * X) q

/-- **Richardson recurrence.** `x_{q+1} = x_q + ω (c − A x_q)`, `x_0 = x₀`.
Source: Saad (2003) [`saad03`], §4.2. -/
theorem richardsonIterate_succ (ω : ℝ) (A : Matrix n n ℝ) (c x₀ : n → ℝ) (q : ℕ) :
    richardsonIterate ω A c x₀ (q + 1) =
      richardsonIterate ω A c x₀ q + ω • (c - A *ᵥ richardsonIterate ω A c x₀ q) := by
  have hr := sub_mulVec_polyIterate A c x₀ (C ω * ∑ j ∈ Finset.range q, (1 - C ω * X) ^ j)
  rw [one_sub_X_mul_richardson] at hr
  simp only [richardsonIterate]
  rw [hr, polyIterate, polyIterate]
  simp only [Finset.sum_range_succ, mul_add, map_add, map_mul, aeval_C, Matrix.add_mulVec,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec,
    add_assoc]

/-- `richardsonIterate` at `q = 0` is the starting point. -/
@[simp] theorem richardsonIterate_zero (ω : ℝ) (A : Matrix n n ℝ) (c x₀ : n → ℝ) :
    richardsonIterate ω A c x₀ 0 = x₀ := by
  simp [richardsonIterate, polyIterate]

/-- For `ω ≥ 0` and `x ∈ [a, b]`, `|(1 − ωx)^q| ≤ max(|1 − ωa|, |1 − ωb|)^q`. -/
private lemma abs_eval_richardson_le {ω a b x : ℝ} (hω : 0 ≤ ω) (hx : x ∈ Set.Icc a b) (q : ℕ) :
    |((1 - C ω * X) ^ q : ℝ[X]).eval x| ≤ max |1 - ω * a| |1 - ω * b| ^ q := by
  simp only [eval_pow, eval_sub, eval_one, eval_mul, eval_C, eval_X, abs_pow]
  have h1 : 1 - ω * b ≤ 1 - ω * x := by nlinarith [mul_le_mul_of_nonneg_left hx.2 hω]
  have h2 : 1 - ω * x ≤ 1 - ω * a := by nlinarith [mul_le_mul_of_nonneg_left hx.1 hω]
  exact pow_le_pow_left₀ (abs_nonneg _)
    ((abs_le_max_abs_abs h1 h2).trans (max_comm _ _).le) q

/-- **Richardson contraction, weighted norm.** For symmetric `A` with spectrum in `[a, b]`,
step `ω ≥ 0`, `A x⋆ = c` and a weight `g ≥ 0` on `[a, b]`,
`‖x_q − x⋆‖²_{g(A)} ≤ ρ^{2q} ‖x₀ − x⋆‖²_{g(A)}` with `ρ = max(|1 − ωa|, |1 − ωb|)`. With
`g = X` (`0 ≤ a`) this is the `A`-norm bound of the atlas, with `g = 1` the Euclidean error.
Source: Greenbaum (1997) [`greenbaum97`], §2.1; Saad (2003) [`saad03`], §4.2.
Deviation: unpreconditioned (`P = I`), squared norms.
atlas: richardson-iteration (partial) -/
theorem quadForm_richardsonIterate_sub_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {a b ω : ℝ}
    (hω : 0 ≤ ω) (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b) {g : ℝ[X]}
    (hg : ∀ x ∈ Set.Icc a b, 0 ≤ g.eval x) {c xs : n → ℝ} (hxs : A *ᵥ xs = c) (x₀ : n → ℝ)
    (q : ℕ) :
    quadForm (aeval A g) (richardsonIterate ω A c x₀ q - xs) ≤
      (max |1 - ω * a| |1 - ω * b| ^ q) ^ 2 * quadForm (aeval A g) (x₀ - xs) := by
  refine quadForm_polyIterate_sub_le hA hspec hg (fun x hx => ?_) hxs x₀
  rw [one_sub_X_mul_richardson]
  exact abs_eval_richardson_le hω hx q

/-- **Richardson contraction, residual norm.** For symmetric `A` with spectrum in `[a, b]` and
step `ω ≥ 0`, `‖c − A x_q‖² ≤ ρ^{2q} ‖r₀‖²`, `ρ = max(|1 − ωa|, |1 − ωb|)`.
Source: Saad (2003) [`saad03`], §4.2. Deviation: unpreconditioned (`P = I`), squared norms.
atlas: richardson-iteration (partial) -/
theorem dotProduct_self_sub_mulVec_richardsonIterate_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b ω : ℝ} (hω : 0 ≤ ω) (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b) (c x₀ : n → ℝ)
    (q : ℕ) :
    (c - A *ᵥ richardsonIterate ω A c x₀ q) ⬝ᵥ (c - A *ᵥ richardsonIterate ω A c x₀ q) ≤
      (max |1 - ω * a| |1 - ω * b| ^ q) ^ 2 * ((c - A *ᵥ x₀) ⬝ᵥ (c - A *ᵥ x₀)) := by
  refine dotProduct_self_sub_mulVec_polyIterate_le hA hspec (fun x hx => ?_) c x₀
  rw [one_sub_X_mul_richardson]
  exact abs_eval_richardson_le hω hx q

/-- **Richardson with the optimal step** `ω = 2/(a + b)`: for symmetric positive definite `A`
with spectrum in `[a, b]`, `0 < a ≤ b`, `‖x_q − x⋆‖²_A ≤ ((b − a)/(b + a))^{2q} ‖x₀ − x⋆‖²_A`.
Source: Saad (2003) [`saad03`], §4.2.1; Greenbaum (1997) [`greenbaum97`], §2.1.
Deviation: unpreconditioned (`P = I`), squared norms.
atlas: richardson-iteration (partial) -/
theorem quadForm_richardsonIterate_sub_le_of_optimal {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b)
    {c xs : n → ℝ} (hxs : A *ᵥ xs = c) (x₀ : n → ℝ) (q : ℕ) :
    quadForm A (richardsonIterate (2 / (a + b)) A c x₀ q - xs) ≤
      (((b - a) / (b + a)) ^ q) ^ 2 * quadForm A (x₀ - xs) := by
  have hab' : 0 < a + b := by linarith
  have hne : a + b ≠ 0 := hab'.ne'
  have hne' : b + a ≠ 0 := by linarith
  have h := quadForm_richardsonIterate_sub_le hA (ω := 2 / (a + b)) (by positivity) hspec (g := X)
    (fun x hx => by simpa using ha.le.trans hx.1) hxs x₀ q
  rw [aeval_X] at h
  have h1 : 1 - 2 / (a + b) * a = (b - a) / (b + a) := by field_simp; ring
  have h2 : 1 - 2 / (a + b) * b = -((b - a) / (b + a)) := by field_simp; ring
  have hnn : 0 ≤ (b - a) / (b + a) := div_nonneg (by linarith) (by linarith)
  rwa [h1, h2, abs_neg, max_self, abs_of_nonneg hnn] at h

/-! ### Chebyshev iteration -/

/-- The Chebyshev iterate for spectrum in `[a, b]`: the polynomial method whose residual
polynomial is `chebyshevResidual a b q = T_q((b + a − 2X)/(b − a)) / T_q((b + a)/(b − a))`,
i.e. iteration polynomial `(1 − chebyshevResidual a b q) /ₘ X`. Source: Saad (2003)
[`saad03`], §12.3; Golub–Varga (1961) [`gv61`]. Deviation: defined by its polynomial; the
recurrence of Saad Alg. 12.1 is the theorem `chebyshevIterate_add_two`.
atlas: chebyshev-iteration (partial) -/
def chebyshevIterate (a b : ℝ) (A : Matrix n n ℝ) (c x₀ : n → ℝ) (q : ℕ) : n → ℝ :=
  polyIterate A c x₀ ((1 - chebyshevResidual a b q) /ₘ X)

/-- For a polynomial with `p(0) = 1`, `1 − X ((1 − p) /ₘ X) = p`. -/
private lemma one_sub_X_mul_divByMonic {p : ℝ[X]} (hp0 : p.eval 0 = 1) :
    1 - X * ((1 - p) /ₘ X) = p := by
  have hdvd : X ∣ 1 - p := by
    rw [X_dvd_iff, coeff_zero_eq_eval_zero, eval_sub, hp0, eval_one, sub_self]
  have h := modByMonic_add_div (1 - p) X
  rw [(modByMonic_eq_zero_iff_dvd monic_X).2 hdvd, zero_add] at h
  rw [h]; ring

/-- The Chebyshev iterate lies in `x₀ + K_q(A, r₀)` (its iteration polynomial has degree
`< q`). Source: Saad (2003) [`saad03`], §12.3. -/
theorem chebyshevIterate_sub_mem_krylovSpace {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (A : Matrix n n ℝ) (c x₀ : n → ℝ) (q : ℕ) :
    chebyshevIterate a b A c x₀ q - x₀ ∈ krylovSpace A (c - A *ᵥ x₀) q := by
  obtain ⟨s, hs, h⟩ := exists_degree_lt_one_sub_eq_X_mul_of_eval_zero_eq_one
    (degree_chebyshevResidual_le a b q) (eval_chebyshevResidual_zero ha hab)
  have hs' : (1 - chebyshevResidual a b q) /ₘ X = s := by
    rw [h, mul_divByMonic_cancel_left _ monic_X]
  rw [chebyshevIterate, hs']
  exact polyIterate_sub_mem_krylovSpace A c x₀ hs

/-- **Chebyshev iteration, `A`-norm rate.** For symmetric `A` with spectrum in `[a, b]`,
`0 < a < b`, and `A x⋆ = c`,
`‖x_q − x⋆‖²_A ≤ (2((√b − √a)/(√b + √a))^q)² ‖x₀ − x⋆‖²_A`.
Source: Saad (2003) [`saad03`], §12.3; Golub–Varga (1961) [`gv61`]. Deviation: squared norms;
the iterate is defined by its residual polynomial (no recurrence).
atlas: chebyshev-iteration (partial) -/
theorem quadForm_chebyshevIterate_sub_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b) {c xs : n → ℝ}
    (hxs : A *ᵥ xs = c) (x₀ : n → ℝ) (q : ℕ) :
    quadForm A (chebyshevIterate a b A c x₀ q - xs) ≤
      (2 * ((√b - √a) / (√b + √a)) ^ q) ^ 2 * quadForm A (x₀ - xs) := by
  have h := quadForm_polyIterate_sub_le hA hspec (g := X)
    (fun x hx => by simpa using ha.le.trans hx.1)
    (s := (1 - chebyshevResidual a b q) /ₘ X) (fun x hx => by
      rw [one_sub_X_mul_divByMonic (eval_chebyshevResidual_zero ha hab)]
      exact abs_eval_chebyshevResidual_le_two_mul_pow q ha hab hx) hxs x₀
  rwa [aeval_X] at h

/-- **Chebyshev iteration, residual rate.** For symmetric `A` with spectrum in `[a, b]`,
`0 < a < b`, `‖c − A x_q‖² ≤ (2((√b − √a)/(√b + √a))^q)² ‖r₀‖²`.
Source: Saad (2003) [`saad03`], §12.3. Deviation: squared norms.
atlas: chebyshev-iteration (partial) -/
theorem dotProduct_self_sub_mulVec_chebyshevIterate_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b)
    (c x₀ : n → ℝ) (q : ℕ) :
    (c - A *ᵥ chebyshevIterate a b A c x₀ q) ⬝ᵥ (c - A *ᵥ chebyshevIterate a b A c x₀ q) ≤
      (2 * ((√b - √a) / (√b + √a)) ^ q) ^ 2 * ((c - A *ᵥ x₀) ⬝ᵥ (c - A *ᵥ x₀)) :=
  dotProduct_self_sub_mulVec_polyIterate_le hA hspec (fun x hx => by
    rw [one_sub_X_mul_divByMonic (eval_chebyshevResidual_zero ha hab)]
    exact abs_eval_chebyshevResidual_le_two_mul_pow q ha hab hx) c x₀

/-! ### The Chebyshev three-term recurrence -/

/-- `T_q((b + a)/(b − a)) ≥ 1 > 0` for `0 < a < b`. -/
private lemma one_le_eval_T_chebyshevCenter {a b : ℝ} (ha : 0 < a) (hab : a < b) (q : ℤ) :
    1 ≤ (Chebyshev.T ℝ q).eval ((b + a) / (b - a)) :=
  Chebyshev.one_le_eval_T_real q (by rw [one_le_div (by linarith)]; linarith)

/-- The polynomial identity behind the Chebyshev recurrence: with `τ_k = T_k(σ)`,
`σ = (b + a)/(b − a)`, `θ = (b + a)/2` and `s_k = (1 − R_k) /ₘ X` the iteration polynomials,
`τ_{q+2} s_{q+2} = (4/(b − a)) τ_{q+1} (θ s_{q+1} + R_{q+1}) − τ_q s_q`. -/
private lemma chebyshev_iterationPoly_add_two {a b : ℝ} (ha : 0 < a) (hab : a < b) (q : ℕ) :
    C ((Chebyshev.T ℝ ((q + 2 : ℕ) : ℤ)).eval ((b + a) / (b - a))) *
        ((1 - chebyshevResidual a b (q + 2)) /ₘ X) =
      C (4 / (b - a) * (Chebyshev.T ℝ ((q + 1 : ℕ) : ℤ)).eval ((b + a) / (b - a))) *
          (C ((b + a) / 2) * ((1 - chebyshevResidual a b (q + 1)) /ₘ X) +
            chebyshevResidual a b (q + 1)) -
        C ((Chebyshev.T ℝ (q : ℤ)).eval ((b + a) / (b - a))) *
          ((1 - chebyshevResidual a b q) /ₘ X) := by
  set σ := (b + a) / (b - a)
  have hS : ∀ k : ℕ, X * ((1 - chebyshevResidual a b k) /ₘ X) = 1 - chebyshevResidual a b k :=
    fun k => by
      have h := one_sub_X_mul_divByMonic (eval_chebyshevResidual_zero (q := k) ha hab)
      linear_combination -h
  have hτ : ∀ k : ℕ, (Chebyshev.T ℝ (k : ℤ)).eval σ ≠ 0 := fun k =>
    (zero_lt_one.trans_le (one_le_eval_T_chebyshevCenter ha hab k)).ne'
  have hR : ∀ (k : ℕ) (t : ℝ), (Chebyshev.T ℝ (k : ℤ)).eval σ * (chebyshevResidual a b k).eval t =
      (Chebyshev.T ℝ (k : ℤ)).eval (σ - 2 / (b - a) * t) := fun k t => by
    rw [eval_chebyshevResidual]; exact mul_div_cancel₀ _ (hτ k)
  have hT : ∀ u : ℝ, (Chebyshev.T ℝ ((q + 2 : ℕ) : ℤ)).eval u =
      2 * u * (Chebyshev.T ℝ ((q + 1 : ℕ) : ℤ)).eval u - (Chebyshev.T ℝ (q : ℤ)).eval u := by
    intro u
    rw [show ((q + 2 : ℕ) : ℤ) = (q : ℤ) + 2 by push_cast; ring, Chebyshev.T_add_two,
      show ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 by push_cast; ring]
    simp
  refine mul_left_cancel₀ X_ne_zero (Polynomial.funext fun t => ?_)
  have h2 := congrArg (eval t) (hS (q + 2))
  have h1 := congrArg (eval t) (hS (q + 1))
  have h0 := congrArg (eval t) (hS q)
  simp only [eval_mul, eval_X, eval_sub, eval_one] at h2 h1 h0
  simp only [eval_mul, eval_X, eval_sub, eval_add, eval_C]
  have hσ : 4 / (b - a) * ((b + a) / 2) = 2 * σ := by
    simp only [σ]; field_simp; ring
  linear_combination
    (Chebyshev.T ℝ ((q + 2 : ℕ) : ℤ)).eval σ * h2 -
      4 / (b - a) * (Chebyshev.T ℝ ((q + 1 : ℕ) : ℤ)).eval σ * ((b + a) / 2) * h1 +
      (Chebyshev.T ℝ (q : ℤ)).eval σ * h0 - hR (q + 2) t +
      (4 / (b - a) * ((b + a) / 2) - 4 / (b - a) * t) * hR (q + 1) t - hR q t +
      hT σ - hT (σ - 2 / (b - a) * t) +
      ((Chebyshev.T ℝ ((q + 1 : ℕ) : ℤ)).eval σ -
        (Chebyshev.T ℝ ((q + 1 : ℕ) : ℤ)).eval (σ - 2 / (b - a) * t)) * hσ

/-- The Chebyshev recurrence at the centre `σ = (b + a)/(b − a)`:
`τ_{q+2} = (4/(b − a)) τ_{q+1} (b + a)/2 − τ_q` (that is, `2σ τ_{q+1} − τ_q`). -/
private lemma eval_T_add_two_center {a b : ℝ} (hab : a < b) (q : ℕ) :
    (Chebyshev.T ℝ ((q + 2 : ℕ) : ℤ)).eval ((b + a) / (b - a)) =
      4 / (b - a) * (Chebyshev.T ℝ ((q + 1 : ℕ) : ℤ)).eval ((b + a) / (b - a)) * ((b + a) / 2) -
        (Chebyshev.T ℝ (q : ℤ)).eval ((b + a) / (b - a)) := by
  have hba : b - a ≠ 0 := by linarith
  have e2 : ((q + 2 : ℕ) : ℤ) = (q : ℤ) + 2 := by push_cast; ring
  have e1 : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; ring
  rw [e2, e1, Chebyshev.T_add_two]
  simp only [eval_sub, eval_mul, eval_X, eval_ofNat]
  field_simp
  ring

/-- `chebyshevIterate` at `q = 0` is the starting point. Source: Saad (2003) [`saad03`],
Alg. 12.1. Atlas: `chebyshev-iteration`. -/
@[simp] theorem chebyshevIterate_zero (a b : ℝ) (A : Matrix n n ℝ) (c x₀ : n → ℝ) :
    chebyshevIterate a b A c x₀ 0 = x₀ := by
  simp [chebyshevIterate, polyIterate, chebyshevResidual]

/-- **First Chebyshev step**: `x_1 = x₀ + r₀/θ`, `θ = (b + a)/2`, for `0 < a < b`.
Source: Saad (2003) [`saad03`], Alg. 12.1 (`d_0 = r_0/θ`).
atlas: chebyshev-iteration (partial) -/
theorem chebyshevIterate_one {a b : ℝ} (ha : 0 < a) (hab : a < b) (A : Matrix n n ℝ)
    (c x₀ : n → ℝ) :
    chebyshevIterate a b A c x₀ 1 = x₀ + (2 / (b + a)) • (c - A *ᵥ x₀) := by
  have hba : b - a ≠ 0 := by linarith
  have hab' : b + a ≠ 0 := by linarith
  have hs : (1 - chebyshevResidual a b 1) /ₘ X = C (2 / (b + a)) := by
    have h : 1 - chebyshevResidual a b 1 = X * C (2 / (b + a)) := by
      refine Polynomial.funext fun t => ?_
      simp only [eval_sub, eval_one, eval_chebyshevResidual, Nat.cast_one, Chebyshev.T_one,
        eval_X, eval_mul, eval_C]
      field_simp
      ring
    rw [h, mul_divByMonic_cancel_left _ monic_X]
  rw [chebyshevIterate, polyIterate, hs, aeval_C, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mulVec, Matrix.one_mulVec]

/-- **The Chebyshev three-term recurrence** (Saad Alg. 12.1 in three-term form): for `0 < a < b`,
with `τ_k = T_k(σ)`, `σ = (b + a)/(b − a)`, `θ = (b + a)/2`, `δ = (b − a)/2` and
`r_k = c − A x_k`,
`τ_{q+2} x_{q+2} = (2τ_{q+1}/δ)(θ x_{q+1} + r_{q+1}) − τ_q x_q`, i.e.
`x_{q+2} = τ_{q+2}⁻¹ ((4τ_{q+1}/(b − a)) (θ x_{q+1} + r_{q+1}) − τ_q x_q)`.
No hypothesis on `A` and no solution is needed (a polynomial identity applied to `r₀`).
Saad's two-term form with `ρ_k = τ_k/τ_{k+1}` and `d_k = x_{k+1} − x_k`
(`d_k = ρ_kρ_{k−1} d_{k−1} + (2ρ_k/δ) r_k`) is a rearrangement of this identity together with
`τ_{q+2} = 2σ τ_{q+1} − τ_q`. Proof: `Polynomial.funext` after cancelling `X`, using
`Chebyshev.T_add_two` at `σ − 2t/(b − a)` and at `σ`.
Source: Saad (2003) [`saad03`], §12.3, Alg. 12.1; Golub–Varga (1961) [`gv61`].
atlas: chebyshev-iteration (partial) -/
theorem chebyshevIterate_add_two {a b : ℝ} (ha : 0 < a) (hab : a < b) (A : Matrix n n ℝ)
    (c x₀ : n → ℝ) (q : ℕ) :
    chebyshevIterate a b A c x₀ (q + 2) =
      ((Chebyshev.T ℝ ((q + 2 : ℕ) : ℤ)).eval ((b + a) / (b - a)))⁻¹ •
        ((4 / (b - a) * (Chebyshev.T ℝ ((q + 1 : ℕ) : ℤ)).eval ((b + a) / (b - a))) •
            (((b + a) / 2) • chebyshevIterate a b A c x₀ (q + 1) +
              (c - A *ᵥ chebyshevIterate a b A c x₀ (q + 1))) -
          (Chebyshev.T ℝ (q : ℤ)).eval ((b + a) / (b - a)) • chebyshevIterate a b A c x₀ q) := by
  have hpoly := congrArg (fun p => aeval A p *ᵥ (c - A *ᵥ x₀))
    (chebyshev_iterationPoly_add_two ha hab q)
  simp only [map_sub, map_mul, map_add, aeval_C, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mul, Matrix.one_mul, Matrix.sub_mulVec, Matrix.add_mulVec,
    Matrix.smul_mulVec] at hpoly
  have hr : c - A *ᵥ chebyshevIterate a b A c x₀ (q + 1) =
      aeval A (chebyshevResidual a b (q + 1)) *ᵥ (c - A *ᵥ x₀) := by
    rw [chebyshevIterate, sub_mulVec_polyIterate,
      one_sub_X_mul_divByMonic (eval_chebyshevResidual_zero ha hab)]
  set σ := (b + a) / (b - a)
  set τ₂ := (Chebyshev.T ℝ ((q + 2 : ℕ) : ℤ)).eval σ
  set τ₁ := (Chebyshev.T ℝ ((q + 1 : ℕ) : ℤ)).eval σ
  set τ₀ := (Chebyshev.T ℝ (q : ℤ)).eval σ
  have hτ₂ : τ₂ ≠ 0 := (zero_lt_one.trans_le (one_le_eval_T_chebyshevCenter ha hab _)).ne'
  have hrec : τ₂ = 4 / (b - a) * τ₁ * ((b + a) / 2) - τ₀ := eval_T_add_two_center hab q
  rw [eq_inv_smul_iff₀ hτ₂, hr]
  simp only [chebyshevIterate, polyIterate]
  rw [smul_add, hpoly, hrec]
  module

end NLAlib
