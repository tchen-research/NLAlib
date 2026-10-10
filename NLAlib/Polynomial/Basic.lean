import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# Polynomial approximation: definitions

Layer 0 (no matrices). The definitions behind the polynomial facts that Krylov, Lanczos and
conjugate-gradient arguments cite. Everything is a real polynomial `ℝ[X]`; Chebyshev polynomials
are Mathlib's `Polynomial.Chebyshev.T ℝ n` and `Polynomial.Chebyshev.U ℝ n`.

* `chebyshevResidual a b q`: the degree-`q` polynomial
  `T_q((b + a − 2x)/(b − a)) / T_q((b + a)/(b − a))`, equal to `1` at `0` and of smallest maximum
  modulus on `[a, b]` among such polynomials (atlas `chebyshev-minimax`; theorems in
  `NLAlib.Polynomial.Minimax`).
* `chebyshevAmplifier α γ q`: the polynomial `T_q(x/α) / T_q(1 + γ)`, equal to `1` at `α(1 + γ)`
  and at most `2/(1 + √(2γ))^q` in modulus on `[−α, α]` (atlas `chebyshev-amplifier`;
  theorems in `NLAlib.Polynomial.Approximation`).
* `chebyshevZero q k = cos((2k + 1)π/(2q))`, `k < q`: the zeros of `T_q`, the Chebyshev
  interpolation nodes (atlas `chebyshev-interpolation-error`; theorems in
  `NLAlib.Polynomial.Interpolation`).

* `exists_degree_lt_one_sub_eq_X_mul_of_eval_zero_eq_one`,
  `degree_le_and_eval_zero_eq_one_iff`: the residual-polynomial factorisation `1 − p = X s`,
  `deg s < q`, for `deg p ≤ q`, `p(0) = 1` (atlas `residual-polynomial`; the Krylov side is in
  `NLAlib.Krylov.Minimiser`).

Atlas: `chebyshev-minimax`, `chebyshev-amplifier`, `chebyshev-interpolation-error` (definitions),
`residual-polynomial` (the polynomial algebra).
-/

noncomputable section

open Polynomial

namespace NLAlib

/-- The shifted, scaled Chebyshev polynomial normalised to `1` at `0`:
`chebyshevResidual a b q = T_q((b + a − 2 X)/(b − a)) / T_q((b + a)/(b − a))`. For `0 < a < b`
it has the smallest maximum modulus on `[a, b]` among polynomials of degree at most `q` with
value `1` at `0` (the residual polynomial of Chebyshev iteration and the model for CG).
Source: Golub–Meurant (2010) [`gm10`], App.; Atlas: `chebyshev-minimax`.
atlas: inverse-polynomial-approx -/
def chebyshevResidual (a b : ℝ) (q : ℕ) : ℝ[X] :=
  C (1 / (Chebyshev.T ℝ q).eval ((b + a) / (b - a))) *
    (Chebyshev.T ℝ q).comp (C ((b + a) / (b - a)) - C (2 / (b - a)) * X)

/-- The gap-amplifying polynomial `chebyshevAmplifier α γ q = T_q(X/α) / T_q(1 + γ)`: equal to
`1` at `α(1 + γ)`, increasing beyond it, and exponentially small on `[−α, α]`.
Source: Musco–Musco (2015) [`mm15`], Lem. 4–5; Atlas: `chebyshev-amplifier`.
atlas: chebyshev-amplifier -/
def chebyshevAmplifier (α γ : ℝ) (q : ℕ) : ℝ[X] :=
  C (1 / (Chebyshev.T ℝ q).eval (1 + γ)) * (Chebyshev.T ℝ q).comp (C (1 / α) * X)

@[simp] theorem chebyshevResidual_def (a b : ℝ) (q : ℕ) :
    chebyshevResidual a b q =
      C (1 / (Chebyshev.T ℝ q).eval ((b + a) / (b - a))) *
        (Chebyshev.T ℝ q).comp (C ((b + a) / (b - a)) - C (2 / (b - a)) * X) := rfl

/-- The Chebyshev zeros `chebyshevZero q k = cos((2k + 1)π/(2q))`, `k < q`: the `q` roots of
`T_q`, in decreasing order. Source: Trefethen (2019) [`trefethen19`], Ch. 2 ("Chebyshev points
of the first kind"); Mathlib `Polynomial.Chebyshev.roots_T_real`.
Atlas: `chebyshev-interpolation-error`.
atlas: chebyshev-interpolation-error -/
def chebyshevZero (q : ℕ) (k : Fin q) : ℝ :=
  Real.cos ((2 * ((k : ℕ) : ℝ) + 1) * Real.pi / (2 * q))

@[simp] theorem chebyshevAmplifier_def (α γ : ℝ) (q : ℕ) :
    chebyshevAmplifier α γ q =
      C (1 / (Chebyshev.T ℝ q).eval (1 + γ)) * (Chebyshev.T ℝ q).comp (C (1 / α) * X) := rfl

/-- `chebyshevResidual a b q` at `x` is `T_q((b + a − 2x)/(b − a)) / T_q((b + a)/(b − a))`.
Atlas: `chebyshev-minimax`. -/
theorem eval_chebyshevResidual (a b : ℝ) (q : ℕ) (x : ℝ) :
    (chebyshevResidual a b q).eval x =
      (Chebyshev.T ℝ q).eval ((b + a) / (b - a) - 2 / (b - a) * x) /
        (Chebyshev.T ℝ q).eval ((b + a) / (b - a)) := by
  simp only [chebyshevResidual_def, eval_mul, eval_C, eval_comp, eval_sub, eval_X]
  rw [one_div_mul_eq_div]

/-- `chebyshevAmplifier α γ q` at `x` is `T_q(x/α) / T_q(1 + γ)`.
Source: Musco–Musco (2015) [`mm15`], Lem. 4. Atlas: `chebyshev-amplifier`. -/
theorem eval_chebyshevAmplifier (α γ : ℝ) (q : ℕ) (x : ℝ) :
    (chebyshevAmplifier α γ q).eval x =
      (Chebyshev.T ℝ q).eval (x / α) / (Chebyshev.T ℝ q).eval (1 + γ) := by
  simp only [chebyshevAmplifier_def, eval_mul, eval_C, eval_comp, eval_X]
  rw [one_div_mul_eq_div, one_div_mul_eq_div]

/-- The Chebyshev zeros lie in `[−1, 1]`. Atlas: `chebyshev-interpolation-error`. -/
theorem chebyshevZero_mem_Icc (q : ℕ) (k : Fin q) : chebyshevZero q k ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- The Chebyshev zeros are distinct (from Mathlib's `roots_T_real_nodup`).
Atlas: `chebyshev-interpolation-error`. -/
theorem chebyshevZero_injective (q : ℕ) : Function.Injective (chebyshevZero q) := by
  intro i j hij
  have h := (Finset.range q).nodup_map_iff_injOn.mp (Chebyshev.roots_T_real_nodup q)
  exact Fin.ext (h (Finset.mem_coe.mpr (Finset.mem_range.mpr i.2))
    (Finset.mem_coe.mpr (Finset.mem_range.mpr j.2)) hij)

/-! ### Residual polynomials -/

/-- **Residual-polynomial factorisation.** If `deg p ≤ q` and `p(0) = 1`, then `1 − p = X s` for
some `s` with `deg s < q`. This is the algebra behind every residual-polynomial Krylov argument:
`x₀ + s(A) r₀ ∈ x₀ + K_q` has error `p(A)(x₀ − x⋆)`. Source: Saad (2003) [`saad03`], §6.11
(the set `P_q^0`); Trefethen–Bau (1997) [`tb97`], Lect. 35. Promoted from the private CG lemma
`exists_degree_lt_one_sub_eq_X_mul` (atlas `residual-polynomial`, helper). -/
theorem exists_degree_lt_one_sub_eq_X_mul_of_eval_zero_eq_one {p : ℝ[X]} {q : ℕ}
    (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1) : ∃ s : ℝ[X], s.degree < q ∧ 1 - p = X * s := by
  have hdvd : X ∣ 1 - p := by
    rw [X_dvd_iff, coeff_zero_eq_eval_zero, eval_sub, hp0, eval_one, sub_self]
  obtain ⟨s, hs⟩ := hdvd
  refine ⟨s, ?_, hs⟩
  rcases eq_or_ne s 0 with h0 | h0
  · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
  · have hdeg : (1 - p).degree ≤ q :=
      (degree_sub_le _ _).trans (max_le (degree_one_le.trans (by exact_mod_cast Nat.zero_le q)) hp)
    rw [hs, mul_comm, degree_mul_X] at hdeg
    rw [degree_eq_natDegree h0] at hdeg ⊢
    have : s.natDegree + 1 ≤ q := by exact_mod_cast hdeg
    exact_mod_cast (by omega : s.natDegree < q)

/-- **Residual polynomials of degree `≤ q`** are exactly the `1 − X s` with `deg s < q`:
`deg p ≤ q ∧ p(0) = 1 ↔ ∃ s, deg s < q ∧ p = 1 − X s`. Source: Saad (2003) [`saad03`], §6.11
(atlas `residual-polynomial`, helper). -/
theorem degree_le_and_eval_zero_eq_one_iff {p : ℝ[X]} {q : ℕ} :
    p.degree ≤ q ∧ p.eval 0 = 1 ↔ ∃ s : ℝ[X], s.degree < q ∧ p = 1 - X * s := by
  constructor
  · rintro ⟨hp, hp0⟩
    obtain ⟨s, hs, h⟩ := exists_degree_lt_one_sub_eq_X_mul_of_eval_zero_eq_one hp hp0
    exact ⟨s, hs, by rw [← h]; ring⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(degree_sub_le _ _).trans (max_le ?_ ?_), by simp⟩
    · exact degree_one_le.trans (by exact_mod_cast Nat.zero_le q)
    · rw [mul_comm]
      rcases eq_or_ne s 0 with h0 | h0
      · simp [h0]
      · rw [degree_mul_X, degree_eq_natDegree h0] at *
        have : s.natDegree < q := by exact_mod_cast hs
        exact_mod_cast (by omega : s.natDegree + 1 ≤ q)

end NLAlib
