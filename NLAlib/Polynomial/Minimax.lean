import NLAlib.Polynomial.Basic
import NLAlib.ForMathlib.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# Extremal properties of Chebyshev polynomials: minimax and monic minimality

Layer 0 (no matrices).

* `abs_eval_le_abs_eval_T_real_of_forall_abs_le_one` and
  `abs_eval_le_mul_abs_eval_T_real_of_forall_abs_le`: a polynomial of degree at most `q` bounded
  by `M` on `[−1, 1]` is bounded by `M |T_q(x)|` outside it (atlas `chebyshev-extremal`).
* The `chebyshevResidual` API: value `1` at `0`, degree at most `q`, and modulus at most
  `1 / T_q((b + a)/(b − a))` on `[a, b]`.
* `inv_eval_T_real_le_of_forall_abs_eval_le`, `isLeast_chebyshev_minimax`: among polynomials of
  degree at most `q` with value `1` at `0`, the smallest possible maximum modulus on `[a, b]`
  (`0 < a < b`) is `1 / T_q((b + a)/(b − a))`, attained by `chebyshevResidual a b q`
  (atlas `chebyshev-minimax`).
* `inv_two_pow_le_of_monic_of_forall_abs_eval_le`: a monic polynomial of degree `q` has maximum
  modulus at least `1 / 2^(q−1)` on `[−1, 1]`, attained by `2^(1−q) T_q`; packaged as
  `isLeast_chebyshev_monic_minimax` (atlas `chebyshev-monic-minimal`).

Atlas: `chebyshev-extremal`, `chebyshev-minimax`, `chebyshev-monic-minimal`.
-/

noncomputable section

open Polynomial Polynomial.Chebyshev

namespace NLAlib

/-- The case `1 ≤ x` of `abs_eval_le_abs_eval_T_real_of_forall_abs_le_one`. -/
private lemma abs_eval_le_eval_T_real_of_one_le {q : ℕ} {P : ℝ[X]} {x : ℝ}
    (hP : P.degree ≤ q) (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) (hx : 1 ≤ x) :
    |P.eval x| ≤ (T ℝ q).eval x := by
  have h1 := eval_iterate_derivative_le_of_forall_abs_le_one (k := 0) hx hP hb
  have h2 := eval_iterate_derivative_le_of_forall_abs_le_one (k := 0) (P := -P) hx
    (by rwa [degree_neg]) (fun y hy => by simpa using hb y hy)
  simp only [Function.iterate_zero, id_eq, eval_neg] at h1 h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- Chebyshev's extremal growth bound: if `P` has degree at most `q` and `|P| ≤ 1` on `[−1, 1]`,
then `|P(x)| ≤ |T_q(x)|` for every `|x| ≥ 1`.
Source: Rivlin, *Chebyshev Polynomials* (1990), Thm 2.20 (case `k = 0`); Mathlib
`Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one` covers `x ≥ 1`;
Atlas: `chebyshev-extremal`.
atlas: chebyshev-extremal -/
theorem abs_eval_le_abs_eval_T_real_of_forall_abs_le_one {q : ℕ} {P : ℝ[X]} {x : ℝ}
    (hP : P.degree ≤ q) (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1) (hx : 1 ≤ |x|) :
    |P.eval x| ≤ |(T ℝ q).eval x| := by
  rcases le_or_gt 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at hx
    exact (abs_eval_le_eval_T_real_of_one_le hP hb hx).trans (le_abs_self _)
  · rw [abs_of_neg h0] at hx
    have hQ : (P.comp (-X)).degree ≤ q := by
      refine (degree_le_natDegree).trans ?_
      have : (P.comp (-X)).natDegree ≤ q := by
        refine (natDegree_comp_le).trans ?_
        rw [natDegree_neg, natDegree_X, mul_one]
        exact natDegree_le_iff_degree_le.mpr hP
      exact_mod_cast this
    have hQb : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |(P.comp (-X)).eval y| ≤ 1 := by
      intro y hy
      simp only [eval_comp, eval_neg, eval_X]
      exact hb (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have := abs_eval_le_eval_T_real_of_one_le hQ hQb hx
    simp only [eval_comp, eval_neg, eval_X, neg_neg] at this
    refine this.trans ?_
    rw [← neg_neg x, T_eval_neg, neg_neg]
    refine (le_abs_self _).trans (le_of_eq ?_)
    rw [abs_mul, abs_unit_intCast, one_mul]

/-- Scaled form of Chebyshev's extremal growth bound: if `P` has degree at most `q` and
`|P| ≤ M` on `[−1, 1]`, then `|P(x)| ≤ M |T_q(x)|` for every `|x| ≥ 1`. No sign condition on `M`
(for `M ≤ 0` the hypothesis forces `P = 0`).
Source: Rivlin, *Chebyshev Polynomials* (1990), Thm 2.20 (case `k = 0`);
Atlas: `chebyshev-extremal`.
atlas: chebyshev-extremal -/
theorem abs_eval_le_mul_abs_eval_T_real_of_forall_abs_le {q : ℕ} {P : ℝ[X]} {M x : ℝ}
    (hP : P.degree ≤ q) (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ M) (hx : 1 ≤ |x|) :
    |P.eval x| ≤ M * |(T ℝ q).eval x| := by
  rcases le_or_gt M 0 with hM | hM
  · have h0 : 0 ≤ M := (abs_nonneg _).trans (hb 0 ⟨by norm_num, by norm_num⟩)
    rw [eq_zero_of_forall_abs_eval_le_of_nonpos hM hb]
    simpa using mul_nonneg h0 (abs_nonneg ((T ℝ q).eval x))
  · have hQ : (C M⁻¹ * P).degree ≤ q := (degree_C_mul_le _ _).trans hP
    have hQb : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |(C M⁻¹ * P).eval y| ≤ 1 := by
      intro y hy
      rw [eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hM), inv_mul_le_iff₀ hM, mul_one]
      exact hb y hy
    have := abs_eval_le_abs_eval_T_real_of_forall_abs_le_one hQ hQb hx
    rwa [eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hM), inv_mul_le_iff₀ hM] at this

/-! ### The shifted Chebyshev residual -/

/-- For `0 ≤ a < b` the point `(b + a)/(b − a)` is at least `1`. -/
private lemma one_le_div_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : 1 ≤ (b + a) / (b - a) := by
  rw [one_le_div (by linarith)]
  linarith

/-- For `0 < a < b`, `T_q((b + a)/(b − a)) ≥ 1`; in particular it is positive. -/
private lemma one_le_eval_T_real_div_sub {a b : ℝ} {q : ℕ} (ha : 0 < a) (hab : a < b) :
    1 ≤ (T ℝ q).eval ((b + a) / (b - a)) :=
  one_le_eval_T_real _ (one_le_div_sub ha.le hab)

/-- The residual polynomial `chebyshevResidual a b q` has value `1` at `0`.
Source: Golub–Meurant (2010) [`gm10`], App.; Atlas: `chebyshev-minimax`.
atlas: chebyshev-minimax -/
theorem eval_chebyshevResidual_zero {a b : ℝ} {q : ℕ} (ha : 0 < a) (hab : a < b) :
    (chebyshevResidual a b q).eval 0 = 1 := by
  have h := one_le_eval_T_real_div_sub (q := q) ha hab
  simp only [chebyshevResidual_def, eval_mul, eval_C, eval_comp, eval_sub, eval_X, mul_zero,
    sub_zero]
  field_simp

/-- The residual polynomial `chebyshevResidual a b q` has degree at most `q`.
Source: Golub–Meurant (2010) [`gm10`], App.; Atlas: `chebyshev-minimax`.
atlas: chebyshev-minimax -/
theorem degree_chebyshevResidual_le (a b : ℝ) (q : ℕ) :
    (chebyshevResidual a b q).degree ≤ q := by
  rw [chebyshevResidual_def]
  refine (degree_C_mul_le _ _).trans (degree_le_natDegree.trans ?_)
  have : ((T ℝ q).comp (C ((b + a) / (b - a)) - C (2 / (b - a)) * X)).natDegree ≤ q := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_T, Int.natAbs_natCast]
    calc q * (C ((b + a) / (b - a)) - C (2 / (b - a)) * X).natDegree ≤ q * 1 := by
          gcongr
          refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
          exact (natDegree_C_mul_le _ _).trans (by simp)
      _ = q := mul_one q
  exact_mod_cast this

/-- On `[a, b]` with `0 < a < b`, the residual polynomial is at most
`1 / T_q((b + a)/(b − a))` in modulus.
Source: Golub–Meurant (2010) [`gm10`], App.; Atlas: `chebyshev-minimax`.
atlas: chebyshev-minimax -/
theorem abs_eval_chebyshevResidual_le {a b x : ℝ} {q : ℕ} (ha : 0 < a) (hab : a < b)
    (hx : x ∈ Set.Icc a b) :
    |(chebyshevResidual a b q).eval x| ≤ 1 / (T ℝ q).eval ((b + a) / (b - a)) := by
  have h := one_le_eval_T_real_div_sub (q := q) ha hab
  have hba : 0 < b - a := by linarith
  have hy : |(b + a) / (b - a) - 2 / (b - a) * x| ≤ 1 := by
    have he : (b + a) / (b - a) - 2 / (b - a) * x = (b + a - 2 * x) / (b - a) := by
      field_simp
    rw [he, abs_le, le_div_iff₀ hba, div_le_iff₀ hba]
    constructor <;> linarith [hx.1, hx.2]
  simp only [chebyshevResidual_def, eval_mul, eval_C, eval_comp, eval_sub, eval_X]
  rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (T ℝ q).eval ((b + a) / (b - a)))]
  exact mul_le_of_le_one_right (by positivity) (abs_eval_T_real_le_one _ hy)

/-! ### The minimax property -/

/-- The minimax lower bound: if `p` has degree at most `q`, `p(0) = 1` and `|p| ≤ M` on `[a, b]`
with `0 < a < b`, then `M ≥ 1 / T_q((b + a)/(b − a))`.
Source: Golub–Meurant (2010) [`gm10`], App.; Trefethen–Bau (1997), Thm 38.5 (there in the
condition-number form); Atlas: `chebyshev-minimax`.
atlas: chebyshev-minimax -/
theorem inv_eval_T_real_le_of_forall_abs_eval_le {a b M : ℝ} {q : ℕ} {p : ℝ[X]} (ha : 0 < a)
    (hab : a < b) (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1)
    (hb : ∀ x ∈ Set.Icc a b, |p.eval x| ≤ M) :
    1 / (T ℝ q).eval ((b + a) / (b - a)) ≤ M := by
  have hba : 0 < b - a := by linarith
  have hs := one_le_div_sub ha.le hab
  have hT := one_le_eval_T_real_div_sub (q := q) ha hab
  set L : ℝ[X] := C ((b + a) / 2) - C ((b - a) / 2) * X with hL
  have hLe : ∀ t, L.eval t = (b + a) / 2 - (b - a) / 2 * t := fun t => by
    simp [hL]
  have hP : (p.comp L).degree ≤ q := by
    refine degree_le_natDegree.trans ?_
    have : (p.comp L).natDegree ≤ q := by
      refine natDegree_comp_le.trans ?_
      calc p.natDegree * L.natDegree ≤ q * 1 := by
            gcongr
            · exact natDegree_le_iff_degree_le.mpr hp
            · refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
              exact (natDegree_C_mul_le _ _).trans (by simp)
        _ = q := mul_one q
    exact_mod_cast this
  have hPb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(p.comp L).eval t| ≤ M := by
    intro t ht
    rw [eval_comp, hLe]
    refine hb _ ⟨?_, ?_⟩ <;> nlinarith [ht.1, ht.2]
  have hPs : (p.comp L).eval ((b + a) / (b - a)) = 1 := by
    rw [eval_comp, hLe, ← hp0]
    congr 1
    field_simp
    ring
  have := abs_eval_le_mul_abs_eval_T_real_of_forall_abs_le hP hPb
    (show 1 ≤ |(b + a) / (b - a)| from hs.trans (le_abs_self _))
  rw [hPs, abs_one, abs_of_pos (by linarith)] at this
  rwa [div_le_iff₀ (by linarith)]

/-- The Chebyshev minimax theorem on `[a, b]`, `0 < a < b`: the least possible bound `M` for
`|p|` on `[a, b]` over polynomials `p` of degree at most `q` with `p(0) = 1` is
`1 / T_q((b + a)/(b − a))`, attained by `chebyshevResidual a b q`.
Source: Golub–Meurant (2010) [`gm10`], App.; Trefethen–Bau (1997), Thm 38.5;
Atlas: `chebyshev-minimax`.
atlas: chebyshev-minimax -/
theorem isLeast_chebyshev_minimax {a b : ℝ} (q : ℕ) (ha : 0 < a) (hab : a < b) :
    IsLeast {M | ∃ p : ℝ[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧ ∀ x ∈ Set.Icc a b, |p.eval x| ≤ M}
      (1 / (T ℝ q).eval ((b + a) / (b - a))) :=
  ⟨⟨chebyshevResidual a b q, degree_chebyshevResidual_le a b q,
      eval_chebyshevResidual_zero ha hab, fun _ hx => abs_eval_chebyshevResidual_le ha hab hx⟩,
    fun _ ⟨_, hp, hp0, hb⟩ => inv_eval_T_real_le_of_forall_abs_eval_le ha hab hp hp0 hb⟩

/-! ### Monic minimality -/

/-- The scaled Chebyshev polynomial `2^(1−q) T_q` is monic (for `q = 0` it is `1`).
Source: Trefethen, *Approximation Theory and Approximation Practice* (2013), Thm 2.2 / Rivlin
(1990), Cor. 2.1.1; Atlas: `chebyshev-monic-minimal`.
atlas: chebyshev-monic-minimal -/
theorem monic_inv_two_pow_mul_T (q : ℕ) : (C (1 / 2 ^ (q - 1) : ℝ) * T ℝ q).Monic := by
  rw [Monic, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_T, Int.natAbs_natCast]
  field_simp

/-- The scaled Chebyshev polynomial `2^(1−q) T_q` has degree `q`.
Source: Rivlin (1990), Cor. 2.1.1; Atlas: `chebyshev-monic-minimal`. -/
theorem natDegree_inv_two_pow_mul_T (q : ℕ) : (C (1 / 2 ^ (q - 1) : ℝ) * T ℝ q).natDegree = q := by
  rw [natDegree_C_mul (by positivity), natDegree_T, Int.natAbs_natCast]

/-- The scaled Chebyshev polynomial `2^(1−q) T_q` is at most `1 / 2^(q−1)` in modulus on
`[−1, 1]`.
Source: Rivlin (1990), Cor. 2.1.1; Atlas: `chebyshev-monic-minimal`. -/
theorem abs_eval_inv_two_pow_mul_T_le {q : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(C (1 / 2 ^ (q - 1) : ℝ) * T ℝ q).eval x| ≤ 1 / 2 ^ (q - 1) := by
  rw [eval_mul, eval_C, abs_mul, abs_of_pos (by positivity)]
  exact mul_le_of_le_one_right (by positivity) (abs_eval_T_real_le_one _ (abs_le.mpr hx))

/-- Monic minimality of Chebyshev polynomials: a monic real polynomial of degree `q` has modulus
at least `1 / 2^(q−1)` somewhere on `[−1, 1]`, i.e. any bound `M` for `|p|` on `[−1, 1]`
satisfies `1 / 2^(q−1) ≤ M`.
Source: Trefethen (2013), Thm 2.2 / Rivlin (1990), Cor. 2.1.1; Mathlib
`Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one` applied to `p / M`;
Atlas: `chebyshev-monic-minimal`. Deviation: no hypothesis `0 < q` (for `q = 0`, `p = 1` and
the bound reads `1 ≤ M`, since `0 - 1 = 0` in `ℕ`).
atlas: chebyshev-monic-minimal -/
theorem inv_two_pow_le_of_monic_of_forall_abs_eval_le {q : ℕ} {p : ℝ[X]} {M : ℝ} (hp : p.Monic)
    (hdeg : p.natDegree = q) (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) :
    1 / 2 ^ (q - 1) ≤ M := by
  have hM : 0 < M := by
    by_contra hM
    exact hp.ne_zero (eq_zero_of_forall_abs_eval_le_of_nonpos (not_lt.mp hM) hb)
  have hQ : (C M⁻¹ * p).degree ≤ q := by
    refine (degree_C_mul_le _ _).trans ?_
    rw [← hdeg]
    exact degree_le_natDegree
  have hQb : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |(C M⁻¹ * p).eval y| ≤ 1 := by
    intro y hy
    rw [eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hM), inv_mul_le_iff₀ hM, mul_one]
    exact hb y hy
  have := leadingCoeff_le_of_forall_abs_le_one hQ hQb
  rw [leadingCoeff_mul, leadingCoeff_C, hp.leadingCoeff, mul_one] at this
  rw [one_div]
  exact inv_le_of_inv_le₀ hM this

/-- The monic Chebyshev minimax theorem: over monic real polynomials of degree `q`, the least
possible bound for `|p|` on `[−1, 1]` is `1 / 2^(q−1)`, attained by `2^(1−q) T_q`.
Source: Trefethen (2013), Thm 2.2 / Rivlin (1990), Cor. 2.1.1; Atlas: `chebyshev-monic-minimal`.
Deviation: stated for all `q`, including `q = 0` (where the value is `1`).
atlas: chebyshev-monic-minimal -/
theorem isLeast_chebyshev_monic_minimax (q : ℕ) :
    IsLeast {M | ∃ p : ℝ[X], p.Monic ∧ p.natDegree = q ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M} (1 / 2 ^ (q - 1)) :=
  ⟨⟨_, monic_inv_two_pow_mul_T q, natDegree_inv_two_pow_mul_T q,
      fun _ hx => abs_eval_inv_two_pow_mul_T_le hx⟩,
    fun _ ⟨_, hp, hdeg, hb⟩ => inv_two_pow_le_of_monic_of_forall_abs_eval_le hp hdeg hb⟩

end NLAlib
