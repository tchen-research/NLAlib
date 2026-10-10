import NLAlib.Polynomial.Basic
import NLAlib.Polynomial.Chebyshev
import NLAlib.Polynomial.Minimax

/-!
# Polynomial approximation: the Chebyshev amplifier and approximation of `1/x`

* `chebyshevAmplifier α γ q = T_q(X/α) / T_q(1 + γ)` (atlas `chebyshev-amplifier`): degree at
  most `q`, value `1` at `α(1 + γ)`, at least `1` beyond it, and at most `2/(1 + √(2γ))^q` in
  modulus on `[−α, α]` (Musco–Musco 2015, Lem. 4–5).
* The condition-number form of the Chebyshev minimax bound (atlas `chebyshev-minimax`): for
  `0 < a < b` the residual `chebyshevResidual a b q` is at most `2((√b − √a)/(√b + √a))^q` in
  modulus on `[a, b]`.
* Polynomial approximation of `1/x` on `[a, b]` (atlas `inverse-polynomial-approx`): a polynomial
  of degree `< q` within `(2/a)((√b − √a)/(√b + √a))^q` of `1/x`, the conjugate-gradient bound in
  the form its consumers use.

Atlas: `chebyshev-amplifier`, `inverse-polynomial-approx`, `chebyshev-minimax` (κ-form).
-/

noncomputable section

open Polynomial Polynomial.Chebyshev

namespace NLAlib

/-! ### The Chebyshev amplifier -/

/-- The amplifier has degree at most `q`.
Source: Musco–Musco (2015) [`mm15`], Lem. 4. Atlas: `chebyshev-amplifier`.
atlas: chebyshev-amplifier -/
theorem degree_chebyshevAmplifier_le (α γ : ℝ) (q : ℕ) :
    (chebyshevAmplifier α γ q).degree ≤ q := by
  rw [chebyshevAmplifier_def, C_mul']
  refine (degree_smul_le _ _).trans (degree_le_natDegree.trans ?_)
  have h1 : (C (1 / α) * X : ℝ[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
  have : ((T ℝ q).comp (C (1 / α) * X)).natDegree ≤ q := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_T, Int.natAbs_natCast]
    nlinarith
  exact_mod_cast this

/-- The amplifier equals `1` at `α(1 + γ)`.
Source: Musco–Musco (2015) [`mm15`], Lem. 4. Atlas: `chebyshev-amplifier`.
atlas: chebyshev-amplifier -/
theorem eval_chebyshevAmplifier_self {α γ : ℝ} (q : ℕ) (hα : 0 < α) (hγ : 0 ≤ γ) :
    (chebyshevAmplifier α γ q).eval (α * (1 + γ)) = 1 := by
  rw [eval_chebyshevAmplifier, mul_div_cancel_left₀ _ hα.ne']
  exact div_self (by linarith [one_le_eval_T_real (q : ℤ) (by linarith : (1 : ℝ) ≤ 1 + γ)])

/-- Beyond `α(1 + γ)` the amplifier is at least `1`: `α(1 + γ) ≤ x → 1 ≤ p(x)`.
Source: Musco–Musco (2015) [`mm15`], Lem. 4 (monotonicity of `T_q` on `[1, ∞)`). Atlas:
`chebyshev-amplifier`.
atlas: chebyshev-amplifier -/
theorem one_le_eval_chebyshevAmplifier {α γ x : ℝ} (q : ℕ) (hα : 0 < α) (hγ : 0 ≤ γ)
    (hx : α * (1 + γ) ≤ x) : 1 ≤ (chebyshevAmplifier α γ q).eval x := by
  rw [eval_chebyshevAmplifier]
  have hT := one_le_eval_T_real (q : ℤ) (by linarith : (1 : ℝ) ≤ 1 + γ)
  have hxa : 1 + γ ≤ x / α := by rw [le_div_iff₀ hα]; linarith
  have hmono := monotoneOn_eval_T_real q (Set.mem_Ici.2 (by linarith : (1 : ℝ) ≤ 1 + γ))
    (Set.mem_Ici.2 (by linarith : (1 : ℝ) ≤ x / α)) hxa
  rw [le_div_iff₀ (by linarith), one_mul]
  exact hmono

/-- On `[−α, α]` the amplifier is exponentially small: `|p(x)| ≤ 2/(1 + √(2γ))^q`.
Source: Musco–Musco (2015) [`mm15`], Lem. 4; Lem. 5 is the case `γ = ε`. Atlas:
`chebyshev-amplifier`.
atlas: chebyshev-amplifier -/
theorem abs_eval_chebyshevAmplifier_le {α γ x : ℝ} (q : ℕ) (hα : 0 < α) (hγ : 0 ≤ γ)
    (hx : x ∈ Set.Icc (-α) α) :
    |(chebyshevAmplifier α γ q).eval x| ≤ 2 / (1 + √(2 * γ)) ^ q := by
  rw [eval_chebyshevAmplifier]
  have hlow := one_add_sqrt_two_mul_pow_div_two_le_eval_T_real hγ q
  have hpos : 0 < (1 + √(2 * γ)) ^ q := by positivity
  have hT : 0 < (T ℝ q).eval (1 + γ) := by linarith [div_pos hpos two_pos]
  have hxa : |x / α| ≤ 1 := by
    rw [abs_div, abs_of_pos hα, div_le_one hα, abs_le]; exact ⟨hx.1, hx.2⟩
  have h1 := abs_eval_T_real_le_one (q : ℤ) hxa
  rw [abs_div, abs_of_pos hT, div_le_div_iff₀ hT hpos]
  calc |(T ℝ q).eval (x / α)| * (1 + √(2 * γ)) ^ q ≤ 1 * (1 + √(2 * γ)) ^ q :=
        mul_le_mul_of_nonneg_right h1 hpos.le
    _ ≤ 2 * (T ℝ q).eval (1 + γ) := by linarith

/-! ### The condition-number form of the minimax bound -/

/-- For `0 < a < b` the reciprocal `1/T_q((b + a)/(b − a))` is at most
`2((√b − √a)/(√b + √a))^q`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 8; Saad (2003), §6.11.3. Atlas: `chebyshev-minimax`
(κ-form).
atlas: chebyshev-minimax -/
theorem inv_eval_T_real_le_two_mul_pow {a b : ℝ} (q : ℕ) (ha : 0 < a) (hab : a < b) :
    1 / (T ℝ q).eval ((b + a) / (b - a)) ≤ 2 * ((√b - √a) / (√b + √a)) ^ q := by
  have hlow := sqrt_add_div_sqrt_sub_pow_div_two_le_eval_T_real ha hab q
  have hsa := Real.sqrt_pos.2 ha
  have hsb : √a < √b := Real.sqrt_lt_sqrt ha.le hab
  have hρ : 0 < ((√b + √a) / (√b - √a)) ^ q := by
    apply pow_pos; apply div_pos <;> linarith
  have hT : 0 < (T ℝ q).eval ((b + a) / (b - a)) := by linarith [div_pos hρ two_pos]
  have hinv : (√b - √a) / (√b + √a) = ((√b + √a) / (√b - √a))⁻¹ := by rw [inv_div]
  rw [hinv, inv_pow, ← div_eq_mul_inv, div_le_div_iff₀ hT hρ]
  linarith

/-- κ-form of the Chebyshev residual bound: for `0 < a < b` and `x ∈ [a, b]`,
`|chebyshevResidual a b q (x)| ≤ 2((√b − √a)/(√b + √a))^q`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 8; Trefethen–Bau (1997), Thm 38.5. Atlas:
`chebyshev-minimax` (κ-form).
atlas: chebyshev-minimax -/
theorem abs_eval_chebyshevResidual_le_two_mul_pow {a b x : ℝ} (q : ℕ) (ha : 0 < a) (hab : a < b)
    (hx : x ∈ Set.Icc a b) :
    |(chebyshevResidual a b q).eval x| ≤ 2 * ((√b - √a) / (√b + √a)) ^ q :=
  (abs_eval_chebyshevResidual_le ha hab hx).trans (inv_eval_T_real_le_two_mul_pow q ha hab)

/-! ### Polynomial approximation of `1/x` -/

/-- Polynomial approximation of `1/x` on `[a, b]`: for `0 < a < b` there is a polynomial `p` of
degree `< q` with `|p(x) − 1/x| ≤ (2/a)((√b − √a)/(√b + √a))^q` on `[a, b]`. The polynomial is
`p = (1 − r)/X` for the Chebyshev residual `r = chebyshevResidual a b q`.
Source: Golub–Meurant (2010) [`gm10`], Ch. 8 (the CG error bound). Atlas:
`inverse-polynomial-approx`.
atlas: inverse-polynomial-approx -/
theorem exists_degree_lt_abs_eval_sub_inv_le {a b : ℝ} (q : ℕ) (ha : 0 < a) (hab : a < b) :
    ∃ p : ℝ[X], p.degree < q ∧ ∀ x ∈ Set.Icc a b,
      |p.eval x - 1 / x| ≤ (2 / a) * ((√b - √a) / (√b + √a)) ^ q := by
  set r := chebyshevResidual a b q with hr
  have hr0 : r.eval 0 = 1 := eval_chebyshevResidual_zero ha hab
  have hdvd : X ∣ r - 1 := by
    rw [X_dvd_iff, coeff_zero_eq_eval_zero, eval_sub, hr0, eval_one, sub_self]
  obtain ⟨s, hs⟩ := hdvd
  refine ⟨-s, ?_, fun x hx => ?_⟩
  · rw [degree_neg]
    rcases eq_or_ne s 0 with h0 | h0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    · have hdeg : (r - 1).degree ≤ q :=
        (degree_sub_le _ _).trans (max_le (degree_chebyshevResidual_le a b q)
          (degree_one_le.trans (by exact_mod_cast Nat.zero_le q)))
      rw [hs, mul_comm, degree_mul_X] at hdeg
      rw [degree_eq_natDegree h0] at hdeg ⊢
      have : s.natDegree + 1 ≤ q := by exact_mod_cast hdeg
      exact_mod_cast (by omega : s.natDegree < q)
  · have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hev : r.eval x - 1 = x * s.eval x := by
      rw [← eval_one (x := x), ← eval_sub, hs, eval_mul, eval_X]
    have hval : (-s).eval x - 1 / x = -(r.eval x / x) := by
      rw [eval_neg]; field_simp; linarith
    rw [hval, abs_neg, abs_div, abs_of_pos hxpos]
    have hbound := abs_eval_chebyshevResidual_le_two_mul_pow q ha hab hx
    calc |r.eval x| / x ≤ |r.eval x| / a := div_le_div_of_nonneg_left (abs_nonneg _) ha hx.1
      _ ≤ (2 * ((√b - √a) / (√b + √a)) ^ q) / a := div_le_div_of_nonneg_right hbound ha.le
      _ = (2 / a) * ((√b - √a) / (√b + √a)) ^ q := by ring

end NLAlib
