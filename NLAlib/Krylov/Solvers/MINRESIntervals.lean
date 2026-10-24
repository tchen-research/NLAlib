import NLAlib.Krylov.Solvers.GMRES
import NLAlib.Polynomial.FunctionApproximation.TwoIntervals

/-! # MINRES convergence on two spectral intervals

The equal-width two-interval Chebyshev polynomial gives the explicit
indefinite MINRES rate. The symmetric two-interval specialization is
also stated using the ratio of the outer and inner spectral radii.
Source: Greenbaum (1997), §3.1; Liesen--Strakoš (2013), §5.6.
Realises the remaining indefinite clauses of `minres-bound`.
-/

noncomputable section

open Matrix Polynomial
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ} {c x₀ x : n → ℝ} {q : ℕ}

/-- The symmetric spectral GMRES estimate in the native vector 2-norm.
Source: Greenbaum (1997), §3.1.
atlas: minres-bound (partial) -/
theorem IsGMRESIterate.norm_sub_mulVec_le_of_isHermitian
    (hx : IsGMRESIterate A c x₀ q x) (hA : A.IsHermitian)
    {p : ℝ[X]} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, |p.eval (hA.eigenvalues i)| ≤ M) :
    ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ≤ M * ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖ := by
  have hs := hx.dotProduct_le_sq_mul_of_isHermitian hA hp hp0 hM
  have hnorm : ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ^ 2 ≤
      (M * ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖) ^ 2 := by
    simpa only [mul_pow, norm_toLp_sq_eq_dotProduct_self] using hs
  exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hM0 (norm_nonneg _)) hnorm

/-- The definite MINRES Chebyshev rate in the vector 2-norm.
Source: Greenbaum (1997), §3.1; Liesen--Strakoš (2013), §5.6.
atlas: minres-bound (partial) -/
theorem IsGMRESIterate.norm_sub_mulVec_le_of_eigenvalues_mem_Icc
    (hx : IsGMRESIterate A c x₀ q x) (hA : A.IsHermitian)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b) :
    ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ≤
      (2 * ((Real.sqrt b - Real.sqrt a) / (Real.sqrt b + Real.sqrt a)) ^ q) *
        ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖ := by
  exact hx.norm_sub_mulVec_le_of_isHermitian hA (degree_chebyshevResidual_le a b q)
    (eval_chebyshevResidual_zero ha hab)
    ((abs_nonneg _).trans (abs_eval_chebyshevResidual_le_two_mul_pow q ha hab
      ⟨le_rfl, hab.le⟩))
    (fun i => abs_eval_chebyshevResidual_le_two_mul_pow q ha hab (hspec i))

/-- MINRES at step `2k` has the equal-width indefinite two-interval rate.
Source: Greenbaum (1997), §3.1; Liesen--Strakoš (2013), §5.6. The
polynomial argument needs no separate invertibility hypothesis: the
spectral containment already excludes zero in a nonempty dimension.
atlas: minres-bound (partial) -/
theorem IsGMRESIterate.norm_sub_mulVec_le_of_eigenvalues_mem_two_intervals
    {a b c₁ d : ℝ} (hA : A.IsHermitian)
    (hab : a < b) (hb : b < 0) (hc : 0 < c₁) (hcd : c₁ < d)
    (hlen : d - c₁ = b - a) (k : ℕ)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b ∪ Set.Icc c₁ d)
    (hx : IsGMRESIterate A c x₀ (2 * k) x) :
    ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ≤
      (2 * ((Real.sqrt |a * d| - Real.sqrt |b * c₁|) /
        (Real.sqrt |a * d| + Real.sqrt |b * c₁|)) ^ k) *
        ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖ := by
  obtain ⟨p, hp, hp0, hbound⟩ :=
    exists_degree_le_abs_eval_le_on_two_intervals hab hb hc hcd hlen k
  exact hx.norm_sub_mulVec_le_of_isHermitian hA hp hp0
    ((abs_nonneg _).trans (hbound a (Or.inl ⟨le_rfl, hab.le⟩)))
    (fun i => hbound _ (hspec i))

/-- For spectrum in `[-d,-c] ∪ [c,d]`, MINRES contracts at the
explicit rate `2 ((d-c)/(d+c))^k` every `2k` steps.
Source: Greenbaum (1997), §3.1; Liesen--Strakoš (2013), §5.6.
atlas: minres-bound (partial) -/
theorem IsGMRESIterate.norm_sub_mulVec_le_of_eigenvalues_mem_symmetric_intervals
    {c₁ d : ℝ} (hA : A.IsHermitian) (hc : 0 < c₁) (hcd : c₁ < d) (k : ℕ)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc (-d) (-c₁) ∪ Set.Icc c₁ d)
    (hx : IsGMRESIterate A c x₀ (2 * k) x) :
    ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ≤
      (2 * ((d - c₁) / (d + c₁)) ^ k) * ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖ := by
  have h := hx.norm_sub_mulVec_le_of_eigenvalues_mem_two_intervals hA
    (neg_lt_neg hcd) (neg_neg_of_pos hc) hc hcd (by ring) k hspec
  simpa only [neg_mul, abs_neg, ← sq, abs_sq, Real.sqrt_sq_eq_abs,
    abs_of_pos hc, abs_of_pos (hc.trans hcd)] using h

/-- The symmetric two-interval rate expressed using `κ = d/c`.
Source: Greenbaum (1997), §3.1; Liesen--Strakoš (2013), §5.6.
atlas: minres-bound (partial) -/
theorem IsGMRESIterate.norm_sub_mulVec_le_of_eigenvalues_mem_symmetric_intervals_ratio
    {c₁ d : ℝ} (hA : A.IsHermitian) (hc : 0 < c₁) (hcd : c₁ < d) (k : ℕ)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc (-d) (-c₁) ∪ Set.Icc c₁ d)
    (hx : IsGMRESIterate A c x₀ (2 * k) x) :
    ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ≤
      (2 * (((d / c₁) - 1) / ((d / c₁) + 1)) ^ k) *
        ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖ := by
  have hr : ((d / c₁) - 1) / ((d / c₁) + 1) = (d - c₁) / (d + c₁) := by
    rw [div_sub_one hc.ne', div_add_one hc.ne', div_div_div_cancel_right₀ hc.ne']
  rw [hr]
  exact hx.norm_sub_mulVec_le_of_eigenvalues_mem_symmetric_intervals hA hc hcd k hspec

end NLAlib
