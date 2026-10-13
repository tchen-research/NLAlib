import NLAlib.Polynomial.Quadrature.ChebyshevError

/-! # Sharp errors for symmetric positive Gauss rules

Finite positive symmetric rules of mass two and exact degree `2n+1` have the
Lebesgue `32/15` Chebyshev even-mode tail bound.
-/
noncomputable section
open Polynomial Polynomial.Chebyshev MeasureTheory Finset Set
namespace NLAlib

private theorem sum_mul_eval_T_eq_zero_of_symmetric {ι : Type*} [Fintype ι]
    (v w : ι → ℝ) (σ : ι ≃ ι) (hv : ∀ i, v (σ i) = -v i) (hw : ∀ i, w (σ i) = w i)
    {k : ℕ} (hk : Odd k) : ∑ i, w i * (T ℝ k).eval (v i) = 0 := by
  have h := σ.sum_comp (fun i => w i * (T ℝ k).eval (v i))
  simp only [hv, hw, T_eval_neg, Int.cast_negOnePow_natCast, hk.neg_one_pow,
    neg_one_mul, mul_neg] at h
  rw [Finset.sum_neg_distrib] at h
  linarith

private theorem abs_sum_mul_eval_T_le_two {ι : Type*} [Fintype ι]
    (v w : ι → ℝ) (hv : ∀ i, v i ∈ Icc (-1 : ℝ) 1) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i = 2) (k : ℕ) : |∑ i, w i * (T ℝ k).eval (v i)| ≤ 2 := by
  calc _ ≤ ∑ i, |w i * (T ℝ k).eval (v i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i * |(T ℝ k).eval (v i)| := by
      apply sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i)]
    _ ≤ ∑ i, w i := by
      apply sum_le_sum
      intro i hi
      exact mul_le_of_le_one_right (hw i) (abs_eval_T_real_le_one _ (abs_le.mpr (hv i)))
    _ = 2 := hmass

/-- Every symmetric positive quadrature rule of mass two, exact through degree
`2n+1`, has the sharp Gauss even-coefficient-tail error bound. Source: Trefethen,
ATAP, Theorem 19.4. Reflection is stated by the actual node-and-weight permutation.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem abs_integral_sub_symmetric_quadrature_le_even_tail
    {ι : Type*} [Fintype ι] (v w : ι → ℝ) (hv : ∀ i, v i ∈ Icc (-1 : ℝ) 1)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 2)
    (σ : ι ≃ ι) (hvσ : ∀ i, v (σ i) = -v i) (hwσ : ∀ i, w (σ i) = w i)
    {n : ℕ} (hn : 1 ≤ n)
    (hexact : ∀ p : ℝ[X], p.degree ≤ (2 * n + 1 : ℕ) →
      (∫ x in (-1 : ℝ)..1, p.eval x) = ∑ i, w i * p.eval (v i))
    {c : ℕ → ℝ} {f : ℝ → ℝ} (hs : Summable (fun k => |c k|))
    (hf : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k => c k * (T ℝ k).eval x) (f x)) :
    |(∫ x in (-1 : ℝ)..1, f x) - ∑ i, w i * f (v i)| ≤
      (32 / 15 : ℝ) * ∑' k, if 2 * n + 1 < k ∧ Even k then |c k| else 0 := by
  let Q : ℕ → ℝ := fun k => ∑ i, w i * (T ℝ k).eval (v i)
  let u := fun k => c k * (chebyshevMoment k - Q k)
  let tail := fun k => if 2 * n + 1 < k ∧ Even k then |c k| else 0
  have hQ : HasSum (fun k => c k * Q k) (∑ i, w i * f (v i)) := by
    have h := hasSum_sum (s := Finset.univ) (fun i hi => (hf (v i) (hv i)).mul_left (w i))
    convert h using 1 <;> try rfl
    funext k
    dsimp [Q]
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  have he : HasSum u ((∫ x in (-1 : ℝ)..1, f x) - ∑ i, w i * f (v i)) := by
    have h := (hasSum_mul_chebyshevMoment_of_hasSum hs hf).sub hQ
    convert h using 1 <;> try rfl
    funext k
    dsimp [u]
    ring
  have ht : Summable tail := hs.of_nonneg_of_le (by intro k; dsimp [tail]; split_ifs <;> positivity)
    (by intro k; dsimp [tail]; split_ifs <;> simp)
  have hb (k : ℕ) : ‖u k‖ ≤ (32 / 15 : ℝ) * tail k := by
    by_cases hkn : 2 * n + 1 < k
    · by_cases hk : Even k
      · have hk4 : 4 ≤ k := by omega
        have h1 := abs_chebyshevMoment_le_two_div_fifteen hk4
        have h2 := abs_sum_mul_eval_T_le_two v w hv hw hmass k
        have hmode : |chebyshevMoment k - Q k| ≤ 32 / 15 := by
          have h := abs_sub (chebyshevMoment k) (Q k)
          dsimp [Q] at h ⊢
          linarith
        dsimp [u, tail]
        rw [if_pos ⟨hkn, hk⟩, abs_mul]
        calc |c k| * |chebyshevMoment k - Q k| ≤ |c k| * (32 / 15) :=
            mul_le_mul_of_nonneg_left hmode (abs_nonneg _)
          _ = _ := mul_comm _ _
      · have hko : Odd k := Nat.not_even_iff_odd.mp hk
        have hodd := sum_mul_eval_T_eq_zero_of_symmetric v w σ hvσ hwσ hko
        simp [u, Q, tail, chebyshevMoment, hk, hodd]
    · have hdeg : (T ℝ k).degree ≤ (2 * n + 1 : ℕ) := by
        rw [degree_T, Int.natAbs_natCast]
        exact_mod_cast (show k ≤ 2 * n + 1 by omega)
      have h := hexact (T ℝ k) hdeg
      rw [integral_eval_T] at h
      change chebyshevMoment k = Q k at h
      simp [u, tail, hkn, h]
  have hnorm : Summable (fun k => ‖u k‖) := Summable.of_nonneg_of_le (fun k => norm_nonneg _) hb
    (ht.mul_left (32 / 15 : ℝ))
  have hnormle := norm_tsum_le_tsum_norm hnorm
  rw [he.tsum_eq, Real.norm_eq_abs] at hnormle
  refine hnormle.trans ?_
  calc (∑' k, ‖u k‖) ≤ ∑' k, (32 / 15 : ℝ) * tail k :=
      Summable.tsum_le_tsum hb hnorm (ht.mul_left (32 / 15 : ℝ))
    _ = _ := by rw [tsum_mul_left]

/-- A symmetric positive rule exact through degree `2n+1` has the sharp analytic
Gauss constant when its actual Chebyshev coefficients decay geometrically.
Source: Trefethen, ATAP, Theorem 19.4.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem abs_integral_sub_symmetric_quadrature_le_geometric
    {ι : Type*} [Fintype ι] (v w : ι → ℝ) (hv : ∀ i, v i ∈ Icc (-1 : ℝ) 1)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 2)
    (σ : ι ≃ ι) (hvσ : ∀ i, v (σ i) = -v i) (hwσ : ∀ i, w (σ i) = w i)
    {n : ℕ} (hn : 1 ≤ n)
    (hexact : ∀ p : ℝ[X], p.degree ≤ (2 * n + 1 : ℕ) →
      (∫ x in (-1 : ℝ)..1, p.eval x) = ∑ i, w i * p.eval (v i))
    {c : ℕ → ℝ} {f : ℝ → ℝ} (hs : Summable (fun k => |c k|))
    (hf : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k => c k * (T ℝ k).eval x) (f x))
    {q M : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hM : 0 ≤ M)
    (hc : ∀ k, 0 < k → |c k| ≤ 2 * M * q ^ k) :
    |(∫ x in (-1 : ℝ)..1, f x) - ∑ i, w i * f (v i)| ≤
      (64 / 15 : ℝ) * M * q ^ (2 * n + 2) / (1 - q ^ 2) := by
  have htail := tsum_even_abs_tail_le_of_geometric hs hq0 hq1 hM hc (2 * n + 1)
  refine (abs_integral_sub_symmetric_quadrature_le_even_tail v w hv hw hmass σ hvσ hwσ hn hexact hs hf).trans ?_
  have h := mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 32 / 15)
  convert h using 1
  ring

/-- A concrete symmetric positive rule exact through degree `2n+1` has the sharp
Gauss analytic error `(64/15)Mρ^(-2n)/(ρ²−1)` for an open-ellipse analytic function.
Source: Trefethen, ATAP, Theorem 19.4. All structural hypotheses refer to the rule's
actual nodes and weights.
atlas: gauss-clenshaw-curtis-quadrature-error (partial) -/
theorem abs_integral_re_sub_symmetric_quadrature_le_of_open_ellipse
    {ι : Type*} [Fintype ι] (v w : ι → ℝ) (hv : ∀ i, v i ∈ Icc (-1 : ℝ) 1)
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = 2)
    (σ : ι ≃ ι) (hvσ : ∀ i, v (σ i) = -v i) (hwσ : ∀ i, w (σ i) = w i)
    {n : ℕ} (hn : 1 ≤ n)
    (hexact : ∀ p : ℝ[X], p.degree ≤ (2 * n + 1 : ℕ) →
      (∫ x in (-1 : ℝ)..1, p.eval x) = ∑ i, w i * p.eval (v i))
    {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : ∀ z ∈ openBernsteinEllipse ρ, ‖F z‖ ≤ M) :
    |(∫ x in (-1 : ℝ)..1, (F x).re) - ∑ i, w i * (F (v i)).re| ≤
      (64 / 15 : ℝ) * M / (ρ ^ (2 * n) * (ρ ^ 2 - 1)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans
    (abs_chebyshevAnalyticCoeff_zero_le_of_open_ellipse hρ hFd hM)
  have hρ0 : 0 < ρ := by linarith
  have hq0 : 0 < ρ⁻¹ := inv_pos.mpr hρ0
  have hq1 : ρ⁻¹ < 1 := (inv_lt_one₀ hρ0).mpr hρ
  have hc (k : ℕ) (hk : 0 < k) : |chebyshevAnalyticCoeff F k| ≤ 2 * M * (ρ⁻¹) ^ k := by
    have h := abs_chebyshevAnalyticCoeff_le_of_open_ellipse hρ hFd hM hk
    simpa only [div_eq_mul_inv, inv_pow] using h
  have hs : Summable (fun k => |chebyshevAnalyticCoeff F k|) := by
    apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) ?_
      ((summable_geometric_of_lt_one hq0.le hq1).mul_left (2 * M))
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h := abs_chebyshevAnalyticCoeff_zero_le_of_open_ellipse hρ hFd hM
      simpa only [pow_zero, mul_one] using h.trans (by linarith : M ≤ 2 * M)
    · exact hc k hk
  have h := abs_integral_sub_symmetric_quadrature_le_geometric v w hv hw hmass σ hvσ hwσ hn hexact hs
    (fun x hx => hasSum_chebyshevAnalyticCoeff_mul_eval_T_of_open_ellipse hρ hFd hM hx)
    hq0 hq1 hM0 hc
  have heq : (64 / 15 : ℝ) * M * (ρ⁻¹) ^ (2 * n + 2) / (1 - (ρ⁻¹) ^ 2) =
      (64 / 15 : ℝ) * M / (ρ ^ (2 * n) * (ρ ^ 2 - 1)) := by
    rw [pow_add]
    simp only [inv_pow]
    have hsq : ρ ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp [ne_of_gt hρ0, hsq]
  exact h.trans_eq heq

end NLAlib
