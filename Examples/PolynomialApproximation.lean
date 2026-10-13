import NLAlib

/-! Downstream uses of the polynomial approximation API through the default import.
The examples combine coefficient, minimax, and interpolation interfaces under ordinary
Lean options, without access to private helpers or experimental modules. -/

noncomputable section

open NLAlib Polynomial Set

-- Polynomial data can be recovered exactly from the integral coefficient interface.
example {p : ℝ[X]} {n : ℕ} (hp : p.degree ≤ n) : chebyshevTrunc p.eval n = p :=
  chebyshevTrunc_eval_eq_of_degree_le hp

-- The coefficient interface detects an identically zero tail for finite expansions.
example {p : ℝ[X]} {n : ℕ} (hp : p.degree ≤ n) (k : ℕ) :
    chebyshevCoeff p.eval (n + k + 1) = 0 :=
  chebyshevCoeff_eval_eq_zero_of_degree_lt hp (by omega)

-- Attainment and uniqueness combine into the familiar unique-best-polynomial statement.
example {a b : ℝ} (hab : a < b) (n : ℕ) (f : C(Icc a b, ℝ)) :
    ∃! p : ℝ[X], p.degree ≤ n ∧
      ‖f - p.toContinuousMapOn (Icc a b)‖ = minimaxError n f := by
  obtain ⟨p, hp, hbest⟩ := exists_degree_le_norm_sub_eq_minimaxError n f
  refine ⟨p, ⟨hp, hbest⟩, ?_⟩
  intro q hq
  exact eq_of_norm_sub_eq_minimaxError hab f hq.1 hp hq.2 hbest

-- A certified best-error tolerance gives an explicit error bound for Chebyshev interpolation.
example {n : ℕ} (hn : 0 < n) (f : C(Icc (-1 : ℝ) 1, ℝ)) {ε : ℝ}
    (hbest : minimaxError n f ≤ ε) :
    ‖f - interpolationLinearMap (Icc (-1 : ℝ) 1) (chebyshevExtrema n) f‖ ≤
      (2 + (2 / Real.pi) * Real.log ((n : ℝ) + 1)) * ε := by
  apply (norm_sub_chebyshev_interpolation_le_minimaxError hn f).trans
  exact mul_le_mul_of_nonneg_left hbest (by
    have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))
    positivity)

-- The explicit absolute-value expansion supplies a quantitative bound on best approximation.
example (m : ℕ) (f : C(Icc (-1 : ℝ) 1, ℝ))
    (hf : ∀ x : Icc (-1 : ℝ) 1, f x = |(x : ℝ)|) :
    minimaxError (2 * m) f ≤ 2 / (Real.pi * (2 * (m : ℝ) + 1)) := by
  have hp := degree_chebyshevTrunc_le (fun x : ℝ => |x|) (2 * m)
  apply (minimaxError_le_norm_sub f
    (mem_polynomialApproximationSpace_iff.mpr
      ⟨chebyshevTrunc (fun x : ℝ => |x|) (2 * m), hp, rfl⟩)).trans
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change |f x - (chebyshevTrunc (fun x : ℝ => |x|) (2 * m)).eval (x : ℝ)| ≤ _
  rw [hf]
  exact abs_abs_sub_eval_chebyshevTrunc_le m x.property

-- Positive Fejér approximation preserves a caller's range constraint.
example {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hrange : ∀ x ∈ Icc (-1 : ℝ) 1, f x ∈ Icc 0 1)
    (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (fejerChebyshevMean f n).eval x ∈ Icc 0 1 := by
  refine ⟨eval_fejerChebyshevMean_nonneg hf (fun y hy => (hrange y hy).1) n hx, ?_⟩
  have hbound := abs_eval_fejerChebyshevMean_le hf
    (fun y hy => by rw [abs_of_nonneg (hrange y hy).1]; exact (hrange y hy).2) n hx
  exact (abs_le.mp hbound).2

-- Clenshaw evaluates a truncation without constructing its monomial coefficients.
example (f : ℝ → ℝ) (t : ℝ) (n : ℕ) :
    (chebyshevTrunc f n).eval t =
      (clenshawState (fun _ => 2 * t) (fun _ => 1) (chebyshevCoeff f) 0 (n + 1)).1 -
        t * (clenshawState (fun _ => 2 * t) (fun _ => 1) (chebyshevCoeff f) 0 (n + 1)).2 := by
  simpa only [chebyshevTrunc, eval_finsetSum, eval_mul, eval_C] using
    sum_mul_eval_T_eq_clenshawState (chebyshevCoeff f) t n
