import NLAlib.Probability.ChiSquare.DirectionalSquaredNorm

/-! A continuous Gaussian sample space uses the native directional sub-Gaussian tail
theorem directly. No finite-support model or discrete sample-space instance is needed. -/

open MeasureTheory ProbabilityTheory NLAlib
open scoped NNReal

-- The squared standard Gaussian has the one-dimensional Laurent–Massart upper tail.
example {x : ℝ} (hx : 0 ≤ x) :
    (gaussianReal 0 1).real {g : ℝ | 1 + 2 * Real.sqrt x + 2 * x ≤ g ^ 2} ≤
      Real.exp (-x) := by
  have hmgf : ∀ u : Fin 1 → ℝ,
      HasSubgaussianMGF (fun g : ℝ => (fun _ : Fin 1 => g) ⬝ᵥ u)
        (‖WithLp.toLp 2 u‖₊ ^ 2) (gaussianReal 0 1) := by
    intro u
    have hvar : (⟨(u 0) ^ 2, sq_nonneg _⟩ : ℝ≥0) = ‖WithLp.toLp 2 u‖₊ ^ 2 := by
      apply NNReal.eq
      change (u 0) ^ 2 = ((‖WithLp.toLp 2 u‖₊ ^ 2 : ℝ≥0) : ℝ)
      rw [NNReal.coe_pow, coe_nnnorm, norm_toLp_sq_eq_dotProduct_self]
      simp [dotProduct, pow_two]
    have hscaled := (hasSubgaussianMGF_id_gaussianReal 1).const_mul (u 0)
    have hproxy : NNReal.mk ((u 0) ^ 2) (sq_nonneg _) * (1 : NNReal) =
        ‖WithLp.toLp 2 u‖₊ ^ 2 := by
      exact (_root_.mul_one _).trans hvar
    convert hscaled using 1
    · ext g
      simp [dotProduct, mul_comm]
    · exact hproxy.symm
  simpa only [norm_toLp_sq_eq_dotProduct_self, dotProduct, Fin.sum_univ_one,
    Nat.cast_one, one_mul, ← sq] using
    measureReal_sq_norm_ge_add_two_sqrt_mul_add_le
      (gaussianReal 0 1) (fun g : ℝ => fun _ : Fin 1 => g) hmgf hx
