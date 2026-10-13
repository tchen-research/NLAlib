import NLAlib.Matrix.Perturbation.LeastSquaresToolkit
/-!
# Least-squares angle ratios and coordinate perturbation bounds

The existing Euclidean least-squares bounds transported to ordinary coordinates,
including total real division in zero-solution and zero-data cases.
Sources: Trefethen–Bau 1997, Lecture 18; Higham 2002, Theorem 20.1.
Supports atlas `least-squares-perturbation`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- `cos θ = ‖y‖/‖b‖` for the least-squares fit `y = A A⁺ b`: `θ` is the angle between `b` and
`range A`. Trefethen–Bau 1997, Lecture 18 (eq. (18.3)); `0` when `b = 0` (total convention).
atlas: least-squares-perturbation (partial) -/
def leastSquaresCos (A : Matrix m n ℝ) (b : m → ℝ) : ℝ :=
  Real.sqrt (((A * moorePenroseInverse A) *ᵥ b) ⬝ᵥ ((A * moorePenroseInverse A) *ᵥ b)) /
    Real.sqrt (b ⬝ᵥ b)

/-- `tan θ = ‖b - y‖/‖y‖` for the least-squares fit `y = A A⁺ b`. Trefethen–Bau 1997,
Lecture 18; `0` when `y = 0` (total convention, `θ = π/2` is excluded in the source).
atlas: least-squares-perturbation (partial) -/
def leastSquaresTan (A : Matrix m n ℝ) (b : m → ℝ) : ℝ :=
  Real.sqrt ((b - (A * moorePenroseInverse A) *ᵥ b) ⬝ᵥ (b - (A * moorePenroseInverse A) *ᵥ b)) /
    Real.sqrt (((A * moorePenroseInverse A) *ᵥ b) ⬝ᵥ ((A * moorePenroseInverse A) *ᵥ b))

/-- `η = ‖A‖‖x‖/‖y‖` for `x = A⁺ b`, `y = A x`; `1 ≤ η ≤ κ(A)` when `y ≠ 0`. Trefethen–Bau 1997,
Lecture 18 (eq. (18.4)); `0` when `y = 0`.
atlas: least-squares-perturbation (partial) -/
def leastSquaresEta (A : Matrix m n ℝ) (b : m → ℝ) : ℝ :=
  specNorm A * Real.sqrt ((moorePenroseInverse A *ᵥ b) ⬝ᵥ (moorePenroseInverse A *ᵥ b)) /
    Real.sqrt (((A * moorePenroseInverse A) *ᵥ b) ⬝ᵥ ((A * moorePenroseInverse A) *ᵥ b))

/-- **Wedin's least-squares bound (solution).** Higham's finite relative least-squares solution
bound in ordinary coordinates, with total division covering a zero old solution: for full column
rank `A`, `x = A⁺ b`, `r = b - A x`, `‖E‖₂ ≤ ε‖A‖₂`, `‖f‖ ≤ ε‖b‖` and `κ(A) ε < 1`,
`‖x - y‖/‖x‖ ≤ κε/(1 - κε) · (2 + (κ + 1) ‖r‖/(‖A‖₂‖x‖))` for `y = (A + E)⁺(b + f)`.
Higham 2002, Theorem 20.1 (from Wedin 1973, §5); first-order form Golub–Van Loan 2013,
Thm 5.3.1. Transports `norm_least_squares_sub_div_le`.
atlas: least-squares-perturbation (partial) -/
theorem sqrt_pinv_solution_sub_div_le (A E : Matrix m n ℝ)
    (hA : A.rank = Fintype.card n) (b f : m → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hE : specNorm E ≤ ε * specNorm A)
    (hf : Real.sqrt (f ⬝ᵥ f) ≤ ε * Real.sqrt (b ⬝ᵥ b))
    (hsmall : moorePenroseConditionNumber A * ε < 1) :
    Real.sqrt ((moorePenroseInverse A *ᵥ b - moorePenroseInverse (A + E) *ᵥ (b + f)) ⬝ᵥ
        (moorePenroseInverse A *ᵥ b - moorePenroseInverse (A + E) *ᵥ (b + f))) /
      Real.sqrt ((moorePenroseInverse A *ᵥ b) ⬝ᵥ (moorePenroseInverse A *ᵥ b)) ≤
      moorePenroseConditionNumber A * ε / (1 - moorePenroseConditionNumber A * ε) *
        (2 + (moorePenroseConditionNumber A + 1) *
          Real.sqrt ((b - A *ᵥ (moorePenroseInverse A *ᵥ b)) ⬝ᵥ
            (b - A *ᵥ (moorePenroseInverse A *ᵥ b))) /
          (specNorm A * Real.sqrt ((moorePenroseInverse A *ᵥ b) ⬝ᵥ
            (moorePenroseInverse A *ᵥ b)))) := by
  by_cases hx : moorePenroseInverse A *ᵥ b = 0
  · simp only [hx, dotProduct_zero, Real.sqrt_zero, mul_zero, div_zero, add_zero]
    have hκ := moorePenroseConditionNumber_nonneg A
    have hgap : 0 < 1 - moorePenroseConditionNumber A * ε := sub_pos.mpr hsmall
    exact mul_nonneg (div_nonneg (mul_nonneg hκ hε) hgap.le) (by norm_num)
  have hx' : (moorePenroseInverse A).toEuclideanLin (WithLp.toLp 2 b) ≠ 0 := by
    intro hz
    apply hx
    exact congrArg WithLp.ofLp hz
  have hf' : ‖(WithLp.toLp 2 f : EuclideanSpace ℝ m)‖ ≤
      ε * ‖(WithLp.toLp 2 b : EuclideanSpace ℝ m)‖ := by
    simpa only [sqrt_dotProduct_self_eq_norm] using hf
  have h := norm_least_squares_sub_div_le hA (WithLp.toLp 2 b) (WithLp.toLp 2 f)
    hx' hε hE hf' hsmall
  simpa only [norm_sub_rev, norm_eq_sqrt_dotProduct, WithLp.ofLp_sub, WithLp.ofLp_add,
    Matrix.toEuclideanLin, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, WithLp.ofLp_toLp] using h

/-- **Wedin's least-squares bound (residual).** Higham's finite residual bound in ordinary
coordinates, including zero data: under the hypotheses of `sqrt_pinv_solution_sub_div_le`,
`‖r - s‖/‖b‖ ≤ (1 + 2κ(A)) ε`. Higham 2002, Theorem 20.1; Wedin 1973, §5. Transports the
stronger Euclidean coefficient `1+κ`.
atlas: least-squares-perturbation (partial) -/
theorem sqrt_pinv_residual_sub_div_le (A E : Matrix m n ℝ)
    (hA : A.rank = Fintype.card n) (b f : m → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hE : specNorm E ≤ ε * specNorm A)
    (hf : Real.sqrt (f ⬝ᵥ f) ≤ ε * Real.sqrt (b ⬝ᵥ b))
    (hsmall : moorePenroseConditionNumber A * ε < 1) :
    Real.sqrt ((b - A *ᵥ (moorePenroseInverse A *ᵥ b) -
          ((b + f) - (A + E) *ᵥ (moorePenroseInverse (A + E) *ᵥ (b + f)))) ⬝ᵥ
        (b - A *ᵥ (moorePenroseInverse A *ᵥ b) -
          ((b + f) - (A + E) *ᵥ (moorePenroseInverse (A + E) *ᵥ (b + f))))) /
      Real.sqrt (b ⬝ᵥ b) ≤ (1 + 2 * moorePenroseConditionNumber A) * ε := by
  by_cases hb : b = 0
  · simp only [hb, dotProduct_zero, Real.sqrt_zero, div_zero]
    have hκ := moorePenroseConditionNumber_nonneg A
    positivity
  have hb' : (WithLp.toLp 2 b : EuclideanSpace ℝ m) ≠ 0 := by
    intro hz
    apply hb
    exact congrArg WithLp.ofLp hz
  have hf' : ‖(WithLp.toLp 2 f : EuclideanSpace ℝ m)‖ ≤
      ε * ‖(WithLp.toLp 2 b : EuclideanSpace ℝ m)‖ := by
    simpa only [sqrt_dotProduct_self_eq_norm] using hf
  have h := norm_least_squares_residual_sub_div_le hA (WithLp.toLp 2 b)
    (WithLp.toLp 2 f) hb' hE hf' hsmall
  have h' := h.trans (mul_le_mul_of_nonneg_right
    (show 1 + moorePenroseConditionNumber A ≤ 1 + 2 * moorePenroseConditionNumber A by
      linarith [moorePenroseConditionNumber_nonneg A]) hε)
  simpa only [norm_eq_sqrt_dotProduct, WithLp.ofLp_sub, WithLp.ofLp_add,
    Matrix.toEuclideanLin, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, WithLp.ofLp_toLp] using h'

end NLAlib
