import NLAlib.Matrix.Perturbation.LeastSquaresCoordinateBounds
/-!
# First-order least-squares bounds for matrix perturbations

The exact projector gap supplies the fitted-value coefficient. The existing
finite pseudoinverse estimate supplies the solution coefficient after choosing
an explicit small perturbation radius. Trefethen–Bau 1997, Theorem 18.1.
Supports atlas `least-squares-perturbation`.
-/

noncomputable section
set_option maxHeartbeats 800000
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Least squares, `y` under perturbation of `A` (first order).** The fitted-value sensitivity
under a pure matrix perturbation has coefficient `κ/cos θ`, in epsilon–delta form: for full column
rank `A` and `y = A A⁺ b`, `‖Δy‖/‖y‖ ≤ (κ(A)/cos θ + ε) ‖ΔA‖/‖A‖` once `‖ΔA‖₂ < δ`.
Trefethen–Bau 1997, Theorem 18.1 (third entry); the projector gap gives the coefficient exactly
inside a rank-preserving neighborhood.
atlas: least-squares-perturbation (partial) -/
theorem exists_pos_forall_sqrt_pinv_fit_sub_div_le (A : Matrix m n ℝ)
    (hA : A.rank = Fintype.card n) (b : m → ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ E : Matrix m n ℝ, specNorm E < δ →
      Real.sqrt ((((A + E) * moorePenroseInverse (A + E)) *ᵥ b -
            (A * moorePenroseInverse A) *ᵥ b) ⬝ᵥ
          (((A + E) * moorePenroseInverse (A + E)) *ᵥ b -
            (A * moorePenroseInverse A) *ᵥ b)) /
        Real.sqrt (((A * moorePenroseInverse A) *ᵥ b) ⬝ᵥ ((A * moorePenroseInverse A) *ᵥ b)) ≤
        (conditionNumber A / leastSquaresCos A b + ε) * (specNorm E / specNorm A) := by
  intro ε hε
  let a := specNorm (moorePenroseInverse A)
  have ha : 0 ≤ a := specNorm_nonneg _
  refine ⟨1 / (a + 1), by positivity, ?_⟩
  intro E hE
  have he : 0 ≤ specNorm E := specNorm_nonneg _
  have hsmall : a * specNorm E < 1 := by
    have h := (lt_div_iff₀ (show 0 < a + 1 by positivity)).mp hE
    nlinarith
  have hB := rank_add_eq_card_of_pinv_mul_specNorm_lt_one hA hsmall
  let P := A * moorePenroseInverse A
  let Q := (A + E) * moorePenroseInverse (A + E)
  let Ny := Real.sqrt ((P *ᵥ b) ⬝ᵥ (P *ᵥ b))
  let Nb := Real.sqrt (b ⬝ᵥ b)
  have hRHS : 0 ≤ (conditionNumber A / leastSquaresCos A b + ε) *
      (specNorm E / specNorm A) := by
    unfold leastSquaresCos
    have hκ := conditionNumber_nonneg A
    have hM := specNorm_nonneg A
    positivity
  by_cases hy : P *ᵥ b = 0
  · change _ / Ny ≤ _
    have hNy : Ny = 0 := by simp [Ny, hy]
    rw [hNy, div_zero]
    exact hRHS
  have hb : b ≠ 0 := by
    intro hz
    exact hy (by rw [hz, Matrix.mulVec_zero])
  have hA0 : A ≠ 0 := by
    intro hz
    exact hy (by simp [P, hz])
  have hM : 0 < specNorm A := by
    rw [specNorm_eq_norm]
    exact norm_pos_iff.mpr hA0
  have hNy : 0 < Ny := by
    dsimp [Ny]
    rw [sqrt_dotProduct_self_eq_norm]
    exact norm_pos_iff.mpr (fun hz => hy (congrArg WithLp.ofLp hz))
  have hNb : 0 < Nb := by
    dsimp [Nb]
    rw [sqrt_dotProduct_self_eq_norm]
    exact norm_pos_iff.mpr (fun hz => hb (congrArg WithLp.ofLp hz))
  have hgap : specNorm (Q - P) ≤ a * specNorm E := by
    rw [specNorm_sub_comm]
    have h := specNorm_sub_columnProjector_le_pinv_mul_specNorm
      (A := A) (B := A + E) (hA.trans hB.symm)
    simpa only [add_sub_cancel_left] using h
  have hdiff : Q *ᵥ b - P *ᵥ b = (Q - P) *ᵥ b := (Matrix.sub_mulVec Q P b).symm
  have hbound : Real.sqrt ((Q *ᵥ b - P *ᵥ b) ⬝ᵥ (Q *ᵥ b - P *ᵥ b)) ≤
      a * specNorm E * Nb := by
    rw [hdiff]
    exact (sqrt_mulVec_dotProduct_le_specNorm_mul (Q - P) b).trans
      (mul_le_mul_of_nonneg_right hgap hNb.le)
  have hcoeff : a * specNorm E * Nb / Ny =
      conditionNumber A / leastSquaresCos A b * (specNorm E / specNorm A) := by
    unfold conditionNumber leastSquaresCos
    change a * specNorm E * Nb / Ny =
      specNorm A * a / (Ny / Nb) * (specNorm E / specNorm A)
    field_simp
  change _ / Ny ≤ _
  calc
    _ ≤ a * specNorm E * Nb / Ny := div_le_div_of_nonneg_right hbound hNy.le
    _ = conditionNumber A / leastSquaresCos A b * (specNorm E / specNorm A) := hcoeff
    _ ≤ (conditionNumber A / leastSquaresCos A b + ε) * (specNorm E / specNorm A) :=
      mul_le_mul_of_nonneg_right (by linarith) (div_nonneg he hM.le)

/-- **Least squares, `x` under perturbation of `A` (first order).** The solution sensitivity
under a pure matrix perturbation has coefficient `κ+κ² tan θ/η`, in epsilon–delta form.
Trefethen–Bau 1997, Theorem 18.1 (fourth entry); Golub–Van Loan 2013, Thm 5.3.1 (first-order
`κ² tan θ` form); the finite pseudoinverse denominator is absorbed in the prescribed epsilon.
atlas: least-squares-perturbation (partial) -/
theorem exists_pos_forall_sqrt_pinv_solution_sub_div_le (A : Matrix m n ℝ)
    (hA : A.rank = Fintype.card n) (b : m → ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ E : Matrix m n ℝ, specNorm E < δ →
      Real.sqrt ((moorePenroseInverse (A + E) *ᵥ b - moorePenroseInverse A *ᵥ b) ⬝ᵥ
          (moorePenroseInverse (A + E) *ᵥ b - moorePenroseInverse A *ᵥ b)) /
        Real.sqrt ((moorePenroseInverse A *ᵥ b) ⬝ᵥ (moorePenroseInverse A *ᵥ b)) ≤
        (conditionNumber A + conditionNumber A ^ 2 * leastSquaresTan A b / leastSquaresEta A b +
          ε) * (specNorm E / specNorm A) := by
  intro ε hε
  let a := specNorm (moorePenroseInverse A)
  let C := conditionNumber A + conditionNumber A ^ 2 * leastSquaresTan A b / leastSquaresEta A b
  have ha : 0 ≤ a := specNorm_nonneg _
  have hC : 0 ≤ C := by
    dsimp [C]
    unfold leastSquaresTan leastSquaresEta
    have hκ := conditionNumber_nonneg A
    have hM := specNorm_nonneg A
    positivity
  by_cases hx : moorePenroseInverse A *ᵥ b = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro E _
    simp only [hx, dotProduct_zero, Real.sqrt_zero, div_zero]
    change 0 ≤ (C + ε) * (specNorm E / specNorm A)
    exact mul_nonneg (add_nonneg hC hε.le) (div_nonneg (specNorm_nonneg _) (specNorm_nonneg _))
  let x := moorePenroseInverse A *ᵥ b
  let r := b - A *ᵥ x
  let X := Real.sqrt (x ⬝ᵥ x)
  let R := Real.sqrt (r ⬝ᵥ r)
  let Y := Real.sqrt (((A * moorePenroseInverse A) *ᵥ b) ⬝ᵥ
    ((A * moorePenroseInverse A) *ᵥ b))
  have hX : 0 < X := by
    dsimp [X, x]
    rw [sqrt_dotProduct_self_eq_norm]
    exact norm_pos_iff.mpr (fun hz => hx (congrArg WithLp.ofLp hz))
  have hx' : (moorePenroseInverse A).toEuclideanLin (WithLp.toLp 2 b) ≠ 0 := by
    intro hz
    exact hx (congrArg WithLp.ofLp hz)
  have hM : 0 < specNorm A := specNorm_pos_of_pinv_solution_ne_zero hA (WithLp.toLp 2 b) hx'
  have hY : 0 < Y := by
    have h := (pinv_solution_norm_pos hA (WithLp.toLp 2 b) hx').1
    simpa only [norm_eq_sqrt_dotProduct, Matrix.toEuclideanLin, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec] using h
  have hcoeff : C = specNorm A * a + specNorm A * a ^ 2 * R / X := by
    dsimp [C]
    unfold conditionNumber leastSquaresTan leastSquaresEta
    have hr : b - (A * moorePenroseInverse A) *ᵥ b = r := by
      dsimp [r, x]
      rw [Matrix.mulVec_mulVec]
    rw [hr]
    change specNorm A * a + (specNorm A * a) ^ 2 * (R / Y) /
      (specNorm A * X / Y) = _
    field_simp
  refine ⟨min (1 / (2 * (a + 1))) (ε / (2 * (a + 1) * (C + ε + 1))),
    lt_min (by positivity) (by positivity), ?_⟩
  intro E hE
  let e := specNorm E
  have he : 0 ≤ e := specNorm_nonneg _
  have hsmall : a * e < 1 := by
    have h := (lt_div_iff₀ (show 0 < 2 * (a + 1) by positivity)).mp
      (hE.trans_le (min_le_left _ _))
    nlinarith
  have hgap : 0 < 1 - a * e := sub_pos.mpr hsmall
  have hprod : (C + ε) * (a * e) ≤ ε := by
    have h := (lt_div_iff₀ (show 0 < 2 * (a + 1) * (C + ε + 1) by positivity)).mp
      (hE.trans_le (min_le_right _ _))
    have h1 : a * e ≤ (a + 1) * e := mul_le_mul_of_nonneg_right (by linarith) he
    have h2 : (C + ε) * (a * e) ≤ (C + ε + 1) * ((a + 1) * e) :=
      mul_le_mul (by linarith) h1 (mul_nonneg ha he) (by positivity)
    nlinarith
  have hden : C / (1 - a * e) ≤ C + ε := by
    apply (div_le_iff₀ hgap).mpr
    nlinarith
  have hdirect :
      Real.sqrt ((moorePenroseInverse (A + E) *ᵥ b - x) ⬝ᵥ
        (moorePenroseInverse (A + E) *ᵥ b - x)) ≤
      specNorm (moorePenroseInverse (A + E)) * (e * X + a * e * R) := by
    have h := norm_least_squares_sub_le_pinv hA hsmall (WithLp.toLp 2 b) 0
    simpa only [add_zero, norm_zero, zero_add, norm_eq_sqrt_dotProduct,
      WithLp.ofLp_sub, Matrix.toEuclideanLin, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, WithLp.ofLp_toLp] using h
  have hbound := hdirect.trans (mul_le_mul_of_nonneg_right
    (specNorm_pinv_add_le_of_rank_eq_card hA hsmall)
    (add_nonneg (mul_nonneg he hX.le) (mul_nonneg (mul_nonneg ha he) (Real.sqrt_nonneg _))))
  have halg : (a / (1 - a * e) * (e * X + a * e * R)) / X =
      C / (1 - a * e) * (e / specNorm A) := by
    rw [hcoeff]
    field_simp
  change _ / X ≤ (C + ε) * (e / specNorm A)
  calc
    _ ≤ (a / (1 - a * e) * (e * X + a * e * R)) / X :=
      div_le_div_of_nonneg_right hbound hX.le
    _ = C / (1 - a * e) * (e / specNorm A) := halg
    _ ≤ (C + ε) * (e / specNorm A) :=
      mul_le_mul_of_nonneg_right hden (div_nonneg he hM.le)

end NLAlib
