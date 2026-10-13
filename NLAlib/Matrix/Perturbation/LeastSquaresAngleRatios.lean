import NLAlib.Matrix.Perturbation.LeastSquaresPerturbation
import NLAlib.Matrix.Perturbation.LeastSquaresAngle
import NLAlib.Matrix.Perturbation.LeastSquaresEuclidean
import NLAlib.Matrix.Perturbation.LeastSquaresScalar
/-!
# Complete full-rank least-squares perturbation contract

 unique least-squares solutions, rank preservation, the exact finite
relative error and residual bounds, and the geometric angle coefficient with
an explicit quadratic first-order remainder. Source: Higham, Theorem 20.1;
Wedin 1973, §5; Golub–Van Loan, Theorem 5.3.1.
Atlas target: `least-squares-perturbation`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- A nonzero full-rank least-squares solution forces a positive matrix
spectral norm. Higham, Theorem 20.1; supports relative least-squares bounds. -/
theorem specNorm_pos_of_pinv_solution_ne_zero {A : Matrix m n ℝ}
    (hA : A.rank=Fintype.card n) (b : EuclideanSpace ℝ m)
    (hx : (moorePenroseInverse A).toEuclideanLin b ≠ 0) : 0 < specNorm A := by
  have hfit := (pinv_solution_norm_pos hA b hx).1
  have hbound := norm_toEuclideanLin_apply_le A ((moorePenroseInverse A).toEuclideanLin b)
  by_contra h
  have hz : specNorm A=0 := le_antisymm (le_of_not_gt h) (specNorm_nonneg A)
  rw [hz,zero_mul] at hbound
  linarith

open scoped Matrix.Norms.L2Operator in
/-- The exact advertised relative solution-error coefficient for the Moore–Penrose least-squares solutions. Higham, Theorem 20.1; Wedin §5.
atlas: least-squares-perturbation (partial) -/
theorem norm_least_squares_sub_div_le {A E : Matrix m n ℝ} {ε : ℝ}
    (hA : A.rank=Fintype.card n) (b f : EuclideanSpace ℝ m)
    (hx : (moorePenroseInverse A).toEuclideanLin b ≠ 0) (hε : 0 ≤ ε)
    (hE : specNorm E ≤ ε*specNorm A) (hf : ‖f‖ ≤ ε*‖b‖)
    (hsmall : moorePenroseConditionNumber A*ε < 1) :
    let x := (moorePenroseInverse A).toEuclideanLin b
    let y := (moorePenroseInverse (A+E)).toEuclideanLin (b+f)
    let r := b-A.toEuclideanLin x
    ‖y-x‖/‖x‖ ≤ moorePenroseConditionNumber A*ε/(1-moorePenroseConditionNumber A*ε)*
      (2+(moorePenroseConditionNumber A+1)*‖r‖/(specNorm A*‖x‖)) := by
  intro x y r
  have hb : ‖b‖ ≤ specNorm A*‖x‖+‖r‖ := by
    calc
      ‖b‖ = ‖A.toEuclideanLin x+r‖ := by congr 1; dsimp only [r]; abel
      _ ≤ ‖A.toEuclideanLin x‖+‖r‖ := norm_add_le _ _
      _ ≤ specNorm A*‖x‖+‖r‖ :=
        add_le_add (norm_toEuclideanLin_apply_le A x) (le_refl ‖r‖)
  have hQ := norm_least_squares_sub_le_relative_data hA hε hE b f hf hsmall
  exact least_squares_forward_ratio_le
    (specNorm_pos_of_pinv_solution_ne_zero hA b hx) (norm_pos_iff.mpr hx)
    (specNorm_nonneg _) (norm_nonneg r) (norm_nonneg b) hε hsmall hb hQ

open scoped Matrix.Norms.L2Operator in
/-- The residual relative error admits the stronger coefficient `1+κ`.
Higham, Theorem 20.1; Wedin §5.
atlas: least-squares-perturbation (partial) -/
theorem norm_least_squares_residual_sub_div_le {A E : Matrix m n ℝ} {ε : ℝ}
    (hA : A.rank=Fintype.card n) (b f : EuclideanSpace ℝ m) (hb : b ≠ 0)
    (hE : specNorm E ≤ ε*specNorm A) (hf : ‖f‖ ≤ ε*‖b‖)
    (hsmall : moorePenroseConditionNumber A*ε < 1) :
    let r := b-A.toEuclideanLin ((moorePenroseInverse A).toEuclideanLin b)
    let s := (b+f)-(A+E).toEuclideanLin ((moorePenroseInverse (A+E)).toEuclideanLin (b+f))
    ‖r-s‖/‖b‖ ≤ (1+moorePenroseConditionNumber A)*ε := by
  intro r s
  apply (div_le_iff₀ (norm_pos_iff.mpr hb)).mpr
  exact norm_least_squares_residual_sub_le_relative_data hA hE b f hf hsmall

open scoped Matrix.Norms.L2Operator in
/-- The first-order angle coefficient, with finite denominator, follows from
the fitted-vector length. Golub–Van Loan, Theorem 5.3.1.
atlas: least-squares-perturbation (partial) -/
theorem norm_least_squares_sub_div_le_angle_ratios {A E : Matrix m n ℝ} {ε : ℝ}
    (hA : A.rank=Fintype.card n) (b f : EuclideanSpace ℝ m)
    (hx : (moorePenroseInverse A).toEuclideanLin b ≠ 0) (hε : 0 ≤ ε)
    (hE : specNorm E ≤ ε*specNorm A) (hf : ‖f‖ ≤ ε*‖b‖)
    (hsmall : moorePenroseConditionNumber A*ε < 1) :
    let x := (moorePenroseInverse A).toEuclideanLin b
    let y := (moorePenroseInverse (A+E)).toEuclideanLin (b+f)
    let r := b-A.toEuclideanLin x
    ‖y-x‖/‖x‖ ≤ ε*(2*moorePenroseConditionNumber A/(‖A.toEuclideanLin x‖/‖b‖)+
      moorePenroseConditionNumber A^2*(‖r‖/‖A.toEuclideanLin x‖))/(1-moorePenroseConditionNumber A*ε) := by
  intro x y r
  obtain ⟨hL,hb⟩ := pinv_solution_norm_pos hA b hx
  exact least_squares_forward_angle_coefficient_le
    (specNorm_pos_of_pinv_solution_ne_zero hA b hx) (norm_pos_iff.mpr hx)
    (specNorm_nonneg _) (norm_nonneg r) hb hε hsmall hL
    (norm_toEuclideanLin_apply_le A x) (norm_pinv_fit_le_norm_data A b)
    (norm_least_squares_sub_le_relative_data hA hε hE b f hf hsmall)

open scoped Matrix.Norms.L2Operator in
/-- The geometric least-squares angle gives the source first-order
coefficient and the explicit remainder `2κ C ε²` for `ε≤1/(2κ)`.
Golub–Van Loan, Theorem 5.3.1.
atlas: least-squares-perturbation (partial) -/
theorem exists_least_squares_angle_error_bound {A E : Matrix m n ℝ} {ε : ℝ}
    (hA : A.rank=Fintype.card n) (b f : EuclideanSpace ℝ m)
    (hx : (moorePenroseInverse A).toEuclideanLin b ≠ 0) (hε : 0 ≤ ε)
    (hE : specNorm E ≤ ε*specNorm A) (hf : ‖f‖ ≤ ε*‖b‖)
    (hsmall : moorePenroseConditionNumber A*ε < 1) :
    let x := (moorePenroseInverse A).toEuclideanLin b
    let y := (moorePenroseInverse (A+E)).toEuclideanLin (b+f)
    let r := b-A.toEuclideanLin x
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < Real.pi/2 ∧
      Real.cos θ=‖A.toEuclideanLin x‖/‖b‖ ∧
      Real.sin θ=‖r‖/‖b‖ ∧ Real.tan θ=‖r‖/‖A.toEuclideanLin x‖ ∧
      (let C := 2*moorePenroseConditionNumber A/Real.cos θ+moorePenroseConditionNumber A^2*Real.tan θ
       ‖y-x‖/‖x‖ ≤ ε*C/(1-moorePenroseConditionNumber A*ε) ∧
       (ε ≤ 1/(2*moorePenroseConditionNumber A) →
         ‖y-x‖/‖x‖ ≤ ε*C+2*moorePenroseConditionNumber A*C*ε^2)) := by
  intro x y r
  obtain ⟨θ,hθ,hθ',hc,hs,ht⟩ := exists_least_squares_angle hA b hx
  have hbound := norm_least_squares_sub_div_le_angle_ratios hA b f hx hε hE hf hsmall
  have hC : 0 ≤ 2*moorePenroseConditionNumber A/Real.cos θ+moorePenroseConditionNumber A^2*Real.tan θ := by
    have hκ := moorePenroseConditionNumber_nonneg A
    rw [hc,ht]
    positivity
  refine ⟨θ,hθ,hθ',hc,hs,ht,?_,?_⟩
  · simpa only [hc,ht] using hbound
  · intro hhalf
    have hκpos : 0 < moorePenroseConditionNumber A := by
      have hA0 : A ≠ 0 := by
        intro hz
        have hnorm := specNorm_pos_of_pinv_solution_ne_zero hA b hx
        rw [hz,specNorm_zero] at hnorm
        linarith
      have hκ := one_le_moorePenroseConditionNumber hA0
      linarith
    have hhalf' : moorePenroseConditionNumber A*ε ≤ 1/2 := by
      have h := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hκpos)).mp hhalf
      nlinarith
    have he := first_order_reciprocal_bound_le (moorePenroseConditionNumber_nonneg A) hC hε hhalf'
    apply (show ‖y-x‖/‖x‖ ≤ ε*(2*moorePenroseConditionNumber A/Real.cos θ+
      moorePenroseConditionNumber A^2*Real.tan θ)/(1-moorePenroseConditionNumber A*ε) from by
        simpa only [hc,ht] using hbound).trans he

end NLAlib
