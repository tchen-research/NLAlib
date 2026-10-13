import NLAlib.Matrix.Perturbation.LeastSquaresGeometry

/-!
# The geometric least-squares angle

The angle is derived from the orthogonal least-squares decomposition.
Golub–Van Loan, Theorem 5.3.1; supports `least-squares-perturbation`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- A nonzero full-rank Moore–Penrose solution has nonzero fitted value and
nonzero data. Golub–Van Loan, Theorem 5.3.1. -/
theorem pinv_solution_norm_pos {A : Matrix m n ℝ} (hA : A.rank=Fintype.card n)
    (b : EuclideanSpace ℝ m)
    (hx : (moorePenroseInverse A).toEuclideanLin b ≠ 0) :
    0 < ‖A.toEuclideanLin ((moorePenroseInverse A).toEuclideanLin b)‖ ∧ 0 < ‖b‖ := by
  constructor
  · apply norm_pos_iff.mpr
    intro hz
    have h := congrArg (fun v => (moorePenroseInverse A).toEuclideanLin v) hz
    rw [← toEuclideanLin_mul_apply,
      moorePenroseInverse_mul_eq_one_of_rank_eq_card hA, toEuclideanLin_one_apply,
      map_zero] at h
    exact hx h
  · apply norm_pos_iff.mpr
    intro hz
    apply hx
    rw [hz, map_zero]

open scoped Matrix.Norms.L2Operator in
/-- The fitted value and residual form an orthogonal decomposition
of the data. Golub–Van Loan, Theorem 5.3.1. -/
theorem norm_data_sq_eq_pinv_fit_sq_add_residual_sq (A : Matrix m n ℝ)
    (b : EuclideanSpace ℝ m) :
    ‖b‖^2 = ‖A.toEuclideanLin ((moorePenroseInverse A).toEuclideanLin b)‖^2+
      ‖b-A.toEuclideanLin ((moorePenroseInverse A).toEuclideanLin b)‖^2 := by
  have h := norm_pinv_residual_sq_add_eq A b 0
  simp only [map_zero, sub_zero, zero_sub, map_neg, norm_neg] at h
  linarith

open scoped Matrix.Norms.L2Operator in
/-- The least-squares fitted value has norm at most the data norm.
Orthogonal-projector contraction; supports the first-order least-squares bound. -/
theorem norm_pinv_fit_le_norm_data (A : Matrix m n ℝ) (b : EuclideanSpace ℝ m) :
    ‖A.toEuclideanLin ((moorePenroseInverse A).toEuclideanLin b)‖ ≤ ‖b‖ := by
  have h := norm_data_sq_eq_pinv_fit_sq_add_residual_sq A b
  nlinarith [sq_nonneg ‖b-A.toEuclideanLin ((moorePenroseInverse A).toEuclideanLin b)‖,
    norm_nonneg b, norm_nonneg (A.toEuclideanLin ((moorePenroseInverse A).toEuclideanLin b))]

open scoped Matrix.Norms.L2Operator in
/-- The least-squares angle lies in `[0,π/2)` and has the fitted and
residual norm ratios as cosine and sine. Its tangent is their ratio.
Golub–Van Loan, Theorem 5.3.1; no angle relations are assumed. -/
theorem exists_least_squares_angle {A : Matrix m n ℝ} (hA : A.rank=Fintype.card n)
    (b : EuclideanSpace ℝ m)
    (hx : (moorePenroseInverse A).toEuclideanLin b ≠ 0) :
    let x := (moorePenroseInverse A).toEuclideanLin b
    let r := b-A.toEuclideanLin x
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < Real.pi/2 ∧
      Real.cos θ = ‖A.toEuclideanLin x‖/‖b‖ ∧
      Real.sin θ = ‖r‖/‖b‖ ∧
      Real.tan θ = ‖r‖/‖A.toEuclideanLin x‖ := by
  intro x r
  obtain ⟨hL,hb⟩ := pinv_solution_norm_pos hA b hx
  have hcpos : 0 < ‖A.toEuclideanLin x‖/‖b‖ := div_pos hL hb
  have hcle : ‖A.toEuclideanLin x‖/‖b‖ ≤ 1 :=
    (div_le_one hb).mpr (norm_pinv_fit_le_norm_data A b)
  let θ := Real.arccos (‖A.toEuclideanLin x‖/‖b‖)
  have hcos : Real.cos θ=‖A.toEuclideanLin x‖/‖b‖ :=
    Real.cos_arccos (by linarith) hcle
  have hsin : Real.sin θ=‖r‖/‖b‖ := by
    rw [Real.sin_arccos]
    apply (Real.sqrt_eq_iff_mul_self_eq
      (by nlinarith [sq_nonneg (‖A.toEuclideanLin x‖/‖b‖),
        mul_nonneg hcpos.le (sub_nonneg.mpr hcle)])
      (div_nonneg (norm_nonneg _) hb.le)).mpr
    have hsq := norm_data_sq_eq_pinv_fit_sq_add_residual_sq A b
    change ‖b‖^2=‖A.toEuclideanLin x‖^2+‖r‖^2 at hsq
    field_simp [hb.ne']
    nlinarith
  refine ⟨θ, Real.arccos_nonneg _, ?_, hcos, hsin, ?_⟩
  · exact Real.arccos_lt_pi_div_two.mpr hcpos
  · rw [Real.tan_eq_sin_div_cos, hsin, hcos]
    field_simp [hb.ne', hL.ne']

end NLAlib
