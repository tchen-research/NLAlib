import NLAlib.Matrix.Perturbation.DistanceToSingularity
import NLAlib.Matrix.Perturbation.LeastSquaresPurePerturbation
/-!
# Sensitivity of linear systems and least squares

* Condition number (`conditionNumber`, `moorePenroseConditionNumber`, their API and the distance
 to singularity live in `NLAlib.Matrix.Perturbation.ConditionNumber` and
 `…DistanceToSingularity`): here `κ⁺(A) = ‖A‖₂/σ_min(A)` under full column rank
 (`moorePenroseConditionNumber_eq_specNorm_div_singularValues_last`). Golub–Van Loan 2013,
 §5.3.2. Atlas: `condition-number-def`.
* Linear systems (Trefethen–Bau 1997, Thm 12.1–12.2; Higham 2002, Thm 7.2; Golub–Van Loan
 2013, Thm 2.6.2): perturbation of `b`, the a posteriori residual bound, and the joint bound
 `‖Δx‖/‖x‖ ≤ κ/(1 - κ‖ΔA‖/‖A‖) (‖ΔA‖/‖A‖ + ‖Δb‖/‖b‖)` under `κ‖ΔA‖/‖A‖ < 1`, all with
 `κ = (conditionNumber A).toReal` for invertible `A`. Atlas: `linear-system-perturbation`.
* Least squares (Trefethen–Bau 1997, Thm 18.1, with its `κ, θ, η`; Higham 2002, Thm 20.1):
 the two exact bounds for perturbations of `b` (any rank, with the pseudoinverse condition
 number). The first-order bounds for perturbations of `A` and Higham's non-asymptotic bounds
 are `exists_pos_forall_sqrt_pinv_fit_sub_div_le`, `exists_pos_forall_sqrt_pinv_solution_sub_div_le`
 (`…LeastSquaresPurePerturbation`), `sqrt_pinv_solution_sub_div_le` and
 `sqrt_pinv_residual_sub_div_le` (`…LeastSquaresCoordinateBounds`).
 Atlas: `least-squares-perturbation`.

Euclidean vector norms are written `‖WithLp.toLp 2 v‖`. Exact arithmetic only.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

/-! ### The pseudoinverse condition number at full column rank -/

section Def

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- Under full column rank (`rank A = card n ≥ 1`), `κ⁺(A) = ‖A‖₂ / σ_min(A)` with
`σ_min(A) = singularValues A (card n - 1)`; this covers invertible square `A`.
Golub–Van Loan 2013, §5.3.2 (`κ₂(A) = σ₁/σ_n`); Trefethen–Bau 1997, eq. (12.14).
atlas: condition-number-def -/
theorem moorePenroseConditionNumber_eq_specNorm_div_singularValues_last (A : Matrix m n 𝕜)
    (hn : 0 < Fintype.card n) (hA : A.rank = Fintype.card n) :
    moorePenroseConditionNumber A = specNorm A / singularValues A (Fintype.card n - 1) := by
  rw [moorePenroseConditionNumber,
    specNorm_moorePenroseInverse_eq_inv_singularValues_last_positive A (by omega), hA,
    mul_one_div]

end Def

/-! ### Linear systems -/

section LinearSystem

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **A posteriori error bound.** For invertible `A`, `A x = b ≠ 0` and any `x̂`,
`‖x - x̂‖/‖x‖ ≤ κ₂(A) ‖b - A x̂‖/‖b‖`. Higham 2002, eq. (7.4) / Thm 7.2 discussion;
Golub–Van Loan 2013, §3.5.3; Trefethen–Bau 1997, Thm 12.1 (eq. (12.15)).
atlas: linear-system-perturbation -/
theorem norm_sub_div_le_conditionNumber_mul {A : Matrix n n ℝ} (hA : IsUnit A)
    {x b : n → ℝ} (hx : A *ᵥ x = b) (hb : b ≠ 0) (x' : n → ℝ) :
    ‖WithLp.toLp 2 (x - x')‖ / ‖WithLp.toLp 2 x‖ ≤
      (conditionNumber A).toReal * (‖WithLp.toLp 2 (b - A *ᵥ x')‖ / ‖WithLp.toLp 2 b‖) := by
  simp only [← sqrt_dotProduct_self_eq_norm]
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  rw [conditionNumber_toReal_of_isUnit hA]
  have hbpos : 0 < Real.sqrt (b ⬝ᵥ b) := sqrt_dotProduct_self_pos hb
  have hbx : Real.sqrt (b ⬝ᵥ b) ≤ specNorm A * Real.sqrt (x ⬝ᵥ x) := by
    rw [← hx]; exact sqrt_mulVec_dotProduct_le_specNorm_mul A x
  have hxpos : 0 < Real.sqrt (x ⬝ᵥ x) := by
    rcases (Real.sqrt_nonneg (x ⬝ᵥ x)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hbx; linarith
  have hdiff : x - x' = A⁻¹ *ᵥ (b - A *ᵥ x') := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec,
      ← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]
  have h1 : Real.sqrt ((x - x') ⬝ᵥ (x - x')) ≤
      specNorm A⁻¹ * Real.sqrt ((b - A *ᵥ x') ⬝ᵥ (b - A *ᵥ x')) := by
    rw [hdiff]; exact sqrt_mulVec_dotProduct_le_specNorm_mul _ _
  rw [div_le_iff₀ hxpos]
  set R := Real.sqrt ((b - A *ᵥ x') ⬝ᵥ (b - A *ᵥ x'))
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hAi := specNorm_nonneg A⁻¹
  calc Real.sqrt ((x - x') ⬝ᵥ (x - x')) ≤ specNorm A⁻¹ * R := h1
    _ = specNorm A⁻¹ * R / Real.sqrt (b ⬝ᵥ b) * Real.sqrt (b ⬝ᵥ b) := by field_simp
    _ ≤ specNorm A⁻¹ * R / Real.sqrt (b ⬝ᵥ b) * (specNorm A * Real.sqrt (x ⬝ᵥ x)) :=
        mul_le_mul_of_nonneg_left hbx (by positivity)
    _ = specNorm A * specNorm A⁻¹ * (R / Real.sqrt (b ⬝ᵥ b)) * Real.sqrt (x ⬝ᵥ x) := by ring

/-- **Perturbation of the right-hand side.** For invertible `A`, `A x = b ≠ 0` and
`A (x + Δx) = b + Δb`: `‖Δx‖/‖x‖ ≤ κ₂(A) ‖Δb‖/‖b‖`. Trefethen–Bau 1997, Thm 12.1 (condition
number of `b ↦ x` is at most `κ(A)`); Golub–Van Loan 2013, Thm 2.6.2 with `ΔA = 0`.
atlas: linear-system-perturbation -/
theorem norm_div_le_conditionNumber_mul_of_mulVec_add {A : Matrix n n ℝ}
    (hA : IsUnit A) {x b Δx Δb : n → ℝ} (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hΔ : A *ᵥ (x + Δx) = b + Δb) :
    ‖WithLp.toLp 2 Δx‖ / ‖WithLp.toLp 2 x‖ ≤
      (conditionNumber A).toReal * (‖WithLp.toLp 2 Δb‖ / ‖WithLp.toLp 2 b‖) := by
  have h := norm_sub_div_le_conditionNumber_mul hA hx hb (x + Δx)
  have e1 : x - (x + Δx) = -Δx := by abel
  have e2 : b - A *ᵥ (x + Δx) = -Δb := by rw [hΔ]; abel
  rwa [e1, e2, WithLp.toLp_neg, WithLp.toLp_neg, norm_neg, norm_neg] at h

/-- **Perturbation of a linear system.** For invertible `A`, `A x = b ≠ 0`,
`(A + ΔA)(x + Δx) = b + Δb` and `κ₂(A) ‖ΔA‖/‖A‖ < 1`:
`‖Δx‖/‖x‖ ≤ κ₂(A)/(1 - κ₂(A)‖ΔA‖/‖A‖) · (‖ΔA‖/‖A‖ + ‖Δb‖/‖b‖)`.
Higham 2002, Thm 7.2 (normwise, with `ε = ‖ΔA‖/‖A‖`-type tolerances); Golub–Van Loan 2013,
Thm 2.6.2; the first-order content is Trefethen–Bau 1997, Thm 12.1–12.2. Proof: `A Δx = Δb -
ΔA (x + Δx)`, so `‖Δx‖ ≤ ‖A⁻¹‖(‖Δb‖ + ‖ΔA‖‖x‖ + ‖ΔA‖‖Δx‖)`; absorb the last term, then use
`‖b‖ ≤ ‖A‖‖x‖`. (`A + ΔA` is then invertible by `isUnit_add_of_specNorm_inv_mul_lt_one`, so
`Δx` is determined.)
atlas: linear-system-perturbation -/
theorem norm_div_le_of_add_mulVec_add {A ΔA : Matrix n n ℝ} (hA : IsUnit A)
    {x b Δx Δb : n → ℝ} (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hΔ : (A + ΔA) *ᵥ (x + Δx) = b + Δb)
    (hsmall : (conditionNumber A).toReal * (specNorm ΔA / specNorm A) < 1) :
    ‖WithLp.toLp 2 Δx‖ / ‖WithLp.toLp 2 x‖ ≤
      (conditionNumber A).toReal /
          (1 - (conditionNumber A).toReal * (specNorm ΔA / specNorm A)) *
        (specNorm ΔA / specNorm A + ‖WithLp.toLp 2 Δb‖ / ‖WithLp.toLp 2 b‖) := by
  simp only [← sqrt_dotProduct_self_eq_norm]
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  rw [conditionNumber_toReal_of_isUnit hA] at hsmall ⊢
  have hbx : Real.sqrt (b ⬝ᵥ b) ≤ specNorm A * Real.sqrt (x ⬝ᵥ x) := by
    rw [← hx]; exact sqrt_mulVec_dotProduct_le_specNorm_mul A x
  have hdx : Δx = A⁻¹ *ᵥ (Δb - ΔA *ᵥ (x + Δx)) := by
    have hAdx : A *ᵥ Δx = Δb - ΔA *ᵥ (x + Δx) := by
      rw [Matrix.add_mulVec, Matrix.mulVec_add A, hx] at hΔ
      rw [eq_sub_iff_add_eq, ← add_right_inj b, ← hΔ]
      abel
    rw [← hAdx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]
  have s1 : Real.sqrt (Δx ⬝ᵥ Δx) ≤
      specNorm A⁻¹ * Real.sqrt ((Δb - ΔA *ᵥ (x + Δx)) ⬝ᵥ (Δb - ΔA *ᵥ (x + Δx))) := by
    conv_lhs => rw [hdx]
    exact sqrt_mulVec_dotProduct_le_specNorm_mul _ _
  have s2 := sqrt_dotProduct_sub_le Δb (ΔA *ᵥ (x + Δx))
  have s3 := sqrt_mulVec_dotProduct_le_specNorm_mul ΔA (x + Δx)
  have s4 := sqrt_dotProduct_add_le x Δx
  set a := specNorm A⁻¹
  set α := specNorm A
  set e := specNorm ΔA
  set Nx := Real.sqrt (x ⬝ᵥ x)
  set Nb := Real.sqrt (b ⬝ᵥ b)
  set Ndx := Real.sqrt (Δx ⬝ᵥ Δx)
  set Ndb := Real.sqrt (Δb ⬝ᵥ Δb)
  have ha : 0 ≤ a := specNorm_nonneg _
  have he : 0 ≤ e := specNorm_nonneg _
  have hNdx : 0 ≤ Ndx := Real.sqrt_nonneg _
  have hNdb : 0 ≤ Ndb := Real.sqrt_nonneg _
  have hbpos : 0 < Nb := sqrt_dotProduct_self_pos hb
  have hxpos : 0 < Nx := by
    rcases (show 0 ≤ Nx from Real.sqrt_nonneg _).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hbx; linarith
  have hαpos : 0 < α := by
    rcases (show 0 ≤ α from specNorm_nonneg _).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hbx; linarith
  have hae : α * a * (e / α) = a * e := by field_simp
  rw [hae] at hsmall ⊢
  have h1 : Ndx ≤ a * (Ndb + e * Nx + e * Ndx) := by
    calc Ndx ≤ a * Real.sqrt ((Δb - ΔA *ᵥ (x + Δx)) ⬝ᵥ (Δb - ΔA *ᵥ (x + Δx))) := s1
      _ ≤ a * (Ndb + e * (Nx + Ndx)) := by
          apply mul_le_mul_of_nonneg_left _ ha
          refine s2.trans (add_le_add le_rfl (s3.trans ?_))
          exact mul_le_mul_of_nonneg_left s4 he
      _ = a * (Ndb + e * Nx + e * Ndx) := by ring
  have hgap : 0 < 1 - a * e := by linarith
  have h2 : Ndx * (1 - a * e) ≤ a * (Ndb + e * Nx) := by nlinarith
  have h3 : Ndb / Nx ≤ α * (Ndb / Nb) := by
    rw [div_le_iff₀ hxpos]
    calc Ndb = Ndb / Nb * Nb := by field_simp
      _ ≤ Ndb / Nb * (α * Nx) := mul_le_mul_of_nonneg_left hbx (by positivity)
      _ = α * (Ndb / Nb) * Nx := by ring
  rw [div_le_iff₀ hxpos]
  have h4 : Ndx ≤ a * (Ndb + e * Nx) / (1 - a * e) := by
    rw [le_div_iff₀ hgap]; exact h2
  calc Ndx ≤ a * (Ndb + e * Nx) / (1 - a * e) := h4
    _ = a / (1 - a * e) * (Ndb / Nx + e) * Nx := by field_simp
    _ ≤ a / (1 - a * e) * (α * (Ndb / Nb) + e) * Nx := by
        apply mul_le_mul_of_nonneg_right _ hxpos.le
        exact mul_le_mul_of_nonneg_left (add_le_add h3 le_rfl) (div_nonneg ha hgap.le)
    _ = α * a / (1 - a * e) * (e / α + Ndb / Nb) * Nx := by field_simp; ring

end LinearSystem

/-! ### Least squares -/

section LeastSquares

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq n] in
/-- **Least squares, `y` under perturbation of `b`.** For `y = A A⁺ b` and any `Δb`:
`‖Δy‖/‖y‖ ≤ (1/cos θ) ‖Δb‖/‖b‖`, where `Δy = A A⁺ Δb`. Exact (the map `b ↦ y` is linear), any
rank, no side conditions (degenerate cases are `0 ≤ ·`). Trefethen–Bau 1997, Thm 18.1 (first
entry of the table: condition number `1/cos θ`).
atlas: least-squares-perturbation (partial) -/
theorem norm_mul_moorePenroseInverse_sub_div_le (A : Matrix m n ℝ) (b Δb : m → ℝ) :
    ‖WithLp.toLp 2 ((A * moorePenroseInverse A) *ᵥ (b + Δb) -
        (A * moorePenroseInverse A) *ᵥ b)‖ /
      ‖WithLp.toLp 2 ((A * moorePenroseInverse A) *ᵥ b)‖ ≤
      1 / leastSquaresCos A b * (‖WithLp.toLp 2 Δb‖ / ‖WithLp.toLp 2 b‖) := by
  simp only [← sqrt_dotProduct_self_eq_norm]
  set P := A * moorePenroseInverse A
  set Ny := Real.sqrt ((P *ᵥ b) ⬝ᵥ (P *ᵥ b))
  set Nb := Real.sqrt (b ⬝ᵥ b)
  set Ndb := Real.sqrt (Δb ⬝ᵥ Δb)
  have hP : specNorm P ≤ 1 :=
    Matrix.IsHermitian.specNorm_le_one_of_isIdempotentElem (mul_moorePenroseInverse_isHermitian A)
      (mul_moorePenroseInverse_isIdempotentElem A)
  have hdy : P *ᵥ (b + Δb) - P *ᵥ b = P *ᵥ Δb := by rw [Matrix.mulVec_add]; abel
  rw [hdy]
  have h1 : Real.sqrt ((P *ᵥ Δb) ⬝ᵥ (P *ᵥ Δb)) ≤ Ndb :=
    (sqrt_mulVec_dotProduct_le_specNorm_mul P Δb).trans
      (by have := Real.sqrt_nonneg (Δb ⬝ᵥ Δb); nlinarith)
  have hcos : leastSquaresCos A b = Ny / Nb := rfl
  rw [hcos]
  rcases (show 0 ≤ Nb from Real.sqrt_nonneg _).lt_or_eq with hb | hb
  · rcases (show 0 ≤ Ny from Real.sqrt_nonneg _).lt_or_eq with hy | hy
    · have : 1 / (Ny / Nb) * (Ndb / Nb) = Ndb / Ny := by
        field_simp
      rw [this]
      exact div_le_div_of_nonneg_right h1 hy.le
    · simp only [Ny, ← hy, div_zero]
      positivity
  · simp only [Ny, Nb, ← hb, div_zero, mul_zero]
    have hb0 : b = 0 := dotProduct_self_eq_zero.mp ((Real.sqrt_eq_zero
      (dotProduct_self_nonneg b)).mp hb.symm)
    rw [hb0, Matrix.mulVec_zero, dotProduct_zero, Real.sqrt_zero, div_zero]

omit [DecidableEq m] [DecidableEq n] in
/-- `x = A⁺ b ≠ 0` forces `A x ≠ 0` (`A⁺ A A⁺ = A⁺`). -/
theorem mulVec_moorePenroseInverse_mulVec_ne_zero {A : Matrix m n ℝ} {b : m → ℝ}
    (hx : moorePenroseInverse A *ᵥ b ≠ 0) : A *ᵥ (moorePenroseInverse A *ᵥ b) ≠ 0 := by
  intro h
  apply hx
  have := congrArg (fun v => moorePenroseInverse A *ᵥ v) h
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
  rwa [← Matrix.mul_assoc, moorePenroseInverse_mul_moorePenroseInverse] at this

open scoped Matrix.Norms.L2Operator in
/-- **Least squares, `x` under perturbation of `b`.** For `x = A⁺ b` and any `Δb`:
`‖Δx‖/‖x‖ ≤ κ⁺(A)/(η cos θ) · ‖Δb‖/‖b‖`, where `Δx = A⁺ Δb` and `κ⁺ = moorePenroseConditionNumber`.
Exact, any rank (`κ/(η cos θ)` equals `‖A⁺‖‖b‖/‖x‖` when `x ≠ 0`). Trefethen–Bau 1997, Thm 18.1
(second entry of the table).
atlas: least-squares-perturbation (partial) -/
theorem norm_moorePenroseInverse_sub_div_le (A : Matrix m n ℝ) (b Δb : m → ℝ) :
    ‖WithLp.toLp 2 (moorePenroseInverse A *ᵥ (b + Δb) - moorePenroseInverse A *ᵥ b)‖ /
      ‖WithLp.toLp 2 (moorePenroseInverse A *ᵥ b)‖ ≤
      moorePenroseConditionNumber A / (leastSquaresEta A b * leastSquaresCos A b) *
        (‖WithLp.toLp 2 Δb‖ / ‖WithLp.toLp 2 b‖) := by
  simp only [← sqrt_dotProduct_self_eq_norm]
  set A' := moorePenroseInverse A
  set x := A' *ᵥ b
  set P := A * A'
  set Nx := Real.sqrt (x ⬝ᵥ x)
  set Ny := Real.sqrt ((P *ᵥ b) ⬝ᵥ (P *ᵥ b))
  set Nb := Real.sqrt (b ⬝ᵥ b)
  set Ndb := Real.sqrt (Δb ⬝ᵥ Δb)
  have hdx : A' *ᵥ (b + Δb) - A' *ᵥ b = A' *ᵥ Δb := by rw [Matrix.mulVec_add]; abel
  rw [hdx]
  have h1 : Real.sqrt ((A' *ᵥ Δb) ⬝ᵥ (A' *ᵥ Δb)) ≤ specNorm A' * Ndb :=
    sqrt_mulVec_dotProduct_le_specNorm_mul A' Δb
  have hRHS : 0 ≤ moorePenroseConditionNumber A / (leastSquaresEta A b * leastSquaresCos A b) *
      (Ndb / Nb) := by
    unfold leastSquaresEta leastSquaresCos
    have := moorePenroseConditionNumber_nonneg A
    have := specNorm_nonneg A
    positivity
  by_cases hx : x = 0
  · have : Nx = 0 := by simp [Nx, hx]
    rw [this, div_zero]
    exact hRHS
  have hy : P *ᵥ b ≠ 0 := by
    have := mulVec_moorePenroseInverse_mulVec_ne_zero hx
    rwa [Matrix.mulVec_mulVec] at this
  have hb : b ≠ 0 := by rintro rfl; exact hy (Matrix.mulVec_zero _)
  have hA : A ≠ 0 := by rintro rfl; exact hy (by simp [P])
  have hNx : 0 < Nx := sqrt_dotProduct_self_pos hx
  have hNy : 0 < Ny := sqrt_dotProduct_self_pos hy
  have hNb : 0 < Nb := sqrt_dotProduct_self_pos hb
  have hα : 0 < specNorm A := by rw [specNorm_eq_norm]; exact norm_pos_iff.mpr hA
  have hconst : moorePenroseConditionNumber A / (leastSquaresEta A b * leastSquaresCos A b) =
      specNorm A' * Nb / Nx := by
    unfold leastSquaresEta leastSquaresCos moorePenroseConditionNumber
    change specNorm A * specNorm A' / (specNorm A * Nx / Ny * (Ny / Nb)) = _
    field_simp
  rw [hconst]
  calc Real.sqrt ((A' *ᵥ Δb) ⬝ᵥ (A' *ᵥ Δb)) / Nx ≤ specNorm A' * Ndb / Nx :=
        div_le_div_of_nonneg_right h1 hNx.le
    _ = specNorm A' * Nb / Nx * (Ndb / Nb) := by field_simp

end LeastSquares

end NLAlib
