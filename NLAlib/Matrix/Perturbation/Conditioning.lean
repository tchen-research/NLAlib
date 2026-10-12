import NLAlib.Matrix.Perturbation.InversePerturbation
import NLAlib.Matrix.Basic.LeastSquares
import NLAlib.Matrix.Perturbation.ConditionNumber
import NLAlib.Matrix.Perturbation.DistanceToSingularity
import NLAlib.Matrix.Perturbation.LeastSquaresPurePerturbation
/-!
# Condition numbers and the sensitivity of linear systems and least squares

* `conditionNumber A := ‖A‖₂ ‖A⁺‖₂` (`specNorm`, `moorePenroseInverse`): total, `0` at `A = 0`;
  `κ(A) = σ₁/σ_r` (`conditionNumber_eq_singularValues_div`), `κ(A) = ‖A‖₂/σ_min(A)` under full
  column rank (`conditionNumber_eq_div_sigmaMin`), `κ(A) = ‖A‖₂‖A⁻¹‖₂` for invertible `A`;
  `κ(A) ≥ 1` for `A ≠ 0`, invariance under transpose, nonzero scaling and orthonormal-column left
  factors, `κ(AᵀA) = κ(A)²`; distance to singularity (Gastinel–Kahan): `‖E‖₂ < 1/‖A⁻¹‖₂` keeps
  `A + E` invertible, and the bound is attained.
  Golub–Van Loan 2013, §2.6.2; Higham 2002, Thm 6.5. Atlas: `condition-number-def`.
* Linear systems (Trefethen–Bau 1997, Thm 12.1–12.2; Higham 2002, Thm 7.2; Golub–Van Loan
  2013, Thm 2.6.2): perturbation of `b`, the a posteriori residual bound, and the joint bound
  `‖Δx‖/‖x‖ ≤ κ/(1 - κ‖ΔA‖/‖A‖) (‖ΔA‖/‖A‖ + ‖Δb‖/‖b‖)` under `κ‖ΔA‖/‖A‖ < 1`.
  Atlas: `linear-system-perturbation`.
* Least squares (Trefethen–Bau 1997, Thm 18.1, with its `κ, θ, η`; Higham 2002, Thm 20.1):
  `leastSquaresCos A b = cos θ = ‖y‖/‖b‖`, `leastSquaresTan A b = tan θ = ‖b - y‖/‖y‖`,
  `leastSquaresEta A b = η = ‖A‖‖x‖/‖y‖` for `x = A⁺b`, `y = Ax`; the two exact bounds for
  perturbations of `b` (proved, any rank), the two first-order bounds for perturbations of `A`
  (stated in `ε`–`δ` form), and Higham's non-asymptotic bounds.
  Atlas: `least-squares-perturbation`.

Euclidean vector norms are written `Real.sqrt (v ⬝ᵥ v)`. Exact arithmetic only.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

/-! ### The condition number -/

section Def

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A nonzero idempotent has `‖P‖₂ ≥ 1` (`‖P‖ = ‖P²‖ ≤ ‖P‖²`). Golub–Van Loan 2013, §2.5.1. -/
theorem one_le_specNorm_of_isIdempotentElem {P : Matrix m m ℝ} (hP : IsIdempotentElem P)
    (h0 : P ≠ 0) : 1 ≤ specNorm P := by
  have hpos : 0 < specNorm P := by rw [specNorm_eq_norm]; exact norm_pos_iff.mpr h0
  have h := specNorm_mul_le P P
  rw [show P * P = P from hP] at h
  nlinarith

/-- The Moore–Penrose inverse of an invertible square matrix is its inverse.
Horn–Johnson 2013, §7.3. -/
theorem moorePenroseInverse_eq_nonsing_inv {A : Matrix n n ℝ} (hA : IsUnit A) :
    moorePenroseInverse A = A⁻¹ := by
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  apply (isMoorePenroseInverse A).unique
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  · rw [Matrix.mul_nonsing_inv _ hd, Matrix.transpose_one]
  · rw [Matrix.nonsing_inv_mul _ hd, Matrix.transpose_one]

/-- For invertible square `A`, `κ(A) = ‖A‖₂ ‖A⁻¹‖₂`. Trefethen–Bau 1997, eq. (12.13);
Golub–Van Loan 2013, eq. (2.6.4).
atlas: condition-number-def (partial) -/
theorem conditionNumber_eq_of_isUnit {A : Matrix n n ℝ} (hA : IsUnit A) :
    conditionNumber A = specNorm A * specNorm A⁻¹ := by
  rw [conditionNumber, moorePenroseInverse_eq_nonsing_inv hA]

omit [DecidableEq n] in
/-- `(Q A)⁺ = A⁺ Qᵀ` when `Q` has orthonormal columns. Golub–Van Loan 2013, §5.5.2. -/
theorem moorePenroseInverse_mul_of_hasOrthonormalCols {p : Type*} [Fintype p]
    {Q : Matrix p m ℝ} (hQ : HasOrthonormalCols Q) (A : Matrix m n ℝ) :
    moorePenroseInverse (Q * A) = moorePenroseInverse A * Qᵀ := by
  have hQ' : Qᵀ * Q = 1 := hQ
  have hA := isMoorePenroseInverse A
  apply (isMoorePenroseInverse (Q * A)).unique
  have e2 : moorePenroseInverse A * Qᵀ * (Q * A) = moorePenroseInverse A * A := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, hQ', Matrix.one_mul]
  have e1 : Q * A * (moorePenroseInverse A * Qᵀ) = Q * (A * moorePenroseInverse A) * Qᵀ := by
    simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc (Q * A), e2, Matrix.mul_assoc Q, ← Matrix.mul_assoc A, hA.mul_mul_eq]
  · rw [e2, ← Matrix.mul_assoc, hA.inv_mul_inv_eq]
  · rw [e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hA.transpose_mul_eq]
    simp only [Matrix.mul_assoc]
  · rw [e2, hA.transpose_inv_mul_eq]

/-- `κ(Q A) = κ(A)` when `Q` has orthonormal columns (`QᵀQ = I`). Golub–Van Loan 2013, §2.6.2
and §5.3.2 (`κ(R) = κ(A)` for `A = QR`).
atlas: condition-number-def (partial) -/
theorem conditionNumber_mul_of_hasOrthonormalCols {p : Type*} [Fintype p] [DecidableEq p]
    {Q : Matrix p m ℝ} (hQ : HasOrthonormalCols Q) (A : Matrix m n ℝ) :
    conditionNumber (Q * A) = conditionNumber A := by
  rw [conditionNumber, conditionNumber, moorePenroseInverse_mul_of_hasOrthonormalCols hQ,
    specNorm_mul_left_of_hasOrthonormalCols hQ,
    specNorm_mul_transpose_right_of_hasOrthonormalCols hQ]

/-- `‖E‖₂ < 1/‖A⁻¹‖₂` keeps `A + E` invertible: the distance from an invertible `A` to the
singular matrices is at least `1/‖A⁻¹‖₂`, i.e. relative distance `≥ 1/κ(A)`. Golub–Van Loan 2013,
Thm 2.6.2 (corollary); Higham 2002, Thm 6.5 (lower bound).
atlas: condition-number-def (partial) -/
theorem isUnit_add_of_specNorm_lt {A E : Matrix n n ℝ} (hA : IsUnit A)
    (hE : specNorm E < 1 / specNorm A⁻¹) : IsUnit (A + E) := by
  have hpos : 0 < specNorm A⁻¹ := by
    by_contra h
    have h0 : specNorm A⁻¹ = 0 := le_antisymm (not_lt.mp h) (specNorm_nonneg _)
    rw [h0, div_zero] at hE
    exact absurd hE (not_lt.mpr (specNorm_nonneg E))
  apply isUnit_add_of_specNorm_inv_mul_lt_one hA
  apply specNorm_inv_mul_lt_one
  rw [lt_div_iff₀ hpos] at hE
  linarith

/-- Coverage: condition-number-def
Distance to singularity is attained (Gastinel–Kahan): for invertible `A` on a nonempty index
there is `E` with `‖E‖₂ = 1/‖A⁻¹‖₂` and `A + E` singular. With `isUnit_add_of_specNorm_lt` this
gives `min {‖E‖₂ : A + E singular} = 1/‖A⁻¹‖₂`, i.e. relative distance `1/κ(A)`.
Higham 2002, Thm 6.5; Golub–Van Loan 2013, §2.6.2.
atlas: condition-number-def (partial) -/
theorem exists_specNorm_eq_not_isUnit_add [Nonempty n] {A : Matrix n n ℝ} (hA : IsUnit A) :
    ∃ E : Matrix n n ℝ, specNorm E = 1 / specNorm A⁻¹ ∧ ¬ IsUnit (A + E) := by
  obtain ⟨E, hE, hNorm⟩ := exists_not_isUnit_add_specNorm_eq_inv_specNorm_inv A hA
  exact ⟨E, hNorm, hE⟩

end Def

section FinIndex

variable {m n : ℕ}

/-- `κ(A) = σ₁(A)/σ_r(A)` for `r = rank A ≥ 1` (zero-indexed singular values: `σ 0 / σ (r-1)`).
Golub–Van Loan 2013, §2.6.2 and §5.5.2.
atlas: condition-number-def (partial) -/
theorem conditionNumber_eq_singularValues_div (A : Matrix (Fin m) (Fin n) ℝ)
    (hr : A.rank ≠ 0) :
    conditionNumber A = singularValues A 0 / singularValues A (A.rank - 1) := by
  rw [conditionNumber, specNorm_moorePenroseInverse_eq_inv_singularValues_last_positive A
    (Nat.pos_of_ne_zero hr), singularValues_zero_eq_specNorm]
  ring

/-- Under full column rank (`rank A = n ≥ 1`), `κ(A) = ‖A‖₂ / σ_min(A)` with the variational
`sigmaMin`. This covers invertible square `A`. Golub–Van Loan 2013, §5.3.2 (`κ₂(A) = σ₁/σ_n`);
Trefethen–Bau 1997, Thm 12.2 discussion / eq. (12.14).
atlas: condition-number-def (partial) -/
theorem conditionNumber_eq_div_sigmaMin (A : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n)
    (hA : A.rank = n) : conditionNumber A = specNorm A / sigmaMin A := by
  rw [conditionNumber, specNorm_moorePenroseInverse_eq_inv_singularValues_last_positive A
    (by omega), sigmaMin_eq_singularValues_last A hn, hA]
  ring

end FinIndex

/-! ### Linear systems -/

section LinearSystem

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A nonzero vector has positive Euclidean length `√(v ⬝ᵥ v)`. -/
theorem sqrt_dotProduct_self_pos {ι : Type*} [Fintype ι] {v : ι → ℝ} (hv : v ≠ 0) :
    0 < Real.sqrt (v ⬝ᵥ v) :=
  Real.sqrt_pos.mpr (lt_of_le_of_ne (dotProduct_self_nonneg v)
    (Ne.symm (fun h => hv (dotProduct_self_eq_zero.mp h))))

/-- Euclidean triangle inequality for a difference, `‖u - v‖ ≤ ‖u‖ + ‖v‖`, in the
`Real.sqrt (v ⬝ᵥ v)` spelling. -/
theorem sqrt_dotProduct_sub_le {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    Real.sqrt ((u - v) ⬝ᵥ (u - v)) ≤ Real.sqrt (u ⬝ᵥ u) + Real.sqrt (v ⬝ᵥ v) := by
  have h := sqrt_dotProduct_add_le u (-v)
  simpa only [sub_eq_add_neg, neg_dotProduct, dotProduct_neg, neg_neg] using h

/-- **A posteriori error bound.** For invertible `A`, `A x = b ≠ 0` and any `x̂`,
`‖x - x̂‖/‖x‖ ≤ κ(A) ‖b - A x̂‖/‖b‖`. Higham 2002, eq. (7.4) / Thm 7.2 discussion;
Golub–Van Loan 2013, §3.5.3; Trefethen–Bau 1997, Thm 12.1 (eq. (12.15)).
atlas: linear-system-perturbation (partial) -/
theorem sqrt_dotProduct_sub_div_le_conditionNumber_mul {A : Matrix n n ℝ} (hA : IsUnit A)
    {x b : n → ℝ} (hx : A *ᵥ x = b) (hb : b ≠ 0) (x' : n → ℝ) :
    Real.sqrt ((x - x') ⬝ᵥ (x - x')) / Real.sqrt (x ⬝ᵥ x) ≤
      conditionNumber A * (Real.sqrt ((b - A *ᵥ x') ⬝ᵥ (b - A *ᵥ x')) /
        Real.sqrt (b ⬝ᵥ b)) := by
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  rw [conditionNumber_eq_of_isUnit hA]
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
`A (x + Δx) = b + Δb`: `‖Δx‖/‖x‖ ≤ κ(A) ‖Δb‖/‖b‖`. Trefethen–Bau 1997, Thm 12.1 (condition number
of `b ↦ x` is at most `κ(A)`); Golub–Van Loan 2013, Thm 2.6.2 with `ΔA = 0`.
atlas: linear-system-perturbation (partial) -/
theorem sqrt_dotProduct_div_le_conditionNumber_mul_of_mulVec_add {A : Matrix n n ℝ}
    (hA : IsUnit A) {x b Δx Δb : n → ℝ} (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hΔ : A *ᵥ (x + Δx) = b + Δb) :
    Real.sqrt (Δx ⬝ᵥ Δx) / Real.sqrt (x ⬝ᵥ x) ≤
      conditionNumber A * (Real.sqrt (Δb ⬝ᵥ Δb) / Real.sqrt (b ⬝ᵥ b)) := by
  have h := sqrt_dotProduct_sub_div_le_conditionNumber_mul hA hx hb (x + Δx)
  have e1 : x - (x + Δx) = -Δx := by abel
  have e2 : b - A *ᵥ (x + Δx) = -Δb := by rw [hΔ]; abel
  rwa [e1, e2, neg_dotProduct, dotProduct_neg, neg_neg, neg_dotProduct, dotProduct_neg,
    neg_neg] at h

/-- **Perturbation of a linear system.** For invertible `A`, `A x = b ≠ 0`,
`(A + ΔA)(x + Δx) = b + Δb` and `κ(A) ‖ΔA‖/‖A‖ < 1`:
`‖Δx‖/‖x‖ ≤ κ(A)/(1 - κ(A)‖ΔA‖/‖A‖) · (‖ΔA‖/‖A‖ + ‖Δb‖/‖b‖)`.
Higham 2002, Thm 7.2 (normwise, with `ε = ‖ΔA‖/‖A‖`-type tolerances); Golub–Van Loan 2013,
Thm 2.6.2; the first-order content is Trefethen–Bau 1997, Thm 12.1–12.2. Proof: `A Δx = Δb -
ΔA (x + Δx)`, so `‖Δx‖ ≤ ‖A⁻¹‖(‖Δb‖ + ‖ΔA‖‖x‖ + ‖ΔA‖‖Δx‖)`; absorb the last term, then use
`‖b‖ ≤ ‖A‖‖x‖`. (`A + ΔA` is then invertible by `isUnit_add_of_specNorm_lt`, so `Δx` is
determined.)
atlas: linear-system-perturbation (partial) -/
theorem sqrt_dotProduct_div_le_of_add_mulVec_add {A ΔA : Matrix n n ℝ} (hA : IsUnit A)
    {x b Δx Δb : n → ℝ} (hx : A *ᵥ x = b) (hb : b ≠ 0)
    (hΔ : (A + ΔA) *ᵥ (x + Δx) = b + Δb)
    (hsmall : conditionNumber A * (specNorm ΔA / specNorm A) < 1) :
    Real.sqrt (Δx ⬝ᵥ Δx) / Real.sqrt (x ⬝ᵥ x) ≤
      conditionNumber A / (1 - conditionNumber A * (specNorm ΔA / specNorm A)) *
        (specNorm ΔA / specNorm A + Real.sqrt (Δb ⬝ᵥ Δb) / Real.sqrt (b ⬝ᵥ b)) := by
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  rw [conditionNumber_eq_of_isUnit hA] at hsmall ⊢
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
theorem sqrt_dotProduct_mul_moorePenroseInverse_sub_div_le (A : Matrix m n ℝ) (b Δb : m → ℝ) :
    Real.sqrt (((A * moorePenroseInverse A) *ᵥ (b + Δb) - (A * moorePenroseInverse A) *ᵥ b) ⬝ᵥ
        ((A * moorePenroseInverse A) *ᵥ (b + Δb) - (A * moorePenroseInverse A) *ᵥ b)) /
      Real.sqrt (((A * moorePenroseInverse A) *ᵥ b) ⬝ᵥ ((A * moorePenroseInverse A) *ᵥ b)) ≤
      1 / leastSquaresCos A b * (Real.sqrt (Δb ⬝ᵥ Δb) / Real.sqrt (b ⬝ᵥ b)) := by
  set P := A * moorePenroseInverse A
  set Ny := Real.sqrt ((P *ᵥ b) ⬝ᵥ (P *ᵥ b))
  set Nb := Real.sqrt (b ⬝ᵥ b)
  set Ndb := Real.sqrt (Δb ⬝ᵥ Δb)
  have hP : specNorm P ≤ 1 :=
    specNorm_le_one_of_isSymm_of_isIdempotentElem (mul_moorePenroseInverse_isSymm A)
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

/-- **Least squares, `x` under perturbation of `b`.** For `x = A⁺ b` and any `Δb`:
`‖Δx‖/‖x‖ ≤ κ(A)/(η cos θ) · ‖Δb‖/‖b‖`, where `Δx = A⁺ Δb`. Exact, any rank (`κ/(η cos θ)`
equals `‖A⁺‖‖b‖/‖x‖` when `x ≠ 0`). Trefethen–Bau 1997, Thm 18.1 (second entry of the table).
atlas: least-squares-perturbation (partial) -/
theorem sqrt_dotProduct_moorePenroseInverse_sub_div_le (A : Matrix m n ℝ) (b Δb : m → ℝ) :
    Real.sqrt ((moorePenroseInverse A *ᵥ (b + Δb) - moorePenroseInverse A *ᵥ b) ⬝ᵥ
        (moorePenroseInverse A *ᵥ (b + Δb) - moorePenroseInverse A *ᵥ b)) /
      Real.sqrt ((moorePenroseInverse A *ᵥ b) ⬝ᵥ (moorePenroseInverse A *ᵥ b)) ≤
      conditionNumber A / (leastSquaresEta A b * leastSquaresCos A b) *
        (Real.sqrt (Δb ⬝ᵥ Δb) / Real.sqrt (b ⬝ᵥ b)) := by
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
  have hRHS : 0 ≤ conditionNumber A / (leastSquaresEta A b * leastSquaresCos A b) *
      (Ndb / Nb) := by
    unfold leastSquaresEta leastSquaresCos
    have := conditionNumber_nonneg A
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
  have hconst : conditionNumber A / (leastSquaresEta A b * leastSquaresCos A b) =
      specNorm A' * Nb / Nx := by
    unfold leastSquaresEta leastSquaresCos conditionNumber
    change specNorm A * specNorm A' / (specNorm A * Nx / Ny * (Ny / Nb)) = _
    field_simp
  rw [hconst]
  calc Real.sqrt ((A' *ᵥ Δb) ⬝ᵥ (A' *ᵥ Δb)) / Nx ≤ specNorm A' * Ndb / Nx :=
        div_le_div_of_nonneg_right h1 hNx.le
    _ = specNorm A' * Nb / Nx * (Ndb / Nb) := by field_simp

/--
**Least squares, `y` under perturbation of `A` (first order).** For full column rank `A`,
`y = A A⁺ b`: for every `ε > 0` there is `δ > 0` such that `‖ΔA‖₂ < δ` implies
`‖Δy‖/‖y‖ ≤ (κ(A)/cos θ + ε) ‖ΔA‖/‖A‖`, where `Δy = (A + ΔA)(A + ΔA)⁺ b - A A⁺ b`.
Trefethen–Bau 1997, Thm 18.1 (third entry: condition number `≤ κ/cos θ`), stated in `ε`–`δ`
form since the source bound is a first-order (condition-number) statement. The exact
equal-rank projector bound gives `‖Δy‖ ≤ ‖ΔA‖‖A⁺‖‖b‖` in a rank-preserving neighborhood.
atlas: least-squares-perturbation (partial) -/
theorem exists_pos_forall_sqrt_fit_sub_div_le (A : Matrix m n ℝ)
    (hA : A.rank = Fintype.card n) (b : m → ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ ΔA : Matrix m n ℝ, specNorm ΔA < δ →
      Real.sqrt ((((A + ΔA) * moorePenroseInverse (A + ΔA)) *ᵥ b -
            (A * moorePenroseInverse A) *ᵥ b) ⬝ᵥ
          (((A + ΔA) * moorePenroseInverse (A + ΔA)) *ᵥ b -
            (A * moorePenroseInverse A) *ᵥ b)) /
        Real.sqrt (((A * moorePenroseInverse A) *ᵥ b) ⬝ᵥ ((A * moorePenroseInverse A) *ᵥ b)) ≤
        (conditionNumber A / leastSquaresCos A b + ε) * (specNorm ΔA / specNorm A) := by
  exact exists_pos_forall_sqrt_pinv_fit_sub_div_le A hA b

/--
**Least squares, `x` under perturbation of `A` (first order).** For full column rank `A`,
`x = A⁺ b`: for every `ε > 0` there is `δ > 0` such that `‖ΔA‖₂ < δ` implies
`‖Δx‖/‖x‖ ≤ (κ(A) + κ(A)² tan θ/η + ε) ‖ΔA‖/‖A‖`, where `Δx = (A + ΔA)⁺ b - A⁺ b`.
Trefethen–Bau 1997, Thm 18.1 (fourth entry: `κ + κ² tan θ/η`); Golub–Van Loan 2013, Thm 5.3.1
(first-order `κ² tan θ` form). The finite pseudoinverse perturbation estimate gives
the coefficient with denominator `1 - ‖A⁺‖‖ΔA‖`, absorbed by choosing a small enough `δ`;
`κ² tan θ/η = κ²‖r‖/(‖A‖‖x‖)`.
atlas: least-squares-perturbation (partial) -/
theorem exists_pos_forall_sqrt_solution_sub_div_le (A : Matrix m n ℝ)
    (hA : A.rank = Fintype.card n) (b : m → ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ ΔA : Matrix m n ℝ, specNorm ΔA < δ →
      Real.sqrt ((moorePenroseInverse (A + ΔA) *ᵥ b - moorePenroseInverse A *ᵥ b) ⬝ᵥ
          (moorePenroseInverse (A + ΔA) *ᵥ b - moorePenroseInverse A *ᵥ b)) /
        Real.sqrt ((moorePenroseInverse A *ᵥ b) ⬝ᵥ (moorePenroseInverse A *ᵥ b)) ≤
        (conditionNumber A + conditionNumber A ^ 2 * leastSquaresTan A b / leastSquaresEta A b +
          ε) * (specNorm ΔA / specNorm A) := by
  exact exists_pos_forall_sqrt_pinv_solution_sub_div_le A hA b

/--
**Wedin's least-squares bound (solution).** Let `A` have full column rank, `x = A⁺ b`,
`r = b - A x`, `y = (A + ΔA)⁺(b + Δb)`, `0 ≤ ε`, `‖ΔA‖₂ ≤ ε‖A‖₂`, `‖Δb‖ ≤ ε‖b‖` and
`κ(A) ε < 1`. Then `‖x - y‖/‖x‖ ≤ κε/(1 - κε) · (2 + (κ + 1) ‖r‖/(‖A‖₂‖x‖))`.
Higham 2002, Thm 20.1 (from Wedin 1973, §5); first-order form Golub–Van Loan 2013, Thm 5.3.1.
`A + ΔA` has full column rank automatically (`σ_min(A + ΔA) ≥ σ_min(A)(1 - κε) > 0`), and `y` is
its unique least-squares solution. This is the coordinate transport of the existing
Euclidean finite bound, with total division including a zero old solution.
atlas: least-squares-perturbation (partial) -/
theorem sqrt_dotProduct_solution_sub_div_le (A ΔA : Matrix m n ℝ)
    (hA : A.rank = Fintype.card n) (b Δb : m → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hΔA : specNorm ΔA ≤ ε * specNorm A)
    (hΔb : Real.sqrt (Δb ⬝ᵥ Δb) ≤ ε * Real.sqrt (b ⬝ᵥ b))
    (hκ : conditionNumber A * ε < 1) :
    Real.sqrt ((moorePenroseInverse A *ᵥ b - moorePenroseInverse (A + ΔA) *ᵥ (b + Δb)) ⬝ᵥ
        (moorePenroseInverse A *ᵥ b - moorePenroseInverse (A + ΔA) *ᵥ (b + Δb))) /
      Real.sqrt ((moorePenroseInverse A *ᵥ b) ⬝ᵥ (moorePenroseInverse A *ᵥ b)) ≤
      conditionNumber A * ε / (1 - conditionNumber A * ε) *
        (2 + (conditionNumber A + 1) *
          Real.sqrt ((b - A *ᵥ (moorePenroseInverse A *ᵥ b)) ⬝ᵥ
            (b - A *ᵥ (moorePenroseInverse A *ᵥ b))) /
          (specNorm A * Real.sqrt ((moorePenroseInverse A *ᵥ b) ⬝ᵥ
            (moorePenroseInverse A *ᵥ b)))) := by
  exact sqrt_pinv_solution_sub_div_le A ΔA hA b Δb hε hΔA hΔb hκ

/--
**Wedin's least-squares bound (residual).** Under the hypotheses of
`sqrt_dotProduct_solution_sub_div_le`, with `r = b - A x`, `s = (b + Δb) - (A + ΔA) y`:
`‖r - s‖/‖b‖ ≤ (1 + 2κ(A)) ε`. Higham 2002, Thm 20.1; Wedin 1973, §5.
This transports the stronger Euclidean coefficient `1 + κ(A)`, with total division
including zero data.
atlas: least-squares-perturbation (partial) -/
theorem sqrt_dotProduct_residual_sub_div_le (A ΔA : Matrix m n ℝ)
    (hA : A.rank = Fintype.card n) (b Δb : m → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hΔA : specNorm ΔA ≤ ε * specNorm A)
    (hΔb : Real.sqrt (Δb ⬝ᵥ Δb) ≤ ε * Real.sqrt (b ⬝ᵥ b))
    (hκ : conditionNumber A * ε < 1) :
    Real.sqrt ((b - A *ᵥ (moorePenroseInverse A *ᵥ b) -
          ((b + Δb) - (A + ΔA) *ᵥ (moorePenroseInverse (A + ΔA) *ᵥ (b + Δb)))) ⬝ᵥ
        (b - A *ᵥ (moorePenroseInverse A *ᵥ b) -
          ((b + Δb) - (A + ΔA) *ᵥ (moorePenroseInverse (A + ΔA) *ᵥ (b + Δb))))) /
      Real.sqrt (b ⬝ᵥ b) ≤ (1 + 2 * conditionNumber A) * ε := by
  exact sqrt_pinv_residual_sub_div_le A ΔA hA b Δb hε hΔA hΔb hκ

end LeastSquares

end NLAlib
