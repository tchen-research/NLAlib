import NLAlib.Matrix.LeastSquaresGeometry
import NLAlib.Matrix.ConditionNumber

/-!
# Quantitative full-rank least-squares perturbation

The actual Moore–Penrose solutions are used with Euclidean vector norms.
Higham, Theorem 20.1; Wedin §5; Golub–Van Loan, Theorem 5.3.1.
Atlas target: `least-squares-perturbation`.
-/

noncomputable section
set_option maxHeartbeats 800000
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The orthogonal range projector annihilates its Moore–Penrose residual.
Penrose idempotence; supports least-squares perturbation. -/
theorem columnProjector_apply_pinv_residual_eq_zero (A : Matrix m n ℝ)
    (b : EuclideanSpace ℝ m) :
    (A*moorePenroseInverse A).toEuclideanLin
      (b-A.toEuclideanLin ((moorePenroseInverse A).toEuclideanLin b))=0 := by
  have h := mul_moorePenroseInverse_isIdempotentElem A
  change (A*moorePenroseInverse A)*(A*moorePenroseInverse A)=A*moorePenroseInverse A at h
  rw [← toEuclideanLin_mul_apply, map_sub, ← toEuclideanLin_mul_apply, h, sub_self]

omit [DecidableEq n] in
/-- The complement of the Moore–Penrose column projector is a contraction.
Orthogonal-projector norm bound; supports least-squares perturbation. -/
theorem specNorm_complement_columnProjector_le_one (A : Matrix m n ℝ) :
    specNorm (1-A*moorePenroseInverse A) ≤ 1 := by
  apply specNorm_le_one_of_isSymm_of_isIdempotentElem
  · simp [Matrix.IsSymm, (mul_moorePenroseInverse_isSymm A).eq]
  · change (1-A*moorePenroseInverse A)*(1-A*moorePenroseInverse A)=1-A*moorePenroseInverse A
    have h : (A*moorePenroseInverse A)*(A*moorePenroseInverse A)=A*moorePenroseInverse A :=
      mul_moorePenroseInverse_isIdempotentElem A
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h]
    abel

/-- The perturbed inverse applied to the old residual is controlled by the
equal-rank projector gap. Higham, Theorem 20.1; Wedin §5. -/
theorem norm_pinv_apply_pinv_residual_le {A B : Matrix m n ℝ}
    (hr : A.rank=B.rank) (b : EuclideanSpace ℝ m) :
    let r := b-A.toEuclideanLin ((moorePenroseInverse A).toEuclideanLin b)
    ‖(moorePenroseInverse B).toEuclideanLin r‖ ≤
      specNorm (moorePenroseInverse B)*specNorm (moorePenroseInverse A)*specNorm (B-A)*‖r‖ := by
  intro r
  have hz : (A*moorePenroseInverse A).toEuclideanLin r=0 :=
    columnProjector_apply_pinv_residual_eq_zero A b
  have he : (moorePenroseInverse B).toEuclideanLin r =
      (moorePenroseInverse B).toEuclideanLin
        ((B*moorePenroseInverse B-A*moorePenroseInverse A).toEuclideanLin r) := by
    rw [map_sub (Matrix.toEuclideanLin (m := m) (n := m) (𝕜 := ℝ)),
      LinearMap.sub_apply, hz, sub_zero, ← toEuclideanLin_mul_apply,
      ← Matrix.mul_assoc, moorePenroseInverse_mul_moorePenroseInverse]
  have hgap : specNorm (B*moorePenroseInverse B-A*moorePenroseInverse A) ≤
      specNorm (moorePenroseInverse A)*specNorm (B-A) := by
    rw [specNorm_sub_comm]
    exact specNorm_sub_columnProjector_le_pinv_mul_specNorm hr
  rw [he]
  calc
    _ ≤ specNorm (moorePenroseInverse B)*
        ‖(B*moorePenroseInverse B-A*moorePenroseInverse A).toEuclideanLin r‖ :=
      norm_toEuclideanLin_apply_le _ _
    _ ≤ specNorm (moorePenroseInverse B)*
        (specNorm (B*moorePenroseInverse B-A*moorePenroseInverse A)*‖r‖) :=
      mul_le_mul_of_nonneg_left (norm_toEuclideanLin_apply_le _ _) (specNorm_nonneg _)
    _ ≤ specNorm (moorePenroseInverse B)*(specNorm (moorePenroseInverse A)*specNorm (B-A)*‖r‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgap (norm_nonneg _))
        (specNorm_nonneg _)
    _ = _ := by ring

/-- A direct finite perturbation estimate retaining the old residual and the
actual perturbed pseudoinverse. Higham, Theorem 20.1; Wedin §5. -/
theorem norm_least_squares_sub_le_pinv {A E : Matrix m n ℝ}
    (hA : A.rank=Fintype.card n)
    (hE : specNorm (moorePenroseInverse A)*specNorm E < 1)
    (b f : EuclideanSpace ℝ m) :
    let x := (moorePenroseInverse A).toEuclideanLin b
    let y := (moorePenroseInverse (A+E)).toEuclideanLin (b+f)
    let r := b-A.toEuclideanLin x
    ‖y-x‖ ≤ specNorm (moorePenroseInverse (A+E))*
      (‖f‖+specNorm E*‖x‖+specNorm (moorePenroseInverse A)*specNorm E*‖r‖) := by
  intro x y r
  have hB := rank_add_eq_card_of_pinv_mul_specNorm_lt_one hA hE
  have hleft := moorePenroseInverse_mul_eq_one_of_rank_eq_card hB
  have hsum : b+f = (A+E).toEuclideanLin x+(f-E.toEuclideanLin x)+r := by
    dsimp [r]
    rw [map_add, LinearMap.add_apply]
    abel
  have he : y-x = (moorePenroseInverse (A+E)).toEuclideanLin (f-E.toEuclideanLin x)+
      (moorePenroseInverse (A+E)).toEuclideanLin r := by
    dsimp [y]
    rw [hsum, map_add, map_add, ← toEuclideanLin_mul_apply, hleft,
      toEuclideanLin_one_apply]
    abel
  have hr := norm_pinv_apply_pinv_residual_le (A := A) (B := A+E) (hA.trans hB.symm) b
  simp only [add_sub_cancel_left] at hr
  have hf : ‖f-E.toEuclideanLin x‖ ≤ ‖f‖+specNorm E*‖x‖ :=
    (norm_sub_le _ _).trans (add_le_add (le_refl _) (norm_toEuclideanLin_apply_le E x))
  rw [he]
  calc
    _ ≤ ‖(moorePenroseInverse (A+E)).toEuclideanLin (f-E.toEuclideanLin x)‖+
        ‖(moorePenroseInverse (A+E)).toEuclideanLin r‖ := norm_add_le _ _
    _ ≤ specNorm (moorePenroseInverse (A+E))*(‖f‖+specNorm E*‖x‖)+
        specNorm (moorePenroseInverse (A+E))*specNorm (moorePenroseInverse A)*specNorm E*‖r‖ :=
      add_le_add ((norm_toEuclideanLin_apply_le _ _).trans
        (mul_le_mul_of_nonneg_left hf (specNorm_nonneg _))) hr
    _ = _ := by ring

/-- The residual perturbation uses only the projector gap and the perturbed
right-hand side. Higham, Theorem 20.1; a stronger constant follows. -/
theorem norm_least_squares_residual_sub_le {A B : Matrix m n ℝ}
    (hr : A.rank=B.rank) (b f : EuclideanSpace ℝ m) :
    let r := b-A.toEuclideanLin ((moorePenroseInverse A).toEuclideanLin b)
    let s := (b+f)-B.toEuclideanLin ((moorePenroseInverse B).toEuclideanLin (b+f))
    ‖r-s‖ ≤ specNorm (moorePenroseInverse A)*specNorm (B-A)*‖b‖+‖f‖ := by
  intro r s
  have halg (P Q : EuclideanSpace ℝ m →ₗ[ℝ] EuclideanSpace ℝ m) :
      (b-P b)-((b+f)-Q (b+f))=(Q-P) b-(1-Q) f := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_add]
    abel
  have he : r-s = (B*moorePenroseInverse B-A*moorePenroseInverse A).toEuclideanLin b-
      (1-B*moorePenroseInverse B).toEuclideanLin f := by
    have h := halg (A*moorePenroseInverse A).toEuclideanLin
      (B*moorePenroseInverse B).toEuclideanLin
    change (b-A.toEuclideanLin ((moorePenroseInverse A).toEuclideanLin b))-
      ((b+f)-B.toEuclideanLin ((moorePenroseInverse B).toEuclideanLin (b+f)))=_
    rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply,
      map_sub (Matrix.toEuclideanLin (m := m) (n := m) (𝕜 := ℝ)),
      map_sub (Matrix.toEuclideanLin (m := m) (n := m) (𝕜 := ℝ))]
    convert h using 1
    simp only [LinearMap.sub_apply, toEuclideanLin_one_apply, Module.End.one_apply]
  have hgap : specNorm (B*moorePenroseInverse B-A*moorePenroseInverse A) ≤
      specNorm (moorePenroseInverse A)*specNorm (B-A) := by
    rw [specNorm_sub_comm]
    exact specNorm_sub_columnProjector_le_pinv_mul_specNorm hr
  rw [he]
  have h1 : ‖(B*moorePenroseInverse B-A*moorePenroseInverse A).toEuclideanLin b‖ ≤
      specNorm (moorePenroseInverse A)*specNorm (B-A)*‖b‖ :=
    (norm_toEuclideanLin_apply_le (B*moorePenroseInverse B-A*moorePenroseInverse A) b).trans
      (mul_le_mul_of_nonneg_right hgap (norm_nonneg b))
  have h2 : ‖(1-B*moorePenroseInverse B).toEuclideanLin f‖ ≤ ‖f‖ := by
    have hbound := norm_toEuclideanLin_apply_le (1-B*moorePenroseInverse B) f
    have hcontract := mul_le_mul_of_nonneg_right
      (specNorm_complement_columnProjector_le_one B) (norm_nonneg f)
    exact hbound.trans (by simpa only [one_mul] using hcontract)
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

/-- Relative matrix perturbations below the condition-number threshold
preserve full column rank. Higham, Theorem 20.1. -/
theorem rank_add_eq_card_of_conditionNumber_mul_lt_one {A E : Matrix m n ℝ}
    {ε : ℝ} (hA : A.rank=Fintype.card n) (hE : specNorm E ≤ ε*specNorm A)
    (hsmall : conditionNumber A*ε < 1) : (A+E).rank=Fintype.card n := by
  apply rank_add_eq_card_of_pinv_mul_specNorm_lt_one hA
  calc
    _ ≤ specNorm (moorePenroseInverse A)*(ε*specNorm A) :=
      mul_le_mul_of_nonneg_left hE (specNorm_nonneg _)
    _ = conditionNumber A*ε := by unfold conditionNumber; ring
    _ < 1 := hsmall

/-- The perturbed pseudoinverse norm retains the condition-number
denominator under the source's relative data hypothesis. Higham, Theorem 20.1. -/
theorem specNorm_pinv_add_le_of_conditionNumber_mul_lt_one {A E : Matrix m n ℝ}
    {ε : ℝ} (hA : A.rank=Fintype.card n) (hE : specNorm E ≤ ε*specNorm A)
    (hsmall : conditionNumber A*ε < 1) :
    specNorm (moorePenroseInverse (A+E)) ≤
      specNorm (moorePenroseInverse A)/(1-conditionNumber A*ε) := by
  have hp : specNorm (moorePenroseInverse A)*specNorm E ≤ conditionNumber A*ε := by
    calc
      _ ≤ specNorm (moorePenroseInverse A)*(ε*specNorm A) :=
        mul_le_mul_of_nonneg_left hE (specNorm_nonneg _)
      _ = _ := by unfold conditionNumber; ring
  exact (specNorm_pinv_add_le_of_rank_eq_card hA (hp.trans_lt hsmall)).trans
    (div_le_div_of_nonneg_left (specNorm_nonneg _) (sub_pos.mpr hsmall)
      (sub_le_sub_left hp 1))

/-- The direct solution error with both relative perturbations substituted,
before dividing by the nonzero solution. Higham, Theorem 20.1; Wedin §5. -/
theorem norm_least_squares_sub_le_relative_data {A E : Matrix m n ℝ} {ε : ℝ}
    (hA : A.rank=Fintype.card n) (_hε : 0 ≤ ε)
    (hE : specNorm E ≤ ε*specNorm A) (b f : EuclideanSpace ℝ m)
    (hf : ‖f‖ ≤ ε*‖b‖) (hsmall : conditionNumber A*ε < 1) :
    let x := (moorePenroseInverse A).toEuclideanLin b
    let y := (moorePenroseInverse (A+E)).toEuclideanLin (b+f)
    let r := b-A.toEuclideanLin x
    ‖y-x‖ ≤ specNorm (moorePenroseInverse A)/(1-conditionNumber A*ε)*
      (ε*‖b‖+ε*specNorm A*‖x‖+specNorm (moorePenroseInverse A)*ε*specNorm A*‖r‖) := by
  intro x y r
  have hp : specNorm (moorePenroseInverse A)*specNorm E < 1 := by
    calc
      _ ≤ specNorm (moorePenroseInverse A)*(ε*specNorm A) :=
        mul_le_mul_of_nonneg_left hE (specNorm_nonneg _)
      _ = conditionNumber A*ε := by unfold conditionNumber; ring
      _ < 1 := hsmall
  have ht : ‖f‖+specNorm E*‖x‖+specNorm (moorePenroseInverse A)*specNorm E*‖r‖ ≤
      ε*‖b‖+ε*specNorm A*‖x‖+specNorm (moorePenroseInverse A)*ε*specNorm A*‖r‖ := by
    have h1 := mul_le_mul_of_nonneg_right hE (norm_nonneg x)
    have h2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hE (specNorm_nonneg (moorePenroseInverse A))) (norm_nonneg r)
    nlinarith
  exact (norm_least_squares_sub_le_pinv hA hp b f).trans
    (mul_le_mul (specNorm_pinv_add_le_of_conditionNumber_mul_lt_one hA hE hsmall) ht
      (by
        exact add_nonneg (add_nonneg (norm_nonneg f)
          (mul_nonneg (specNorm_nonneg E) (norm_nonneg x)))
          (mul_nonneg (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg E)) (norm_nonneg r)))
      (div_nonneg (specNorm_nonneg _) (sub_pos.mpr hsmall).le))

/-- The residual perturbation has the stronger coefficient `1+κ` under the
relative data hypotheses. Higham, Theorem 20.1; Wedin §5. -/
theorem norm_least_squares_residual_sub_le_relative_data {A E : Matrix m n ℝ} {ε : ℝ}
    (hA : A.rank=Fintype.card n) (hE : specNorm E ≤ ε*specNorm A)
    (b f : EuclideanSpace ℝ m) (hf : ‖f‖ ≤ ε*‖b‖)
    (hsmall : conditionNumber A*ε < 1) :
    let r := b-A.toEuclideanLin ((moorePenroseInverse A).toEuclideanLin b)
    let s := (b+f)-(A+E).toEuclideanLin ((moorePenroseInverse (A+E)).toEuclideanLin (b+f))
    ‖r-s‖ ≤ (1+conditionNumber A)*ε*‖b‖ := by
  intro r s
  have hB := rank_add_eq_card_of_conditionNumber_mul_lt_one hA hE hsmall
  have h := norm_least_squares_residual_sub_le (A := A) (B := A+E) (hA.trans hB.symm) b f
  simp only [add_sub_cancel_left] at h
  have h1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hE (specNorm_nonneg (moorePenroseInverse A))) (norm_nonneg b)
  apply h.trans
  unfold conditionNumber
  nlinarith

end NLAlib
