import NLAlib.Matrix.Inequalities.DeterminantRoot
/-!
# Minkowski's determinant inequality and exact equality

Normalize both matrices to determinant one and apply strict log-determinant
concavity. The equality condition becomes positive proportionality.
Positive dimension is explicit because the determinant root is otherwise
not the intended homogeneous function. Source: Horn--Johnson (2013),
Corollary 7.6.8 and Theorem 7.6.10; atlas `log-det-concavity`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Minkowski's determinant inequality for positive definite matrices, with
equality exactly at positive proportionality. Positive dimension is essential;
all repeated spectra are allowed. Horn--Johnson (2013), Corollary 7.6.8 and
Theorem 7.6.10.
atlas: log-det-concavity (partial) -/
theorem det_add_rpow_inv_card_ge_and_eq_iff {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hN : 0 < Fintype.card n) :
    A.det ^ (1 / (Fintype.card n : ℝ)) + B.det ^ (1 / (Fintype.card n : ℝ)) ≤
      (A + B).det ^ (1 / (Fintype.card n : ℝ)) ∧
    ((A + B).det ^ (1 / (Fintype.card n : ℝ)) =
      A.det ^ (1 / (Fintype.card n : ℝ)) + B.det ^ (1 / (Fintype.card n : ℝ)) ↔
      ∃ c : ℝ, 0 < c ∧ A = c • B) := by
  let p := A.det ^ (1 / (Fintype.card n : ℝ))
  let q := B.det ^ (1 / (Fintype.card n : ℝ))
  have hp : 0 < p := Real.rpow_pos_of_pos hA.det_pos _
  have hq : 0 < q := Real.rpow_pos_of_pos hB.det_pos _
  have hpq : 0 < p + q := add_pos hp hq
  have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  let P := p⁻¹ • A
  let Q := q⁻¹ • B
  let α := p / (p + q)
  let β := q / (p + q)
  have hP : P.PosDef := hA.smul (inv_pos.mpr hp)
  have hQ : Q.PosDef := hB.smul (inv_pos.mpr hq)
  have hPd : P.det = 1 := det_inv_rpow_smul_eq_one hA hN
  have hQd : Q.det = 1 := det_inv_rpow_smul_eq_one hB hN
  have hα : 0 < α := div_pos hp hpq
  have hβ : 0 < β := div_pos hq hpq
  have hαβ : α + β = 1 := by dsimp [α, β]; rw [← add_div, div_self hpq.ne']
  have hcombo : α • P + β • Q = (p + q)⁻¹ • (A + B) := by
    have hαp : α * p⁻¹ = (p + q)⁻¹ := by dsimp [α]; field_simp
    have hβq : β * q⁻¹ = (p + q)⁻¹ := by dsimp [β]; field_simp
    simp only [P, Q, smul_smul, hαp, hβq, smul_add]
  have hC : ((p + q)⁻¹ • (A + B)).PosDef := (hA.add hB).smul (inv_pos.mpr hpq)
  have hlog : 0 ≤ Real.log ((p + q)⁻¹ • (A + B)).det := by
    have h := log_det_smul_add_ge hP hQ hα.le hβ.le hαβ
    simpa only [hPd, hQd, Real.log_one, mul_zero, zero_add, hcombo] using h
  have hdet1 : 1 ≤ ((p + q)⁻¹ • (A + B)).det := by
    apply (Real.log_le_log_iff zero_lt_one hC.det_pos).mp
    simpa only [Real.log_one] using hlog
  have hdetN : ((p + q)⁻¹ • (A + B)).det = ((p + q) ^ Fintype.card n)⁻¹ * (A + B).det := by
    rw [Matrix.det_smul, inv_pow]
  have hpowPos : 0 < (p + q) ^ Fintype.card n := pow_pos hpq _
  have hdet : (p + q) ^ Fintype.card n ≤ (A + B).det := by
    rw [hdetN] at hdet1
    have h := mul_le_mul_of_nonneg_left hdet1 hpowPos.le
    simpa only [mul_one, ← mul_assoc, mul_inv_cancel₀ hpowPos.ne', one_mul] using h
  have hroot : p + q ≤ (A + B).det ^ (1 / (Fintype.card n : ℝ)) := by
    have h := Real.rpow_le_rpow hpowPos.le hdet
      (show 0 ≤ 1 / (Fintype.card n : ℝ) by positivity)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpq.le, mul_one_div_cancel hn, Real.rpow_one] at h
    exact h
  refine ⟨hroot, ?_⟩
  constructor
  · intro heq
    change (A + B).det ^ (1 / (Fintype.card n : ℝ)) = p + q at heq
    have hpow := det_rpow_inv_card_pow_card (hA.add hB) hN
    rw [heq] at hpow
    have hdetEq : ((p + q)⁻¹ • (A + B)).det = 1 := by
      rw [hdetN, ← hpow, inv_mul_cancel₀ hpowPos.ne']
    have hPQ : P = Q := by
      apply (log_det_smul_add_eq_iff hP hQ hα hβ hαβ).mp
      simp only [hcombo, hdetEq, hPd, hQd, Real.log_one, mul_zero, zero_add]
    refine ⟨p / q, div_pos hp hq, ?_⟩
    have h := congrArg (fun M : Matrix n n ℝ => p • M) hPQ
    simpa only [P, Q, smul_smul, mul_inv_cancel₀ hp.ne', one_smul, div_eq_mul_inv] using h
  · rintro ⟨c, hc, hAB⟩
    have hsum : A + B = (c + 1) • B := by rw [hAB, add_smul, one_smul]
    rw [hsum, det_smul_rpow_inv_card hB hN (by positivity), hAB,
      det_smul_rpow_inv_card hB hN hc.le]
    ring

/-- The positive determinant root is concave on the positive definite cone
in every positive dimension. Both endpoint weights are included.
Horn--Johnson (2013), Theorem 7.6.10.
atlas: log-det-concavity (partial) -/
theorem concaveOn_det_rpow_inv_card (hN : 0 < Fintype.card n) :
    ConcaveOn ℝ {A : Matrix n n ℝ | A.PosDef}
      (fun A => A.det ^ (1 / (Fintype.card n : ℝ))) := by
  refine ⟨convex_setOf_posDef, ?_⟩
  intro A hA B hB a b ha hb hab
  rcases lt_or_eq_of_le ha with ha | ha
  · rcases lt_or_eq_of_le hb with hb | hb
    · have h := (det_add_rpow_inv_card_ge_and_eq_iff (hA.smul ha) (hB.smul hb) hN).1
      simpa only [det_smul_rpow_inv_card hA hN ha.le, det_smul_rpow_inv_card hB hN hb.le,
        smul_eq_mul] using h
    · have ha1 : a = 1 := by linarith
      simp only [← hb, ha1, zero_smul, one_smul, add_zero, le_refl]
  · have hb1 : b = 1 := by linarith
    simp only [← ha, hb1, zero_smul, one_smul, zero_add, le_refl]

/-- Interior equality in determinant-root concavity is exactly positive
proportionality. The homogeneous statement allows arbitrary positive weights.
Horn--Johnson (2013), Theorem 7.6.10.
atlas: log-det-concavity (partial) -/
theorem det_smul_add_rpow_inv_card_eq_iff {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hN : 0 < Fintype.card n)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a • A + b • B).det ^ (1 / (Fintype.card n : ℝ)) =
      a * A.det ^ (1 / (Fintype.card n : ℝ)) + b * B.det ^ (1 / (Fintype.card n : ℝ)) ↔
      ∃ c : ℝ, 0 < c ∧ A = c • B := by
  have h := (det_add_rpow_inv_card_ge_and_eq_iff (hA.smul ha) (hB.smul hb) hN).2
  rw [det_smul_rpow_inv_card hA hN ha.le, det_smul_rpow_inv_card hB hN hb.le] at h
  rw [h]
  constructor
  · rintro ⟨c, hc, heq⟩
    refine ⟨a⁻¹ * (c * b), mul_pos (inv_pos.mpr ha) (mul_pos hc hb), ?_⟩
    have he := congrArg (fun M : Matrix n n ℝ => a⁻¹ • M) heq
    simpa only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] using he
  · rintro ⟨c, hc, heq⟩
    refine ⟨a * c / b, div_pos (mul_pos ha hc) hb, ?_⟩
    rw [heq, smul_smul, smul_smul, div_mul_cancel₀ _ hb.ne']

/-- The dimension restriction in Minkowski's determinant-root inequality
is necessary: in zero dimensions both positive definite identity matrices
have determinant root one, as does their sum, so the inequality is false.
Horn--Johnson (2013), Section 7.6; explicit repair for the dimension-free
wording of `log-det-concavity`. -/
theorem exists_posDef_zero_dim_not_det_root_add_ge :
    ∃ A B : Matrix (Fin 0) (Fin 0) ℝ, A.PosDef ∧ B.PosDef ∧
      ¬(A.det ^ (1 / (Fintype.card (Fin 0) : ℝ)) + B.det ^ (1 / (Fintype.card (Fin 0) : ℝ)) ≤
        (A + B).det ^ (1 / (Fintype.card (Fin 0) : ℝ))) := by
  refine ⟨1, 1, Matrix.PosDef.one, Matrix.PosDef.one, ?_⟩
  norm_num

end NLAlib
