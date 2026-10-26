import NLAlib.Matrix.Spectral.PrincipalDeletionResolvent

/-!
# Principal selection from an inverse-trace budget

A positive definite matrix with inverse trace at most `T` has a `k` by `k`
principal submatrix whose smallest eigenvalue exceeds
`(r-k+1)/(2T)`. The proof is a finite principal-coordinate deletion
iteration with a lower barrier, using only scalar reciprocal estimates.
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib.RestrictedInvertibility

private theorem exists_embedding_posDef_shift_trace_le_aux
    (k q : ℕ) {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) (hstep : 2 * δ * T ≤ 1)
    (G : Matrix (Fin (k + q)) (Fin (k + q)) ℝ) (hG : G.PosDef) (htrace : G⁻¹.trace ≤ T) :
    ∃ e : Fin k ↪ Fin (k + q),
      (G.submatrix e e - ((q : ℝ) * δ) • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef ∧
      (G.submatrix e e - ((q : ℝ) * δ) • (1 : Matrix (Fin k) (Fin k) ℝ))⁻¹.trace ≤ T := by
  induction q with
  | zero =>
    refine ⟨Function.Embedding.refl _, ?_, ?_⟩
    · simpa only [Function.Embedding.coe_refl, Matrix.submatrix_id_id, Nat.cast_zero,
        zero_mul, zero_smul, sub_zero] using hG
    · simpa only [Function.Embedding.coe_refl, Matrix.submatrix_id_id, Nat.cast_zero,
        zero_mul, zero_smul, sub_zero] using htrace
  | succ q ih =>
    obtain ⟨j, hjPos, hjTrace⟩ :=
      exists_principal_deletion_posDef_and_trace_inv_le hG hδ hT htrace hstep
    let B := (G - δ • (1 : Matrix (Fin (k + q + 1)) (Fin (k + q + 1)) ℝ)).submatrix
      j.succAbove j.succAbove
    obtain ⟨f, hfPos, hfTrace⟩ := ih B hjPos hjTrace
    let e : Fin k ↪ Fin (k + (q + 1)) :=
      ⟨fun i => j.succAbove (f i), Fin.succAbove_right_injective.comp f.injective⟩
    have heq : G.submatrix e e - (((q + 1 : ℕ) : ℝ) * δ) • (1 : Matrix (Fin k) (Fin k) ℝ) =
        B.submatrix f f - ((q : ℝ) * δ) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
      ext a b
      simp only [B, e, Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply]
      have hId : (1 : Matrix (Fin (k + q + 1)) (Fin (k + q + 1)) ℝ)
          (j.succAbove (f a)) (j.succAbove (f b)) = (1 : Matrix (Fin k) (Fin k) ℝ) a b :=
        congrArg (fun P : Matrix (Fin k) (Fin k) ℝ => P a b) (Matrix.submatrix_one e e.injective)
      rw [hId]
      simp only [Function.Embedding.coeFn_mk]
      push_cast
      ring
    exact ⟨e, heq.symm ▸ hfPos, heq.symm ▸ hfTrace⟩

/-- An inverse-trace budget supplies a principal submatrix with a quantitative
strict lower barrier. The lower bound gains one decrement for each deleted
coordinate and one final decrement from the retained inverse-trace budget. -/
theorem exists_embedding_posDef_sub_smul_one_of_trace_inv_le
    {r k : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) (hG : G.PosDef)
    (hk : k ≤ r) {T : ℝ} (hT : 0 < T) (htrace : G⁻¹.trace ≤ T) :
    ∃ e : Fin k ↪ Fin r,
      (G.submatrix e e - (((r - k + 1 : ℕ) : ℝ) / (2 * T)) •
        (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hk
  let δ : ℝ := 1 / (2 * T)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hstep : 2 * δ * T ≤ 1 := by
    dsimp [δ]
    exact le_of_eq (by field_simp)
  obtain ⟨e, hePos, heTrace⟩ :=
    exists_embedding_posDef_shift_trace_le_aux k q hδ hT hstep G hG htrace
  have hcap : δ * (G.submatrix e e - ((q : ℝ) * δ) •
      (1 : Matrix (Fin k) (Fin k) ℝ))⁻¹.trace < 1 := by
    have hh := mul_le_mul_of_nonneg_left heTrace hδ.le
    nlinarith
  have hfinal := hePos.sub_smul_one_posDef_of_mul_trace_inv_lt_one hδ hcap
  refine ⟨e, ?_⟩
  have heq : G.submatrix e e - ((q : ℝ) * δ) • (1 : Matrix (Fin k) (Fin k) ℝ) -
      δ • (1 : Matrix (Fin k) (Fin k) ℝ) =
      G.submatrix e e - (((k + q - k + 1 : ℕ) : ℝ) / (2 * T)) •
        (1 : Matrix (Fin k) (Fin k) ℝ) := by
    rw [Nat.add_sub_cancel_left]
    push_cast
    dsimp [δ]
    module
  rwa [heq] at hfinal

end NLAlib.RestrictedInvertibility
