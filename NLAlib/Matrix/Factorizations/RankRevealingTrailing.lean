import NLAlib.Matrix.Factorizations.RankRevealingLeading

/-!
# Trailing singular-value bound from the RRQR exchange budget

The top right-singular subspace of the trailing block, together with all
leading coordinates, supplies a max-min subspace. A single Frobenius estimate
keeps the exact shared budget and hence the Gu–Eisenstat factor.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The trailing singular-value estimate with the exact shared RRQR budget,
at every zero-padded index: `σⱼ(D) ≤ sqrt(1+b) σₖ₊ⱼ([R RT;0 D])`.
The leading block is genuinely invertible; no rank assumption is imposed on
the trailing block. Gu–Eisenstat 1996, Theorem 3.2; derivations equation
alg:rrqr-trailing. Supports `rank-revealing-qr`. -/
theorem singularValues_trailing_le_sqrt_budget_mul {k r q : ℕ}
    (R : Matrix (Fin k) (Fin k) ℝ) (T : Matrix (Fin k) (Fin q) ℝ)
    (D : Matrix (Fin r) (Fin q) ℝ) (hR : IsUnit R) (b : ℝ) (hb : 0 ≤ b)
    (hBudget : frobSq T + frobSq R⁻¹ * frobSq D ≤ b) (j : ℕ) :
    singularValues D j ≤ Real.sqrt (1 + b) *
      singularValues (Matrix.fromBlocks R (R * T) 0 D) (k + j) := by
  by_cases hj : j < q
  swap
  · rw [singularValues_eq_zero_of_width_le D
      (by simpa only [Fintype.card_fin] using Nat.le_of_not_gt hj)]
    exact mul_nonneg (Real.sqrt_nonneg _) (singularValues_nonneg _ _)
  let s := singularValues D j
  let M := Matrix.fromBlocks R (R * T) (0 : Matrix (Fin r) (Fin k) ℝ) D
  have hs0 : 0 ≤ s := singularValues_nonneg D j
  have hb1 : 0 < 1 + b := by linarith
  have hc : 0 < Real.sqrt (1 + b) := Real.sqrt_pos.mpr hb1
  obtain ⟨Y, hYdim, hY⟩ := exists_submodule_sq_singularValues_mul_le_mulVec_dotProduct D
    (by simpa only [Fintype.card_fin] using hj)
  let tail : ((Fin k ⊕ Fin q) → ℝ) →ₗ[ℝ] (Fin q → ℝ) :=
    { toFun := fun z a => z (Sum.inr a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let S := Y.comap tail
  let e : S ≃ₗ[ℝ] ((Fin k → ℝ) × Y) :=
    { toFun := fun z => (fun a => z.val (Sum.inl a), ⟨tail z.val, z.property⟩)
      invFun := fun z => ⟨Sum.elim z.1 z.2.val, z.2.property⟩
      left_inv := by intro z; apply Subtype.ext; funext a; cases a <;> rfl
      right_inv := by intro z; apply Prod.ext <;> rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hSdim : k + j + 1 ≤ Module.finrank ℝ S := by
    rw [e.finrank_eq, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
    omega
  have hLower : s / Real.sqrt (1 + b) ≤ singularValues M (k + j) := by
    apply le_singularValues_of_forall_mem M (k + j) S hSdim
    intro z hz
    let x : Fin k → ℝ := fun a => z (Sum.inl a)
    let y : Fin q → ℝ := fun a => z (Sum.inr a)
    let u := R *ᵥ (x + T *ᵥ y)
    let v := D *ᵥ y
    have hy : y ∈ Y := hz
    have hYv : s ^ 2 * (y ⬝ᵥ y) ≤ v ⬝ᵥ v := hY y hy
    have hu : R⁻¹ *ᵥ u = x + T *ᵥ y := by
      dsimp only [u]
      rw [Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det _).mp hR), Matrix.one_mulVec]
    have hScaled : Matrix.fromCols (s • R⁻¹) (-T) *ᵥ Sum.elim u (s • y) = s • x := by
      rw [Matrix.fromCols_mulVec_sumElim, Matrix.smul_mulVec, Matrix.neg_mulVec,
        Matrix.mulVec_smul, hu, smul_add, add_neg_cancel_right]
    have hFrob := mulVec_dotProduct_mulVec_le_frobSq_mul
      (Matrix.fromCols (s • R⁻¹) (-T)) (Sum.elim u (s • y))
    rw [hScaled, frobSq_fromCols, frobSq_smul, frobSq_neg,
      sumElim_dotProduct_sumElim, smul_dotProduct, dotProduct_smul,
      smul_dotProduct, dotProduct_smul] at hFrob
    simp only [smul_eq_mul] at hFrob
    have ha0 : 0 ≤ s ^ 2 * frobSq R⁻¹ + frobSq T :=
      add_nonneg (mul_nonneg (sq_nonneg s) (frobSq_nonneg R⁻¹)) (frobSq_nonneg T)
    have hMono := mul_le_mul_of_nonneg_left hYv ha0
    have hMain : s ^ 2 * (x ⬝ᵥ x + y ⬝ᵥ y) ≤
        (1 + s ^ 2 * frobSq R⁻¹ + frobSq T) * (u ⬝ᵥ u + v ⬝ᵥ v) := by
      nlinarith [dotProduct_self_nonneg u]
    have hsF : s ^ 2 ≤ frobSq D := by
      have hsd := singularValues_le_specNorm D j
      have hsn := singularValues_nonneg D j
      have hf := specNorm_sq_le_frobSq D
      dsimp only [s]
      nlinarith [specNorm_nonneg D]
    have hCoef : 1 + s ^ 2 * frobSq R⁻¹ + frobSq T ≤ 1 + b := by
      have hmul := mul_le_mul_of_nonneg_right hsF (frobSq_nonneg R⁻¹)
      nlinarith
    have hMono' := mul_le_mul_of_nonneg_right hCoef
      (add_nonneg (dotProduct_self_nonneg u) (dotProduct_self_nonneg v))
    have hzSplit : z = Sum.elim x y := by funext a; cases a <;> rfl
    have hImage : M *ᵥ z = Sum.elim u v := by
      rw [hzSplit, Matrix.fromBlocks_mulVec]
      simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
        Matrix.zero_mulVec, zero_add, u, v, Matrix.mulVec_add, Matrix.mulVec_mulVec]
    simp only [RCLike.re_to_real, star_trivial]
    rw [hImage, hzSplit, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim,
      div_pow, Real.sq_sqrt hb1.le, div_mul_eq_mul_div, div_le_iff₀ hb1]
    nlinarith
  exact (div_le_iff₀ hc).mp hLower |>.trans_eq (mul_comm _ _)

end NLAlib
