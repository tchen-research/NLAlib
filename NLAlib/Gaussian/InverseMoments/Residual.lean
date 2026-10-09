/-
Ported from the Prove2me workspace (Gaussian Random Matrices series, solutions
`Sol_GaussianMatrix_schur_diag_inv`, `Sol_GaussianMatrix_residual_law`).
-/
import NLAlib.Gaussian.InverseMoments.SchurComplement

/-!
# Diagonal of the inverse Gram matrix and the law of the residual

For `G` with rows indexed by `Fin (n + 1)`, `H` the matrix of the rows other than `i` and
`g = Gᵢ`:

* `inv_self_mul_transpose_apply_self`: `(G Gᵀ)⁻¹ᵢᵢ = (‖g‖² - (H g)ᵀ (H Hᵀ)⁻¹ (H g))⁻¹`, the
  inverse squared distance from `g` to the row space of `H` (Schur complement);
* `pi_gaussianReal_map_sq_dist_rowSpace`: for a standard Gaussian row `g` and fixed `H` of full
  rank `n`, that squared distance is `χ²_{k-n}`.

Atlas: `inverse-wishart-mean` (helpers). Proof source: Prove2me workspace, Gaussian Random
Matrices series (`schur_diag_inv`, `residual_law`), with the block law
`NLAlib.gaussianMatrix_map_block` (atlas `block-law-indep`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-! ### Schur complement formula for a diagonal entry of `(G Gᵀ)⁻¹` -/

/-- **Diagonal entry of the inverse Gram matrix (Schur complement).** Let `G` have rows indexed by
`Fin (n + 1)`, let `H` be `G` with row `i` removed and `g = G i`. If `H Hᵀ` is invertible, then
`(G Gᵀ)⁻¹ᵢᵢ = (‖g‖² - (H g)ᵀ (H Hᵀ)⁻¹ (H g))⁻¹`, the inverse squared distance from `g` to the
row space of `H`.

Helper for Tropp–Webber 2023, Lemma B.2 / HMT 2011, Prop A.5 (proof of `E (G Gᵀ)⁻¹`).
Atlas: `inverse-wishart-mean` (helper). Proof ported from the Prove2me solution
`Sol_GaussianMatrix_schur_diag_inv` (adjugate computation). -/
theorem inv_self_mul_transpose_apply_self {n k : ℕ} (G : Matrix (Fin (n + 1)) (Fin k) ℝ)
    (i : Fin (n + 1))
    (hH : (G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ).det ≠ 0) :
    (G * Gᵀ)⁻¹ i i =
      (G i ⬝ᵥ G i - (G.submatrix i.succAbove id *ᵥ G i) ⬝ᵥ
        ((G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᵀ)⁻¹ *ᵥ
          (G.submatrix i.succAbove id *ᵥ G i)))⁻¹ := by
  set H : Matrix (Fin n) (Fin k) ℝ := G.submatrix i.succAbove id with hHdef
  set g : Fin k → ℝ := G i with hg
  set M : Matrix (Fin n) (Fin n) ℝ := H * Hᵀ with hM
  set c : Fin n → ℝ := M⁻¹ *ᵥ (H *ᵥ g) with hc
  set s : ℝ := g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ c with hs
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := G * Gᵀ with hA
  set w : Fin k → ℝ := g - Hᵀ *ᵥ c with hw
  set x : Fin (n + 1) → ℝ := Fin.insertNth i (1 : ℝ) (-c) with hx
  -- residual is orthogonal to the other rows
  have hHw : H *ᵥ w = 0 := by
    rw [hw, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← hM, hc, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH), Matrix.one_mulVec, sub_self]
  have hgw : g ⬝ᵥ w = s := by
    rw [hw, dotProduct_sub, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  -- Gᵀ x = w
  have hGx : Gᵀ *ᵥ x = w := by
    funext l
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hw, hx, Pi.sub_apply, hg,
      hHdef, Matrix.submatrix_apply, id]
    rw [Fin.sum_univ_succAbove _ i]
    simp [sub_eq_add_neg, Finset.sum_neg_distrib]
  -- G w = s e_i
  have hGw : G *ᵥ w = Pi.single i s := by
    funext b
    induction b using Fin.succAboveCases i with
    | x =>
      simp only [Pi.single_eq_same]
      rw [← hgw]; rfl
    | p a =>
      rw [Pi.single_eq_of_ne (Fin.succAbove_ne i a)]
      have := congrFun hHw a
      simpa [Matrix.mulVec, hHdef] using this
  have hAx : A *ᵥ x = Pi.single i s := by
    rw [hA, ← Matrix.mulVec_mulVec, hGx, hGw]
  -- the adjugate diagonal entry is det M
  have hadj : A.adjugate i i = M.det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have : A.submatrix i.succAbove i.succAbove = M := by
      ext a b
      simp [hA, hM, hHdef, Matrix.mul_apply]
    rw [this, ← two_mul, pow_mul]
    norm_num
  -- det A = s * det M
  have hdetA : A.det = s * M.det := by
    have h1 : A.adjugate *ᵥ (A *ᵥ x) = A.det • x := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hAx] at h1
    have h2 := congrFun h1 i
    have h3 : (A.adjugate *ᵥ Pi.single i s) i = A.adjugate i i * s := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h3, Pi.smul_apply, smul_eq_mul, hx, Fin.insertNth_apply_same, mul_one, hadj] at h2
    rw [← h2, mul_comm]
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', hdetA, hadj,
    mul_inv, mul_assoc, inv_mul_cancel₀ hH, mul_one]

/-! ### Law of the residual of a Gaussian row -/

/-- A standard Gaussian vector mapped by `Vᵀ`, with `V` having orthonormal columns, is a
standard Gaussian vector (the case `t = 1` of `gaussianMatrix_map_block`, reshaped). -/
private lemma pi_gaussianReal_map_transpose_mulVec {m d : ℕ} (V : Matrix (Fin m) (Fin d) ℝ)
    (hV : Vᵀ * V = 1) :
    Measure.map (fun g : Fin m → ℝ => Vᵀ *ᵥ g) (Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
  have hι : ∀ p : ℕ, MeasurePreserving
      (fun (g : Fin p → ℝ) (a : Fin p) => (MeasurableEquiv.funUnique (Fin 1) ℝ).symm (g a))
      (Measure.pi fun _ : Fin p => gaussianReal 0 1) (gaussianMatrix p 1) := fun p =>
    measurePreserving_pi _ _ fun _ =>
      (measurePreserving_funUnique (gaussianReal 0 1) (Fin 1)).symm
  have hev : ∀ p : ℕ, MeasurePreserving
      (fun (G : Fin p → Fin 1 → ℝ) (a : Fin p) => MeasurableEquiv.funUnique (Fin 1) ℝ (G a))
      (gaussianMatrix p 1) (Measure.pi fun _ : Fin p => gaussianReal 0 1) := fun p =>
    measurePreserving_pi _ _ fun _ => measurePreserving_funUnique (gaussianReal 0 1) (Fin 1)
  have hB := gaussianMatrix_map_block (t := 1) V hV
  have hFm : Measurable (fun G : Fin m → Fin 1 → ℝ => Matrix.of.symm (Vᵀ * Matrix.of G)) := by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hfun : (fun g : Fin m → ℝ => Vᵀ *ᵥ g) =
      (fun (G : Fin d → Fin 1 → ℝ) (a : Fin d) => MeasurableEquiv.funUnique (Fin 1) ℝ (G a)) ∘
      (fun G : Fin m → Fin 1 → ℝ => Matrix.of.symm (Vᵀ * Matrix.of G)) ∘
      (fun (g : Fin m → ℝ) (a : Fin m) => (MeasurableEquiv.funUnique (Fin 1) ℝ).symm (g a)) := by
    funext g a
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, MeasurableEquiv.funUnique]
  rw [hfun, ← Measure.map_map (hev d).measurable (hFm.comp (hι m).measurable),
    ← Measure.map_map hFm (hι m).measurable, (hι m).map_eq, hB, (hev d).map_eq]

/-- **Law of the residual of a Gaussian row.** Let `H` be a fixed `n × k` real matrix of rank
`n` and `g` a standard Gaussian vector in `ℝᵏ`. The squared distance from `g` to the row space of
`H`, `‖g‖² - (H g)ᵀ (H Hᵀ)⁻¹ (H g)`, has the `χ²_{k-n}` law (the law of `∑ⱼ Xⱼ²`,
`X ~ N(0, I_{k-n})`).

Helper for Tropp–Webber 2023, Lemma B.2 / HMT 2011, Prop A.5. Atlas: `inverse-wishart-mean`
(helper). Proof ported from the Prove2me solution `Sol_GaussianMatrix_residual_law`
(orthonormal basis of `ker H` and the block law `gaussianMatrix_map_block`, atlas
`block-law-indep`). -/
theorem pi_gaussianReal_map_sq_dist_rowSpace {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℝ)
    (hH : H.rank = n) :
    Measure.map (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))
        (Measure.pi fun _ : Fin k => gaussianReal 0 1)
      = Measure.map (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2)
        (Measure.pi fun _ : Fin (k - n) => gaussianReal 0 1) := by
  obtain ⟨V, hV, -, hq⟩ := exists_orthonormal_ker_sq_dist_rowSpace H hH
  have hfun : (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g))) =
      (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2) ∘ (fun g : Fin k → ℝ => Vᵀ *ᵥ g) := funext hq
  have hS : Measurable (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2) := by fun_prop
  have hVm : Measurable (fun g : Fin k → ℝ => Vᵀ *ᵥ g) := by
    refine measurable_pi_lambda _ fun a => ?_
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  rw [hfun, ← Measure.map_map hS hVm, pi_gaussianReal_map_transpose_mulVec V hV]

end NLAlib
