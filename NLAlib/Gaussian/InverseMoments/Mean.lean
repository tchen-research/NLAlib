/-
Ported from the Prove2me workspace (Gaussian Random Matrices series, solutions
`Sol_GaussianMatrix_inverse_wishart_mean`, `Sol_GaussianMatrix_pinv_frobenius_moment`).
-/
import NLAlib.Gaussian.InverseMoments.Residual
import NLAlib.Gaussian.Moments
import NLAlib.Gaussian.Extreme.ChiSquare
import NLAlib.Matrix.Measurable
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Mean of the inverse Wishart matrix and the Frobenius moment of the pseudoinverse

The key Gaussian input of the randomized SVD and generalized Nyström error bounds:
for a standard Gaussian `r × k` matrix `G` with `r + 2 ≤ k`,
`E (G Gᵀ)⁻¹ = (k - r - 1)⁻¹ I` and hence `E ‖G†‖_F² = r / (k - r - 1)`.

* `integrable_and_integral_inv_self_mul_transpose_gaussianMatrix`:
  `E (G Gᵀ)⁻¹ = (k - r - 1)⁻¹ I`, entrywise, with integrability (atlas `inverse-wishart-mean`);
  `integral_inv_self_mul_transpose_gaussianMatrix` is the matrix form.
* `integrable_and_integral_frobSq_pinvR_gaussianMatrix`: `E ‖G†‖_F² = r / (k - r - 1)`
  (atlas `pinv-frob-moment`).

Proof source: Prove2me workspace, Gaussian Random Matrices series; the proofs are ported with
the workspace's `rotation_invariance`, `block_law`, `full_rank_ae` replaced by
`NLAlib.gaussianMatrix_map_orthogonal`, `NLAlib.gaussianMatrix_map_block`,
`NLAlib.gaussianMatrix_ae_rank_eq`. The scalar input `E[1/χ²_d] = 1/(d-2)` is
`NLAlib.integrable_and_integral_inv_sum_sq_gaussianReal` (`Gaussian/Extreme/ChiSquare.lean`), the
identity `‖G†‖_F² = tr (G Gᵀ)⁻¹` is `NLAlib.frobSq_pinvR_eq_trace_inv`
(`Matrix/Pseudoinverse.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped Matrix

namespace NLAlib

/-! ### Mean of the inverse Wishart matrix -/

private lemma integral_inv_self_mul_transpose_apply_of_ne {r k : ℕ} (i j : Fin r)
    (hij : i ≠ j) :
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ∂(gaussianMatrix r k) = 0 := by
  classical
  set D : Matrix (Fin r) (Fin r) ℝ := Matrix.diagonal fun a => if a = i then -1 else 1 with hD
  have hDD : D * D = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> norm_num
  have hDt : Dᵀ = D := Matrix.diagonal_transpose _
  have hU : Dᵀ * D = 1 := by rw [hDt, hDD]
  have hrot := gaussianMatrix_map_orthogonal D (1 : Matrix (Fin k) (Fin k) ℝ) hU (by simp)
  have hmeas : Measurable (fun G : Fin r → Fin k → ℝ =>
      Matrix.of.symm (D * Matrix.of G * (1 : Matrix (Fin k) (Fin k) ℝ))) := by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    simp only [Matrix.of_symm_apply, Matrix.mul_one, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hDinv : D⁻¹ = D := Matrix.inv_eq_left_inv hDD
  have key : ∀ G : Fin r → Fin k → ℝ,
      (Matrix.of (Matrix.of.symm (D * Matrix.of G * (1 : Matrix (Fin k) (Fin k) ℝ))) *
        (Matrix.of (Matrix.of.symm (D * Matrix.of G * (1 : Matrix (Fin k) (Fin k) ℝ))))ᵀ)⁻¹ i j
        = -(Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j := by
    intro G
    simp only [Equiv.apply_symm_apply, Matrix.mul_one, Matrix.transpose_mul, hDt]
    rw [show D * Matrix.of G * ((Matrix.of G)ᵀ * D) = D * (Matrix.of G * (Matrix.of G)ᵀ) * D by
      simp [Matrix.mul_assoc]]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hDinv, hD]
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Ne.symm hij]
  have h1 : ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ∂(gaussianMatrix r k) =
      ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j
        ∂(Measure.map (fun G => Matrix.of.symm (D * Matrix.of G *
          (1 : Matrix (Fin k) (Fin k) ℝ))) (gaussianMatrix r k)) := by
    rw [hrot]
  rw [integral_map hmeas.aemeasurable
    (measurable_inv_self_mul_transpose_apply i j).aestronglyMeasurable] at h1
  simp_rw [key, integral_neg] at h1
  linarith

private lemma integrable_and_integral_inv_sq_dist_rowSpace {n k : ℕ} (hnk : n + 3 ≤ k)
    (H : Matrix (Fin n) (Fin k) ℝ)
    (hH : H.rank = n) :
    Integrable (fun g : Fin k → ℝ => (g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹)
        (Measure.pi fun _ : Fin k => gaussianReal 0 1) ∧
    ∫ g, (g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹
        ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) = 1 / ((k : ℝ) - n - 2) := by
  have hq : Measurable
      (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g))) := by
    apply Continuous.measurable
    fun_prop
  have hlaw := pi_gaussianReal_map_sq_dist_rowSpace H hH
  obtain ⟨hint, hval⟩ :=
    integrable_and_integral_inv_sum_sq_gaussianReal_fin (d := k - n) (by omega)
  have hφ : Measurable (fun s : ℝ => s⁻¹) := measurable_inv
  have hS : Measurable (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2) := by fun_prop
  constructor
  · have h := (integrable_map_measure hφ.aestronglyMeasurable hS.aemeasurable).mpr hint
    rw [← hlaw] at h
    exact (integrable_map_measure hφ.aestronglyMeasurable hq.aemeasurable).mp h
  · rw [← integral_map hq.aemeasurable hφ.aestronglyMeasurable, hlaw,
      integral_map hS.aemeasurable hφ.aestronglyMeasurable, hval,
      Nat.cast_sub (by omega : n ≤ k)]

private lemma integrable_and_integral_inv_self_mul_transpose_apply_self {n k : ℕ}
    (hnk : n + 3 ≤ k) (i : Fin (n + 1)) :
    Integrable (fun G : Fin (n + 1) → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i)
        (gaussianMatrix (n + 1) k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ∂(gaussianMatrix (n + 1) k)
      = 1 / ((k : ℝ) - n - 2) := by
  set μ : Measure (Fin k → ℝ) := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hμ
  set ν : Measure (Fin n → Fin k → ℝ) := Measure.pi fun _ : Fin n => μ with hν
  set F : (Fin (n + 1) → Fin k → ℝ) → ℝ :=
    fun G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i with hF
  have hFm : Measurable F := measurable_inv_self_mul_transpose_apply i i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin k → ℝ) i with he
  have hmp : MeasurePreserving e (gaussianMatrix (n + 1) k) (μ.prod ν) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  set Φ : (Fin k → ℝ) × (Fin n → Fin k → ℝ) → ℝ := fun p => F (e.symm p) with hΦ
  have hΦm : Measurable Φ := hFm.comp e.symm.measurable
  have hΦnn : ∀ p, 0 ≤ Φ p := fun p => (posSemidef_inv_self_mul_transpose _).diag_nonneg
  -- on the full-rank event, the inner integrand is the inverse residual
  have hschur : ∀ H : Fin n → Fin k → ℝ, (Matrix.of H).rank = n → ∀ g : Fin k → ℝ,
      Φ (g, H) = (g ⬝ᵥ g - (Matrix.of H *ᵥ g) ⬝ᵥ
        ((Matrix.of H * (Matrix.of H)ᵀ)⁻¹ *ᵥ (Matrix.of H *ᵥ g)))⁻¹ := by
    intro H hH g
    set G0 : Fin (n + 1) → Fin k → ℝ := Fin.insertNth i g H with hG0
    have hsub : (Matrix.of G0).submatrix i.succAbove id = Matrix.of H := by
      ext a b; simp [hG0]
    have hrow : Matrix.of G0 i = g := by funext b; simp [hG0]
    have hdet : ((Matrix.of G0).submatrix i.succAbove id *
        ((Matrix.of G0).submatrix i.succAbove id)ᵀ).det ≠ 0 := by
      rw [hsub]
      exact det_ne_zero_of_rank_eq _ (by rw [Matrix.rank_self_mul_transpose, hH, Fintype.card_fin])
    have := inv_self_mul_transpose_apply_self (Matrix.of G0) i hdet
    rw [hsub, hrow] at this
    simp only [hΦ, hF, he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    exact this
  have hrank : ∀ᵐ H ∂ν, (Matrix.of H).rank = n := by
    have := gaussianMatrix_ae_rank_eq n k
    filter_upwards [this] with H hH
    rw [hH]; omega
  have hinner : ∀ᵐ H ∂ν, Integrable (fun g => Φ (g, H)) μ ∧
      ∫ g, Φ (g, H) ∂μ = 1 / ((k : ℝ) - n - 2) := by
    filter_upwards [hrank] with H hH
    simp_rw [hschur H hH]
    exact integrable_and_integral_inv_sq_dist_rowSpace hnk (Matrix.of H) hH
  have hint : Integrable Φ (μ.prod ν) := by
    rw [integrable_prod_iff' hΦm.aestronglyMeasurable]
    refine ⟨hinner.mono fun H h => h.1, ?_⟩
    refine (integrable_const (1 / ((k : ℝ) - n - 2))).congr ?_
    filter_upwards [hinner] with H hH
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hΦnn _)]
    exact hH.2.symm
  constructor
  · have := (hmp.integrable_comp_emb e.measurableEmbedding (g := Φ)).mpr hint
    refine this.congr (Filter.Eventually.of_forall fun G => ?_)
    simp [hΦ, hF]
  · have h1 := hmp.integral_comp' Φ
    simp only [hΦ, MeasurableEquiv.symm_apply_apply] at h1
    rw [h1, integral_prod_symm Φ hint]
    rw [integral_congr_ae (hinner.mono fun H h => h.2)]
    simp

/-- **Mean of the inverse Wishart matrix.** If `G` is an `r × k` standard Gaussian matrix with
`r + 2 ≤ k`, every entry of `(G Gᵀ)⁻¹` is integrable and `E (G Gᵀ)⁻¹ = (k - r - 1)⁻¹ I`
(stated entrywise: `E[(G Gᵀ)⁻¹ᵢⱼ] = (k - r - 1)⁻¹ δᵢⱼ`).

Tropp–Webber 2023, Lemma B.2; HMT 2011, Prop A.5 (used in Prop 10.2). Atlas:
`inverse-wishart-mean`. The source writes `E (G Gᵀ)⁻¹` as a matrix; here it is entrywise, which
avoids choosing a norm on matrices. Proof ported from the Prove2me solution
`Sol_GaussianMatrix_inverse_wishart_mean`: off-diagonal entries vanish by sign-flip invariance
(atlas `rotation-invariance`); a diagonal entry is the inverse squared residual of one row
against the others (`inv_self_mul_transpose_apply_self`), which given the other rows (full rank
a.s., atlas `gaussian-full-rank-ae`) is `1/χ²_{k-r+1}` (`pi_gaussianReal_map_sq_dist_rowSpace`,
atlas `block-law-indep`; `integrable_and_integral_inv_sum_sq_gaussianReal`, atlas
`inverse-chi-square-moment`). -/
theorem integrable_and_integral_inv_self_mul_transpose_gaussianMatrix {r k : ℕ}
    (hrk : r + 2 ≤ k) :
    (∀ i j : Fin r, Integrable (fun G : Fin r → Fin k → ℝ =>
        (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j) (gaussianMatrix r k)) ∧
    ∀ i j : Fin r, ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ∂(gaussianMatrix r k)
      = (1 / ((k : ℝ) - r - 1)) * (1 : Matrix (Fin r) (Fin r) ℝ) i j := by
  have hdiag : ∀ i : Fin r, Integrable (fun G : Fin r → Fin k → ℝ =>
      (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i) (gaussianMatrix r k) := by
    intro i
    cases r with
    | zero => exact i.elim0
    | succ n =>
      exact (integrable_and_integral_inv_self_mul_transpose_apply_self (by omega) i).1
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · refine Integrable.mono' ((hdiag i).add (hdiag j))
      (measurable_inv_self_mul_transpose_apply i j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun G => ?_)
    rw [Real.norm_eq_abs]
    exact abs_apply_le_apply_self_add_apply_self _
      (posSemidef_inv_self_mul_transpose (Matrix.of G)) i j
  · by_cases hij : i = j
    · subst hij
      cases r with
      | zero => exact i.elim0
      | succ n =>
        rw [(integrable_and_integral_inv_self_mul_transpose_apply_self (by omega) i).2,
          Matrix.one_apply_eq, mul_one]
        push_cast
        ring_nf
    · rw [integral_inv_self_mul_transpose_apply_of_ne i j hij, Matrix.one_apply_ne hij,
        mul_zero]

/-- **Mean of the inverse Wishart matrix, matrix form.** For an `r × k` standard Gaussian matrix
`G` with `r + 2 ≤ k`, the matrix of entrywise expectations of `(G Gᵀ)⁻¹` is `(k - r - 1)⁻¹ • I`.

Tropp–Webber 2023, Lemma B.2; HMT 2011, Prop A.5. Atlas: `inverse-wishart-mean`. Corollary of
`integrable_and_integral_inv_self_mul_transpose_gaussianMatrix` (entrywise integrability is its
first component). -/
theorem integral_inv_self_mul_transpose_gaussianMatrix {r k : ℕ} (hrk : r + 2 ≤ k) :
    (Matrix.of fun i j : Fin r =>
        ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ∂(gaussianMatrix r k))
      = (1 / ((k : ℝ) - r - 1)) • (1 : Matrix (Fin r) (Fin r) ℝ) := by
  ext i j
  rw [Matrix.of_apply, (integrable_and_integral_inv_self_mul_transpose_gaussianMatrix hrk).2 i j,
    Matrix.smul_apply, smul_eq_mul]

/-! ### Frobenius moment of the pseudoinverse -/

/-- **Frobenius moment of the Gaussian pseudoinverse.** If `G` is an `r × k` standard Gaussian
matrix with `r + 2 ≤ k`, then `‖G†‖_F²` is integrable and `E ‖G†‖_F² = r / (k - r - 1)`, where
`G† = Gᵀ (G Gᵀ)⁻¹ = pinvR G`.

Tropp–Webber 2023, Lemma B.2; HMT 2011, Prop 10.2 (`E ‖Ω₁†‖_F² = k/(p-1)` with `Ω₁` of size
`k × (k+p)`). Atlas: `pinv-frob-moment`. Proof ported from the Prove2me solution
`Sol_GaussianMatrix_pinv_frobenius_moment`: `‖G†‖_F² = tr (G Gᵀ)⁻¹`
(`frobSq_pinvR_eq_trace_inv`, atlas `pseudoinverse`) and
`integrable_and_integral_inv_self_mul_transpose_gaussianMatrix` (atlas `inverse-wishart-mean`). -/
theorem integrable_and_integral_frobSq_pinvR_gaussianMatrix {r k : ℕ} (hrk : r + 2 ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => frobSq (pinvR (Matrix.of G)))
      (gaussianMatrix r k) ∧
    ∫ G, frobSq (pinvR (Matrix.of G)) ∂(gaussianMatrix r k) = (r : ℝ) / ((k : ℝ) - r - 1) := by
  obtain ⟨hint, hval⟩ := integrable_and_integral_inv_self_mul_transpose_gaussianMatrix hrk
  have hfun : (fun G : Fin r → Fin k → ℝ => frobSq (pinvR (Matrix.of G)))
      = fun G => ∑ i, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i := by
    funext G; rw [frobSq_pinvR_eq_trace_inv]; rfl
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun i _ => hint i i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hint i i]
  simp only [hval, Matrix.one_apply_eq, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

end NLAlib
