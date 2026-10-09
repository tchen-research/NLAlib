/-
Ported from the Prove2me workspace (Gaussian Random Matrices series, solutions
`Sol_GaussianMatrix_inverse_wishart_diag_law`, `Sol_GaussianMatrix_inverse_wishart_diag_sq_moment`).
-/
import NLAlib.Gaussian.InverseMoments.Residual
import NLAlib.Gaussian.Moments
import NLAlib.Matrix.Measurable
import NLAlib.Gaussian.Extreme.ChiSquare

/-!
# Diagonal entries of the inverse Wishart matrix

For an `r × k` standard Gaussian matrix `G` with `r ≤ k`, each diagonal entry of `(G Gᵀ)⁻¹` is
the inverse of a `χ²_{k-r+1}` variable: it is the inverse squared distance from one row to the
span of the others (Schur complement), and given the other rows that squared distance is
`χ²_{k-r+1}`.

* `gaussianMatrix_map_inv_self_mul_transpose_apply_self`: the law of `(G Gᵀ)⁻¹ᵢᵢ` is the law of
  `1/χ²_{k-r+1}`;
* `integrable_and_integral_inv_sq_dist_rowSpace_sq`: for fixed full-rank `H` and a standard
  Gaussian vector `g`, `E[Q_H(g)^{-2}] = 1/((k-n-2)(k-n-4))` (`Q_H(g)` the squared distance
  from `g` to the row space of `H`);
* `integrable_and_integral_inv_self_mul_transpose_apply_self_sq_gaussianMatrix`:
  `E[(G Gᵀ)⁻¹ᵢᵢ²] = 1/((k-r-1)(k-r-3))` for `r + 4 ≤ k`.

Atlas: `inverse-wishart-frob-moment`, `pinv-frob-tail` (helpers). Proof source: Prove2me
workspace, Gaussian Random Matrices series, with the workspace's `full_rank_ae`,
`schur_diag_inv`, `residual_law`, `inv_sq_chi_square_moment` replaced by
`gaussianMatrix_ae_rank_eq`, `inv_self_mul_transpose_apply_self`,
`pi_gaussianReal_map_sq_dist_rowSpace`, `integrable_and_integral_inv_sum_sq_pow_two_gaussianReal`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- The law of the inverse squared residual of a standard Gaussian vector against a fixed
full-rank `n × k` matrix is the law of `1/χ²_{k-n}`. -/
private lemma pi_gaussianReal_map_inv_sq_dist_rowSpace {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℝ)
    (hH : H.rank = n) :
    Measure.map (fun g : Fin k → ℝ => (g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹)
        (Measure.pi fun _ : Fin k => gaussianReal 0 1)
      = Measure.map (fun x : Fin (k - n) → ℝ => (∑ j, x j ^ 2)⁻¹)
        (Measure.pi fun _ : Fin (k - n) => gaussianReal 0 1) := by
  have hq : Measurable (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g))) := by
    apply Continuous.measurable
    fun_prop
  have hS : Measurable (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2) := by fun_prop
  have h1 := Measure.map_map (μ := Measure.pi fun _ : Fin k => gaussianReal 0 1) measurable_inv hq
  have h2 := Measure.map_map (μ := Measure.pi fun _ : Fin (k - n) => gaussianReal 0 1)
    measurable_inv hS
  rw [Function.comp_def] at h1 h2
  rw [← h1, ← h2, pi_gaussianReal_map_sq_dist_rowSpace H hH]

/-- Schur complement in product coordinates: inserting a row `g` at position `i` into a
full-rank `H`, the `i`-th diagonal entry of the inverse Gram matrix is the inverse squared
residual of `g` against `H`. -/
private lemma inv_self_mul_transpose_insertNth_apply_self {n k : ℕ} (i : Fin (n + 1))
    (H : Fin n → Fin k → ℝ) (hH : (Matrix.of H).rank = n) (g : Fin k → ℝ) :
    (Matrix.of (Fin.insertNth i g H) * (Matrix.of (Fin.insertNth i g H))ᵀ)⁻¹ i i
      = (g ⬝ᵥ g - (Matrix.of H *ᵥ g) ⬝ᵥ
          ((Matrix.of H * (Matrix.of H)ᵀ)⁻¹ *ᵥ (Matrix.of H *ᵥ g)))⁻¹ := by
  set G0 : Fin (n + 1) → Fin k → ℝ := Fin.insertNth i g H with hG0
  have hsub : (Matrix.of G0).submatrix i.succAbove id = Matrix.of H := by
    ext a b; simp [hG0]
  have hrow : Matrix.of G0 i = g := by funext b; simp [hG0]
  have hdet : ((Matrix.of G0).submatrix i.succAbove id *
      ((Matrix.of G0).submatrix i.succAbove id)ᵀ).det ≠ 0 := by
    rw [hsub]
    exact det_ne_zero_of_rank_eq _
      (by rw [Matrix.rank_self_mul_transpose, hH, Fintype.card_fin])
  have := inv_self_mul_transpose_apply_self (Matrix.of G0) i hdet
  rw [hsub, hrow] at this
  exact this

private lemma map_inv_self_mul_transpose_apply_self_succ {n k : ℕ} (hnk : n ≤ k)
    (i : Fin (n + 1)) :
    Measure.map (fun G : Fin (n + 1) → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i)
        (gaussianMatrix (n + 1) k)
      = Measure.map (fun x : Fin (k - n) → ℝ => (∑ j, x j ^ 2)⁻¹)
        (Measure.pi fun _ : Fin (k - n) => gaussianReal 0 1) := by
  set μ : Measure (Fin k → ℝ) := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hμ
  set ν : Measure (Fin n → Fin k → ℝ) := Measure.pi fun _ : Fin n => μ with hν
  set F : (Fin (n + 1) → Fin k → ℝ) → ℝ := fun G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i with hF
  have hFm : Measurable F := measurable_inv_self_mul_transpose_apply i i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin k → ℝ) i with he
  have hmp : MeasurePreserving e (gaussianMatrix (n + 1) k) (μ.prod ν) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  set Φ : (Fin k → ℝ) × (Fin n → Fin k → ℝ) → ℝ := fun p => F (e.symm p) with hΦ
  have hΦm : Measurable Φ := hFm.comp e.symm.measurable
  have hschur : ∀ H : Fin n → Fin k → ℝ, (Matrix.of H).rank = n → ∀ g : Fin k → ℝ,
      Φ (g, H) = (g ⬝ᵥ g - (Matrix.of H *ᵥ g) ⬝ᵥ
        ((Matrix.of H * (Matrix.of H)ᵀ)⁻¹ *ᵥ (Matrix.of H *ᵥ g)))⁻¹ := by
    intro H hH g
    simp only [hΦ, hF, he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    exact inv_self_mul_transpose_insertNth_apply_self i H hH g
  have hrank : ∀ᵐ H ∂ν, (Matrix.of H).rank = n := by
    have := gaussianMatrix_ae_rank_eq n k
    filter_upwards [this] with H hH
    rw [hH]; omega
  have hmap : Measure.map F (gaussianMatrix (n + 1) k) = Measure.map Φ (μ.prod ν) := by
    rw [← hmp.map_eq, Measure.map_map hΦm e.measurable]
    congr 1
    funext G
    simp [hΦ]
  rw [hmap]
  ext s hs
  rw [Measure.map_apply hΦm hs, Measure.prod_apply_symm (hΦm hs)]
  have hinner : ∀ᵐ H ∂ν, μ ((fun g => (g, H)) ⁻¹' (Φ ⁻¹' s))
      = (Measure.map (fun x : Fin (k - n) → ℝ => (∑ j, x j ^ 2)⁻¹)
          (Measure.pi fun _ : Fin (k - n) => gaussianReal 0 1)) s := by
    filter_upwards [hrank] with H hH
    have hq : Measurable (fun g : Fin k → ℝ => (g ⬝ᵥ g - (Matrix.of H *ᵥ g) ⬝ᵥ
        ((Matrix.of H * (Matrix.of H)ᵀ)⁻¹ *ᵥ (Matrix.of H *ᵥ g)))⁻¹) := by
      apply Measurable.inv
      apply Continuous.measurable
      fun_prop
    rw [← pi_gaussianReal_map_inv_sq_dist_rowSpace (Matrix.of H) hH, Measure.map_apply hq hs]
    congr 1
    ext g
    simp only [Set.mem_preimage]
    rw [hschur H hH g]
  rw [lintegral_congr_ae hinner, lintegral_const, measure_univ, mul_one]

/-- **Law of a diagonal entry of the inverse Wishart matrix.** For an `r × k` standard Gaussian
matrix `G` with `r ≤ k` and any `i`, `(G Gᵀ)⁻¹ᵢᵢ` has the law of `1/χ²_{k-r+1}`, i.e. of
`(∑ⱼ xⱼ²)⁻¹` for a standard Gaussian vector `x ∈ ℝ^{k-r+1}`.

HMT 2011, proof of Prop A.5 / Tropp–Webber 2023, proof of Lemma B.2 (each diagonal entry of an
inverse Wishart matrix is an inverse chi-square). Atlas: `pinv-frob-tail`,
`inverse-wishart-frob-moment` (helper). Proof: Schur complement
(`inv_self_mul_transpose_apply_self`), conditioning on the other rows, which have full rank
a.s. (`gaussianMatrix_ae_rank_eq`, atlas `gaussian-full-rank-ae`), and the residual law
(`pi_gaussianReal_map_sq_dist_rowSpace`, atlas `block-law-indep`). Ported from Prove2me
solution `GaussianMatrix.inverse_wishart_diag_law`. -/
theorem gaussianMatrix_map_inv_self_mul_transpose_apply_self {r k : ℕ} (hrk : r ≤ k)
    (i : Fin r) :
    Measure.map (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i)
        (gaussianMatrix r k)
      = Measure.map (fun x : Fin (k - r + 1) → ℝ => (∑ j, x j ^ 2)⁻¹)
        (Measure.pi fun _ : Fin (k - r + 1) => gaussianReal 0 1) := by
  cases r with
  | zero => exact i.elim0
  | succ n =>
    have h : k - (n + 1) + 1 = k - n := by omega
    rw [h]
    exact map_inv_self_mul_transpose_apply_self_succ (by omega) i

/-- Squared inverse residual: `E[Q_H(g)^{-2}] = 1/((k-n-2)(k-n-4))` for a fixed full-rank `H`
and a standard Gaussian vector `g ∈ ℝᵏ`, where `Q_H(g)` is the squared distance from `g` to the
row space of `H`.

Helper for Tropp–Webber 2023, Lemma B.2. Atlas: `inverse-wishart-frob-moment` (helper). Ported
from the Prove2me solution `Sol_GaussianMatrix_inverse_wishart_diag_sq_moment`
(`iwd_resid_sq_moment`). -/
theorem integrable_and_integral_inv_sq_dist_rowSpace_sq {n k : ℕ} (hnk : n + 5 ≤ k)
    (H : Matrix (Fin n) (Fin k) ℝ) (hH : H.rank = n) :
    Integrable (fun g : Fin k → ℝ => ((g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹) ^ 2)
        (Measure.pi fun _ : Fin k => gaussianReal 0 1) ∧
    ∫ g, ((g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹) ^ 2
        ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1)
      = 1 / (((k : ℝ) - n - 2) * ((k : ℝ) - n - 4)) := by
  have hq : Measurable (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g))) := by
    apply Continuous.measurable
    fun_prop
  have hlaw := pi_gaussianReal_map_sq_dist_rowSpace H hH
  obtain ⟨hint, hval⟩ := integrable_and_integral_inv_sum_sq_pow_two_gaussianReal (d := k - n)
    (by omega)
  have hφ : Measurable (fun s : ℝ => (s⁻¹) ^ 2) := by fun_prop
  have hS : Measurable (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2) := by fun_prop
  constructor
  · have h := (integrable_map_measure hφ.aestronglyMeasurable hS.aemeasurable).mpr hint
    rw [← hlaw] at h
    exact (integrable_map_measure hφ.aestronglyMeasurable hq.aemeasurable).mp h
  · rw [← integral_map hq.aemeasurable hφ.aestronglyMeasurable, hlaw,
      integral_map hS.aemeasurable hφ.aestronglyMeasurable, hval,
      Nat.cast_sub (by omega : n ≤ k)]

private lemma integrable_and_integral_inv_self_mul_transpose_apply_self_sq_succ {n k : ℕ}
    (hnk : n + 5 ≤ k) (i : Fin (n + 1)) :
    Integrable (fun G : Fin (n + 1) → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2)
        (gaussianMatrix (n + 1) k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2 ∂(gaussianMatrix (n + 1) k)
      = 1 / (((k : ℝ) - n - 2) * ((k : ℝ) - n - 4)) := by
  set μ : Measure (Fin k → ℝ) := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hμ
  set ν : Measure (Fin n → Fin k → ℝ) := Measure.pi fun _ : Fin n => μ with hν
  set F : (Fin (n + 1) → Fin k → ℝ) → ℝ :=
    fun G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2 with hF
  have hFm : Measurable F := (measurable_inv_self_mul_transpose_apply i i).pow_const 2
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin k → ℝ) i with he
  have hmp : MeasurePreserving e (gaussianMatrix (n + 1) k) (μ.prod ν) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  set Φ : (Fin k → ℝ) × (Fin n → Fin k → ℝ) → ℝ := fun p => F (e.symm p) with hΦ
  have hΦm : Measurable Φ := hFm.comp e.symm.measurable
  have hΦnn : ∀ p, 0 ≤ Φ p := fun p => sq_nonneg _
  have hschur : ∀ H : Fin n → Fin k → ℝ, (Matrix.of H).rank = n → ∀ g : Fin k → ℝ,
      Φ (g, H) = ((g ⬝ᵥ g - (Matrix.of H *ᵥ g) ⬝ᵥ
        ((Matrix.of H * (Matrix.of H)ᵀ)⁻¹ *ᵥ (Matrix.of H *ᵥ g)))⁻¹) ^ 2 := by
    intro H hH g
    simp only [hΦ, hF, he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    rw [← inv_self_mul_transpose_insertNth_apply_self i H hH g]
    rfl
  have hrank : ∀ᵐ H ∂ν, (Matrix.of H).rank = n := by
    have := gaussianMatrix_ae_rank_eq n k
    filter_upwards [this] with H hH
    rw [hH]; omega
  have hinner : ∀ᵐ H ∂ν, Integrable (fun g => Φ (g, H)) μ ∧
      ∫ g, Φ (g, H) ∂μ = 1 / (((k : ℝ) - n - 2) * ((k : ℝ) - n - 4)) := by
    filter_upwards [hrank] with H hH
    simp_rw [hschur H hH]
    exact integrable_and_integral_inv_sq_dist_rowSpace_sq hnk (Matrix.of H) hH
  have hint : Integrable Φ (μ.prod ν) := by
    rw [integrable_prod_iff' hΦm.aestronglyMeasurable]
    refine ⟨hinner.mono fun H h => h.1, ?_⟩
    refine (integrable_const (1 / (((k : ℝ) - n - 2) * ((k : ℝ) - n - 4)))).congr ?_
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

/-- **Second moment of a diagonal entry of the inverse Wishart matrix.** For an `r × k`
standard Gaussian matrix `G` with `r + 4 ≤ k` and any `i`, `(G Gᵀ)⁻¹ᵢᵢ²` is integrable and
`E[(G Gᵀ)⁻¹ᵢᵢ²] = 1/((k-r-1)(k-r-3))`.

Tropp–Webber 2023, proof of Lemma B.2 (`E[1/χ⁴_d] = 1/((d-2)(d-4))` with `d = k-r+1`). Atlas:
`inverse-wishart-frob-moment` (helper). Proof: Schur complement and conditioning on the other
rows (atlas `gaussian-full-rank-ae`, `block-law-indep`) and the inverse chi-square second moment
(`integrable_and_integral_inv_sum_sq_pow_two_gaussianReal`, atlas `chi-square-neg-moment`).
Ported from Prove2me solution `GaussianMatrix.inverse_wishart_diag_sq_moment`. -/
theorem integrable_and_integral_inv_self_mul_transpose_apply_self_sq_gaussianMatrix {r k : ℕ}
    (hrk : r + 4 ≤ k) (i : Fin r) :
    Integrable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2)
      (gaussianMatrix r k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2 ∂(gaussianMatrix r k)
      = 1 / (((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by
  cases r with
  | zero => exact i.elim0
  | succ n =>
    obtain ⟨h1, h2⟩ :=
      integrable_and_integral_inv_self_mul_transpose_apply_self_sq_succ (by omega : n + 5 ≤ k) i
    refine ⟨h1, ?_⟩
    rw [h2]
    push_cast
    ring_nf

end NLAlib
