/-
Ported from the Prove2me workspace (Gaussian Random Matrices series, solutions
`Sol_GaussianMatrix_inverse_wishart_offdiag_sq_moment`,
`Sol_GaussianMatrix_inverse_wishart_rotation_relation`,
`Sol_GaussianMatrix_inverse_wishart_diag_prod_moment`).
-/
import NLAlib.Gaussian.InverseMoments.DiagonalLaw

/-!
# Second moments of the inverse Wishart matrix

For an `r × k` standard Gaussian matrix `G` with `r + 4 ≤ k` and `i ≠ j`, with
`N = (G Gᵀ)⁻¹`:

* `integrable_and_integral_dotProduct_sq_pi_gaussianReal`: `E[(w ⬝ g)²] = w ⬝ w` for a
  standard Gaussian vector `g`;
* `integrable_and_integral_inv_self_mul_transpose_apply_sq_gaussianMatrix`:
  `E[Nᵢⱼ²] = 1/((k-r)(k-r-1)(k-r-3))`;
* `integral_inv_self_mul_transpose_apply_self_sq_eq`: the rotation relation
  `E[Nᵢᵢ²] = E[Nᵢᵢ Nⱼⱼ] + 2 E[Nᵢⱼ²]` (orthogonal invariance under the 45° rotation in the
  `(i, j)` plane);
* `integrable_and_integral_inv_self_mul_transpose_apply_self_mul_apply_self_gaussianMatrix`:
  `E[Nᵢᵢ Nⱼⱼ] = (k-r-2)/((k-r)(k-r-1)(k-r-3))`.

Together with the diagonal moment
(`integrable_and_integral_inv_self_mul_transpose_apply_self_sq_gaussianMatrix`) these are all
the second moments of `N`; they give `E‖N‖_F²` and `E‖G†‖_F⁴` (`FrobeniusMoments.lean`).

Atlas: `inverse-wishart-frob-moment`, `pinv-frob-fourth-moment` (helpers). Proof source:
Prove2me workspace, Gaussian Random Matrices series; the workspace's `rotation_invariance`,
`inverse_wishart_mean`, `regression_residual_indep`, `schur_offdiag_inv` are
`gaussianMatrix_map_orthogonal`, `integrable_and_integral_inv_self_mul_transpose_gaussianMatrix`,
`indepFun_mulVec_sq_dist_rowSpace`, `inv_self_mul_transpose_apply_succAbove`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-! ### Off-diagonal second moment -/

/-- **Second moment of a linear form of a standard Gaussian vector.** For `w ∈ ℝᵏ` and `g` a
standard Gaussian vector, `(w ⬝ g)²` is integrable and `E[(w ⬝ g)²] = w ⬝ w`.

Helper for Tropp–Webber 2023, Lemma B.2. Atlas: `inverse-wishart-frob-moment` (helper). Ported
from the Prove2me solution `Sol_GaussianMatrix_inverse_wishart_offdiag_sq_moment`
(`iwg_gauss_sq`). -/
theorem integrable_and_integral_dotProduct_sq_pi_gaussianReal {k : ℕ} (w : Fin k → ℝ) :
    Integrable (fun g : Fin k → ℝ => (w ⬝ᵥ g) ^ 2) (Measure.pi fun _ : Fin k => gaussianReal 0 1) ∧
    ∫ g, (w ⬝ᵥ g) ^ 2 ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) = w ⬝ᵥ w := by
  set μ := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hμ
  have hmono : ∀ (a b : Fin k) (g : Fin k → ℝ),
      g a * g b = ∏ c, g c ^ ((if a = c then 1 else 0) + (if b = c then 1 else 0)) := by
    intro a b g
    simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_pow_boole, Finset.mem_univ, if_true]
  have gint : ∀ m : ℕ, Integrable (fun x : ℝ => x ^ m) (gaussianReal 0 1) := by
    intro m
    have h := (memLp_id_gaussianReal (μ := 0) (v := 1) (m : NNReal)).integrable_norm_pow'
    refine h.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_pow]
  have hint2 : ∀ a b : Fin k, Integrable (fun g : Fin k → ℝ => g a * g b) μ := by
    intro a b
    simp_rw [hmono a b]
    exact Integrable.fintype_prod (f := fun c (x : ℝ) =>
      x ^ ((if a = c then 1 else 0) + (if b = c then 1 else 0))) (fun c => gint _)
  have gm2 : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have h := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_of_integral_eq_zero aemeasurable_id
      (by simp [integral_id_gaussianReal (μ := 0) (v := 1)])] at h
    simpa using h
  have hval2 : ∀ a b : Fin k, ∫ g, g a * g b ∂μ = if a = b then 1 else 0 := by
    intro a b
    simp_rw [hmono a b]
    rw [hμ, integral_fintype_prod_eq_prod (fun c (x : ℝ) =>
      x ^ ((if a = c then 1 else 0) + (if b = c then 1 else 0)))]
    by_cases h : a = b
    · subst h
      rw [Finset.prod_eq_single a]
      · simp [gm2]
      · intro c _ hc; simp [Ne.symm hc]
      · simp
    · rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [Ne.symm h])
  have hexp : (fun g : Fin k → ℝ => (w ⬝ᵥ g) ^ 2)
      = fun g => ∑ a, ∑ b, (w a * w b) * (g a * g b) := by
    funext g
    simp only [dotProduct, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hexp]
  refine ⟨integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (hint2 a b).const_mul _, ?_⟩
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint2 a b).const_mul _]
  simp_rw [integral_finsetSum _ fun b _ => (hint2 _ b).const_mul _, integral_const_mul, hval2]
  simp [dotProduct]

/-- Conditional moment: for fixed full-rank `H`, with `c = (HHᵀ)⁻¹ H g` the regression
coefficients and `Q` the residual, `E[c_a² / Q²] = ((HHᵀ)⁻¹)_{aa} / ((k-n-2)(k-n-4))`. -/
private lemma integrable_and_integral_coeff_sq_mul_inv_sq_dist_rowSpace_sq {n k : ℕ}
    (hnk : n + 5 ≤ k) (H : Matrix (Fin n) (Fin k) ℝ) (hH : H.rank = n) (a : Fin n) :
    Integrable (fun g : Fin k → ℝ => (((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)) a) ^ 2 *
        ((g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹) ^ 2)
        (Measure.pi fun _ : Fin k => gaussianReal 0 1) ∧
    ∫ g, (((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)) a) ^ 2 *
        ((g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹) ^ 2
        ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1)
      = (H * Hᵀ)⁻¹ a a * (1 / (((k : ℝ) - n - 2) * ((k : ℝ) - n - 4))) := by
  set μ := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hμ
  set N := (H * Hᵀ)⁻¹ with hN
  have hdet : IsUnit (H * Hᵀ).det := by
    refine isUnit_iff_ne_zero.mpr (det_ne_zero_of_rank_eq _ ?_)
    rw [Matrix.rank_self_mul_transpose, hH]
  have hind := indepFun_mulVec_sq_dist_rowSpace H hH
  set X : (Fin k → ℝ) → (Fin n → ℝ) := fun g => H *ᵥ g with hX
  set Y : (Fin k → ℝ) → ℝ := fun g => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ (N *ᵥ (H *ᵥ g)) with hY
  set f : (Fin n → ℝ) → ℝ := fun y => ((N *ᵥ y) a) ^ 2 with hf
  set h : ℝ → ℝ := fun q => (q⁻¹) ^ 2 with hh
  have hXm : Measurable X := by
    refine measurable_pi_lambda _ fun b => ?_
    simp only [hX, Matrix.mulVec, dotProduct]; fun_prop
  have hYm : Measurable Y := by apply Continuous.measurable; simp only [hY]; fun_prop
  have hfm : Measurable f := by
    simp only [hf, Matrix.mulVec, dotProduct]; fun_prop
  have hhm : Measurable h := by simp only [hh]; fun_prop
  set w : Fin k → ℝ := (N * H) a with hw
  have hfX : ∀ g, f (X g) = (w ⬝ᵥ g) ^ 2 := by
    intro g
    simp only [hf, hX, hw, Matrix.mulVec_mulVec]
    rfl
  have hww : w ⬝ᵥ w = N a a := by
    have h1 : w ⬝ᵥ w = (N * H * (N * H)ᵀ) a a := by
      simp [hw, Matrix.mul_apply, dotProduct, mul_comm]
    have hNt : Nᵀ = N := by
      rw [hN, Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [h1, Matrix.transpose_mul, hNt, show N * H * (Hᵀ * N) = N * (H * Hᵀ) * N by
      simp [Matrix.mul_assoc], hN, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  obtain ⟨hwint, hwval⟩ := integrable_and_integral_dotProduct_sq_pi_gaussianReal (k := k) w
  obtain ⟨hqint, hqval⟩ := integrable_and_integral_inv_sq_dist_rowSpace_sq hnk H hH
  have hfXint : Integrable (fun g => f (X g)) μ := by simp_rw [hfX]; exact hwint
  have hhYint : Integrable (fun g => h (Y g)) μ := hqint
  have hind' := hind.comp hfm hhm
  constructor
  · exact hind'.integrable_mul hfXint hhYint
  · have := hind.integral_fun_comp_mul_comp hXm.aemeasurable hYm.aemeasurable
      hfm.aestronglyMeasurable hhm.aestronglyMeasurable
    change ∫ g, f (X g) * h (Y g) ∂μ = _
    rw [this]
    simp_rw [hfX]
    rw [hwval, hww]
    change N a a * ∫ g, ((g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹) ^ 2 ∂μ = _
    rw [hqval]

private lemma integrable_and_integral_inv_self_mul_transpose_apply_succAbove_sq {n k : ℕ}
    (hnk : n + 5 ≤ k) (i : Fin (n + 1)) (a : Fin n) :
    Integrable (fun G : Fin (n + 1) → Fin k → ℝ =>
        (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i (i.succAbove a) ^ 2) (gaussianMatrix (n + 1) k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i (i.succAbove a) ^ 2 ∂(gaussianMatrix (n + 1) k)
      = (1 / ((k : ℝ) - n - 1)) * (1 / (((k : ℝ) - n - 2) * ((k : ℝ) - n - 4))) := by
  set μ : Measure (Fin k → ℝ) := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hμ
  set ν : Measure (Fin n → Fin k → ℝ) := Measure.pi fun _ : Fin n => μ with hν
  set C : ℝ := 1 / (((k : ℝ) - n - 2) * ((k : ℝ) - n - 4)) with hC
  set F : (Fin (n + 1) → Fin k → ℝ) → ℝ :=
    fun G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i (i.succAbove a) ^ 2 with hF
  have hFm : Measurable F := (measurable_inv_self_mul_transpose_apply i (i.succAbove a)).pow_const 2
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin k → ℝ) i with he
  have hmp : MeasurePreserving e (gaussianMatrix (n + 1) k) (μ.prod ν) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  set Φ : (Fin k → ℝ) × (Fin n → Fin k → ℝ) → ℝ := fun p => F (e.symm p) with hΦ
  have hΦm : Measurable Φ := hFm.comp e.symm.measurable
  have hΦnn : ∀ p, 0 ≤ Φ p := fun p => sq_nonneg _
  have hschur : ∀ H : Fin n → Fin k → ℝ, (Matrix.of H).rank = n → ∀ g : Fin k → ℝ,
      Φ (g, H) = ((((Matrix.of H) * (Matrix.of H)ᵀ)⁻¹ *ᵥ (Matrix.of H *ᵥ g)) a) ^ 2 *
        ((g ⬝ᵥ g - (Matrix.of H *ᵥ g) ⬝ᵥ
          ((Matrix.of H * (Matrix.of H)ᵀ)⁻¹ *ᵥ (Matrix.of H *ᵥ g)))⁻¹) ^ 2 := by
    intro H hH g
    set G0 : Fin (n + 1) → Fin k → ℝ := Fin.insertNth i g H with hG0
    have hsub : (Matrix.of G0).submatrix i.succAbove id = Matrix.of H := by
      ext a b; simp [hG0]
    have hrow : Matrix.of G0 i = g := by funext b; simp [hG0]
    have hdet : ((Matrix.of G0).submatrix i.succAbove id *
        ((Matrix.of G0).submatrix i.succAbove id)ᵀ).det ≠ 0 := by
      rw [hsub]
      exact det_ne_zero_of_rank_eq _ (by rw [Matrix.rank_self_mul_transpose, hH])
    have h1 := inv_self_mul_transpose_apply_self (Matrix.of G0) i hdet
    have h2 := inv_self_mul_transpose_apply_succAbove (Matrix.of G0) i a hdet
    rw [hsub, hrow] at h1 h2
    rw [h1] at h2
    have : Φ (g, H) = (Matrix.of G0 * (Matrix.of G0)ᵀ)⁻¹ i (i.succAbove a) ^ 2 := rfl
    rw [this, h2]
    ring
  have hrank : ∀ᵐ H ∂ν, (Matrix.of H).rank = n := by
    have := gaussianMatrix_ae_rank_eq n k
    filter_upwards [this] with H hH
    rw [hH]; omega
  have hinner : ∀ᵐ H ∂ν, Integrable (fun g => Φ (g, H)) μ ∧
      ∫ g, Φ (g, H) ∂μ = (Matrix.of H * (Matrix.of H)ᵀ)⁻¹ a a * C := by
    filter_upwards [hrank] with H hH
    simp_rw [hschur H hH]
    exact integrable_and_integral_coeff_sq_mul_inv_sq_dist_rowSpace_sq hnk (Matrix.of H) hH a
  obtain ⟨hmint, hmval⟩ :=
    integrable_and_integral_inv_self_mul_transpose_gaussianMatrix (r := n) (k := k) (by omega)
  have hmint' : Integrable (fun H : Fin n → Fin k → ℝ =>
      (Matrix.of H * (Matrix.of H)ᵀ)⁻¹ a a * C) ν := (hmint a a).mul_const C
  have hint : Integrable Φ (μ.prod ν) := by
    rw [integrable_prod_iff' hΦm.aestronglyMeasurable]
    refine ⟨hinner.mono fun H h => h.1, ?_⟩
    refine hmint'.congr ?_
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
    rw [integral_mul_const]
    change (∫ H, (Matrix.of H * (Matrix.of H)ᵀ)⁻¹ a a ∂(gaussianMatrix n k)) * C = _
    rw [hmval a a, Matrix.one_apply_eq, mul_one]

/-- **Off-diagonal second moment of the inverse Wishart matrix.** For an `r × k` standard
Gaussian matrix `G` with `r + 4 ≤ k` and `i ≠ j`, `(G Gᵀ)⁻¹ᵢⱼ²` is integrable and
`E[(G Gᵀ)⁻¹ᵢⱼ²] = 1/((k-r)(k-r-1)(k-r-3))`.

Tropp–Webber 2023, proof of Lemma B.2 (second moments of the inverse Wishart matrix). Atlas:
`inverse-wishart-frob-moment` (helper). Proof: Schur complement
(`inv_self_mul_transpose_apply_succAbove`) writes the entry as `-cₐ/Q`; given the other rows
(full rank a.s., atlas `gaussian-full-rank-ae`) the coefficient `cₐ` and the residual `Q` are
independent (`indepFun_mulVec_sq_dist_rowSpace`), `Q ∼ χ²_{k-r+1}` (atlas `block-law-indep`,
`chi-square-neg-moment`), and `E cₐ² = E (H Hᵀ)⁻¹ₐₐ` is the inverse-Wishart mean (atlas
`inverse-wishart-mean`). Ported from Prove2me solution
`GaussianMatrix.inverse_wishart_offdiag_sq_moment`. -/
theorem integrable_and_integral_inv_self_mul_transpose_apply_sq_gaussianMatrix {r k : ℕ}
    (hrk : r + 4 ≤ k) (i j : Fin r) (hij : i ≠ j) :
    Integrable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ^ 2)
      (gaussianMatrix r k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ^ 2 ∂(gaussianMatrix r k)
      = 1 / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by
  cases r with
  | zero => exact i.elim0
  | succ n =>
    obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
    obtain ⟨h1, h2⟩ :=
      integrable_and_integral_inv_self_mul_transpose_apply_succAbove_sq (by omega : n + 5 ≤ k) i a
    refine ⟨h1, ?_⟩
    rw [h2]
    have hx : (4 : ℝ) ≤ (k : ℝ) - (n + 1) := by
      have : ((n + 1 + 4 : ℕ) : ℝ) ≤ k := by exact_mod_cast hrk
      push_cast at this; linarith
    have h3 : (k : ℝ) - n - 1 ≠ 0 := by linarith
    have h4 : (k : ℝ) - n - 2 ≠ 0 := by linarith
    have h5 : (k : ℝ) - n - 4 ≠ 0 := by linarith
    push_cast
    rw [div_mul_div_comm, one_mul]
    congr 1
    ring

/-! ### The rotation relation -/

/-- The 45-degree rotation in the `(i, j)` coordinate plane. -/
private def planeRotation {r : ℕ} (i j : Fin r) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun a => if a = i then (Real.sqrt 2)⁻¹ • (Pi.single i 1 + Pi.single j 1)
    else if a = j then (Real.sqrt 2)⁻¹ • (Pi.single j 1 - Pi.single i 1) else Pi.single a 1

private lemma inv_sqrt_two_mul_self : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num

private lemma planeRotation_transpose_mul {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    (planeRotation i j)ᵀ * planeRotation i j = 1 := by
  rw [mul_eq_one_comm]
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  have hc := inv_sqrt_two_mul_self
  have hji : j ≠ i := Ne.symm hij
  by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;> by_cases hbj : b = j <;>
    simp_all [planeRotation, Pi.single_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Matrix.one_apply, mul_add, add_mul, sub_mul, mul_sub, eq_comm] <;>
    linarith

private lemma planeRotation_conj_apply {r : ℕ} (i j : Fin r) (N : Matrix (Fin r) (Fin r) ℝ) :
    (planeRotation i j * N * (planeRotation i j)ᵀ) i i = (N i i + N i j + N j i + N j j) / 2 := by
  have hc := inv_sqrt_two_mul_self
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp [planeRotation, Pi.single_apply, Finset.sum_add_distrib, add_mul, mul_add, eq_comm]
  linear_combination (-(N i i + N j i + N i j + N j j)) * hc

/-- The inverse Wishart matrix transforms by conjugation under a left orthogonal rotation. -/
private lemma inv_self_mul_transpose_orthogonal_mul {r k : ℕ} (U : Matrix (Fin r) (Fin r) ℝ)
    (hU : Uᵀ * U = 1) (G : Fin r → Fin k → ℝ) :
    (Matrix.of (Matrix.of.symm (U * Matrix.of G * (1 : Matrix (Fin k) (Fin k) ℝ))) *
        (Matrix.of (Matrix.of.symm (U * Matrix.of G * (1 : Matrix (Fin k) (Fin k) ℝ))))ᵀ)⁻¹
      = U * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ * Uᵀ := by
  have hUinv : U⁻¹ = Uᵀ := Matrix.inv_eq_left_inv hU
  simp only [Equiv.apply_symm_apply, Matrix.mul_one, Matrix.transpose_mul]
  rw [show U * Matrix.of G * ((Matrix.of G)ᵀ * Uᵀ) = U * (Matrix.of G * (Matrix.of G)ᵀ) * Uᵀ by
    simp [Matrix.mul_assoc]]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, hUinv,
    Matrix.transpose_transpose, Matrix.mul_assoc]

/-- Invariance of the inverse-Wishart law under orthogonal conjugation. -/
private lemma integral_inv_self_mul_transpose_conj {r k : ℕ} (U : Matrix (Fin r) (Fin r) ℝ)
    (hU : Uᵀ * U = 1) (F : Matrix (Fin r) (Fin r) ℝ → ℝ)
    (hF : Measurable (fun G : Fin r → Fin k → ℝ => F (Matrix.of G * (Matrix.of G)ᵀ)⁻¹)) :
    ∫ G, F (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ∂(gaussianMatrix r k)
      = ∫ G, F (U * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ * Uᵀ) ∂(gaussianMatrix r k) := by
  have hrot := gaussianMatrix_map_orthogonal U (1 : Matrix (Fin k) (Fin k) ℝ) hU (by simp)
  have hmeas : Measurable (fun G : Fin r → Fin k → ℝ =>
      Matrix.of.symm (U * Matrix.of G * (1 : Matrix (Fin k) (Fin k) ℝ))) := by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    simp only [Matrix.of_symm_apply, Matrix.mul_one, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have h1 : ∫ G, F (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ∂(gaussianMatrix r k) =
      ∫ G, F (Matrix.of G * (Matrix.of G)ᵀ)⁻¹
        ∂(Measure.map (fun G => Matrix.of.symm (U * Matrix.of G *
          (1 : Matrix (Fin k) (Fin k) ℝ))) (gaussianMatrix r k)) := by
    rw [hrot]
  rw [integral_map hmeas.aemeasurable hF.aestronglyMeasurable] at h1
  simp_rw [inv_self_mul_transpose_orthogonal_mul U hU] at h1
  exact h1

/-- The sign flip of coordinate `j`. -/
private def signFlip {r : ℕ} (j : Fin r) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.diagonal fun a => if a = j then -1 else 1

private lemma signFlip_transpose_mul {r : ℕ} (j : Fin r) : (signFlip j)ᵀ * signFlip j = 1 := by
  rw [signFlip, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; split_ifs <;> norm_num

private lemma signFlip_conj_apply {r : ℕ} (j : Fin r) (N : Matrix (Fin r) (Fin r) ℝ)
    (a b : Fin r) :
    (signFlip j * N * (signFlip j)ᵀ) a b
      = (if a = j then -1 else 1) * N a b * (if b = j then -1 else 1) := by
  simp [signFlip, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]

private lemma inv_self_mul_transpose_apply_comm {r k : ℕ} (G : Fin r → Fin k → ℝ) (i j : Fin r) :
    (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j i = (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j := by
  have := (posSemidef_inv_self_mul_transpose (Matrix.of G)).isHermitian.apply i j
  simpa using this

/-- A product of two functions with integrable squares is integrable. -/
private lemma integrable_mul_of_integrable_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hg2 : Integrable (fun x => g x ^ 2) μ) :
    Integrable (fun x => f x * g x) μ := by
  refine (hf2.add hg2).mono' (hf.mul hg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_le]
  simp only [Pi.add_apply]
  constructor <;> nlinarith [sq_nonneg (f x + g x), sq_nonneg (f x - g x)]

/-- **Rotation relation for the inverse Wishart matrix.** For an `r × k` standard Gaussian
matrix `G` with `r + 4 ≤ k` and `i ≠ j`, with `N = (G Gᵀ)⁻¹`,
`E[Nᵢᵢ²] = E[Nᵢᵢ Nⱼⱼ] + 2 E[Nᵢⱼ²]`.

Tropp–Webber 2023, proof of Lemma B.2 (orthogonal invariance of the inverse Wishart law).
Atlas: `pinv-frob-fourth-moment` (helper). Proof: the law of `N` is invariant under
`N ↦ U N Uᵀ` for orthogonal `U` (`gaussianMatrix_map_orthogonal`, atlas
`rotation-invariance`); sign flips kill the mixed moments `E[Nₐₐ Nᵢⱼ]` and the 45° rotation in
the `(i, j)` plane gives the relation. Integrability from the diagonal second moment
(`integrable_and_integral_inv_self_mul_transpose_apply_self_sq_gaussianMatrix`). Ported from
Prove2me solution `GaussianMatrix.inverse_wishart_rotation_relation`. -/
theorem integral_inv_self_mul_transpose_apply_self_sq_eq {r k : ℕ} (hrk : r + 4 ≤ k)
    (i j : Fin r) (hij : i ≠ j) :
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2 ∂(gaussianMatrix r k)
      = ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j
            ∂(gaussianMatrix r k)
        + 2 * ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ^ 2 ∂(gaussianMatrix r k) := by
  set μ := gaussianMatrix r k with hμ
  set M : (Fin r → Fin k → ℝ) → Matrix (Fin r) (Fin r) ℝ :=
    fun G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ with hM
  have hm : ∀ a b : Fin r, Measurable (fun G => M G a b) := fun a b =>
    measurable_inv_self_mul_transpose_apply a b
  obtain ⟨hx2, hxval⟩ :=
    integrable_and_integral_inv_self_mul_transpose_apply_self_sq_gaussianMatrix hrk i
  obtain ⟨hy2, hyval⟩ :=
    integrable_and_integral_inv_self_mul_transpose_apply_self_sq_gaussianMatrix hrk j
  have hz2 : Integrable (fun G => M G i j ^ 2) μ := by
    refine Integrable.mono' ((hx2.add hy2).const_mul 2)
      ((hm i j).pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun G => ?_)
    have h := abs_apply_le_apply_self_add_apply_self _
      (posSemidef_inv_self_mul_transpose (Matrix.of G)) i j
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have : M G i j ^ 2 ≤ (M G i i + M G j j) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (M G i i - M G j j)]
  have hxy := integrable_mul_of_integrable_sq (hm i i) (hm j j) hx2 hy2
  have hxz := integrable_mul_of_integrable_sq (hm i i) (hm i j) hx2 hz2
  have hyz := integrable_mul_of_integrable_sq (hm j j) (hm i j) hy2 hz2
  -- sign flip of coordinate `j` kills the mixed moments
  have hflip : ∀ a : Fin r, a ≠ j → ∫ G, M G a a * M G i j ∂μ = 0 := by
    intro a haj
    have h := integral_inv_self_mul_transpose_conj (k := k) (signFlip j)
      (signFlip_transpose_mul j) (fun N => N a a * N i j) ((hm a a).mul (hm i j))
    simp only [signFlip_conj_apply] at h
    have h2 : ∫ G, M G a a * M G i j ∂μ = -∫ G, M G a a * M G i j ∂μ := by
      rw [← integral_neg]
      refine h.trans (integral_congr_ae (ae_of_all _ fun G => ?_))
      simp [haj, hij, hM]
    linarith
  have hflip' : ∫ G, M G j j * M G i j ∂μ = 0 := by
    have h := integral_inv_self_mul_transpose_conj (k := k) (signFlip i)
      (signFlip_transpose_mul i) (fun N => N j j * N i j) ((hm j j).mul (hm i j))
    simp only [signFlip_conj_apply] at h
    have h2 : ∫ G, M G j j * M G i j ∂μ = -∫ G, M G j j * M G i j ∂μ := by
      rw [← integral_neg]
      refine h.trans (integral_congr_ae (ae_of_all _ fun G => ?_))
      simp [Ne.symm hij, hM]
    linarith
  have hxz0 := hflip i hij
  -- the 45-degree rotation
  have hrot := integral_inv_self_mul_transpose_conj (k := k) (planeRotation i j)
    (planeRotation_transpose_mul i j hij) (fun N => N i i ^ 2) ((hm i i).pow_const 2)
  simp only [planeRotation_conj_apply i j] at hrot
  change ∫ G, M G i i ^ 2 ∂μ = ∫ G, ((M G i i + M G i j + M G j i + M G j j) / 2) ^ 2 ∂μ at hrot
  have hexp : (fun G => ((M G i i + M G i j + M G j i + M G j j) / 2) ^ 2)
      = fun G => (1 / 4 : ℝ) * (((((M G i i ^ 2 + M G j j ^ 2) + 4 * M G i j ^ 2)
          + 2 * (M G i i * M G j j)) + 4 * (M G i i * M G i j)) + 4 * (M G j j * M G i j)) := by
    funext G
    rw [show M G j i = M G i j from inv_self_mul_transpose_apply_comm G i j]
    ring
  have hx2' : Integrable (fun G => M G i i ^ 2) μ := hx2
  have hy2' : Integrable (fun G => M G j j ^ 2) μ := hy2
  have h1 : Integrable (fun G => M G i i ^ 2 + M G j j ^ 2) μ := hx2'.add hy2'
  have h2 : Integrable (fun G => M G i i ^ 2 + M G j j ^ 2 + 4 * M G i j ^ 2) μ :=
    h1.add (hz2.const_mul 4)
  have h3 : Integrable (fun G => M G i i ^ 2 + M G j j ^ 2 + 4 * M G i j ^ 2
      + 2 * (M G i i * M G j j)) μ := h2.add (hxy.const_mul 2)
  have h4 : Integrable (fun G => M G i i ^ 2 + M G j j ^ 2 + 4 * M G i j ^ 2
      + 2 * (M G i i * M G j j) + 4 * (M G i i * M G i j)) μ := h3.add (hxz.const_mul 4)
  rw [hexp, integral_const_mul, integral_add h4 (hyz.const_mul 4),
    integral_add h3 (hxz.const_mul 4), integral_add h2 (hxy.const_mul 2),
    integral_add h1 (hz2.const_mul 4), integral_add hx2' hy2',
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    hxz0, hflip'] at hrot
  have hxy' : ∫ G, M G i i ^ 2 ∂μ = ∫ G, M G j j ^ 2 ∂μ := by
    change ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ^ 2 ∂μ
      = ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j ^ 2 ∂μ
    rw [hxval, hyval]
  change ∫ G, M G i i ^ 2 ∂μ = ∫ G, M G i i * M G j j ∂μ + 2 * ∫ G, M G i j ^ 2 ∂μ
  linarith

/-! ### Product of two diagonal entries -/

/-- **Mixed diagonal moment of the inverse Wishart matrix.** For an `r × k` standard Gaussian
matrix `G` with `r + 4 ≤ k` and `i ≠ j`, `(G Gᵀ)⁻¹ᵢᵢ (G Gᵀ)⁻¹ⱼⱼ` is integrable and
`E[(G Gᵀ)⁻¹ᵢᵢ (G Gᵀ)⁻¹ⱼⱼ] = (k-r-2)/((k-r)(k-r-1)(k-r-3))`.

Tropp–Webber 2023, proof of Lemma B.2. Atlas: `pinv-frob-fourth-moment` (helper). Proof: the
rotation relation `integral_inv_self_mul_transpose_apply_self_sq_eq` with the diagonal and
off-diagonal second moments. Ported from Prove2me solution
`GaussianMatrix.inverse_wishart_diag_prod_moment`. -/
theorem integrable_and_integral_inv_self_mul_transpose_apply_self_mul_apply_self_gaussianMatrix
    {r k : ℕ} (hrk : r + 4 ≤ k) (i j : Fin r) (hij : i ≠ j) :
    Integrable (fun G : Fin r → Fin k → ℝ =>
        (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j)
      (gaussianMatrix r k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j
        ∂(gaussianMatrix r k)
      = ((k : ℝ) - r - 2) / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3)) := by
  obtain ⟨hx2, hxval⟩ :=
    integrable_and_integral_inv_self_mul_transpose_apply_self_sq_gaussianMatrix hrk i
  obtain ⟨hy2, -⟩ :=
    integrable_and_integral_inv_self_mul_transpose_apply_self_sq_gaussianMatrix hrk j
  obtain ⟨-, hzval⟩ :=
    integrable_and_integral_inv_self_mul_transpose_apply_sq_gaussianMatrix hrk i j hij
  have hrel := integral_inv_self_mul_transpose_apply_self_sq_eq hrk i j hij
  constructor
  · refine (hx2.add hy2).mono'
      ((measurable_inv_self_mul_transpose_apply i i).mul
        (measurable_inv_self_mul_transpose_apply j j)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun G => ?_)
    rw [Real.norm_eq_abs, abs_le]
    simp only [Pi.add_apply]
    constructor <;>
      nlinarith [sq_nonneg ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i
          + (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j),
        sq_nonneg ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i - (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j)]
  · rw [hxval, hzval] at hrel
    have hx : (4 : ℝ) ≤ (k : ℝ) - r := by
      have : ((r + 4 : ℕ) : ℝ) ≤ k := by exact_mod_cast hrk
      push_cast at this; linarith
    have h1 : (k : ℝ) - r ≠ 0 := by linarith
    have h2 : (k : ℝ) - r - 1 ≠ 0 := by linarith
    have h3 : (k : ℝ) - r - 3 ≠ 0 := by linarith
    have : ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i * (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ j j
        ∂(gaussianMatrix r k)
        = 1 / (((k : ℝ) - r - 1) * ((k : ℝ) - r - 3))
          - 2 * (1 / (((k : ℝ) - r) * ((k : ℝ) - r - 1) * ((k : ℝ) - r - 3))) := by linarith
    rw [this]
    field_simp

end NLAlib
