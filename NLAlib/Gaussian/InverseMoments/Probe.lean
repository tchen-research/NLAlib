import NLAlib.Gaussian.InverseMoments.DiagonalLaw
import NLAlib.Gaussian.PositiveMoments
import NLAlib.Matrix.Spectral
import NLAlib.Matrix.QuadraticProbe
import Mathlib.Analysis.Matrix.PosDef

/-!+# Gaussian quadratic probes for inverse spectral moments

The scalar Schur residual law is transported to every deterministic direction.
Positive semidefinite quadratic probes detect the operator norm without a random
choice of eigenvectors. Atlas: `inverse-wishart-spectral-moment` and
`pinv-spectral-expectation`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

/-- Orthogonal conjugation transports the total inverse Gram matrix, including singular
matrices. Source: Schur/operator inverse-Wishart route; atlas `inverse-wishart-spectral-moment`.
-/
theorem inv_self_mul_transpose_orthogonal_mul {r k : ℕ}
    (U : Matrix (Fin r) (Fin r) ℝ) (hU : Uᵀ * U = 1)
    (G : Matrix (Fin r) (Fin k) ℝ) :
    ((U * G) * (U * G)ᵀ)⁻¹ = U * (G * Gᵀ)⁻¹ * Uᵀ := by
  have hUinv : U⁻¹ = Uᵀ := Matrix.inv_eq_left_inv hU
  rw [Matrix.transpose_mul]
  rw [show U * G * (Gᵀ * Uᵀ) = U * (G * Gᵀ) * Uᵀ by simp [Matrix.mul_assoc]]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, hUinv,
    Matrix.transpose_transpose, Matrix.mul_assoc]

/-- Every admissible positive real moment of an inverse Gram diagonal entry is finite,
with its inverse-chi-square Gamma value. Source: Schur residual law and scalar Gaussian
negative moments; atlas `inverse-wishart-spectral-moment` (directional input). -/
theorem integrable_and_integral_rpow_inv_self_mul_transpose_apply_self_gaussianMatrix
    {r k : ℕ} (hrk : r ≤ k) (i : Fin r) (q : ℝ) (hq : 0 ≤ q)
    (hqd : q < ((k : ℝ) - r + 1) / 2) :
    Integrable (fun G : Fin r → Fin k → ℝ =>
      ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i) ^ q) (gaussianMatrix r k) ∧
    (∫ G : Fin r → Fin k → ℝ, ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i) ^ q
      ∂(gaussianMatrix r k))
      = Real.Gamma (((k : ℝ) - r + 1) / 2 - q) /
        (2 ^ q * Real.Gamma (((k : ℝ) - r + 1) / 2)) := by
  have hdcast : ((k - r + 1 : ℕ) : ℝ) = (k : ℝ) - r + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hrk, Nat.cast_one]
  have hlaw := gaussianMatrix_map_inv_self_mul_transpose_apply_self hrk i
  have hD : Measurable (fun G : Fin r → Fin k → ℝ =>
      (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i) :=
    measurable_inv_self_mul_transpose_apply i i
  have hS : Measurable (fun x : Fin (k - r + 1) → ℝ => (∑ j, x j ^ 2)⁻¹) := by
    fun_prop
  have hφ : Measurable (fun s : ℝ => s ^ q) := by fun_prop
  obtain ⟨hint, hval⟩ := integrable_and_integral_rpow_inv_sum_sq_gaussianReal
    (d := k - r + 1) q hq (by simpa [hdcast] using hqd)
  constructor
  · have h := (integrable_map_measure hφ.aestronglyMeasurable hS.aemeasurable).mpr hint
    rw [← hlaw] at h
    exact (integrable_map_measure hφ.aestronglyMeasurable hD.aemeasurable).mp h
  · rw [← integral_map hD.aemeasurable hφ.aestronglyMeasurable, hlaw,
      integral_map hS.aemeasurable hφ.aestronglyMeasurable, hval, hdcast]

set_option backward.isDefEq.respectTransparency false in
/-- Every unit-direction inverse Gram quadratic form has the inverse-chi-square moments.
Source: Gaussian orthogonal invariance and Schur complement; atlas
`inverse-wishart-spectral-moment`. The rotation is chosen for the fixed direction only. -/
theorem integrable_and_integral_rpow_dotProduct_inv_self_mul_transpose_unit_gaussianMatrix
    {r k : ℕ} (hrk : r ≤ k) (u : Fin r → ℝ) (hu : u ⬝ᵥ u = 1)
    (q : ℝ) (hq : 0 ≤ q) (hqd : q < ((k : ℝ) - r + 1) / 2) :
    Integrable (fun G : Fin r → Fin k → ℝ =>
      (u ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ u)) ^ q) (gaussianMatrix r k) ∧
    (∫ G : Fin r → Fin k → ℝ,
      (u ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ u)) ^ q ∂(gaussianMatrix r k))
      = Real.Gamma (((k : ℝ) - r + 1) / 2 - q) /
        (2 ^ q * Real.Gamma (((k : ℝ) - r + 1) / 2)) := by
  classical
  have hr : 1 ≤ r := by
    by_contra h
    have : r = 0 := by omega
    subst r
    simp [dotProduct] at hu
  let i : Fin r := ⟨0, hr⟩
  let V : Matrix (Fin r) (Fin 1) ℝ := fun a _ => u a
  have hV : Vᵀ * V = 1 := by
    ext a b
    fin_cases a
    fin_cases b
    change (∑ a, u a * u a) = 1
    exact hu
  let e : Fin 1 ↪ Fin r := ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩
  obtain ⟨U, hU, hUcol⟩ := exists_orthogonal_completion V hV e
  have hUi : ∀ a, U a i = u a := fun a => hUcol a 0
  let T : (Fin r → Fin k → ℝ) → (Fin r → Fin k → ℝ) :=
    fun G => Matrix.of.symm (Uᵀ * Matrix.of G * (1 : Matrix (Fin k) (Fin k) ℝ))
  have hTm : Measurable T := by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    simp only [T, Matrix.of_symm_apply, Matrix.mul_one, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hUt : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hrot : MeasurePreserving T (gaussianMatrix r k) (gaussianMatrix r k) :=
    ⟨hTm, gaussianMatrix_map_orthogonal Uᵀ 1 (by simpa using hUt) (by simp)⟩
  let F : (Fin r → Fin k → ℝ) → ℝ := fun G =>
    ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i) ^ q
  have hFm : Measurable F := (measurable_inv_self_mul_transpose_apply i i).pow_const q
  have hFT : F ∘ T = fun G : Fin r → Fin k → ℝ =>
      (u ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ u)) ^ q := by
    funext G
    simp only [Function.comp_apply, F, T, Equiv.apply_symm_apply, Matrix.mul_one]
    rw [inv_self_mul_transpose_orthogonal_mul Uᵀ (by simpa using hUt), Matrix.transpose_transpose]
    congr 1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hUi, dotProduct, Matrix.mulVec]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  obtain ⟨hint, hval⟩ :=
    integrable_and_integral_rpow_inv_self_mul_transpose_apply_self_gaussianMatrix hrk i q hq hqd
  constructor
  · rw [← hFT]
    exact hrot.integrable_comp_of_integrable hint
  · rw [← hFT]
    change (∫ G, F (T G) ∂(gaussianMatrix r k)) = _
    rw [← integral_map hTm.aemeasurable hFm.aestronglyMeasurable, hrot.map_eq]
    exact hval

/-- A fixed inverse Gram quadratic form has a scaled inverse-chi-square moment.
Source: the operator directional-probe route; atlas `inverse-wishart-spectral-moment`.
The fixed vector may vanish, and the exponent is any strictly positive admissible real. -/
theorem integrable_and_integral_rpow_dotProduct_inv_self_mul_transpose_gaussianMatrix
    {r k : ℕ} (hrk : r ≤ k) (v : Fin r → ℝ) (q : ℝ) (hq : 0 < q)
    (hqd : q < ((k : ℝ) - r + 1) / 2) :
    Integrable (fun G : Fin r → Fin k → ℝ =>
      (v ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ v)) ^ q) (gaussianMatrix r k) ∧
    (∫ G : Fin r → Fin k → ℝ,
      (v ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ v)) ^ q ∂(gaussianMatrix r k))
      = (v ⬝ᵥ v) ^ q *
        (Real.Gamma (((k : ℝ) - r + 1) / 2 - q) /
          (2 ^ q * Real.Gamma (((k : ℝ) - r + 1) / 2))) := by
  by_cases hv : v = 0
  · subst v
    simp [Real.zero_rpow hq.ne']
  let S : ℝ := v ⬝ᵥ v
  have hS0 : 0 < S := lt_of_le_of_ne (dotProduct_self_nonneg _) (by
    simpa [S, eq_comm] using (dotProduct_self_eq_zero.not.mpr hv))
  let c : ℝ := Real.sqrt S
  have hc0 : 0 < c := Real.sqrt_pos.2 hS0
  have hcne : c ≠ 0 := hc0.ne'
  have hcsq : c ^ 2 = S := Real.sq_sqrt hS0.le
  let u : Fin r → ℝ := c⁻¹ • v
  have hcu : c • u = v := by simp [u, smul_smul, hcne]
  have hu : u ⬝ᵥ u = 1 := by
    simp only [u, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    change c⁻¹ * (c⁻¹ * S) = 1
    rw [← hcsq]
    field_simp
  have hscale : ∀ G : Fin r → Fin k → ℝ,
      (v ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ v)) ^ q
        = S ^ q * (u ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ u)) ^ q := by
    intro G
    have hform : v ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ v)
        = S * (u ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ u)) := by
      rw [← hcu, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul]
      rw [← mul_assoc, ← sq, hcsq]
    have hQ : 0 ≤ u ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ u) := by
      simpa using (posSemidef_inv_self_mul_transpose (Matrix.of G)).dotProduct_mulVec_nonneg u
    rw [hform, Real.mul_rpow hS0.le hQ]
  obtain ⟨hint, hval⟩ :=
    integrable_and_integral_rpow_dotProduct_inv_self_mul_transpose_unit_gaussianMatrix
      hrk u hu q hq.le hqd
  constructor
  · simpa only [hscale] using hint.const_mul (S ^ q)
  · simp_rw [hscale]
    rw [integral_const_mul, hval]

set_option backward.isDefEq.respectTransparency false in
/-- A unit directional Gaussian probe is a scalar standard Gaussian.
Source: Gaussian orthogonal invariance; atlas `gaussian-positive-moments` (probe interface). -/
theorem pi_gaussianReal_map_dotProduct_unit {r : ℕ} (v : Fin r → ℝ)
    (hv : v ⬝ᵥ v = 1) :
    (Measure.pi fun _ : Fin r => gaussianReal 0 1).map (fun z => v ⬝ᵥ z)
      = gaussianReal 0 1 := by
  let w : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 v
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin r)) := innerSL ℝ w
  have hLsq : ‖L‖ ^ 2 = 1 := by
    rw [show L = innerSL ℝ w from rfl, innerSL_apply_norm, EuclideanSpace.real_norm_sq_eq]
    simpa [w, dotProduct, sq] using hv
  have hfun : (fun z : Fin r → ℝ => v ⬝ᵥ z) = L ∘ (WithLp.toLp 2) := by
    funext z
    simp [L, w, PiLp.inner_apply, dotProduct, mul_comm]
  rw [hfun, ← Measure.map_map L.continuous.measurable (by fun_prop), map_pi_eq_stdGaussian,
    IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, hLsq]
  simp

/-- The moment of a squared unit Gaussian projection has the scalar Gamma value.
Source: scalar Gaussian moments; atlas `gaussian-positive-moments` (operator probe detector).
-/
theorem lintegral_rpow_sq_dotProduct_unit_pi_gaussianReal {r : ℕ}
    (v : Fin r → ℝ) (hv : v ⬝ᵥ v = 1) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ z : Fin r → ℝ, ENNReal.ofReal ((v ⬝ᵥ z) ^ 2) ^ q
      ∂(Measure.pi fun _ : Fin r => gaussianReal 0 1))
      = ENNReal.ofReal (2 ^ q * Real.Gamma (q + 1 / 2) / Real.sqrt Real.pi) := by
  have hφ : Measurable (fun z : ℝ => ENNReal.ofReal (z ^ 2) ^ q) := by fun_prop
  have hm : Measurable (fun z : Fin r → ℝ => v ⬝ᵥ z) := by
    unfold dotProduct
    fun_prop
  rw [← lintegral_map hφ hm, pi_gaussianReal_map_dotProduct_unit v hv]
  have hint := (memLp_id_gaussianReal' (μ := 0) (v := 1)
    (ENNReal.ofReal (2 * q)) ENNReal.ofReal_ne_top).integrable_norm_rpow'
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * q)] at hint
  have hfun : (fun z : ℝ => ENNReal.ofReal (z ^ 2) ^ q)
      = fun z : ℝ => ENNReal.ofReal (|z| ^ (2 * q)) := by
    funext z
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg z) hq, ← sq_abs,
      ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 2
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_abs_rpow_gaussianReal q hq]
  · simpa only [Real.norm_eq_abs, id_eq] using hint
  · exact ae_of_all _ fun z => Real.rpow_nonneg (abs_nonneg z) _

/-- Tonelli evaluates the independent Gaussian quadratic probe of an inverse Gram matrix.
Source: operator directional-probe route; atlas `inverse-wishart-spectral-moment`.
All integration uses nonnegative quantities, so inverse spectral integrability is not assumed. -/
theorem lintegral_lintegral_rpow_dotProduct_inv_self_mul_transpose_gaussianMatrix
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (q : ℝ) (hq : 0 < q)
    (hqd : q < ((k : ℝ) - r + 1) / 2) :
    (∫⁻ G : Fin r → Fin k → ℝ, ∫⁻ v : Fin r → ℝ,
      ENNReal.ofReal (v ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ v)) ^ q
      ∂(Measure.pi fun _ : Fin r => gaussianReal 0 1) ∂(gaussianMatrix r k))
      = ENNReal.ofReal ((2 ^ q * Real.Gamma ((r : ℝ) / 2 + q) /
          Real.Gamma ((r : ℝ) / 2)) *
        (Real.Gamma (((k : ℝ) - r + 1) / 2 - q) /
          (2 ^ q * Real.Gamma (((k : ℝ) - r + 1) / 2)))) := by
  let μ := gaussianMatrix r k
  let ν := Measure.pi fun _ : Fin r => gaussianReal 0 1
  let a : ℝ := Real.Gamma (((k : ℝ) - r + 1) / 2 - q) /
    (2 ^ q * Real.Gamma (((k : ℝ) - r + 1) / 2))
  have ha0 : 0 ≤ a := by
    have h1 := Real.Gamma_pos_of_pos (show 0 < ((k : ℝ) - r + 1) / 2 - q by linarith)
    have h2 := Real.Gamma_pos_of_pos (show 0 < ((k : ℝ) - r + 1) / 2 by linarith)
    positivity
  have hjoint : Measurable (fun z : (Fin r → Fin k → ℝ) × (Fin r → ℝ) =>
      ENNReal.ofReal (z.2 ⬝ᵥ ((Matrix.of z.1 * (Matrix.of z.1)ᵀ)⁻¹ *ᵥ z.2)) ^ q) := by
    have hm (i j : Fin r) : Measurable (fun z : (Fin r → Fin k → ℝ) × (Fin r → ℝ) =>
        (Matrix.of z.1 * (Matrix.of z.1)ᵀ)⁻¹ i j) :=
      (measurable_inv_self_mul_transpose_apply i j).comp measurable_fst
    have hz (i : Fin r) : Measurable (fun z : (Fin r → Fin k → ℝ) × (Fin r → ℝ) =>
        z.2 i) := (measurable_pi_apply i).comp measurable_snd
    exact ((Finset.measurable_sum Finset.univ fun i _ => (hz i).mul
      (Finset.measurable_sum Finset.univ fun j _ => (hm i j).mul (hz j))).ennreal_ofReal).pow_const q
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  have hinner : ∀ v : Fin r → ℝ,
      (∫⁻ G : Fin r → Fin k → ℝ,
        ENNReal.ofReal (v ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ v)) ^ q ∂μ)
        = ENNReal.ofReal ((v ⬝ᵥ v) ^ q * a) := by
    intro v
    obtain ⟨hint, hval⟩ :=
      integrable_and_integral_rpow_dotProduct_inv_self_mul_transpose_gaussianMatrix
        hrk v q hq hqd
    have hnonneg : ∀ G : Fin r → Fin k → ℝ,
        0 ≤ v ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ v) := fun G => by
      simpa using (posSemidef_inv_self_mul_transpose (Matrix.of G)).dotProduct_mulVec_nonneg v
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (hnonneg _) hq.le]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun G => Real.rpow_nonneg (hnonneg G) _), hval]
  change (∫⁻ v : Fin r → ℝ, (∫⁻ G : Fin r → Fin k → ℝ,
    ENNReal.ofReal (v ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ v)) ^ q ∂μ) ∂ν) = _
  simp_rw [hinner]
  have hint := (integrable_rpow_sum_sq_pi_gaussianReal r q hq.le).mul_const a
  simp_rw [dotProduct, ← sq]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun v => mul_nonneg
      (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) _) ha0),
    integral_mul_const, integral_rpow_sum_sq_pi_gaussianReal r hr q hq.le]

/-- A Gaussian quadratic probe detects the spectral norm of a fixed positive semidefinite
matrix at every nonnegative real exponent. Source: direct operator-probe route;
atlas `inverse-wishart-spectral-moment`. No measurable eigenvector selection is needed. -/
theorem ofReal_rpow_specNorm_mul_gaussian_moment_le_lintegral {r : ℕ} (hr : 1 ≤ r)
    {A : Matrix (Fin r) (Fin r) ℝ} (hA : A.PosSemidef) (q : ℝ) (hq : 0 ≤ q) :
    ENNReal.ofReal (2 ^ q * Real.Gamma (q + 1 / 2) / Real.sqrt Real.pi) *
        ENNReal.ofReal (specNorm A) ^ q
      ≤ ∫⁻ z : Fin r → ℝ, ENNReal.ofReal (z ⬝ᵥ (A *ᵥ z)) ^ q
        ∂(Measure.pi fun _ : Fin r => gaussianReal 0 1) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨v, hv, hdet⟩ := exists_unit_specNorm_mul_dotProduct_sq_le hA
  have hproj : Measurable (fun z : Fin r → ℝ => ENNReal.ofReal ((v ⬝ᵥ z) ^ 2) ^ q) := by
    unfold dotProduct
    fun_prop
  calc ENNReal.ofReal (2 ^ q * Real.Gamma (q + 1 / 2) / Real.sqrt Real.pi) *
        ENNReal.ofReal (specNorm A) ^ q
      = ENNReal.ofReal (specNorm A) ^ q *
          ∫⁻ z : Fin r → ℝ, ENNReal.ofReal ((v ⬝ᵥ z) ^ 2) ^ q
            ∂(Measure.pi fun _ : Fin r => gaussianReal 0 1) := by
        rw [lintegral_rpow_sq_dotProduct_unit_pi_gaussianReal v hv q hq, mul_comm]
    _ = ∫⁻ z : Fin r → ℝ, ENNReal.ofReal (specNorm A * (v ⬝ᵥ z) ^ 2) ^ q
          ∂(Measure.pi fun _ : Fin r => gaussianReal 0 1) := by
        simp_rw [ENNReal.ofReal_mul (specNorm_nonneg A), ENNReal.mul_rpow_of_nonneg _ _ hq]
        rw [lintegral_const_mul _ hproj]
    _ ≤ _ := lintegral_mono fun z =>
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hdet z)) hq

/-- The master real inverse spectral moment bound obtained by a Gaussian quadratic probe.
Source: `Re-derivations/inverse-moment-analysis.md`, equation (5); atlas
`inverse-wishart-spectral-moment`, `pinv-spectral-expectation`.
The proof uses scalar Schur residual moments and an operator detector, and proves
integrability without a Wishart eigenvalue density. -/
theorem integrable_and_integral_rpow_specNorm_inv_self_mul_transpose_gaussianMatrix_le
    {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) (q : ℝ) (hq : 0 < q)
    (hqd : q < ((k : ℝ) - r + 1) / 2) :
    Integrable (fun G : Fin r → Fin k → ℝ =>
      specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ q) (gaussianMatrix r k) ∧
    (∫ G : Fin r → Fin k → ℝ, specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ q
      ∂(gaussianMatrix r k)) ≤
      Real.Gamma ((r : ℝ) / 2 + q) * Real.Gamma (((k : ℝ) - r + 1) / 2 - q) *
        Real.sqrt Real.pi /
        (2 ^ q * Real.Gamma ((r : ℝ) / 2) * Real.Gamma (((k : ℝ) - r + 1) / 2) *
          Real.Gamma (q + 1 / 2)) := by
  let μ := gaussianMatrix r k
  let c : ℝ := 2 ^ q * Real.Gamma (q + 1 / 2) / Real.sqrt Real.pi
  let a : ℝ := (2 ^ q * Real.Gamma ((r : ℝ) / 2 + q) / Real.Gamma ((r : ℝ) / 2)) *
    (Real.Gamma (((k : ℝ) - r + 1) / 2 - q) /
      (2 ^ q * Real.Gamma (((k : ℝ) - r + 1) / 2)))
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hG1 := Real.Gamma_pos_of_pos (show 0 < (r : ℝ) / 2 by positivity)
  have hG2 := Real.Gamma_pos_of_pos (show 0 < (r : ℝ) / 2 + q by positivity)
  have hG3 := Real.Gamma_pos_of_pos (show 0 < ((k : ℝ) - r + 1) / 2 - q by linarith)
  have hG4 := Real.Gamma_pos_of_pos (show 0 < ((k : ℝ) - r + 1) / 2 by linarith)
  have hG5 := Real.Gamma_pos_of_pos (show 0 < q + 1 / 2 by linarith)
  have hc : 0 < c := by dsimp [c]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hcm0 : ENNReal.ofReal c ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hc
  have hcmT : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hL : ENNReal.ofReal c *
      (∫⁻ G : Fin r → Fin k → ℝ, ENNReal.ofReal
        (specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹) ^ q ∂μ) ≤ ENNReal.ofReal a := by
    rw [← lintegral_const_mul' _ _ hcmT]
    calc (∫⁻ G : Fin r → Fin k → ℝ, ENNReal.ofReal c * ENNReal.ofReal
        (specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹) ^ q ∂μ)
        ≤ ∫⁻ G : Fin r → Fin k → ℝ, ∫⁻ z : Fin r → ℝ,
          ENNReal.ofReal (z ⬝ᵥ ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹ *ᵥ z)) ^ q
          ∂(Measure.pi fun _ : Fin r => gaussianReal 0 1) ∂μ :=
          lintegral_mono fun G => ofReal_rpow_specNorm_mul_gaussian_moment_le_lintegral
            hr (posSemidef_inv_self_mul_transpose (Matrix.of G)) q hq.le
    _ = ENNReal.ofReal a :=
      lintegral_lintegral_rpow_dotProduct_inv_self_mul_transpose_gaussianMatrix hr hrk q hq hqd
  have hbound : (∫⁻ G : Fin r → Fin k → ℝ, ENNReal.ofReal
      (specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹) ^ q ∂μ) ≤ ENNReal.ofReal (a / c) := by
    have h := mul_le_mul_right hL (ENNReal.ofReal c)⁻¹
    rw [← mul_assoc, ENNReal.inv_mul_cancel hcm0 hcmT, one_mul,
      ← ENNReal.ofReal_inv_of_pos hc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)] at h
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hnn : ∀ G : Fin r → Fin k → ℝ,
      0 ≤ specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ q :=
    fun G => Real.rpow_nonneg (specNorm_nonneg _) _
  have hm : Measurable (fun G : Fin r → Fin k → ℝ =>
      specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ q) :=
    measurable_specNorm_inv_self_mul_transpose.pow_const q
  simp_rw [ENNReal.ofReal_rpow_of_nonneg (specNorm_nonneg _) hq.le] at hbound
  have hint : Integrable (fun G : Fin r → Fin k → ℝ =>
      specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ q) μ := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)]
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  have hreal : (∫ G : Fin r → Fin k → ℝ,
      specNorm (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ ^ q ∂μ) ≤ a / c := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn)] at hbound
    exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg ha hc.le)).1 hbound
  refine ⟨hint, hreal.trans_eq ?_⟩
  dsimp [a, c]
  field_simp

end NLAlib
