/-
Ported from the Prove2me workspace (Gaussian Random Matrices series, solutions
`Sol_GaussianMatrix_inv_chi_square_moment`, `Sol_GaussianMatrix_schur_diag_inv`,
`Sol_GaussianMatrix_residual_law`, `Sol_GaussianMatrix_inverse_wishart_mean`,
`Sol_GaussianMatrix_pinv_frobenius_moment`).
-/
import NLAlib.Gaussian.Invariance
import NLAlib.Gaussian.Moments
import NLAlib.Matrix.Pseudoinverse
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Inverse moments of a standard Gaussian matrix

The key Gaussian input of the randomized SVD and generalized Nyström error bounds:
for a standard Gaussian `r × k` matrix `G` with `r + 2 ≤ k`,
`E (G Gᵀ)⁻¹ = (k - r - 1)⁻¹ I` and hence `E ‖G†‖_F² = r / (k - r - 1)`.

* `NLAlib.inv_chi_square_moment`: `E[1/χ²_d] = 1/(d-2)` for `d ≥ 3`
  (atlas `inverse-chi-square-moment`).
* `NLAlib.schur_diag_inv`: a diagonal entry of `(G Gᵀ)⁻¹` is the inverse of the squared residual
  of the corresponding row against the span of the other rows (Schur complement).
* `NLAlib.gaussian_residual_law`: that squared residual, for a standard Gaussian row and fixed
  rows of full rank `n`, is `χ²_{k-n}`.
* `NLAlib.inverse_wishart_mean`: `E (G Gᵀ)⁻¹ = (k - r - 1)⁻¹ I`, entrywise, with integrability
  (atlas `inverse-wishart-mean`); `inverse_wishart_mean_matrix` is the matrix form.
* `NLAlib.pinv_frobenius_moment`: `E ‖G†‖_F² = r / (k - r - 1)` (atlas `pinv-frob-moment`).

Proof source: Prove2me workspace, Gaussian Random Matrices series; the proofs are ported with
the workspace's `rotation_invariance`, `block_law`, `full_rank_ae` replaced by
`NLAlib.gaussianMatrix_map_orthogonal`, `NLAlib.gaussianMatrix_map_block`,
`NLAlib.gaussianMatrix_ae_rank_eq`. The chi-square moment is stated over an arbitrary finite index
type (the source uses `Fin d`; `inv_chi_square_moment_fin` is the source form).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped Matrix

namespace NLAlib

/-! ### The inverse chi-square moment -/

/-- One-dimensional Gaussian integral: `E[exp(-((u-1)/2) Y²)] = u^{-1/2}` for `Y ~ N(0,1)`. -/
private lemma icm_gauss_exp (u : ℝ) (hu : 0 < u) :
    ∫ y, Real.exp (-((u - 1) / 2) * y ^ 2) ∂(gaussianReal 0 1) = u ^ (-(1 / 2 : ℝ)) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [gaussianPDFReal_def, smul_eq_mul, NNReal.coe_one, sub_zero, mul_one]
  have h : ∀ x : ℝ, (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) * rexp (-((u - 1) / 2) * x ^ 2)
      = (√(2 * π))⁻¹ * rexp (-(u / 2) * x ^ 2) := by
    intro x; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian]
  have h2 : π / (u / 2) = (2 * π) / u := by field_simp
  rw [h2, Real.sqrt_div (by positivity), Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
  have : √(2 * π) ≠ 0 := by positivity
  field_simp

/-- Laplace transform of the chi-square sum: `E[exp(-((u-1)/2) ∑ Xⱼ²)] = u^{-d/2}`. -/
private lemma icm_laplace {ι : Type*} [Fintype ι] (u : ℝ) (hu : 0 < u) :
    ∫ x : ι → ℝ, Real.exp (-((u - 1) / 2) * ∑ j, x j ^ 2)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1) = u ^ (-((Fintype.card ι : ℝ) / 2)) := by
  have h : ∀ x : ι → ℝ, Real.exp (-((u - 1) / 2) * ∑ j, x j ^ 2)
      = ∏ j, Real.exp (-((u - 1) / 2) * x j ^ 2) := by
    intro x; rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h]
  rw [integral_fintype_prod_eq_prod (fun _ y => Real.exp (-((u - 1) / 2) * y ^ 2))]
  simp only [icm_gauss_exp u hu, Finset.prod_const, Finset.card_univ]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
  congr 1; ring

/-- `1/S = ∫_1^∞ exp(-((u-1)/2) S)/2 du` for `S > 0`. -/
private lemma icm_inv_repr (S : ℝ) (hS : 0 < S) :
    IntegrableOn (fun u : ℝ => Real.exp (-((u - 1) / 2) * S) / 2) (Ioi 1) ∧
    ∫ u in Ioi 1, Real.exp (-((u - 1) / 2) * S) / 2 = S⁻¹ := by
  have h : ∀ u : ℝ, Real.exp (-((u - 1) / 2) * S) / 2
      = Real.exp ((-(S / 2)) * u) * (Real.exp (S / 2) / 2) := by
    intro u; rw [mul_div_assoc', ← Real.exp_add]; congr 2; ring
  simp_rw [h]
  have hneg : -(S / 2) < 0 := by linarith
  refine ⟨(integrableOn_exp_mul_Ioi hneg 1).mul_const _, ?_⟩
  rw [integral_mul_const, integral_exp_mul_Ioi hneg]
  have he : rexp (-(S / 2)) * rexp (S / 2) = 1 := by rw [← Real.exp_add]; simp
  have hS0 : S ≠ 0 := hS.ne'
  rw [mul_one, show -rexp (-(S / 2)) / -(S / 2) * (rexp (S / 2) / 2)
    = (rexp (-(S / 2)) * rexp (S / 2)) / S by field_simp, he, one_div]

private lemma icm_sum_pos_ae {ι : Type*} [Fintype ι] (hd : 1 ≤ Fintype.card ι) :
    ∀ᵐ x ∂(Measure.pi fun _ : ι => gaussianReal 0 1), 0 < ∑ j, x j ^ 2 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hnull : (Measure.pi fun _ : ι => gaussianReal 0 1)
      (Function.eval i₀ ⁻¹' {0}) = 0 :=
    Measure.pi_eval_preimage_null _ (measure_singleton 0)
  have := measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [this] with x hx
  have hx0 : x i₀ ≠ 0 := by simpa using hx
  have h1 : x i₀ ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ _)
  have h2 : 0 < x i₀ ^ 2 := by positivity
  linarith

private lemma icm_lintegral {ι : Type*} [Fintype ι] (hd : 3 ≤ Fintype.card ι) :
    ∫⁻ x, ENNReal.ofReal (∑ j, x j ^ 2)⁻¹ ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      = ENNReal.ofReal (1 / ((Fintype.card ι : ℝ) - 2)) := by
  set d := Fintype.card ι with hdd
  set μ := Measure.pi fun _ : ι => gaussianReal 0 1 with hμ
  set K : (ι → ℝ) → ℝ → ℝ := fun x u => Real.exp (-((u - 1) / 2) * ∑ j, x j ^ 2) / 2 with hK
  have hK_cont : Continuous (Function.uncurry K) := by
    simp only [hK]; fun_prop
  -- step 1: inner representation
  have step1 : ∀ᵐ x ∂μ, ENNReal.ofReal (∑ j, x j ^ 2)⁻¹
      = ∫⁻ u in Ioi 1, ENNReal.ofReal (K x u) := by
    filter_upwards [icm_sum_pos_ae (ι := ι) (by omega)] with x hx
    obtain ⟨hint, hval⟩ := icm_inv_repr _ hx
    rw [← hval, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun u => by positivity)]
  rw [lintegral_congr_ae step1]
  rw [lintegral_lintegral_swap (hK_cont.measurable.ennreal_ofReal.aemeasurable)]
  -- step 2: inner integral over x
  have step2 : ∀ u ∈ Ioi (1 : ℝ), ∫⁻ x, ENNReal.ofReal (K x u) ∂μ
      = ENNReal.ofReal (u ^ (-((d : ℝ) / 2)) / 2) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
    have hmeas : Measurable fun x => K x u :=
      (hK_cont.comp (Continuous.prodMk_left u)).measurable
    have hint : Integrable (fun x => K x u) μ := by
      refine (integrable_const (1 / 2 : ℝ)).mono' hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hS : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      have : -((u - 1) / 2) * ∑ j, x j ^ 2 ≤ 0 := by
        have : 0 ≤ (u - 1) / 2 := by have := hu.out; linarith
        nlinarith
      have := Real.exp_le_one_iff.mpr this
      simp only [hK]; linarith
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1
    simp only [hK]
    rw [integral_div, icm_laplace u hu0]
  rw [setLIntegral_congr_fun measurableSet_Ioi step2]
  -- step 3: the outer integral
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : -((d : ℝ) / 2) < -1 := by linarith
  have hint3 : IntegrableOn (fun u : ℝ => u ^ (-((d : ℝ) / 2)) / 2) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt ha one_pos).div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hint3]
  · congr 1
    rw [integral_div, integral_Ioi_rpow_of_lt ha one_pos, Real.one_rpow]
    have : (d : ℝ) - 2 ≠ 0 := by linarith
    have : -((d : ℝ) / 2) + 1 ≠ 0 := by linarith
    have : (2 : ℝ) - d ≠ 0 := by linarith
    field_simp
    linear_combination inv_mul_cancel₀ this
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
    positivity

/-- **Inverse chi-square moment.** If `X` is a standard Gaussian vector indexed by a finite type
`ι` with `d = |ι| ≥ 3`, then `1/‖X‖²` is integrable and `E[1/‖X‖²] = E[1/χ²_d] = 1/(d - 2)`.

Tropp–Webber 2023, Lemma B.2 (scalar step); HMT 2011, proof of Prop 10.2 / Prop A.5
(`E[1/χ²_d] = 1/(d-2)`). Atlas: `inverse-chi-square-moment`. The source states it for
`ι = Fin d` (see `inv_chi_square_moment_fin`). Proof ported from the Prove2me solution
`Sol_GaussianMatrix_inv_chi_square_moment` (Laplace-transform representation of `1/S`). -/
theorem inv_chi_square_moment {ι : Type*} [Fintype ι] (hd : 3 ≤ Fintype.card ι) :
    Integrable (fun x : ι → ℝ => (∑ j, x j ^ 2)⁻¹)
        (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
    ∫ x, (∑ j, x j ^ 2)⁻¹ ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      = 1 / ((Fintype.card ι : ℝ) - 2) := by
  have hnn : 0 ≤ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1]
      (fun x : ι → ℝ => (∑ j, x j ^ 2)⁻¹) :=
    Filter.Eventually.of_forall fun x =>
      inv_nonneg.mpr (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hmeas : Measurable (fun x : ι → ℝ => (∑ j, x j ^ 2)⁻¹) := by fun_prop
  have hpos : (0 : ℝ) ≤ 1 / ((Fintype.card ι : ℝ) - 2) := by
    have : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
    apply div_nonneg zero_le_one; linarith
  refine ⟨⟨hmeas.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn, icm_lintegral hd]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable, icm_lintegral hd,
      ENNReal.toReal_ofReal hpos]

/-- **Inverse chi-square moment**, source form over `Fin d`: for `d ≥ 3`,
`E[1/χ²_d] = 1/(d - 2)`.

Tropp–Webber 2023, Lemma B.2 (scalar step); HMT 2011, proof of Prop 10.2.
Atlas: `inverse-chi-square-moment`. Ported from the Prove2me solution
`Sol_GaussianMatrix_inv_chi_square_moment`. -/
theorem inv_chi_square_moment_fin {d : ℕ} (hd : 3 ≤ d) :
    Integrable (fun x : Fin d → ℝ => (∑ j, x j ^ 2)⁻¹)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) ∧
    ∫ x, (∑ j, x j ^ 2)⁻¹ ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1)
      = 1 / ((d : ℝ) - 2) := by
  simpa using inv_chi_square_moment (ι := Fin d) (by simpa using hd)

/-! ### Schur complement formula for a diagonal entry of `(G Gᵀ)⁻¹` -/

/-- **Diagonal entry of the inverse Gram matrix (Schur complement).** Let `G` have rows indexed by
`Fin (n + 1)`, let `H` be `G` with row `i` removed and `g = G i`. If `H Hᵀ` is invertible, then
`(G Gᵀ)⁻¹ᵢᵢ = (‖g‖² - (H g)ᵀ (H Hᵀ)⁻¹ (H g))⁻¹`, the inverse squared distance from `g` to the
row space of `H`.

Helper for Tropp–Webber 2023, Lemma B.2 / HMT 2011, Prop A.5 (proof of `E (G Gᵀ)⁻¹`).
Atlas: `inverse-wishart-mean` (helper `schur_diag_inv`). Proof ported from the Prove2me solution
`Sol_GaussianMatrix_schur_diag_inv` (adjugate computation). -/
theorem schur_diag_inv {n k : ℕ} (G : Matrix (Fin (n + 1)) (Fin k) ℝ) (i : Fin (n + 1))
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
private lemma rl_vec_law {m d : ℕ} (V : Matrix (Fin m) (Fin d) ℝ) (hV : Vᵀ * V = 1) :
    Measure.map (fun g : Fin m → ℝ => Vᵀ *ᵥ g) (Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
  have hι : ∀ p : ℕ, MeasurePreserving
      (fun (g : Fin p → ℝ) (a : Fin p) => (MeasurableEquiv.funUnique (Fin 1) ℝ).symm (g a))
      (Measure.pi fun _ : Fin p => gaussianReal 0 1) (gaussianMatrix p 1) := fun p =>
    measurePreserving_pi _ _ fun _ => (measurePreserving_funUnique (gaussianReal 0 1) (Fin 1)).symm
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

private lemma rl_inner {k : ℕ} (x y : EuclideanSpace ℝ (Fin k)) :
    inner ℝ x y = x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- A square real matrix of full rank `n` has nonzero determinant. -/
private lemma det_ne_zero_of_rank_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (h : M.rank = n) :
    M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hker : v ∈ LinearMap.ker M.mulVecLin := by simpa using hMv
  have h1 : 0 < Module.finrank ℝ (LinearMap.ker M.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hker⟩, by simpa using hv⟩
  have h2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Matrix.rank] at h
  simp only [Module.finrank_fin_fun] at h2
  omega

private lemma rl_exists_V {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℝ) (hH : H.rank = n) :
    ∃ V : Matrix (Fin k) (Fin (k - n)) ℝ, Vᵀ * V = 1 ∧ ∀ g : Fin k → ℝ,
      g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)) = ∑ j, (Vᵀ *ᵥ g) j ^ 2 := by
  set E := EuclideanSpace ℝ (Fin k)
  set T : E →ₗ[ℝ] (Fin n → ℝ) :=
    (Matrix.mulVecLin H).comp (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap with hT
  set K : Submodule ℝ E := LinearMap.ker T with hK
  have hrange : LinearMap.range T = ⊤ := by
    rw [hT, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hH
  have hfin : Module.finrank ℝ K = k - n := by
    have h := LinearMap.finrank_range_add_finrank_ker T
    rw [hrange, finrank_top, Module.finrank_fin_fun, finrank_euclideanSpace_fin] at h
    rw [hK]; omega
  set b : OrthonormalBasis (Fin (k - n)) ℝ K := (stdOrthonormalBasis ℝ K).reindex (finCongr hfin)
  set V : Matrix (Fin k) (Fin (k - n)) ℝ := Matrix.of fun l j => ((b j : K) : E).ofLp l with hV
  have hbK : ∀ j, H *ᵥ ((b j : K) : E).ofLp = 0 := by
    intro j
    have : T ((b j : K) : E) = 0 := LinearMap.mem_ker.mp (b j).2
    exact this
  have hVcol : ∀ (j : Fin (k - n)) (g : Fin k → ℝ), (Vᵀ *ᵥ g) j = ((b j : K) : E).ofLp ⬝ᵥ g := by
    intro j g; simp [hV, Matrix.mulVec, dotProduct]
  refine ⟨V, ?_, ?_⟩
  · ext j j'
    have h1 : (Vᵀ * V) j j' = inner ℝ ((b j : K) : E) ((b j' : K) : E) := by
      rw [rl_inner]; simp [hV, Matrix.mul_apply, dotProduct]
    rw [h1, ← Submodule.coe_inner, orthonormal_iff_ite.mp b.orthonormal, Matrix.one_apply]
  · intro g
    set M := H * Hᵀ with hM
    have hdet : IsUnit M.det := by
      refine isUnit_iff_ne_zero.mpr (det_ne_zero_of_rank_eq _ ?_)
      rw [hM, Matrix.rank_self_mul_transpose, hH]
    set c := M⁻¹ *ᵥ (H *ᵥ g) with hc
    set p := Hᵀ *ᵥ c with hp
    set r := g - p with hr
    have hHr : H *ᵥ r = 0 := by
      rw [hr, Matrix.mulVec_sub, hp, Matrix.mulVec_mulVec, ← hM, hc, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec, sub_self]
    have hq : g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ c = r ⬝ᵥ r := by
      have h1 : r ⬝ᵥ p = 0 := by
        rw [hp, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hHr, zero_dotProduct]
      have h2 : g ⬝ᵥ p = (H *ᵥ g) ⬝ᵥ c := by
        rw [hp, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      have h3 : r ⬝ᵥ r = r ⬝ᵥ g - r ⬝ᵥ p := by
        rw [← dotProduct_sub]
      rw [h3, h1, hr, sub_dotProduct, dotProduct_comm p g, h2, sub_zero]
    have hcoord : ∀ j, (Vᵀ *ᵥ g) j = ((b j : K) : E).ofLp ⬝ᵥ r := by
      intro j
      rw [hVcol, hr, dotProduct_sub, hp, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
        hbK, zero_dotProduct, sub_zero]
    have hrK : (WithLp.toLp 2 r : E) ∈ K := by
      simpa [hK, hT] using hHr
    set rK : K := ⟨WithLp.toLp 2 r, hrK⟩
    have hpars := b.sum_inner_mul_inner rK rK
    rw [hq]
    simp_rw [hcoord]
    have hrr : inner ℝ rK rK = r ⬝ᵥ r := by
      rw [Submodule.coe_inner, rl_inner]
    have hbj : ∀ j, inner ℝ (b j) rK = ((b j : K) : E).ofLp ⬝ᵥ r := by
      intro j; rw [Submodule.coe_inner, rl_inner]
    rw [← hrr, ← hpars]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm, hbj, sq]

/-- **Law of the residual of a Gaussian row.** Let `H` be a fixed `n × k` real matrix of rank
`n` and `g` a standard Gaussian vector in `ℝᵏ`. The squared distance from `g` to the row space of
`H`, `‖g‖² - (H g)ᵀ (H Hᵀ)⁻¹ (H g)`, has the `χ²_{k-n}` law (the law of `∑ⱼ Xⱼ²`,
`X ~ N(0, I_{k-n})`).

Helper for Tropp–Webber 2023, Lemma B.2 / HMT 2011, Prop A.5. Atlas: `inverse-wishart-mean`
(helper `residual_law`). Proof ported from the Prove2me solution `Sol_GaussianMatrix_residual_law`
(orthonormal basis of `ker H` and the block law `gaussianMatrix_map_block`, atlas
`block-law-indep`). -/
theorem gaussian_residual_law {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℝ) (hH : H.rank = n) :
    Measure.map (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))
        (Measure.pi fun _ : Fin k => gaussianReal 0 1)
      = Measure.map (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2)
        (Measure.pi fun _ : Fin (k - n) => gaussianReal 0 1) := by
  obtain ⟨V, hV, hq⟩ := rl_exists_V H hH
  have hfun : (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g))) =
      (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2) ∘ (fun g : Fin k → ℝ => Vᵀ *ᵥ g) := funext hq
  have hS : Measurable (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2) := by fun_prop
  have hVm : Measurable (fun g : Fin k → ℝ => Vᵀ *ᵥ g) := by
    refine measurable_pi_lambda _ fun a => ?_
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  rw [hfun, ← Measure.map_map hS hVm, rl_vec_law V hV]

/-! ### Mean of the inverse Wishart matrix -/

private lemma iwm_measurable_inv_entry {r k : ℕ} (i j : Fin r) :
    Measurable (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j) := by
  have hc : Continuous (fun G : Fin r → Fin k → ℝ => Matrix.of G * (Matrix.of G)ᵀ) :=
    Continuous.matrix_mul continuous_id (Continuous.matrix_transpose continuous_id)
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hc.matrix_det.measurable.inv).mul (hc.matrix_adjugate.matrix_elem i j).measurable

private lemma iwm_psd_inv {r k : ℕ} (G : Fin r → Fin k → ℝ) :
    ((Matrix.of G * (Matrix.of G)ᵀ)⁻¹).PosSemidef := by
  have := Matrix.posSemidef_self_mul_conjTranspose (Matrix.of G)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact this.inv

private lemma iwm_psd_offdiag {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) (hM : M.PosSemidef)
    (i j : Fin r) : |M i j| ≤ M i i + M j j := by
  have hs : M j i = M i j := by
    have := hM.isHermitian.apply i j
    simpa using this
  by_cases hij : i = j
  · subst hij
    have := hM.diag_nonneg (i := i)
    rw [abs_of_nonneg this]; linarith
  have h1 := hM.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have h2 := hM.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub, Matrix.mulVec_single, single_dotProduct,
    hs] at h1 h2
  rw [abs_le]; constructor <;> linarith

private lemma iwm_offdiag_integral {r k : ℕ} (i j : Fin r) (hij : i ≠ j) :
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
  rw [integral_map hmeas.aemeasurable (iwm_measurable_inv_entry i j).aestronglyMeasurable] at h1
  simp_rw [key, integral_neg] at h1
  linarith

private lemma iwm_resid_moment {n k : ℕ} (hnk : n + 3 ≤ k) (H : Matrix (Fin n) (Fin k) ℝ)
    (hH : H.rank = n) :
    Integrable (fun g : Fin k → ℝ => (g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹)
        (Measure.pi fun _ : Fin k => gaussianReal 0 1) ∧
    ∫ g, (g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))⁻¹
        ∂(Measure.pi fun _ : Fin k => gaussianReal 0 1) = 1 / ((k : ℝ) - n - 2) := by
  have hq : Measurable
      (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g))) := by
    apply Continuous.measurable
    fun_prop
  have hlaw := gaussian_residual_law H hH
  obtain ⟨hint, hval⟩ := inv_chi_square_moment_fin (d := k - n) (by omega)
  have hφ : Measurable (fun s : ℝ => s⁻¹) := measurable_inv
  have hS : Measurable (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2) := by fun_prop
  constructor
  · have h := (integrable_map_measure hφ.aestronglyMeasurable hS.aemeasurable).mpr hint
    rw [← hlaw] at h
    exact (integrable_map_measure hφ.aestronglyMeasurable hq.aemeasurable).mp h
  · rw [← integral_map hq.aemeasurable hφ.aestronglyMeasurable, hlaw,
      integral_map hS.aemeasurable hφ.aestronglyMeasurable, hval,
      Nat.cast_sub (by omega : n ≤ k)]

private lemma iwm_diag {n k : ℕ} (hnk : n + 3 ≤ k) (i : Fin (n + 1)) :
    Integrable (fun G : Fin (n + 1) → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i)
        (gaussianMatrix (n + 1) k) ∧
    ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i ∂(gaussianMatrix (n + 1) k)
      = 1 / ((k : ℝ) - n - 2) := by
  set μ : Measure (Fin k → ℝ) := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hμ
  set ν : Measure (Fin n → Fin k → ℝ) := Measure.pi fun _ : Fin n => μ with hν
  set F : (Fin (n + 1) → Fin k → ℝ) → ℝ :=
    fun G => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i with hF
  have hFm : Measurable F := iwm_measurable_inv_entry i i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin k → ℝ) i with he
  have hmp : MeasurePreserving e (gaussianMatrix (n + 1) k) (μ.prod ν) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  set Φ : (Fin k → ℝ) × (Fin n → Fin k → ℝ) → ℝ := fun p => F (e.symm p) with hΦ
  have hΦm : Measurable Φ := hFm.comp e.symm.measurable
  have hΦnn : ∀ p, 0 ≤ Φ p := fun p => (iwm_psd_inv _).diag_nonneg
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
      exact det_ne_zero_of_rank_eq _ (by rw [Matrix.rank_self_mul_transpose, hH])
    have := schur_diag_inv (Matrix.of G0) i hdet
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
    exact iwm_resid_moment hnk (Matrix.of H) hH
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
against the others (`schur_diag_inv`), which given the other rows (full rank a.s., atlas
`gaussian-full-rank-ae`) is `1/χ²_{k-r+1}` (`gaussian_residual_law`, atlas `block-law-indep`;
`inv_chi_square_moment`, atlas `inverse-chi-square-moment`). -/
theorem inverse_wishart_mean {r k : ℕ} (hrk : r + 2 ≤ k) :
    (∀ i j : Fin r, Integrable (fun G : Fin r → Fin k → ℝ =>
        (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j) (gaussianMatrix r k)) ∧
    ∀ i j : Fin r, ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ∂(gaussianMatrix r k)
      = (1 / ((k : ℝ) - r - 1)) * (1 : Matrix (Fin r) (Fin r) ℝ) i j := by
  have hdiag : ∀ i : Fin r, Integrable (fun G : Fin r → Fin k → ℝ =>
      (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i) (gaussianMatrix r k) := by
    intro i
    cases r with
    | zero => exact i.elim0
    | succ n => exact (iwm_diag (by omega) i).1
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · refine Integrable.mono' ((hdiag i).add (hdiag j))
      (iwm_measurable_inv_entry i j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun G => ?_)
    rw [Real.norm_eq_abs]
    exact iwm_psd_offdiag _ (iwm_psd_inv G) i j
  · by_cases hij : i = j
    · subst hij
      cases r with
      | zero => exact i.elim0
      | succ n =>
        rw [(iwm_diag (by omega) i).2, Matrix.one_apply_eq, mul_one]
        push_cast
        ring_nf
    · rw [iwm_offdiag_integral i j hij, Matrix.one_apply_ne hij, mul_zero]

/-- **Mean of the inverse Wishart matrix, matrix form.** For an `r × k` standard Gaussian matrix
`G` with `r + 2 ≤ k`, the matrix of entrywise expectations of `(G Gᵀ)⁻¹` is `(k - r - 1)⁻¹ • I`.

Tropp–Webber 2023, Lemma B.2; HMT 2011, Prop A.5. Atlas: `inverse-wishart-mean`. Corollary of
`inverse_wishart_mean` (entrywise integrability is its first component). -/
theorem inverse_wishart_mean_matrix {r k : ℕ} (hrk : r + 2 ≤ k) :
    (Matrix.of fun i j : Fin r =>
        ∫ G, (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i j ∂(gaussianMatrix r k))
      = (1 / ((k : ℝ) - r - 1)) • (1 : Matrix (Fin r) (Fin r) ℝ) := by
  ext i j
  rw [Matrix.of_apply, (inverse_wishart_mean hrk).2 i j, Matrix.smul_apply, smul_eq_mul]

/-! ### Frobenius moment of the pseudoinverse -/

/-- `‖G†‖_F² = tr (G Gᵀ)⁻¹` for every real matrix `G`, with `G† = pinvR G`: the unconditional
form of `frobSq_pinvR` (if `G Gᵀ` is singular both sides are `0`, by Mathlib's convention
`A⁻¹ = 0`).

HMT 2011 §A.2 (proof of Prop 10.1). Atlas `pseudoinverse`. Ported from the Prove2me solution
`Sol_GaussianMatrix_pinv_frobenius_moment` (`frobSq_pinvR_eq_trace_inv`). -/
theorem frobSq_pinvR_eq_trace_inv {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (G : Matrix m n ℝ) : frobSq (pinvR G) = ((G * Gᵀ)⁻¹).trace := by
  by_cases h : IsUnit (G * Gᵀ)
  · exact frobSq_pinvR h
  · have h0 : (G * Gᵀ)⁻¹ = 0 :=
      Matrix.nonsing_inv_apply_not_isUnit _ (by rwa [← Matrix.isUnit_iff_isUnit_det])
    have hp : pinvR G = 0 := by simp [pinvR, h0]
    rw [h0, hp, Matrix.trace_zero, frobSq_eq_sum_sq]
    simp

/-- **Frobenius moment of the Gaussian pseudoinverse.** If `G` is an `r × k` standard Gaussian
matrix with `r + 2 ≤ k`, then `‖G†‖_F²` is integrable and `E ‖G†‖_F² = r / (k - r - 1)`, where
`G† = Gᵀ (G Gᵀ)⁻¹ = pinvR G`.

Tropp–Webber 2023, Lemma B.2; HMT 2011, Prop 10.2 (`E ‖Ω₁†‖_F² = k/(p-1)` with `Ω₁` of size
`k × (k+p)`). Atlas: `pinv-frob-moment`. Proof ported from the Prove2me solution
`Sol_GaussianMatrix_pinv_frobenius_moment`: `‖G†‖_F² = tr (G Gᵀ)⁻¹`
(`frobSq_pinvR_eq_trace_inv`, atlas `pseudoinverse`) and `inverse_wishart_mean`
(atlas `inverse-wishart-mean`). -/
theorem pinv_frobenius_moment {r k : ℕ} (hrk : r + 2 ≤ k) :
    Integrable (fun G : Fin r → Fin k → ℝ => frobSq (pinvR (Matrix.of G))) (gaussianMatrix r k) ∧
    ∫ G, frobSq (pinvR (Matrix.of G)) ∂(gaussianMatrix r k) = (r : ℝ) / ((k : ℝ) - r - 1) := by
  obtain ⟨hint, hval⟩ := inverse_wishart_mean hrk
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
