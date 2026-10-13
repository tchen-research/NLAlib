import NLAlib.RandomMatrix.Gaussian.Basic.Lipschitz
import NLAlib.RandomMatrix.Gaussian.Moments.FourthMoment
/-!
# Linear forms of a Gaussian matrix

The Gaussian processes of the comparison proofs in `NLAlib.RandomMatrix.Gaussian.Spectral` are families of
linear forms of a standard Gaussian matrix `G`:

* `linForm c G = ∑ᵢⱼ cᵢⱼ Gᵢⱼ` (the Frobenius pairing `⟨c, G⟩_F` of a coefficient array `c` with
  the Gaussian matrix `G : Matrix (Fin p) (Fin m) ℝ`; `linForm_eq_frobInner` is the bridge to
  `NLAlib.frobInner`), and `linFormCLM a` packaging a family `(linForm (a t))ₜ` as a continuous
  linear map;
* `hasGaussianLaw_linForm_gaussianMatrix`: any finite family `(⟨a t, G⟩)ₜ` is jointly Gaussian;
* `integral_linForm_gaussianMatrix`, `integral_linForm_sq_gaussianMatrix`: `𝔼⟨c, G⟩ = 0`,
  `𝔼⟨c, G⟩² = ∑ᵢⱼ cᵢⱼ²` (the diagonal case of the covariance
  `integral_linForm_mul_two_gaussianMatrix` of `Moments/FourthMoment`);
* `𝔼 √(∑ⱼ H_{0,σ(j)}²) ≤ √k` (`integral_sqrt_sum_sq_gaussianMatrix_entry_le`).

The definition `linForm` with `linForm_eq_frobInner`, `continuous_linForm`, and the entrywise
facts (`hasGaussianLaw_id_gaussianMatrix`, the instance `isGaussian_gaussianMatrix`, `𝔼 Gᵢⱼ = 0`,
`𝔼 Gᵢⱼ² = 1`) live in `NLAlib.RandomMatrix.Gaussian.Basic.GaussianMatrix`.

Ported from the Prove2me solutions `GaussianMatrix.gordon_upper`, `GaussianMatrix.gordon_lower`
and `GaussianMatrix.spectral_second_moment_bound` (identical helper sections, deduplicated).

Atlas: helpers of `gordon`, `spectral-second-moment`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- A finite family of linear forms `(⟨a t, ·⟩)ₜ` as one continuous linear map into `ι → ℝ`.
Ported from Prove2me solution `GaussianMatrix.gordon_upper` (`guLinCLM`). -/
noncomputable def linFormCLM {ι : Type*} {p m : ℕ} (a : ι → Fin p → Fin m → ℝ) :
    Matrix (Fin p) (Fin m) ℝ →L[ℝ] (ι → ℝ) where
  toFun G t := linForm (a t) G
  map_add' G H := by
    funext t; simp [linForm, mul_add, Finset.sum_add_distrib]
  map_smul' c G := by
    funext t; simp [linForm, Finset.mul_sum, mul_left_comm]
  cont := continuous_pi fun t => continuous_linForm _

/-- A finite family of linear forms `(⟨a t, G⟩)ₜ` of a standard Gaussian matrix is jointly
Gaussian. Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper
`gu_hasGaussianLaw_lin`). Atlas: helper of `gordon`. -/
theorem hasGaussianLaw_linForm_gaussianMatrix {ι : Type*} [Fintype ι] {p m : ℕ}
    (a : ι → Fin p → Fin m → ℝ) :
    HasGaussianLaw (fun G t => linForm (a t) G) (gaussianMatrix (Fin p) (Fin m)) := by
  have e : (fun G t => linForm (a t) G) = fun G => linFormCLM a G := rfl
  rw [e]
  exact ⟨isGaussian_map_of_measurable (linFormCLM a).continuous.measurable⟩

/-- `⟨c, G⟩` is integrable. Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper
`gu_integrable_lin`). Atlas: helper of `gordon`. -/
theorem integrable_linForm_gaussianMatrix {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    Integrable (linForm c) (gaussianMatrix (Fin p) (Fin m)) := by
  unfold linForm
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((memLp_gaussianMatrix_entry i j 2 (by simp)).integrable (by simp)).const_mul _

/-- `𝔼⟨c, G⟩ = 0`. Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper
`gu_integral_lin`). Atlas: helper of `gordon`. -/
theorem integral_linForm_gaussianMatrix {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    ∫ G, linForm c G ∂(gaussianMatrix (Fin p) (Fin m)) = 0 := by
  have h : ∀ i j, Integrable (fun G : Matrix (Fin p) (Fin m) ℝ => c i j * G i j)
      (gaussianMatrix (Fin p) (Fin m)) := fun i j =>
    ((memLp_gaussianMatrix_entry i j 2 (by simp)).integrable (by simp)).const_mul _
  unfold linForm
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => h i j]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => h i j]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul, integral_gaussianMatrix_entry_eq_zero, mul_zero]

/-- `⟨c, G⟩ - ⟨d, G⟩ = ⟨c - d, G⟩`. Ported from Prove2me solution `GaussianMatrix.gordon_upper`
(helper `gu_lin_sub`). -/
theorem linForm_sub_linForm {p m : ℕ} (c d : Fin p → Fin m → ℝ) (G : Matrix (Fin p) (Fin m) ℝ) :
    linForm c G - linForm d G = linForm (c - d) G := by
  simp only [linForm, ← Finset.sum_sub_distrib, Pi.sub_apply, sub_mul]

/-- `𝔼⟨c, G⟩² = ∑ᵢⱼ cᵢⱼ²`: the case `u = v` of `integral_linForm_mul_two_gaussianMatrix`.
Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper `gu_integral_lin_sq`).
Atlas: helper of `gordon`. -/
theorem integral_linForm_sq_gaussianMatrix {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    ∫ G, linForm c G ^ 2 ∂(gaussianMatrix (Fin p) (Fin m)) = ∑ i, ∑ j, c i j ^ 2 := by
  simp only [sq]
  exact integral_linForm_mul_two_gaussianMatrix c c

/-- `⟨c, G⟩ ∈ L²`. Ported from Prove2me solution
`GaussianMatrix.spectral_second_moment_bound` (helper `ssb_memLp_lin`). Atlas: helper of
`spectral-second-moment`. -/
theorem memLp_linForm_gaussianMatrix {p m : ℕ} (c : Fin p → Fin m → ℝ) :
    MemLp (linForm c) 2 (gaussianMatrix (Fin p) (Fin m)) := by
  unfold linForm
  exact memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ =>
    (memLp_gaussianMatrix_entry i j 2 (by simp)).const_mul _

/-- `𝔼 √(∑ⱼ H_{0,σ(j)}²) ≤ √k` for `k` coordinates of a Gaussian row (Jensen). Ported from
Prove2me solution `GaussianMatrix.gordon_upper` (helper `gu_integral_sqrt_sumsq_le`). Atlas:
helper of `gordon`. -/
theorem integral_sqrt_sum_sq_gaussianMatrix_entry_le {k m : ℕ} (σ : Fin k → Fin m) :
    ∫ H, Real.sqrt (∑ j, H 0 (σ j) ^ 2) ∂(gaussianMatrix (Fin 1) (Fin m)) ≤ Real.sqrt k := by
  have hQ : Integrable (fun H : Matrix (Fin 1) (Fin m) ℝ => ∑ j, H 0 (σ j) ^ 2) (gaussianMatrix (Fin 1) (Fin m)) :=
    integrable_finsetSum _ fun j _ => (memLp_gaussianMatrix_entry 0 (σ j) 2 (by simp)).integrable_sq
  have hQ0 : ∀ H : Matrix (Fin 1) (Fin m) ℝ, 0 ≤ ∑ j, H 0 (σ j) ^ 2 := fun H =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcont : Continuous (fun H : Matrix (Fin 1) (Fin m) ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2)) := by
    fun_prop
  have hS : Integrable (fun H : Matrix (Fin 1) (Fin m) ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2))
      (gaussianMatrix (Fin 1) (Fin m)) := by
    refine Integrable.mono' ((integrable_const 1).add hQ) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun H => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 := Real.sq_sqrt (hQ0 H)
    have h2 := Real.sqrt_nonneg (∑ j, H 0 (σ j) ^ 2)
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (Real.sqrt (∑ j, H 0 (σ j) ^ 2) - 1)]
  have hS2 : Integrable (fun H : Matrix (Fin 1) (Fin m) ℝ => Real.sqrt (∑ j, H 0 (σ j) ^ 2) ^ 2)
      (gaussianMatrix (Fin 1) (Fin m)) := by
    refine hQ.congr (Filter.Eventually.of_forall fun H => ?_)
    exact (Real.sq_sqrt (hQ0 H)).symm
  refine MeasureTheory.integral_le_of_integral_sq_le _ _ hS hS2 _ (Real.sqrt_nonneg _) (le_of_eq ?_)
  rw [Real.sq_sqrt (Nat.cast_nonneg k)]
  simp_rw [Real.sq_sqrt (hQ0 _)]
  rw [integral_finsetSum _ fun j _ =>
    (memLp_gaussianMatrix_entry 0 (σ j) 2 (by simp)).integrable_sq]
  simp [integral_gaussianMatrix_entry_sq_eq_one]

end NLAlib
