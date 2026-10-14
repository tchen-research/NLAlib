/-
Ported from the Prove2me workspace (Gaussian Random Matrices series, solutions
`Sol_GaussianMatrix_frobenius_second_moment`, `Sol_GaussianMatrix_full_rank_ae`).
-/
import NLAlib.RandomMatrix.Gaussian.Basic.GaussianMatrix
import NLAlib.Matrix.Norms.Core
import NLAlib.Matrix.Structured.GenericRank
import NLAlib.ForMathlib.MeasureTheory.PolynomialZeroSets

/-!
# Moments and almost-sure rank of the standard Gaussian matrix

* `NLAlib.integral_frobSq_mul_gaussianMatrix_mul`: `E ‖S G T‖_F² = ‖S‖_F² ‖T‖_F²`
  (HMT 2011 Prop 10.1, first identity; atlas `gaussian-frob-second-moment`).
* `NLAlib.ae_ne_zero_mvPolynomial`, `NLAlib.gaussianMatrix_ae_eval_ne_zero`: a nonzero polynomial
  in i.i.d. atomless coordinates (in particular in the entries of a Gaussian matrix) is a.s.
  nonzero.
* `NLAlib.gaussianMatrix_ae_rank_eq`: a standard Gaussian matrix has full rank almost surely,
  with the corollaries `gaussianMatrix_ae_isUnit_mul_transpose` (wide case, `G Gᵀ` invertible)
  and `gaussianMatrix_ae_isUnit_transpose_mul` (tall case) (HMT 2011 Prop A.5 / §10.2; atlas
  `gaussian-full-rank-ae`).

The entry-level facts (`integral_gaussianMatrix_entry_mul`, `gaussianMatrix_map_uncurry`) are in
`NLAlib.RandomMatrix.Gaussian.Basic.GaussianMatrix`. Proof source: Prove2me workspace, Gaussian Random Matrices series
(Frobenius second moment, full rank a.s.).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-! ### The sandwiched second moment -/

private lemma frobSq_expand {ι κ p m : Type*} [Fintype ι] [Fintype κ] [Fintype p] [Fintype m]
    (S : Matrix ι p ℝ) (T : Matrix m κ ℝ) (G : Matrix p m ℝ) :
    frobSq (S * G * T) = ∑ i, ∑ j, ∑ k, ∑ c, ∑ b, ∑ d,
      (S i k * T b j * S i c * T d j) * (G k b * G c d) := by
  rw [frobSq_eq_sum_sq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : (S * G * T) i j = ∑ k, ∑ b, S i k * G k b * T b j := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [h, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
  ring

private lemma integral_quadratic {ι κ p m : Type*} [Fintype ι] [Fintype κ] [Fintype p] [Fintype m]
    (w : ι → κ → p → p → m → m → ℝ) :
    ∫ G, (∑ i, ∑ j, ∑ k, ∑ c, ∑ b, ∑ d, w i j k c b d * (G k b * G c d))
        ∂(gaussianMatrix p m)
      = ∑ i, ∑ j, ∑ k, ∑ b, w i j k k b b := by
  classical
  have hI : ∀ (k c : p) (b : m) (f : m → ℝ),
      Integrable (fun G : Matrix p m ℝ => ∑ d, f d * (G k b * G c d))
        (gaussianMatrix p m) :=
    fun k c b f => integrable_finsetSum _ fun d _ =>
      integrable_const_mul_gaussianMatrix_entry_mul k c b d _
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun b _ => hI k c b _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun b _ => hI k c b _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun b _ => hI k c b _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun b _ => hI k c b _]
  rw [Finset.sum_eq_single k]
  · rw [integral_finsetSum _ fun b _ => hI k k b _]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finsetSum _ fun d _ => integrable_const_mul_gaussianMatrix_entry_mul k k b d _]
    simp [integral_const_mul, integral_gaussianMatrix_entry_mul]
  · intro c _ hck
    rw [integral_finsetSum _ fun b _ => hI k c b _]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [integral_finsetSum _ fun d _ => integrable_const_mul_gaussianMatrix_entry_mul k c b d _]
    refine Finset.sum_eq_zero fun d _ => ?_
    simp [integral_const_mul, integral_gaussianMatrix_entry_mul, Ne.symm hck]
  · simp

/-- **Second Frobenius moment of a sandwiched Gaussian matrix.** For fixed `S` and `T` and a
`p × m` standard Gaussian matrix `G`, `E ‖S G T‖_F² = ‖S‖_F² ‖T‖_F²`.

HMT 2011 (Halko–Martinsson–Tropp), Prop 10.1, first identity (`E‖SGT‖_F² = ‖S‖_F² ‖T‖_F²`).
Atlas: `gaussian-frob-second-moment`. All four dimensions are arbitrary finite index types
(the source and the Prove2me statement use `Fin`). Ported from the Prove2me
workspace, Gaussian Random Matrices series.
atlas: gaussian-frob-second-moment -/
theorem integral_frobSq_mul_gaussianMatrix_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p m : Type*} [Fintype p] [Fintype m] (S : Matrix ι p ℝ) (T : Matrix m κ ℝ) :
    ∫ G, frobSq (S * G * T) ∂(gaussianMatrix p m) = frobSq S * frobSq T := by
  simp_rw [frobSq_expand]
  rw [integral_quadratic (fun i j k c b d => S i k * T b j * S i c * T d j)]
  rw [frobSq_eq_sum_sq, frobSq_eq_sum_sq]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `integral_frobSq_mul_gaussianMatrix_mul` for a random matrix `X` with
`HasLaw X (gaussianMatrix p m) μ`: `E ‖S X T‖_F² = ‖S‖_F² ‖T‖_F²`.
Atlas: `gaussian-frob-second-moment`. -/
theorem integral_frobSq_mul_gaussianMatrix_mul_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ι κ p m : Type*} [Fintype ι] [Fintype κ] [Fintype p] [Fintype m]
    {X : Ω → Matrix p m ℝ} (hX : HasLaw X (gaussianMatrix p m) μ) (S : Matrix ι p ℝ)
    (T : Matrix m κ ℝ) :
    ∫ ω, frobSq (S * X ω * T) ∂μ = frobSq S * frobSq T := by
  have hc : Continuous fun G : Matrix p m ℝ => frobSq (S * G * T) := by
    simp only [frobSq_eq_sum_sq]; fun_prop
  rw [← integral_frobSq_mul_gaussianMatrix_mul S T]
  exact hX.integral_comp hc.aestronglyMeasurable

/-! ### Zero sets of polynomials and full rank -/

/-- A nonzero real polynomial is almost everywhere nonzero in atomless
sigma-finite product coordinates. Compatibility name for the general
`MvPolynomial.ae_eval_ne_zero` interface; HMT 2011, Proposition A.5. -/
theorem ae_ne_zero_mvPolynomial {ι : Type*} [Fintype ι] (μ : Measure ℝ)
    [SigmaFinite μ] [NullSingletonClass μ] (f : MvPolynomial ι ℝ) (hf : f ≠ 0) :
    ∀ᵐ x ∂(Measure.pi fun _ : ι => μ), MvPolynomial.eval x f ≠ 0 :=
  MvPolynomial.ae_eval_ne_zero μ f hf

/-- A nonzero polynomial in the entries of a standard Gaussian matrix is almost surely nonzero.

Helper for HMT 2011 Prop A.5; atlas `gaussian-full-rank-ae`. -/
theorem gaussianMatrix_ae_eval_ne_zero (p m : ℕ) (f : MvPolynomial (Fin p × Fin m) ℝ)
    (hf : f ≠ 0) :
    ∀ᵐ G ∂(gaussianMatrix (Fin p) (Fin m)), MvPolynomial.eval (fun ab => G ab.1 ab.2) f ≠ 0 := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have h := ae_ne_zero_mvPolynomial (gaussianReal 0 1) f hf
  rw [← gaussianMatrix_map_uncurry] at h
  exact ae_of_ae_map (measurable_pi_lambda _ fun ab =>
    (measurable_pi_apply ab.2).comp (measurable_pi_apply ab.1)).aemeasurable h

/-- **A wide Gaussian matrix has full row rank a.s.** If `k ≤ t` and `G` is a `k × t`
standard Gaussian matrix, then `G Gᵀ` is invertible almost surely.

HMT 2011 (Halko–Martinsson–Tropp), Prop A.5 / §10.2 (`Ω₁` has full row rank with probability
one). Atlas: `gaussian-full-rank-ae`. Ported from the Prove2me workspace, Gaussian Random
Matrices series.
atlas: gaussian-full-rank-ae -/
theorem gaussianMatrix_ae_isUnit_mul_transpose {k t : ℕ} (h : k ≤ t) :
    ∀ᵐ G ∂(gaussianMatrix (Fin k) (Fin t)), IsUnit (G * Gᵀ) := by
  have hP := Matrix.det_mvPolynomialX_mul_transpose_ne_zero h
  filter_upwards [gaussianMatrix_ae_eval_ne_zero k t _ hP] with G hG
  rw [Matrix.eval_det_mvPolynomialX_mul_transpose] at hG
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hG)

/-- **A tall Gaussian matrix has full column rank a.s.** If `t ≤ k` and `G` is a `k × t`
standard Gaussian matrix, then `Gᵀ G` is invertible almost surely.

HMT 2011 (Halko–Martinsson–Tropp), Prop A.5 (transposed form). Atlas: `gaussian-full-rank-ae`.
Ported from the Prove2me workspace, Gaussian Random Matrices series.
atlas: gaussian-full-rank-ae -/
theorem gaussianMatrix_ae_isUnit_transpose_mul {k t : ℕ} (h : t ≤ k) :
    ∀ᵐ G ∂(gaussianMatrix (Fin k) (Fin t)), IsUnit (Gᵀ * G) := by
  have hP := Matrix.det_transpose_mvPolynomialX_mul_ne_zero h
  filter_upwards [gaussianMatrix_ae_eval_ne_zero k t _ hP] with G hG
  rw [Matrix.eval_det_transpose_mvPolynomialX_mul] at hG
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hG)

/-- **A Gaussian matrix has full rank a.s.** A `p × m` standard Gaussian matrix has rank
`min p m` almost surely.

HMT 2011 (Halko–Martinsson–Tropp), Prop A.5 / §10.2. Atlas: `gaussian-full-rank-ae`. Ported
from the Prove2me workspace, Gaussian Random Matrices series.
atlas: gaussian-full-rank-ae -/
theorem gaussianMatrix_ae_rank_eq (p m : ℕ) :
    ∀ᵐ G ∂(gaussianMatrix (Fin p) (Fin m)), G.rank = min p m := by
  rcases le_total p m with h | h
  · filter_upwards [gaussianMatrix_ae_isUnit_mul_transpose h] with G hu
    have h1 := Matrix.rank_of_isUnit _ hu
    have h2 := Matrix.rank_mul_le_left G Gᵀ
    have h3 := Matrix.rank_le_height G
    rw [Fintype.card_fin] at h1
    rw [min_eq_left h]; omega
  · filter_upwards [gaussianMatrix_ae_isUnit_transpose_mul h] with G hu
    have h1 := Matrix.rank_of_isUnit _ hu
    have h2 := Matrix.rank_mul_le_right Gᵀ G
    have h3 := Matrix.rank_le_width G
    rw [Fintype.card_fin] at h1
    rw [min_eq_right h]; omega

end NLAlib
