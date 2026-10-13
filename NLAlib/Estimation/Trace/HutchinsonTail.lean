import NLAlib.Probability.Concentration.QuadraticForms.HansonWright
import NLAlib.Estimation.QuadraticForms.HutchinsonLaws
import NLAlib.Matrix.Spectral.QuadraticProbe
import NLAlib.Matrix.Perturbation.EigenvalueTrace

/-!
# Tail bound for Hutchinson's trace estimator

The `m`-sample Hutchinson estimator `tr_m(A) = (1/m) ∑ₖ zₖᵀ A zₖ` (`NLAlib.hutchinsonEstimate`,
samples the columns of a test matrix `Z : Matrix n κ ℝ`, `m = |κ|`) is a single quadratic form
`vec(Z)ᵀ B vec(Z)` in the `n·m` independent entries of `Z`, with the block-diagonal
`B = (1/m) diag(A, …, A)` (`NLAlib.hutchinsonBlock`). Since `‖B‖_F² = ‖A‖_F²/m` and
`‖B‖ ≤ ‖A‖/m`, the Hanson–Wright inequality (`NLAlib.hanson_wright_mgf`) gives

`P(|tr_m(A) − 𝔼 tr_m(A)| ≥ t) ≤ 2 exp(−(1/(256e²)) min(m t²/(K⁴‖A‖_F²), m t/(K²‖A‖)))`

for sub-Gaussian entries with variance proxy `K²`, and with `𝔼 tr_m(A) = tr A`, `K = 1` for
standard Gaussian (`HasLaw Z (gaussianMatrix n κ) μ`) and Rademacher
(`HasLaw (fun ω e => Z ω e.1 e.2) (rademacherVector (n × κ)) μ`) test matrices.

## Main results

* `NLAlib.measureReal_le_abs_hutchinsonEstimate_sub_integral_le`: general sub-Gaussian entries.
* `NLAlib.measureReal_le_abs_hutchinsonEstimate_sub_trace_le_of_hasLaw_gaussianMatrix`: Gaussian.
* `NLAlib.measureReal_le_abs_hutchinsonEstimate_sub_trace_le_of_hasLaw_rademacherVector`: Rademacher.
* `NLAlib.measureReal_le_abs_hutchinsonEstimate_sub_trace_le_mul_trace_of_hasLaw_gaussianMatrix`:
  relative error for positive semidefinite `A`, `P(|tr_m(A) − tr A| ≥ ε tr A) ≤ 2exp(−m ε²/(256e²))`,
  and the sample-size form `m ≥ 256e² ε⁻² log(2/δ)` (`…_of_le_card`).

Source: Avron–Toledo (2011) [`at11`], Thm 5.2; Cortinovis–Kressner (2021) [`ck21`], Thm 1 and
Thm 3 (sharper constants); Meyer–Musco–Musco–Woodruff (2021) [`mmmw21`], Lem. 2.
Atlas: `hutchinson-tail`; uses `hanson-wright`, `hutchinson-unbiased`.
Constants: the proved constant is the Hanson–Wright constant `1/(256 e²)` of `hanson_wright_mgf`
(sample size `256 e² ε⁻² log(2/δ)`); the source constants are `P ≤ 2exp(−m t²/(4‖A‖_F² + 4t‖A‖))`
(CK21 Thm 1) and `m ≥ 8 ε⁻² log(2/δ)` (CK21 Cor. 1). Constants are not improved in this round.
-/

noncomputable section

open scoped Matrix
open MeasureTheory ProbabilityTheory Real

namespace NLAlib

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ]

/-! ### Definitions and the block matrix -/

/-- The `m`-sample Hutchinson estimator `(1/m) ∑ₖ zₖᵀ A zₖ`, with the samples `zₖ` the columns of
the test matrix `Z : Matrix n κ ℝ` and `m = |κ|`. Source: Hutchinson (1989) [`hutch89`];
Avron–Toledo (2011) [`at11`], §2.
atlas: trace-estimators-def -/
def hutchinsonEstimate (A : Matrix n n ℝ) (Z : Matrix n κ ℝ) : ℝ :=
  (∑ k, quadForm A (fun i => Z i k)) / Fintype.card κ

/-- The block-diagonal matrix `(1/m) diag(A, …, A)` on `n × κ` whose quadratic form at
`vec(Z)` is the Hutchinson estimator. Atlas: `hutchinson-tail` (helper). -/
def hutchinsonBlock (A : Matrix n n ℝ) : Matrix (n × κ) (n × κ) ℝ :=
  (Fintype.card κ : ℝ)⁻¹ • Matrix.blockDiagonal (fun _ : κ => A)

omit [DecidableEq n] in
/-- The quadratic form of the block matrix at `vec(Z)` is the Hutchinson estimator.
Atlas: `hutchinson-tail` (helper). -/
theorem quadForm_hutchinsonBlock (A : Matrix n n ℝ) (Z : Matrix n κ ℝ) :
    quadForm (hutchinsonBlock (κ := κ) A) (fun e => Z e.1 e.2) = hutchinsonEstimate A Z := by
  have h : ∀ (i : n) (k : κ) (j : n), ∑ l : κ,
      (Fintype.card κ : ℝ)⁻¹ * (if k = l then A i j else 0) * (Z i k * Z j l) =
        (Fintype.card κ : ℝ)⁻¹ * (A i j * (Z i k * Z j k)) := fun i k j => by
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
    simp only [if_true]; ring
  rw [quadForm_eq_sum, hutchinsonEstimate, div_eq_inv_mul]
  simp only [hutchinsonBlock, Matrix.smul_apply, Matrix.blockDiagonal_apply, smul_eq_mul,
    Fintype.sum_prod_type, quadForm_eq_sum, star_trivial, h]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_comm]

omit [DecidableEq n] in
/-- `‖B‖_F² = ‖A‖_F² / m` for the Hutchinson block matrix. Atlas: `hutchinson-tail` (helper). -/
theorem frobSq_hutchinsonBlock [Nonempty κ] (A : Matrix n n ℝ) :
    frobSq (hutchinsonBlock (κ := κ) A) = frobSq A / Fintype.card κ := by
  have hm : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h : ∀ (i : n) (k : κ) (j : n), ∑ l : κ, (if k = l then A i j else 0) ^ 2 = A i j ^ 2 :=
    fun i k j => by
      rw [Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
      simp
  rw [hutchinsonBlock, frobSq_smul, frobSq_eq_sum_sq, frobSq_eq_sum_sq]
  simp only [Fintype.sum_prod_type, Matrix.blockDiagonal_apply, h, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  field_simp

open scoped Matrix.Norms.L2Operator in
/-- `‖B‖₂ ≤ ‖A‖₂ / m` for the Hutchinson block matrix. Atlas: `hutchinson-tail` (helper). -/
theorem specNorm_hutchinsonBlock_le (A : Matrix n n ℝ) :
    specNorm (hutchinsonBlock (κ := κ) A) ≤ specNorm A / Fintype.card κ := by
  rw [hutchinsonBlock, specNorm_eq_norm, norm_smul, ← specNorm_eq_norm, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (specNorm_blockDiagonal_const_le A)
    (inv_nonneg.2 (Nat.cast_nonneg _))

omit [DecidableEq n] in
/-- `tr B = tr A` for the Hutchinson block matrix. Atlas: `hutchinson-tail` (helper). -/
theorem trace_hutchinsonBlock [Nonempty κ] (A : Matrix n n ℝ) :
    (hutchinsonBlock (κ := κ) A).trace = A.trace := by
  have hm : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [hutchinsonBlock, Matrix.trace_smul, Matrix.trace_blockDiagonal]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  field_simp

omit [Fintype n] [DecidableEq n] in
/-- The Hutchinson block matrix vanishes only for `A = 0`. -/
private lemma hutchinsonBlock_ne_zero [Nonempty κ] {A : Matrix n n ℝ} (hA : A ≠ 0) :
    hutchinsonBlock (κ := κ) A ≠ 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (Matrix.ext h)
  obtain ⟨k⟩ := ‹Nonempty κ›
  have hm : (Fintype.card κ : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  intro h0
  have := congrFun (congrFun h0 (i, k)) (j, k)
  simp [hutchinsonBlock, Matrix.blockDiagonal_apply, hij, hm] at this

/-! ### Entry laws of a standard Gaussian test matrix -/

omit [DecidableEq n] [DecidableEq κ] in
/-- Flattening a standard Gaussian matrix gives a standard Gaussian vector on `n × κ`.
Helper for `hutchinson-tail`. -/
theorem hasLaw_uncurry_gaussianMatrix :
    HasLaw (fun G : Matrix n κ ℝ => fun e : n × κ => G e.1 e.2) (gaussianVector (n × κ))
      (gaussianMatrix n κ) :=
  ⟨(measurable_pi_lambda (fun (G : Matrix n κ ℝ) (e : n × κ) => G e.1 e.2)
      fun e => Matrix.measurable_entry e.1 e.2).aemeasurable,
    gaussianMatrix_map_uncurry⟩

/-! ### The tail bound -/

section Tail

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

open scoped Matrix.Norms.L2Operator in
/-- **Hutchinson tail bound, sub-Gaussian entries.** If the entries `Z(i, k)` of the test
matrix are independent and sub-Gaussian with variance proxy `K²`, then for `m = |κ| ≥ 1` and
`t ≥ 0`,
`P(|tr_m(A) − 𝔼 tr_m(A)| ≥ t) ≤ 2 exp(−(1/(256e²)) min(m t²/(K⁴‖A‖_F²), m t/(K²‖A‖)))`.
Source: Avron–Toledo (2011) [`at11`], Thm 5.2; Cortinovis–Kressner (2021) [`ck21`], Thm 3;
Vershynin (2018), Thm 6.2.1 applied to `diag(A, …, A)/m`. Atlas: `hutchinson-tail`; uses
`hanson-wright`. Deviation: Hanson–Wright constant `1/(256 e²)`; any matrix `A` (not only
symmetric); the centring is the true mean (equal to `tr A` for isotropic entries, see the
Gaussian and Rademacher corollaries). -/
theorem measureReal_le_abs_hutchinsonEstimate_sub_integral_le [Nonempty κ] (A : Matrix n n ℝ)
    {Z : Ω → Matrix n κ ℝ} (K : ℝ) (hK : 0 < K)
    (hind : iIndepFun (fun (e : n × κ) ω => Z ω e.1 e.2) μ)
    (hmgf : ∀ e : n × κ, HasSubgaussianMGF (fun ω => Z ω e.1 e.2) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |hutchinsonEstimate A (Z ω) - ∫ ω', hutchinsonEstimate A (Z ω') ∂μ|} ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (Fintype.card κ * t ^ 2 / (K ^ 4 * frobNorm A ^ 2))
          (Fintype.card κ * t / (K ^ 2 * specNorm A))) := by
  set m : ℝ := (Fintype.card κ : ℝ) with hmdef
  have hm : 0 < m := Nat.cast_pos.2 Fintype.card_pos
  by_cases hA0 : A = 0
  · subst hA0
    have h1 : μ.real {ω | t ≤ |hutchinsonEstimate (0 : Matrix n n ℝ) (Z ω) -
        ∫ ω', hutchinsonEstimate (0 : Matrix n n ℝ) (Z ω') ∂μ|} ≤ 1 := measureReal_le_one
    have hF : frobNorm (0 : Matrix n n ℝ) = 0 := by
      rw [frobNorm_eq_zero_iff]
    have hS : specNorm (0 : Matrix n n ℝ) = 0 := specNorm_zero
    simp only [hF, hS]
    norm_num
    exact h1.trans (by norm_num)
  have h := hanson_wright_mgf (hutchinsonBlock (κ := κ) A) (fun (e : n × κ) ω => Z ω e.1 e.2) K hK
    hind hmgf t ht
  simp only [quadForm_hutchinsonBlock] at h
  refine h.trans ?_
  gcongr 2 * exp ?_
  rw [neg_mul, neg_mul, neg_le_neg_iff]
  refine mul_le_mul_of_nonneg_left (min_le_min (le_of_eq ?_) ?_) (by positivity)
  · rw [frobNorm_sq, frobNorm_sq, frobSq_hutchinsonBlock, ← hmdef, mul_div_assoc',
      div_div_eq_mul_div, mul_comm m]
  · have hB : 0 < specNorm (hutchinsonBlock (κ := κ) A) := by
      simpa only [specNorm_eq_norm] using norm_pos_iff.mpr (hutchinsonBlock_ne_zero hA0)
    have hle := specNorm_hutchinsonBlock_le (κ := κ) A
    rw [← hmdef] at hle
    calc m * t / (K ^ 2 * specNorm A) = t / (K ^ 2 * (specNorm A / m)) := by
          field_simp
      _ ≤ t / (K ^ 2 * specNorm (hutchinsonBlock (κ := κ) A)) :=
          div_le_div_of_nonneg_left ht (by positivity)
            (mul_le_mul_of_nonneg_left hle (by positivity))

private lemma nnreal_one_sq : (⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ : NNReal) = 1 := by ext; simp

/-- **Hutchinson tail bound, Gaussian test matrix.** If `Z` is a standard Gaussian `n × κ`
matrix (`HasLaw Z (gaussianMatrix n κ) μ`), then for `m = |κ| ≥ 1` and `t ≥ 0`,
`P(|tr_m(A) − tr A| ≥ t) ≤ 2 exp(−(1/(256e²)) min(m t²/‖A‖_F², m t/‖A‖))`.
Source: Avron–Toledo (2011) [`at11`], Thm 5.2; Cortinovis–Kressner (2021) [`ck21`], Thm 1.
Atlas: `hutchinson-tail`; uses `hanson-wright`, `hutchinson-unbiased`. Constants: proved
`1/(256 e²)` (CK21 Thm 1: `P ≤ 2exp(−m t²/(4‖A‖_F² + 4t‖A‖))`); any matrix `A`.
atlas: hutchinson-tail -/
theorem measureReal_le_abs_hutchinsonEstimate_sub_trace_le_of_hasLaw_gaussianMatrix [Nonempty κ]
    (A : Matrix n n ℝ) {Z : Ω → Matrix n κ ℝ} (hZ : HasLaw Z (gaussianMatrix n κ) μ) (t : ℝ)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |hutchinsonEstimate A (Z ω) - A.trace|} ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (Fintype.card κ * t ^ 2 / frobNorm A ^ 2) (Fintype.card κ * t / specNorm A)) := by
  have hflat : HasLaw (fun ω (e : n × κ) => Z ω e.1 e.2) (gaussianVector (n × κ)) μ :=
    hasLaw_uncurry_gaussianMatrix.comp hZ
  have hind : iIndepFun (fun (e : n × κ) ω => Z ω e.1 e.2) μ :=
    hflat.iIndepFun_eval_of_gaussianVector
  have hlaw : ∀ e : n × κ, HasLaw (fun ω => Z ω e.1 e.2) (gaussianReal 0 1) μ := fun e =>
    hflat.hasLaw_eval_gaussianReal e
  have hmean : ∫ ω, hutchinsonEstimate A (Z ω) ∂μ = A.trace := by
    simp_rw [← quadForm_hutchinsonBlock]
    rw [integral_quadForm_eq_trace_of_hasLaw_gaussianVector _ hflat, trace_hutchinsonBlock]
  have h := measureReal_le_abs_hutchinsonEstimate_sub_integral_le A 1 one_pos hind
    (fun e => by rw [nnreal_one_sq]; exact hasSubgaussianMGF_of_hasLaw_gaussianReal (hlaw e)) t ht
  simpa [hmean] using h

/-- **Hutchinson tail bound, Rademacher test matrix.** If the entries of `Z` are independent
Rademacher signs (`HasLaw (fun ω e => Z ω e.1 e.2) (rademacherVector (n × κ)) μ`), then for
`m = |κ| ≥ 1` and `t ≥ 0`,
`P(|tr_m(A) − tr A| ≥ t) ≤ 2 exp(−(1/(256e²)) min(m t²/‖A‖_F², m t/‖A‖))`.
Source: Avron–Toledo (2011) [`at11`], Thm 5.2 (Rademacher case); Cortinovis–Kressner (2021)
[`ck21`], Thm 3. Atlas: `hutchinson-tail`; uses `hanson-wright`, `hutchinson-unbiased`,
`rademacher-khintchine`. Constants: proved `1/(256 e²)`; any matrix `A`.
atlas: hutchinson-tail -/
theorem measureReal_le_abs_hutchinsonEstimate_sub_trace_le_of_hasLaw_rademacherVector
    [Nonempty κ] (A : Matrix n n ℝ) {Z : Ω → Matrix n κ ℝ}
    (hZ : HasLaw (fun ω (e : n × κ) => Z ω e.1 e.2) (rademacherVector (n × κ)) μ) (t : ℝ)
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |hutchinsonEstimate A (Z ω) - A.trace|} ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (Fintype.card κ * t ^ 2 / frobNorm A ^ 2) (Fintype.card κ * t / specNorm A)) := by
  have hind : iIndepFun (fun (e : n × κ) ω => Z ω e.1 e.2) μ :=
    hZ.iIndepFun_eval_of_rademacherVector
  have hlaw : ∀ e : n × κ, HasLaw (fun ω => Z ω e.1 e.2) rademacherMeasure μ := fun e =>
    hZ.hasLaw_eval_rademacherMeasure e
  have hmean : ∫ ω, hutchinsonEstimate A (Z ω) ∂μ = A.trace := by
    simp_rw [← quadForm_hutchinsonBlock]
    rw [integral_quadForm_eq_trace_of_hasLaw_rademacherVector _ hZ, trace_hutchinsonBlock]
  have h := measureReal_le_abs_hutchinsonEstimate_sub_integral_le A 1 one_pos hind
    (fun e => by
      rw [nnreal_one_sq]; exact hasSubgaussianMGF_of_hasLaw_rademacherMeasure (hlaw e)) t ht
  simpa [hmean] using h

end Tail

/-! ### Relative error for positive semidefinite matrices -/

section Relative

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq κ] in
open scoped Matrix.Norms.L2Operator in
/-- The Hanson–Wright exponent at `t = ε tr A` is at least `m ε²` for positive semidefinite
`A` with positive trace and `0 < ε ≤ 1`.
Source: Cortinovis–Kressner (2021), proof of Corollary 1; helper for `hutchinson-tail`
and the relative-error stochastic Lanczos quadrature bound `slq-error`. -/
theorem mul_sq_le_min_hutchinson_exponent_of_posSemidef [Nonempty κ]
    {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (htr : 0 < A.trace) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Fintype.card κ * ε ^ 2 ≤ min (Fintype.card κ * (ε * A.trace) ^ 2 / frobNorm A ^ 2)
      (Fintype.card κ * (ε * A.trace) / specNorm A) := by
  have hm : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  have hA0 : A ≠ 0 := by rintro rfl; simp at htr
  have hF : 0 < frobNorm A := lt_of_le_of_ne (frobNorm_nonneg A)
    (Ne.symm fun h => hA0 ((frobNorm_eq_zero_iff A).1 h))
  have hS : 0 < specNorm A := by
    simpa only [specNorm_eq_norm] using norm_pos_iff.mpr hA0
  have hFt := frobNorm_le_trace_of_posSemidef hA
  have hSt := specNorm_le_trace_of_posSemidef hA
  refine le_min ?_ ?_
  · rw [le_div_iff₀ (by positivity)]
    have : frobNorm A ^ 2 ≤ A.trace ^ 2 := pow_le_pow_left₀ hF.le hFt 2
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ Fintype.card κ * ε ^ 2)]
  · rw [le_div_iff₀ hS]
    have h1 : ε ^ 2 ≤ ε := by nlinarith
    have h2 : Fintype.card κ * ε ^ 2 * specNorm A ≤ Fintype.card κ * ε * A.trace := by
      have := mul_le_mul h1 hSt hS.le hε.le
      nlinarith
    linarith

/-- **Hutchinson relative-error tail, PSD `A`, Gaussian test matrix.** For positive
semidefinite `A` with `tr A > 0`, `0 < ε ≤ 1`, and a standard Gaussian `n × κ` test matrix
(`m = |κ|`), `P(|tr_m(A) − tr A| ≥ ε tr A) ≤ 2 exp(−m ε²/(256 e²))`.
Source: Cortinovis–Kressner (2021) [`ck21`], Cor. 1; Meyer–Musco–Musco–Woodruff (2021)
[`mmmw21`], Lem. 2. Atlas: `hutchinson-tail`; uses `hanson-wright`, `hutchinson-unbiased`.
Constants: proved `1/(256 e²)` (CK21: `exp(−m ε²/8)`, roughly).
atlas: hutchinson-tail -/
theorem measureReal_le_abs_hutchinsonEstimate_sub_trace_le_mul_trace_of_hasLaw_gaussianMatrix
    [Nonempty κ] {A : Matrix n n ℝ} (hA : A.PosSemidef) (htr : 0 < A.trace)
    {Z : Ω → Matrix n κ ℝ} (hZ : HasLaw Z (gaussianMatrix n κ) μ) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    μ.real {ω | ε * A.trace ≤ |hutchinsonEstimate A (Z ω) - A.trace|} ≤
      2 * exp (-(Fintype.card κ * ε ^ 2 / (256 * exp 1 ^ 2))) := by
  refine (measureReal_le_abs_hutchinsonEstimate_sub_trace_le_of_hasLaw_gaussianMatrix A hZ
    (ε * A.trace) (by positivity)).trans ?_
  gcongr 2 * exp ?_
  have h := mul_sq_le_min_hutchinson_exponent_of_posSemidef (κ := κ) hA htr hε hε1
  have hc : (0 : ℝ) ≤ 1 / (256 * exp 1 ^ 2) := by positivity
  have := mul_le_mul_of_nonneg_left h hc
  rw [neg_mul, neg_le_neg_iff]
  calc Fintype.card κ * ε ^ 2 / (256 * exp 1 ^ 2) = 1 / (256 * exp 1 ^ 2) *
        (Fintype.card κ * ε ^ 2) := by ring
    _ ≤ _ := this

/-- **Hutchinson sample size, PSD `A`, Gaussian test matrix.** If `A` is positive semidefinite
with `tr A > 0`, `0 < ε ≤ 1`, `0 < δ`, and `m ≥ 256 e² ε⁻² log(2/δ)`, then
`P(|tr_m(A) − tr A| ≥ ε tr A) ≤ δ`.
Source: Cortinovis–Kressner (2021) [`ck21`], Cor. 1; Meyer–Musco–Musco–Woodruff (2021)
[`mmmw21`], Lem. 2. Atlas: `hutchinson-tail`. Constants: proved `256 e²` (CK21:
`m ≥ 8 ε⁻² log(2/δ)`).
atlas: hutchinson-tail -/
theorem measureReal_le_abs_hutchinsonEstimate_sub_trace_le_of_le_card [Nonempty κ]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (htr : 0 < A.trace) {Z : Ω → Matrix n κ ℝ}
    (hZ : HasLaw Z (gaussianMatrix n κ) μ) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hm : 256 * exp 1 ^ 2 * Real.log (2 / δ) / ε ^ 2 ≤ Fintype.card κ) :
    μ.real {ω | ε * A.trace ≤ |hutchinsonEstimate A (Z ω) - A.trace|} ≤ δ := by
  refine (measureReal_le_abs_hutchinsonEstimate_sub_trace_le_mul_trace_of_hasLaw_gaussianMatrix
    hA htr hZ hε hε1).trans ?_
  have hlog : Real.log (2 / δ) ≤ Fintype.card κ * ε ^ 2 / (256 * exp 1 ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hm
    linarith
  calc 2 * exp (-(Fintype.card κ * ε ^ 2 / (256 * exp 1 ^ 2)))
      ≤ 2 * exp (-Real.log (2 / δ)) := by gcongr
    _ = δ := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp

end Relative

end NLAlib
