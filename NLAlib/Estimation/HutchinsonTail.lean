import Mathlib.Data.Matrix.Block
import NLAlib.Concentration.HansonWright
import NLAlib.Concentration.Scalar.Rademacher
import NLAlib.Estimation.HutchinsonLaws
import NLAlib.Krylov.GaussQuadrature
import NLAlib.Matrix.QuadraticProbe
import Mathlib.Analysis.Matrix.PosDef

/-!
# Tail bound for Hutchinson's trace estimator

The `m`-sample Hutchinson estimator `tr_m(A) = (1/m) ∑ₖ zₖᵀ A zₖ` (`NLAlib.hutchinsonEstimate`,
samples indexed by any finite type `κ` with `m = |κ|`) is a single quadratic form
`vec(Z)ᵀ B vec(Z)` in the `n·m` independent entries of `Z`, with the block-diagonal
`B = (1/m) diag(A, …, A)` (`NLAlib.hutchinsonBlock`). Since `‖B‖_F² = ‖A‖_F²/m` and
`‖B‖ ≤ ‖A‖/m`, the proved Hanson–Wright inequality (`NLAlib.hanson_wright_mgf`) gives

`P(|tr_m(A) − 𝔼 tr_m(A)| ≥ t) ≤ 2 exp(−(1/(256e²)) min(m t²/(K⁴‖A‖_F²), m t/(K²‖A‖)))`

for sub-Gaussian entries with variance proxy `K²`, and with `𝔼 tr_m(A) = tr A`, `K = 1` for
standard Gaussian and Rademacher test vectors.

## Main results

* `NLAlib.measure_le_abs_hutchinsonEstimate_sub_integral_le`: general sub-Gaussian entries.
* `NLAlib.measure_le_abs_hutchinsonEstimate_sub_trace_le_of_standardGaussian`: Gaussian.
* `NLAlib.measure_le_abs_hutchinsonEstimate_sub_trace_le_of_rademacher`: Rademacher.
* `NLAlib.measure_le_abs_hutchinsonEstimate_sub_trace_le_mul_trace_of_standardGaussian`: relative
  error for positive semidefinite `A`, `P(|tr_m(A) − tr A| ≥ ε tr A) ≤ 2exp(−m ε²/(256e²))`, and
  the sample-size form `m ≥ 256e² ε⁻² log(2/δ)` (`…_le_of_le_card`).

Source: Avron–Toledo (2011) [`at11`], Thm 5.2; Cortinovis–Kressner (2021) [`ck21`], Thm 1 and
Thm 3 (sharper constants); Meyer–Musco–Musco–Woodruff (2021) [`mmmw21`], Lem. 2.
Atlas: `hutchinson-tail`; uses `hanson-wright`, `hutchinson-unbiased`.
Deviation: the constant is the Hanson–Wright constant `1/(256 e²)` of `hanson_wright_mgf`, not
the printed ones; constants are explicit (the atlas conclusion is stated with `O(·)`).
-/

noncomputable section

open scoped Matrix
open MeasureTheory ProbabilityTheory Real
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ]

/-! ### Definitions and the block matrix -/

/-- The `m`-sample Hutchinson estimator `(1/m) ∑ₖ zₖᵀ A zₖ`, with the samples `zₖ = Z(·, k)` the
columns of `Z : n → κ → ℝ` and `m = |κ|`. Source: Hutchinson (1989) [`hutch89`];
Avron–Toledo (2011) [`at11`], §2. Atlas: `hutchinson-tail`, `hutchinson-unbiased`.
atlas: trace-estimators-def -/
def hutchinsonEstimate (A : Matrix n n ℝ) (Z : n → κ → ℝ) : ℝ :=
  (∑ k, quadForm A (fun i => Z i k)) / Fintype.card κ

/-- The block-diagonal matrix `(1/m) diag(A, …, A)` on `n × κ` whose quadratic form at
`vec(Z)` is the Hutchinson estimator. Atlas: `hutchinson-tail` (helper).
atlas: trace-estimators-def -/
def hutchinsonBlock (κ : Type*) [Fintype κ] [DecidableEq κ] (A : Matrix n n ℝ) :
    Matrix (n × κ) (n × κ) ℝ :=
  (Fintype.card κ : ℝ)⁻¹ • Matrix.blockDiagonal (fun _ : κ => A)

omit [DecidableEq n] in
/-- The quadratic form of the block matrix at `vec(Z)` is the Hutchinson estimator.
Atlas: `hutchinson-tail` (helper). -/
theorem quadForm_hutchinsonBlock (A : Matrix n n ℝ) (Z : n → κ → ℝ) :
    quadForm (hutchinsonBlock κ A) (fun e => Z e.1 e.2) = hutchinsonEstimate A Z := by
  have h : ∀ (i : n) (k : κ) (j : n), ∑ l : κ,
      (Fintype.card κ : ℝ)⁻¹ * (if k = l then A i j else 0) * (Z i k * Z j l) =
        (Fintype.card κ : ℝ)⁻¹ * (A i j * (Z i k * Z j k)) := fun i k j => by
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
    simp only [if_true]; ring
  rw [quadForm_eq_sum, hutchinsonEstimate, div_eq_inv_mul]
  simp only [hutchinsonBlock, Matrix.smul_apply, Matrix.blockDiagonal_apply, smul_eq_mul,
    Fintype.sum_prod_type, quadForm_eq_sum, h]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_comm]

omit [DecidableEq n] in
/-- `‖B‖_F² = ‖A‖_F² / m` for the Hutchinson block matrix. Atlas: `hutchinson-tail` (helper). -/
theorem frobSq_hutchinsonBlock [Nonempty κ] (A : Matrix n n ℝ) :
    frobSq (hutchinsonBlock κ A) = frobSq A / Fintype.card κ := by
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

/-- A spectral-norm bound from a bound on `‖Ax‖²`: if `0 ≤ C` and `∑ᵢ (Ax)ᵢ² ≤ C² ∑ⱼ xⱼ²` for
every `x`, then `‖A‖₂ ≤ C`. Atlas: `norms-frob-spec` (helper; belongs in `NLAlib.Matrix.Norms`). -/
theorem specNorm_le_of_forall_sum_sq_mulVec_le {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] (A : Matrix m p ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : p → ℝ, ∑ i, (A *ᵥ x) i ^ 2 ≤ C ^ 2 * ∑ j, x j ^ 2) : specNorm A ≤ C := by
  unfold specNorm
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  have h := h x.ofLp
  have hx : ∑ j, x.ofLp j ^ 2 = ‖x‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq x).symm
  have hy : ‖(Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A x‖ ^ 2 =
      ∑ i, (A *ᵥ x.ofLp) i ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; rfl
  rw [hx, ← mul_pow, ← hy] at h
  exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hC (norm_nonneg x)) h

/-- `‖diag(A, …, A)‖₂ ≤ ‖A‖₂`. Atlas: `hutchinson-tail` (helper). -/
theorem specNorm_blockDiagonal_const_le (A : Matrix n n ℝ) :
    specNorm (Matrix.blockDiagonal (fun _ : κ => A)) ≤ specNorm A := by
  refine specNorm_le_of_forall_sum_sq_mulVec_le _ (specNorm_nonneg A) fun x => ?_
  have hD : ∀ i k, (Matrix.blockDiagonal (fun _ : κ => A) *ᵥ x) (i, k) =
      (A *ᵥ fun j => x (j, k)) i := fun i k => by
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single k
      (fun l _ hl => by simp [Matrix.blockDiagonal_apply, Ne.symm hl]) (by simp)]
    simp [Matrix.blockDiagonal_apply]
  simp only [Fintype.sum_prod_type, hD]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun j k => x (j, k) ^ 2), Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => sum_sq_mulVec_le_specNorm_sq A _

/-- `‖B‖₂ ≤ ‖A‖₂ / m` for the Hutchinson block matrix. Atlas: `hutchinson-tail` (helper). -/
theorem specNorm_hutchinsonBlock_le (A : Matrix n n ℝ) :
    specNorm (hutchinsonBlock κ A) ≤ specNorm A / Fintype.card κ := by
  rw [hutchinsonBlock, specNorm_eq_norm, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (specNorm_blockDiagonal_const_le A)
    (inv_nonneg.2 (Nat.cast_nonneg _))

omit [DecidableEq n] in
/-- `tr B = tr A` for the Hutchinson block matrix. Atlas: `hutchinson-tail` (helper). -/
theorem trace_hutchinsonBlock [Nonempty κ] (A : Matrix n n ℝ) :
    (hutchinsonBlock κ A).trace = A.trace := by
  have hm : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [hutchinsonBlock, Matrix.trace_smul, Matrix.trace_blockDiagonal]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  field_simp

omit [Fintype n] [DecidableEq n] in
/-- The Hutchinson block matrix vanishes only for `A = 0`. -/
private lemma hutchinsonBlock_ne_zero [Nonempty κ] {A : Matrix n n ℝ} (hA : A ≠ 0) :
    hutchinsonBlock κ A ≠ 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (Matrix.ext h)
  obtain ⟨k⟩ := ‹Nonempty κ›
  have hm : (Fintype.card κ : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  intro h0
  have := congrFun (congrFun h0 (i, k)) (j, k)
  simp [hutchinsonBlock, Matrix.blockDiagonal_apply, hij, hm] at this

/-! ### The tail bound -/

section Tail

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Hutchinson tail bound, sub-Gaussian entries.** If the entries `Z(i, k)` of the test
matrix are independent and sub-Gaussian with variance proxy `K²`, then for `m = |κ| ≥ 1` and
`t ≥ 0`,
`P(|tr_m(A) − 𝔼 tr_m(A)| ≥ t) ≤ 2 exp(−(1/(256e²)) min(m t²/(K⁴‖A‖_F²), m t/(K²‖A‖)))`.
Source: Avron–Toledo (2011) [`at11`], Thm 5.2; Cortinovis–Kressner (2021) [`ck21`], Thm 3;
Vershynin (2018), Thm 6.2.1 applied to `diag(A, …, A)/m`. Atlas: `hutchinson-tail`; uses
`hanson-wright`. Deviation: Hanson–Wright constant `1/(256 e²)`; any matrix `A` (not only
symmetric); the centring is the true mean (equal to `tr A` for isotropic entries, see the
Gaussian and Rademacher corollaries). -/
theorem measure_le_abs_hutchinsonEstimate_sub_integral_le [Nonempty κ] (A : Matrix n n ℝ)
    {Z : Ω → n → κ → ℝ} (K : ℝ) (hK : 0 < K)
    (hind : iIndepFun (fun (e : n × κ) ω => Z ω e.1 e.2) μ)
    (hmgf : ∀ e : n × κ, HasSubgaussianMGF (fun ω => Z ω e.1 e.2) ⟨K ^ 2, sq_nonneg K⟩ μ)
    (t : ℝ) (ht : 0 ≤ t) :
    (μ {ω | t ≤ |hutchinsonEstimate A (Z ω) - ∫ ω', hutchinsonEstimate A (Z ω') ∂μ|}).toReal ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (Fintype.card κ * t ^ 2 / (K ^ 4 * frobNorm A ^ 2))
          (Fintype.card κ * t / (K ^ 2 * specNorm A))) := by
  set m : ℝ := (Fintype.card κ : ℝ) with hmdef
  have hm : 0 < m := Nat.cast_pos.2 Fintype.card_pos
  by_cases hA0 : A = 0
  · subst hA0
    have h1 : (μ {ω | t ≤ |hutchinsonEstimate (0 : Matrix n n ℝ) (Z ω) -
        ∫ ω', hutchinsonEstimate (0 : Matrix n n ℝ) (Z ω') ∂μ|}).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have hF : frobNorm (0 : Matrix n n ℝ) = 0 := by
      rw [frobNorm_eq_zero_iff]
    have hS : specNorm (0 : Matrix n n ℝ) = 0 := by rw [specNorm_eq_norm, norm_zero]
    simp only [hF, hS]
    norm_num
    exact h1.trans (by norm_num)
  have h := hanson_wright_mgf (hutchinsonBlock κ A) (fun (e : n × κ) ω => Z ω e.1 e.2) K hK
    hind hmgf t ht
  simp only [quadForm_hutchinsonBlock] at h
  refine h.trans ?_
  gcongr 2 * exp ?_
  rw [neg_mul, neg_mul, neg_le_neg_iff]
  refine mul_le_mul_of_nonneg_left (min_le_min (le_of_eq ?_) ?_) (by positivity)
  · rw [frobNorm_sq, frobNorm_sq, frobSq_hutchinsonBlock, ← hmdef, mul_div_assoc',
      div_div_eq_mul_div, mul_comm m]
  · have hB : 0 < specNorm (hutchinsonBlock κ A) := by
      rw [specNorm_eq_norm]; exact norm_pos_iff.2 (hutchinsonBlock_ne_zero hA0)
    have hle := specNorm_hutchinsonBlock_le (κ := κ) A
    rw [← hmdef] at hle
    calc m * t / (K ^ 2 * specNorm A) = t / (K ^ 2 * (specNorm A / m)) := by
          field_simp
      _ ≤ t / (K ^ 2 * specNorm (hutchinsonBlock κ A)) :=
          div_le_div_of_nonneg_left ht (by positivity)
            (mul_le_mul_of_nonneg_left hle (by positivity))

omit [IsProbabilityMeasure μ] in
/-- A standard Gaussian variable is sub-Gaussian with variance proxy `1`.
Source: Vershynin (2018), Example 2.5.8(i). Atlas: `hutchinson-tail` (helper; belongs in
`NLAlib.Concentration.Scalar.SubGaussian`). -/
theorem hasSubgaussianMGF_of_isStandardGaussian {g : Ω → ℝ} (hg : IsStandardGaussian μ g) :
    HasSubgaussianMGF g 1 μ := by
  have hm : AEMeasurable g μ := aemeasurable_of_isStandardGaussian hg
  rw [← HasSubgaussianMGF.id_map_iff hm, show μ.map g = gaussianReal 0 1 from hg]
  exact HansonWrightProof.hasSubgaussianMGF_id_gaussianReal_zero_one

private lemma nnreal_one_sq : (⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ : NNReal) = 1 := by ext; simp

/-- **Hutchinson tail bound, Gaussian test vectors.** If the entries of `Z : n → κ → ℝ` are
independent standard Gaussians, then for `m = |κ| ≥ 1` and `t ≥ 0`,
`P(|tr_m(A) − tr A| ≥ t) ≤ 2 exp(−(1/(256e²)) min(m t²/‖A‖_F², m t/‖A‖))`.
Source: Avron–Toledo (2011) [`at11`], Thm 5.2; Cortinovis–Kressner (2021) [`ck21`], Thm 1.
Atlas: `hutchinson-tail`; uses `hanson-wright`, `hutchinson-unbiased`. Deviation: constant
`1/(256 e²)` (CK21: `P ≤ 2exp(−m t²/(4‖A‖_F² + 4t‖A‖))`); any matrix `A`.
atlas: hutchinson-tail -/
theorem measure_le_abs_hutchinsonEstimate_sub_trace_le_of_standardGaussian [Nonempty κ]
    (A : Matrix n n ℝ) {Z : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => Z ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsStandardGaussian μ (fun ω => Z ω e.1 e.2)) (t : ℝ) (ht : 0 ≤ t) :
    (μ {ω | t ≤ |hutchinsonEstimate A (Z ω) - A.trace|}).toReal ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (Fintype.card κ * t ^ 2 / frobNorm A ^ 2) (Fintype.card κ * t / specNorm A)) := by
  have hmean : ∫ ω, hutchinsonEstimate A (Z ω) ∂μ = A.trace := by
    simp_rw [← quadForm_hutchinsonBlock]
    rw [integral_quadForm_eq_trace_of_standardGaussian _
      (fun e => aemeasurable_of_isStandardGaussian (hlaw e)) hind hlaw, trace_hutchinsonBlock]
  have h := measure_le_abs_hutchinsonEstimate_sub_integral_le A 1 one_pos hind
    (fun e => by rw [nnreal_one_sq]; exact hasSubgaussianMGF_of_isStandardGaussian (hlaw e)) t ht
  simpa [hmean] using h

/-- **Hutchinson tail bound, Rademacher test vectors.** If the entries of `Z : n → κ → ℝ` are
independent Rademacher signs, then for `m = |κ| ≥ 1` and `t ≥ 0`,
`P(|tr_m(A) − tr A| ≥ t) ≤ 2 exp(−(1/(256e²)) min(m t²/‖A‖_F², m t/‖A‖))`.
Source: Avron–Toledo (2011) [`at11`], Thm 5.2 (Rademacher case); Cortinovis–Kressner (2021)
[`ck21`], Thm 3. Atlas: `hutchinson-tail`; uses `hanson-wright`, `hutchinson-unbiased`,
`rademacher-khintchine`. Deviation: constant `1/(256 e²)`; any matrix `A`.
atlas: hutchinson-tail -/
theorem measure_le_abs_hutchinsonEstimate_sub_trace_le_of_rademacher [Nonempty κ]
    (A : Matrix n n ℝ) {Z : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => Z ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsRademacher μ (fun ω => Z ω e.1 e.2)) (t : ℝ) (ht : 0 ≤ t) :
    (μ {ω | t ≤ |hutchinsonEstimate A (Z ω) - A.trace|}).toReal ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (Fintype.card κ * t ^ 2 / frobNorm A ^ 2) (Fintype.card κ * t / specNorm A)) := by
  have hmean : ∫ ω, hutchinsonEstimate A (Z ω) ∂μ = A.trace := by
    simp_rw [← quadForm_hutchinsonBlock]
    rw [integral_quadForm_eq_trace_of_rademacher _
      (fun e => aemeasurable_of_isRademacher (hlaw e)) hind hlaw, trace_hutchinsonBlock]
  have h := measure_le_abs_hutchinsonEstimate_sub_integral_le A 1 one_pos hind
    (fun e => by rw [nnreal_one_sq]; exact hasSubgaussianMGF_of_isRademacher (hlaw e)) t ht
  simpa [hmean] using h

end Tail

/-! ### Relative error for positive semidefinite matrices -/

/-- `‖A‖_F² = ∑ᵢ λᵢ²` for symmetric `A`. Atlas: `hutchinson-tail` (helper; belongs in
`NLAlib.Matrix.PolynomialCalculus`). -/
theorem frobSq_eq_sum_eigenvalues_sq {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    frobSq A = ∑ i, hA.eigenvalues i ^ 2 := by
  have hcol : ∀ j, (A *ᵥ Pi.single j 1) ⬝ᵥ (A *ᵥ Pi.single j 1) =
      ∑ i, hA.eigenvalues i ^ 2 * (hA.eigenvectorBasis i : n → ℝ) j ^ 2 := fun j => by
    have h := dotProduct_aeval_mulVec_self_eq_sum hA Polynomial.X (Pi.single j 1)
    simpa using h
  have hF : frobSq A = ∑ j, (A *ᵥ Pi.single j 1) ⬝ᵥ (A *ᵥ Pi.single j 1) := by
    rw [frobSq_eq_sum_sq, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [dotProduct, sq]
  rw [hF]
  simp_rw [hcol]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum]
  have h1 : ∑ j, (hA.eigenvectorBasis i : n → ℝ) j ^ 2 = 1 := by
    simpa [dotProduct, sq] using eigenvectorBasis_dotProduct_self hA i
  rw [h1, mul_one]

/-- `‖A‖_F ≤ tr A` for positive semidefinite `A`. Source: Cortinovis–Kressner (2021) [`ck21`],
proof of Cor. 1; Meyer–Musco–Musco–Woodruff (2021) [`mmmw21`], Lem. 2. Atlas: `hutchinson-tail`
(helper; belongs in `NLAlib.Matrix`). -/
theorem frobNorm_le_trace_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    frobNorm A ≤ A.trace := by
  have hH := hA.isHermitian
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := hA.eigenvalues_nonneg
  have htr : A.trace = ∑ i, hH.eigenvalues i := by
    simpa using hH.trace_eq_sum_eigenvalues
  have htr0 : 0 ≤ A.trace := htr ▸ Finset.sum_nonneg fun i _ => hnn i
  rw [← abs_of_nonneg (frobNorm_nonneg A), ← abs_of_nonneg htr0, ← sq_le_sq, frobNorm_sq,
    frobSq_eq_sum_eigenvalues_sq hH, htr]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hnn i

section Relative

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq κ] in
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
  have hS : 0 < specNorm A := by rw [specNorm_eq_norm]; exact norm_pos_iff.2 hA0
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

/-- **Hutchinson relative-error tail, PSD `A`, Gaussian test vectors.** For positive
semidefinite `A` with `tr A > 0`, `0 < ε ≤ 1`, and `m = |κ|` independent standard Gaussian test
vectors, `P(|tr_m(A) − tr A| ≥ ε tr A) ≤ 2 exp(−m ε²/(256 e²))`.
Source: Cortinovis–Kressner (2021) [`ck21`], Cor. 1 (constant differs); Meyer–Musco–Musco–Woodruff
(2021) [`mmmw21`], Lem. 2. Atlas: `hutchinson-tail`; uses `hanson-wright`,
`hutchinson-unbiased`. Deviation: constant `1/(256 e²)`.
atlas: hutchinson-tail -/
theorem measure_le_abs_hutchinsonEstimate_sub_trace_le_mul_trace_of_standardGaussian [Nonempty κ]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (htr : 0 < A.trace) {Z : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => Z ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsStandardGaussian μ (fun ω => Z ω e.1 e.2)) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    (μ {ω | ε * A.trace ≤ |hutchinsonEstimate A (Z ω) - A.trace|}).toReal ≤
      2 * exp (-(Fintype.card κ * ε ^ 2 / (256 * exp 1 ^ 2))) := by
  refine (measure_le_abs_hutchinsonEstimate_sub_trace_le_of_standardGaussian A hind hlaw
    (ε * A.trace) (by positivity)).trans ?_
  gcongr 2 * exp ?_
  have h := mul_sq_le_min_hutchinson_exponent_of_posSemidef (κ := κ) hA htr hε hε1
  have hc : (0 : ℝ) ≤ 1 / (256 * exp 1 ^ 2) := by positivity
  have := mul_le_mul_of_nonneg_left h hc
  rw [neg_mul, neg_le_neg_iff]
  calc Fintype.card κ * ε ^ 2 / (256 * exp 1 ^ 2) = 1 / (256 * exp 1 ^ 2) *
        (Fintype.card κ * ε ^ 2) := by ring
    _ ≤ _ := this

/-- **Hutchinson sample size, PSD `A`, Gaussian test vectors.** If `A` is positive semidefinite
with `tr A > 0`, `0 < ε ≤ 1`, `0 < δ`, and `m ≥ 256 e² ε⁻² log(2/δ)`, then
`P(|tr_m(A) − tr A| ≥ ε tr A) ≤ δ`.
Source: Cortinovis–Kressner (2021) [`ck21`], Cor. 1 (`m ≥ 8ε⁻² log(2/δ)` with sharp constants);
Meyer–Musco–Musco–Woodruff (2021) [`mmmw21`], Lem. 2. Atlas: `hutchinson-tail`.
Deviation: constant `256 e²`.
atlas: hutchinson-tail -/
theorem measure_le_abs_hutchinsonEstimate_sub_trace_le_of_le_card [Nonempty κ]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (htr : 0 < A.trace) {Z : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => Z ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsStandardGaussian μ (fun ω => Z ω e.1 e.2)) {ε δ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hm : 256 * exp 1 ^ 2 * Real.log (2 / δ) / ε ^ 2 ≤ Fintype.card κ) :
    (μ {ω | ε * A.trace ≤ |hutchinsonEstimate A (Z ω) - A.trace|}).toReal ≤ δ := by
  refine (measure_le_abs_hutchinsonEstimate_sub_trace_le_mul_trace_of_standardGaussian hA htr
    hind hlaw hε hε1).trans ?_
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
