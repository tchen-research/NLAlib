import NLAlib.Estimation.Trace.HutchinsonTail
import NLAlib.Krylov.Quadrature.SpectralMeasure
import NLAlib.ForMathlib.Probability.Independence
import NLAlib.Matrix.Subspaces.OrthonormalBasisMatrix
/-!
# Deflated trace kernels and sketch-based estimator constructions

Hutch++ (Meyer–Musco–Musco–Woodruff 2021) and XTrace (Epperly–Tropp–Webber 2024) split
`tr A = tr(QᵀAQ) + tr((I − QQᵀ)A(I − QQᵀ))` for an orthonormal `Q` built from a sketch of `A`, and
estimate the second term by Hutchinson with test vectors independent of `Q`. Unbiasedness needs
only this split, Hutchinson unbiasedness for the fixed deflated matrix, and Fubini for
independent variables; no Gaussian law, exchangeability or low-rank error bound is used.

## Main results

* `NLAlib.trace_eq_trace_mul_mul_add_trace_sub_mul_mul_sub`: `tr A = tr(PAP) + tr((I−P)A(I−P))`
  for idempotent `P`; `NLAlib.trace_eq_trace_transpose_mul_mul_add`: the `P = QQᵀ` form.
* `NLAlib.integral_hutchinsonEstimate_eq_trace`: multi-sample Hutchinson is unbiased for
  test matrices with isotropic columns.
* `NLAlib.integral_deflatedTraceEstimate_eq_trace`: independent deflation is unbiased for a fixed `Q`.
* `NLAlib.integral_comp_of_indepFun_of_forall_integral_eq`: Fubini step for independent inputs.
* `NLAlib.integral_deflatedTraceEstimate_comp_eq_trace`: independent deflation is unbiased for a random `Q`
  independent of the Hutchinson test matrix.
* `NLAlib.integral_leaveOneOutDeflatedTraceEstimate_eq_trace`: the supplied leave-one-out deflation kernel is unbiased.
* `NLAlib.integral_integral_spectralMeasure_eq_trace`: `𝔼_z ∫ f dμ_z = tr f(A)` (the Hutchinson
  clause of `spectral-measure`).

Atlas: `hutchpp-unbiased` (new), `xtrace-unbiased`, `spectral-measure` (expectation clause);
uses `hutchinson-unbiased`, `gaussian-conditioning`.
-/

noncomputable section

open scoped Matrix
open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The trace split -/

/-- **Trace split by an idempotent.** If `P² = P` then
`tr A = tr(P A P) + tr((I − P) A (I − P))`. Source: Meyer–Musco–Musco–Woodruff (2021)
[`mmmw21`], eq. (3) (with `P = QQᵀ`). Atlas: `hutchpp-unbiased` (helper; belongs in
`NLAlib.Matrix.Subspaces.Projections`). -/
theorem trace_eq_trace_mul_mul_add_trace_sub_mul_mul_sub {P : Matrix n n ℝ} (hP : P * P = P)
    (A : Matrix n n ℝ) :
    A.trace = (P * A * P).trace + ((1 - P) * A * (1 - P)).trace := by
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hP]; simp
  rw [Matrix.trace_mul_cycle, hP, Matrix.trace_mul_cycle (1 - P), hQ, ← Matrix.trace_add,
    ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]

variable {r : Type*} [Fintype r] [DecidableEq r]

/-- **Trace split by an orthonormal basis.** If `QᵀQ = I` then
`tr A = tr(QᵀAQ) + tr((I − QQᵀ) A (I − QQᵀ))`. Source: Meyer–Musco–Musco–Woodruff (2021)
[`mmmw21`], eq. (3); Epperly–Tropp–Webber (2024) [`etw24`], eq. (1.4). Atlas: `hutchpp-unbiased`
(helper).
atlas: hutchpp-unbiased (partial) -/
theorem trace_eq_trace_transpose_mul_mul_add {Q : Matrix n r ℝ} (hQ : HasOrthonormalCols Q)
    (A : Matrix n n ℝ) :
    A.trace = (Qᵀ * A * Q).trace + ((1 - Q * Qᵀ) * A * (1 - Q * Qᵀ)).trace := by
  have hPP : Q * Qᵀ * (Q * Qᵀ) = Q * Qᵀ := mul_conjTranspose_mul_mul_conjTranspose hQ
  have h1 : (Q * Qᵀ * A * (Q * Qᵀ)).trace = (Qᵀ * A * Q).trace := by
    rw [show Q * Qᵀ * A * (Q * Qᵀ) = Q * (Qᵀ * A * Q * Qᵀ) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show Qᵀ * A * Q * Qᵀ * Q = Qᵀ * A * Q * (Qᵀ * Q) by simp only [Matrix.mul_assoc],
      show Qᵀ * Q = 1 from hQ, Matrix.mul_one]
  rw [trace_eq_trace_mul_mul_add_trace_sub_mul_mul_sub hPP A, h1]

/-! ### Hutchinson and Hutch++ for fixed matrices -/

section Fixed

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [DecidableEq n] [DecidableEq κ] in
/-- **Multi-sample Hutchinson is unbiased.** If every column `Z(·, k)` of the random test matrix
has isotropic second moments, `𝔼[Z_ik Z_jk] = δ_ij`, then `𝔼[tr_m(A)] = tr A` (`m = |κ| ≥ 1`).
No independence is needed. Source: Hutchinson (1989) [`hutch89`]; Avron–Toledo (2011) [`at11`],
§2. Atlas: `hutchinson-unbiased`. -/
theorem integral_hutchinsonEstimate_eq_trace [DecidableEq n] [Nonempty κ] (A : Matrix n n ℝ)
    {Z : Ω → Matrix n κ ℝ} (hmeas : ∀ i k, AEMeasurable (fun ω => Z ω i k) μ)
    (hsecond : ∀ k i j, ∫ ω, Z ω i k * Z ω j k ∂μ = if i = j then 1 else 0) :
    ∫ ω, hutchinsonEstimate A (Z ω) ∂μ = A.trace := by
  have hm : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hkI := fun k => integrable_quadForm_of_second_moments A
    (z := fun ω i => Z ω i k) (fun i => hmeas i k) (hsecond k)
  have hkE := fun k => integral_quadForm_eq_trace_of_second_moments A
    (z := fun ω i => Z ω i k) (fun i => hmeas i k) (hsecond k)
  simp only [hutchinsonEstimate]
  rw [integral_div, integral_finsetSum _ fun k _ => hkI k]
  simp only [hkE, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The deflated trace kernel with a supplied basis `Q` and Hutchinson test matrix `Z`:
`tr(QᵀAQ) + tr_m((I − QQᵀ)A(I − QQᵀ))`. Source: Meyer–Musco–Musco–Woodruff (2021) [`mmmw21`],
Alg. 1. Atlas: `hutchpp`, `hutchpp-unbiased`. `Q` is arbitrary here; unbiasedness requires orthonormality. The sketch-based
`hutchPlusPlusEstimate` below constructs its basis from `range (A S)`. An empty test family
has a zero residual average, leaving the compressed trace.
atlas: trace-estimators-def -/
def deflatedTraceEstimate (A : Matrix n n ℝ) (Q : Matrix n r ℝ) (Z : Matrix n κ ℝ) : ℝ :=
  (Qᵀ * A * Q).trace + hutchinsonEstimate ((1 - Q * Qᵀ) * A * (1 - Q * Qᵀ)) Z

/-- The orthonormal sketch-image basis used by Hutch++.
Its columns span `range (A S)` exactly and their number is the rank of the sketch image.
Source: Meyer–Musco–Musco–Woodruff (2021), Alg. 1. -/
def hutchPlusPlusBasis {s : Type*} [Fintype s] (A : Matrix n n ℝ) (S : Matrix n s ℝ) :
    Matrix n (Fin (Module.finrank ℝ (LinearMap.range (A * S).mulVecLin))) ℝ :=
  orthonormalBasisMatrix (LinearMap.range (A * S).mulVecLin)

/-- The constructed Hutch++ sketch-image basis has orthonormal columns. -/
theorem hasOrthonormalCols_hutchPlusPlusBasis {s : Type*} [Fintype s]
    (A : Matrix n n ℝ) (S : Matrix n s ℝ) : HasOrthonormalCols (hutchPlusPlusBasis A S) :=
  hasOrthonormalCols_orthonormalBasisMatrix _

/-- The constructed Hutch++ basis spans the sketch image, including rank-deficient sketches. -/
theorem range_hutchPlusPlusBasis {s : Type*} [Fintype s]
    (A : Matrix n n ℝ) (S : Matrix n s ℝ) :
    LinearMap.range (hutchPlusPlusBasis A S).mulVecLin = LinearMap.range (A * S).mulVecLin :=
  range_orthonormalBasisMatrix _

/-- The sketch-image basis has at most as many columns as the sketch. -/
theorem card_hutchPlusPlusBasis_le {s : Type*} [Fintype s]
    (A : Matrix n n ℝ) (S : Matrix n s ℝ) :
    Fintype.card (Fin (Module.finrank ℝ (LinearMap.range (A * S).mulVecLin))) ≤ Fintype.card s := by
  rw [Fintype.card_fin, Matrix.range_mulVecLin]
  exact finrank_range_le_card (R := ℝ) _

/-- Hutch++ with a basis constructed from the sketch image and a separate residual test matrix.
Source: Meyer–Musco–Musco–Woodruff (2021), Alg. 1. Rank-deficient and zero sketches use their
actual image dimension. This definition supplies the sketch-span relation; random-sketch
measurability, independence and complexity guarantees require separate theorems. -/
def hutchPlusPlusEstimate {s : Type*} [Fintype s]
    (A : Matrix n n ℝ) (S : Matrix n s ℝ) (Z : Matrix n κ ℝ) : ℝ :=
  deflatedTraceEstimate A (hutchPlusPlusBasis A S) Z

omit [DecidableEq κ] in
/-- **Fixed orthonormal deflation is unbiased.** If `QᵀQ = I` and the columns of the
random test matrix have isotropic second moments, then the deflated estimate has expectation `tr A`. Source:
Meyer–Musco–Musco–Woodruff (2021) [`mmmw21`], proof of Thm 1 (unbiasedness, conditional on
`S`). Atlas: `hutchpp-unbiased`; uses `hutchinson-unbiased`.
atlas: hutchpp-unbiased (partial) -/
theorem integral_deflatedTraceEstimate_eq_trace [Nonempty κ] [IsProbabilityMeasure μ]
    (A : Matrix n n ℝ) {Q : Matrix n r ℝ} (hQ : HasOrthonormalCols Q)
    {Z : Ω → Matrix n κ ℝ} (hmeas : ∀ i k, AEMeasurable (fun ω => Z ω i k) μ)
    (hsecond : ∀ k i j, ∫ ω, Z ω i k * Z ω j k ∂μ = if i = j then 1 else 0) :
    ∫ ω, deflatedTraceEstimate A Q (Z ω) ∂μ = A.trace := by
  have hk := fun k => integrable_quadForm_of_second_moments
    ((1 - Q * Qᵀ) * A * (1 - Q * Qᵀ)) (z := fun ω i => Z ω i k) (fun i => hmeas i k)
      (hsecond k)
  have hint : Integrable (fun ω => hutchinsonEstimate ((1 - Q * Qᵀ) * A * (1 - Q * Qᵀ)) (Z ω))
      μ := by
    simp only [hutchinsonEstimate]
    exact (integrable_finsetSum _ fun k _ => hk k).div_const _
  simp only [deflatedTraceEstimate]
  rw [integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul,
    integral_hutchinsonEstimate_eq_trace _ hmeas hsecond,
    ← trace_eq_trace_transpose_mul_mul_add hQ A]

/-- For a fixed sketch, the constructed Hutch++ estimator is unbiased under isotropic
residual probes. Source: Meyer–Musco–Musco–Woodruff (2021), proof of Thm 1. -/
theorem integral_hutchPlusPlusEstimate_eq_trace [Nonempty κ] [IsProbabilityMeasure μ]
    {s : Type*} [Fintype s] (A : Matrix n n ℝ) (S : Matrix n s ℝ)
    {Z : Ω → Matrix n κ ℝ} (hmeas : ∀ i k, AEMeasurable (fun ω => Z ω i k) μ)
    (hsecond : ∀ k i j, ∫ ω, Z ω i k * Z ω j k ∂μ = if i = j then 1 else 0) :
    ∫ ω, hutchPlusPlusEstimate A S (Z ω) ∂μ = A.trace :=
  integral_deflatedTraceEstimate_eq_trace A (hasOrthonormalCols_hutchPlusPlusBasis A S)
    hmeas hsecond

/-- The constructed estimator with a fixed sketch and Gaussian residual probes is unbiased;
its probe moments and integrability follow from the Gaussian law.
Source: Meyer–Musco–Musco–Woodruff (2021), proof of Thm 1 (conditional on the sketch). -/
theorem integral_hutchPlusPlusEstimate_eq_trace_of_hasLaw_gaussianMatrix
    [Nonempty κ] [IsProbabilityMeasure μ] {s : Type*} [Fintype s]
    (A : Matrix n n ℝ) (S : Matrix n s ℝ) {Z : Ω → Matrix n κ ℝ}
    (hZ : HasLaw Z (gaussianMatrix n κ) μ) :
    ∫ ω, hutchPlusPlusEstimate A S (Z ω) ∂μ = A.trace := by
  apply integral_hutchPlusPlusEstimate_eq_trace A S
  · intro i k
    exact (Matrix.measurable_entry i k).comp_aemeasurable hZ.aemeasurable
  · intro k i j
    have h := hZ.integral_comp ((Matrix.measurable_entry i k).mul
      (Matrix.measurable_entry j k)).aestronglyMeasurable
    exact h.trans (by simpa using integral_gaussianMatrix_entry_mul i j k k)

end Fixed

/-! ### Random deflation bases independent of the test vectors -/

section Random

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Fubini step for independent inputs.** If `X ⊥ Y`, `g` is integrable for the product of
their laws, and `𝔼[g(x, Y)] = c` for every fixed `x`, then `𝔼[g(X, Y)] = c`. Source: Durrett,
*Probability*, Thm 2.1.12 (Fubini for independent variables). Atlas: `gaussian-conditioning`
(corollary; used by `hutchpp-unbiased`, `xtrace-unbiased`). -/
theorem integral_comp_of_indepFun_of_forall_integral_eq {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {X : Ω → α} {Y : Ω → β} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXY : IndepFun X Y μ) {g : α → β → ℝ}
    (hg : Integrable (fun p : α × β => g p.1 p.2) ((μ.map X).prod (μ.map Y))) {c : ℝ}
    (hc : ∀ x, ∫ ω, g x (Y ω) ∂μ = c) : ∫ ω, g (X ω) (Y ω) ∂μ = c := by
  have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX
  rw [integral_of_indepFun hX hY hXY hg]
  have hae : ∀ᵐ x ∂(μ.map X), ∫ y, g x y ∂(μ.map Y) = c := by
    filter_upwards [hg.prod_right_ae] with x hx
    rw [integral_map hY hx.aestronglyMeasurable, hc x]
  rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul]

variable {κ : Type*} [Fintype κ]

/-- **Independent random orthonormal deflation is unbiased.** Let the deflation basis `Q(S)` be a function of a random sketch `S`
with `Q(s)ᵀQ(s) = I` for every `s`, and let the Hutchinson test matrix `G` be independent of `S`
with isotropic columns. If the estimator is integrable for the product of the laws, then
`𝔼[tr(QᵀAQ) + tr_m((I − QQᵀ)A(I − QQᵀ))] = tr A`.
Source: Meyer–Musco–Musco–Woodruff (2021) [`mmmw21`], Thm 1 (unbiasedness part).
Atlas: `hutchpp-unbiased`; uses `hutchinson-unbiased`, `gaussian-conditioning`.
Deviation: the integrability of the estimator is a hypothesis (it holds for Gaussian `G`,
bounded `A`); `S` lives in an arbitrary measurable space.
atlas: hutchpp-unbiased (partial) -/
theorem integral_deflatedTraceEstimate_comp_eq_trace [Nonempty κ] {α : Type*}
    [MeasurableSpace α] (A : Matrix n n ℝ) {r : Type*} [Fintype r] [DecidableEq r]
    {Q : α → Matrix n r ℝ} (hQ : ∀ s, HasOrthonormalCols (Q s)) {S : Ω → α}
    {G : Ω → Matrix n κ ℝ} (hS : AEMeasurable S μ) (hG : AEMeasurable G μ) (hSG : IndepFun S G μ)
    (hsecond : ∀ k i j, ∫ ω, G ω i k * G ω j k ∂μ = if i = j then 1 else 0)
    (hint : Integrable (fun p : α × Matrix n κ ℝ => deflatedTraceEstimate A (Q p.1) p.2)
      ((μ.map S).prod (μ.map G))) :
    ∫ ω, deflatedTraceEstimate A (Q (S ω)) (G ω) ∂μ = A.trace := by
  have hmeas : ∀ i k, AEMeasurable (fun ω => G ω i k) μ := fun i k =>
    (Matrix.measurable_entry i k).comp_aemeasurable hG
  exact integral_comp_of_indepFun_of_forall_integral_eq (g := fun s Z =>
    deflatedTraceEstimate A (Q s) Z) hS hG hSG hint
    (fun s => integral_deflatedTraceEstimate_eq_trace A (hQ s) hmeas hsecond)

/-- The supplied leave-one-out deflated trace kernel: the average over `i` of
`tr(Qᵢᵀ A Qᵢ) + ωᵢᵀ (I − QᵢQᵢᵀ) A (I − QᵢQᵢᵀ) ωᵢ`, where `Qᵢ` is supplied. No sketch-span condition is imposed by this kernel.
The average is zero when there are no samples. Source: Epperly–Tropp–Webber (2024) [`etw24`], eq. (1.6) (basic form, before the
normalisation refinements of §2). Atlas: `xtrace-unbiased`. -/
def leaveOneOutDeflatedTraceEstimate (A : Matrix n n ℝ) {r : Type*} [Fintype r] (Q : κ → Matrix n r ℝ)
    (W : Matrix n κ ℝ) : ℝ :=
  (∑ i, (((Q i)ᵀ * A * Q i).trace +
    quadForm ((1 - Q i * (Q i)ᵀ) * A * (1 - Q i * (Q i)ᵀ)) (fun j => W j i))) / Fintype.card κ

/-- The sketch formed by deleting a probe column. Source: Epperly–Tropp–Webber (2024), §2.1. -/
def leaveOneOutSketch (W : Matrix n κ ℝ) (i : κ) : Matrix n {j : κ // j ≠ i} ℝ :=
  W.submatrix id Subtype.val

/-- The basic XTrace deflation estimate with each basis constructed from the other probes.
Source: Epperly–Tropp–Webber (2024), eq. (1.6), before the normalization refinements of §2.
Each summand uses the basis of `range (A W₋ᵢ)`. The empty average is zero. -/
def xtraceEstimate [DecidableEq κ] (A : Matrix n n ℝ) (W : Matrix n κ ℝ) : ℝ :=
  (∑ i, hutchPlusPlusEstimate A (leaveOneOutSketch W i)
    (Matrix.replicateCol Unit (fun j => W j i))) / Fintype.card κ

/-- **Independent leave-one-out deflation is unbiased.** Let `W` be the test matrix with columns `ωᵢ`, and for each `i` let
`Qᵢ = Qf i (Sᵢ)` with `Qf i s` orthonormal for every `s`, where the leave-one-out statistic `Sᵢ`
(in XTrace, `Ω₋ᵢ`) is independent of `ωᵢ`, and each `ωᵢ` has isotropic second moments. If each
term is integrable for the product of the laws of `Sᵢ` and `ωᵢ`, then the leave-one-out deflated estimate has expectation `tr A`.
Source: Epperly–Tropp–Webber (2024) [`etw24`], §2.1 (unbiasedness of the exchangeable estimator).
Atlas: `xtrace-unbiased`; uses `hutchinson-unbiased`, `gaussian-conditioning`.
Deviation: abstract leave-one-out statistics `Sᵢ`; integrability is a hypothesis; the
`rsvd-expected-error` dependency of the atlas entry is not needed.
atlas: xtrace-unbiased (partial) -/
theorem integral_leaveOneOutDeflatedTraceEstimate_eq_trace [Nonempty κ] (A : Matrix n n ℝ) {r : Type*}
    [Fintype r] [DecidableEq r] {α : κ → Type*} [∀ i, MeasurableSpace (α i)]
    {Qf : ∀ i, α i → Matrix n r ℝ} (hQ : ∀ i s, HasOrthonormalCols (Qf i s))
    {S : ∀ i, Ω → α i} {W : Ω → Matrix n κ ℝ} (hS : ∀ i, AEMeasurable (S i) μ)
    (hW : ∀ i, AEMeasurable (fun ω j => W ω j i) μ)
    (hind : ∀ i, IndepFun (S i) (fun ω j => W ω j i) μ)
    (hsecond : ∀ i j j', ∫ ω, W ω j i * W ω j' i ∂μ = if j = j' then 1 else 0)
    (hint : ∀ i, Integrable (fun p : α i × (n → ℝ) => ((Qf i p.1)ᵀ * A * Qf i p.1).trace +
      quadForm ((1 - Qf i p.1 * (Qf i p.1)ᵀ) * A * (1 - Qf i p.1 * (Qf i p.1)ᵀ)) p.2)
      ((μ.map (S i)).prod (μ.map fun ω j => W ω j i))) :
    ∫ ω, leaveOneOutDeflatedTraceEstimate A (fun i => Qf i (S i ω)) (W ω) ∂μ = A.trace := by
  have hm : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hterm : ∀ i, ∫ ω, (((Qf i (S i ω))ᵀ * A * Qf i (S i ω)).trace +
      quadForm ((1 - Qf i (S i ω) * (Qf i (S i ω))ᵀ) * A * (1 - Qf i (S i ω) * (Qf i (S i ω))ᵀ))
        (fun j => W ω j i)) ∂μ = A.trace := fun i => by
    refine integral_comp_of_indepFun_of_forall_integral_eq (X := S i)
      (Y := fun ω j => W ω j i) (g := fun s w => ((Qf i s)ᵀ * A * Qf i s).trace +
        quadForm ((1 - Qf i s * (Qf i s)ᵀ) * A * (1 - Qf i s * (Qf i s)ᵀ)) w)
      (hS i) (hW i) (hind i) (hint i) fun s => ?_
    have hmeas : ∀ j, AEMeasurable (fun ω => W ω j i) μ := fun j =>
      (measurable_pi_apply j).comp_aemeasurable (hW i)
    have hqI := integrable_quadForm_of_second_moments
      ((1 - Qf i s * (Qf i s)ᵀ) * A * (1 - Qf i s * (Qf i s)ᵀ)) (z := fun ω j => W ω j i)
      hmeas (hsecond i)
    have hqE := integral_quadForm_eq_trace_of_second_moments
      ((1 - Qf i s * (Qf i s)ᵀ) * A * (1 - Qf i s * (Qf i s)ᵀ)) (z := fun ω j => W ω j i)
      hmeas (hsecond i)
    rw [integral_add (integrable_const _) hqI, integral_const, probReal_univ, one_smul, hqE,
      ← trace_eq_trace_transpose_mul_mul_add (hQ i s) A]
  have hint' : ∀ i, Integrable (fun ω => ((Qf i (S i ω))ᵀ * A * Qf i (S i ω)).trace +
      quadForm ((1 - Qf i (S i ω) * (Qf i (S i ω))ᵀ) * A * (1 - Qf i (S i ω) * (Qf i (S i ω))ᵀ))
        (fun j => W ω j i)) μ := fun i => by
    have hmap : μ.map (fun ω => (S i ω, fun j => W ω j i)) =
        (μ.map (S i)).prod (μ.map fun ω j => W ω j i) :=
      (indepFun_iff_map_prod_eq_prod_map_map (hS i) (hW i)).1 (hind i)
    have h := hint i
    rw [← hmap] at h
    exact h.comp_aemeasurable ((hS i).prodMk (hW i))
  simp only [leaveOneOutDeflatedTraceEstimate]
  rw [integral_div, integral_finsetSum _ fun i _ => hint' i]
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end Random

/-! ### The Hutchinson clause of the spectral measure -/

/-- **Hutchinson for the spectral measure.** For symmetric `A`, a random vector `z` with
square-integrable, pairwise independent, centred, unit-variance coordinates, and any
`f : ℝ → ℝ`, `𝔼_z[∫ f dμ_z] = 𝔼_z[zᵀ f(A) z] = tr f(A)`.
Source: Ubaru–Chen–Saad (2017) [`ucs17`], §2–3 (the SLQ estimand). Atlas: `spectral-measure`
(expectation clause, layer 4); uses `hutchinson-unbiased`.
atlas: spectral-measure -/
theorem integral_integral_spectralMeasure_eq_trace {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) {z : Ω → n → ℝ} (hz : ∀ i, MemLp (fun ω => z ω i) 2 μ)
    (hind : ∀ i j, i ≠ j → IndepFun (fun ω => z ω i) (fun ω => z ω j) μ)
    (hmean : ∀ i, ∫ ω, z ω i ∂μ = 0) (hsq : ∀ i, ∫ ω, z ω i ^ 2 ∂μ = 1) :
    ∫ ω, (∫ x, f x ∂spectralMeasure hA (z ω)) ∂μ = (cfc f A).trace := by
  simp_rw [integral_spectralMeasure_eq_quadForm]
  exact integral_quadForm_eq_trace _ hz hind hmean hsq

end NLAlib
