import NLAlib.LowRank.RSVD
import NLAlib.LowRank.GeneralizedNystrom
import NLAlib.Gaussian.Conditioning
import NLAlib.Gaussian.InverseMoments

/-!
# Randomized SVD and generalized Nyström with Gaussian test matrices

Instantiates the conditional theorems of `NLAlib/LowRank/RSVD.lean` and
`NLAlib/LowRank/GeneralizedNystrom.lean` with actual standard Gaussian test matrices, so that no
Gaussian expectation hypothesis remains:

* `rsvd_main_gaussian`, `rsvd_truncated_main_gaussian` — Chen–Persson `thm:RSVD`
  (HMT 2011, Thm 10.5, Frobenius case);
* `completion_reduction_gaussian` — Chen–Persson `lem:completion`;
* `gn_main_gaussian` — Chen–Persson `thm:GN` (Tropp–Webber 2023, Thm 5.1).

A random matrix `Ω : Ωs → Matrix (Fin n) (Fin t) ℝ` is standard Gaussian when its array view
has law `gaussianMatrix n t`: `μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n t`.
The Gaussian inputs come from `NLAlib/Gaussian/Conditioning.lean` (block law, independence,
tower property), `NLAlib/Gaussian/InverseMoments.lean` (`E‖G†‖_F² = r/(k−r−1)`) and
`NLAlib/Gaussian/Moments.lean` (full rank a.s.).

Remaining hypotheses are those about the user's choice of `Q = orth(AΩ)` (a.s. orthonormal
columns, `range(AΩ) ⊆ range(Q)`), plus, for `gn_main_gaussian`, that `Q` is a measurable
function of `Ω`.

Atlas: `rsvd-expected-error`, `gn-expected-error`.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

section Block

variable {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs}

/-- If `Ω` is an `n × t` standard Gaussian matrix, `V₁ᵀV₁ = 1` and `k ≤ t`, then `V₁ᵀΩ` has full
row rank almost surely (`(V₁ᵀΩ)(V₁ᵀΩ)ᵀ` is invertible). HMT 2011 §10.2 (block law) with
"a Gaussian matrix has full rank a.s."; hypothesis `hunit` of `rsvd_main`.
Atlas `rsvd-expected-error` (uses `gaussian-conditioning`, `gaussian-full-rank-ae`). -/
theorem ae_isUnit_block {n k t : ℕ} {Ω : Ωs → Fin n → Fin t → ℝ}
    (hΩ : μ.map Ω = gaussianMatrix n t) (V₁ : Matrix (Fin n) (Fin k) ℝ)
    (hV₁ : V₁ᵀ * V₁ = 1) (hkt : k ≤ t) :
    ∀ᵐ ω ∂μ, IsUnit ((V₁ᵀ * Matrix.of (Ω ω)) * (V₁ᵀ * Matrix.of (Ω ω))ᵀ) := by
  have h := gaussianMatrix_ae_isUnit_mul_transpose (k := k) hkt
  rw [← map_block_eq_gaussianMatrix hΩ V₁ hV₁] at h
  exact ae_of_ae_map
    ((measurable_block V₁).comp_aemeasurable (aemeasurable_of_map_eq_gaussianMatrix hΩ)) h

/-- Integrability of `‖(V₁ᵀΩ)†‖_F²` for an `n × t` standard Gaussian `Ω`, `V₁ᵀV₁ = 1`,
`k + 2 ≤ t`: the integrability half of the inverse moment (`pinv_frobenius_moment`) transported
by the block law. HMT 2011 Prop 10.2 and §10.2. Atlas `rsvd-expected-error`
(uses `gaussian-conditioning`, `pinv-frob-moment`). -/
theorem integrable_pinvR_block {n k t : ℕ} {Ω : Ωs → Fin n → Fin t → ℝ}
    (hΩ : μ.map Ω = gaussianMatrix n t) (V₁ : Matrix (Fin n) (Fin k) ℝ)
    (hV₁ : V₁ᵀ * V₁ = 1) (hkt : k + 2 ≤ t) :
    Integrable (fun ω => frobSq (pinvR (V₁ᵀ * Matrix.of (Ω ω)))) μ := by
  have h := (pinv_frobenius_moment hkt).1
  rw [← map_block_eq_gaussianMatrix hΩ V₁ hV₁] at h
  exact h.comp_aemeasurable
    ((measurable_block V₁).comp_aemeasurable (aemeasurable_of_map_eq_gaussianMatrix hΩ))

/-- `E‖(V₁ᵀΩ)†‖_F² = k/(t−k−1)` for an `n × t` standard Gaussian `Ω`, `V₁ᵀV₁ = 1`, `k + 2 ≤ t`.
HMT 2011 Prop 10.2 and §10.2 (Chen–Persson `lem:invmom`). Atlas `rsvd-expected-error`
(uses `gaussian-conditioning`, `pinv-frob-moment`). -/
theorem integral_pinvR_block {n k t : ℕ} {Ω : Ωs → Fin n → Fin t → ℝ}
    (hΩ : μ.map Ω = gaussianMatrix n t) (V₁ : Matrix (Fin n) (Fin k) ℝ)
    (hV₁ : V₁ᵀ * V₁ = 1) (hkt : k + 2 ≤ t) :
    ∫ ω, frobSq (pinvR (V₁ᵀ * Matrix.of (Ω ω))) ∂μ = (k : ℝ) / ((t : ℝ) - k - 1) := by
  rw [integral_pinvR_frobSq_block hΩ V₁ hV₁, (pinv_frobenius_moment hkt).2]

end Block

section RSVD

variable {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
variable {m n k r r' t q : ℕ}

/-- The three Gaussian inputs of `rsvd_main` / `rsvd_truncated_main` for a standard Gaussian test
matrix `Ω` (law `gaussianMatrix n t` of the array view `Matrix.of.symm ∘ Ω`): `hunit` (a.s.
full row rank of `V₁ᵀΩ`), `hinv` (`E‖S₂Ω₂Ω₁†‖_F² = (k/(t−k−1))‖S₂‖_F²`) and `hZi`.
HMT 2011, proof of Thm 10.5; Chen–Persson, proof of `thm:RSVD`. Atlas `rsvd-expected-error`
(uses `gaussian-conditioning`, `pinv-frob-moment`, `gaussian-full-rank-ae`). -/
theorem rsvd_gaussian_inputs {V₁ : Matrix (Fin n) (Fin k) ℝ}
    {V₂ : Matrix (Fin n) (Fin r') ℝ} (S₂ : Matrix (Fin r) (Fin r') ℝ)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (hkt : k + 2 ≤ t) (Ω : Ωs → Matrix (Fin n) (Fin t) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n t) :
    (∀ᵐ ω ∂μ, IsUnit ((V₁ᵀ * Ω ω) * (V₁ᵀ * Ω ω)ᵀ)) ∧
    (∫ ω, frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω)) ∂μ
      = (k : ℝ) / (t - k - 1) * frobSq S₂) ∧
    Integrable (fun ω => frobSq (S₂ * (V₂ᵀ * Ω ω) * pinvR (V₁ᵀ * Ω ω))) μ := by
  refine ⟨ae_isUnit_block hΩ V₁ hV₁ (by omega), ?_, ?_⟩
  · have h := rsvd_inverse_moment_factor hΩ V₁ V₂ hV₁ hV₂ hV S₂
    rw [integral_pinvR_block hΩ V₁ hV₁ hkt] at h
    exact h.trans (mul_comm _ _)
  · exact integrable_rsvd_inverse_moment hΩ V₁ V₂ hV₁ hV₂ hV S₂
      (integrable_pinvR_block hΩ V₁ hV₁ hkt)

/-- The RSVD bound `(1 + k/(t−k−1))‖S₂‖_F²` is nonnegative when `k + 2 ≤ t`. Helper for the
non-integrable case of `rsvd_main_gaussian`. Atlas `rsvd-expected-error` (helper). -/
theorem rsvd_bound_nonneg {k t : ℕ} (hkt : k + 2 ≤ t) {S₂ : Matrix (Fin r) (Fin r') ℝ} :
    0 ≤ (1 + (k : ℝ) / (t - k - 1)) * frobSq S₂ := by
  have : (k : ℝ) + 2 ≤ t := by exact_mod_cast hkt
  have h : 0 ≤ (k : ℝ) / (t - k - 1) := div_nonneg (Nat.cast_nonneg k) (by linarith)
  exact mul_nonneg (by linarith) (frobSq_nonneg _)

/-- **Randomized SVD with a Gaussian test matrix** (Chen–Persson, Theorem `thm:RSVD`, Algorithm
RSVD; HMT 2011, Thm 10.5, Frobenius case): if `Ω` is an `n × t` standard Gaussian matrix,
`t ≥ k + 2`, and `Q ω` has a.s. orthonormal columns with `range(AΩ) ⊆ range(Q)`, then
`E‖A − QQᵀA‖_F² ≤ (1 + k/(t−k−1)) ‖A − ⟦A⟧ₖ‖_F²` (`‖A − ⟦A⟧ₖ‖_F² = frobSq S₂` via the block SVD).
`rsvd_main` with its Gaussian hypotheses `hunit`, `hinv`, `hZi` discharged. The integrability
hypothesis `hXi` is also removed: when the error is not integrable its Bochner integral is `0`
and the (nonnegative) bound holds trivially. No measurability of `Q` is required.
Deviation: row index types `Fin m`, `Fin n`; `q` fixed (see `RSVD.lean`).
Atlas `rsvd-expected-error` (uses `gaussian-conditioning`, `pinv-frob-moment`,
`gaussian-full-rank-ae`, `hmt-9-1-frobenius`). -/
theorem rsvd_main_gaussian
    {A : Matrix (Fin m) (Fin n) ℝ} {U₁ : Matrix (Fin m) (Fin k) ℝ}
    {U₂ : Matrix (Fin m) (Fin r) ℝ} {V₁ : Matrix (Fin n) (Fin k) ℝ}
    {V₂ : Matrix (Fin n) (Fin r') ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ}
    {S₂ : Matrix (Fin r) (Fin r') ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (hkt : k + 2 ≤ t)
    (Ω : Ωs → Matrix (Fin n) (Fin t) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n t)
    (Q : Ωs → Matrix (Fin m) (Fin q) ℝ)
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q ω))
    (hQr : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * (A * Ω ω)) = A * Ω ω) :
    ∫ ω, frobSq (A - Q ω * ((Q ω)ᵀ * A)) ∂μ ≤ (1 + (k : ℝ) / (t - k - 1)) * frobSq S₂ := by
  obtain ⟨hunit, hinv, hZi⟩ := rsvd_gaussian_inputs S₂ hV₁ hV₂ hV hkt Ω hΩ
  by_cases hXi : Integrable (fun ω => frobSq (A - Q ω * ((Q ω)ᵀ * A))) μ
  · exact rsvd_main hA hU₂ hV₁ hV₂ hV hkt Ω Q hQo hQr hunit hinv hXi hZi
  · rw [integral_undef hXi]; exact rsvd_bound_nonneg hkt

/-- **Truncated randomized SVD with a Gaussian test matrix** (Chen–Persson, Theorem `thm:RSVD`,
Algorithm tRSVD, output `Q⟦QᵀA⟧ₖ`; HMT 2011, Thm 10.5): as `rsvd_main_gaussian`, with
`Y ω` any best rank-`k` approximation of `Q ωᵀ A`:
`E‖A − Q⟦QᵀA⟧ₖ‖_F² ≤ (1 + k/(t−k−1)) ‖A − ⟦A⟧ₖ‖_F²`. No Gaussian or integrability hypothesis
remains. Atlas `rsvd-expected-error` (uses `gaussian-conditioning`, `pinv-frob-moment`,
`gaussian-full-rank-ae`, `hmt-9-1-frobenius`). -/
theorem rsvd_truncated_main_gaussian
    {A : Matrix (Fin m) (Fin n) ℝ} {U₁ : Matrix (Fin m) (Fin k) ℝ}
    {U₂ : Matrix (Fin m) (Fin r) ℝ} {V₁ : Matrix (Fin n) (Fin k) ℝ}
    {V₂ : Matrix (Fin n) (Fin r') ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ}
    {S₂ : Matrix (Fin r) (Fin r') ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (hkt : k + 2 ≤ t)
    (Ω : Ωs → Matrix (Fin n) (Fin t) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n t)
    (Q : Ωs → Matrix (Fin m) (Fin q) ℝ) (Y : Ωs → Matrix (Fin q) (Fin n) ℝ)
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q ω))
    (hQr : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * (A * Ω ω)) = A * Ω ω)
    (hY : ∀ ω, IsBestRankApprox k ((Q ω)ᵀ * A) (Y ω)) :
    ∫ ω, frobSq (A - Q ω * Y ω) ∂μ ≤ (1 + (k : ℝ) / (t - k - 1)) * frobSq S₂ := by
  obtain ⟨hunit, hinv, hZi⟩ := rsvd_gaussian_inputs S₂ hV₁ hV₂ hV hkt Ω hΩ
  by_cases hXi : Integrable (fun ω => frobSq (A - Q ω * Y ω)) μ
  · exact rsvd_truncated_main hA hU₂ hV₁ hV₂ hV hkt Ω Q Y hQo hQr hY hunit hinv hXi hZi
  · rw [integral_undef hXi]; exact rsvd_bound_nonneg hkt

end RSVD


section Completion

variable {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs}

/-- If `QᵀQ = 1`, `QpᵀQp = 1` and `QQᵀ + QpQpᵀ = 1`, then `QᵀQp = 0`. Atlas
`gn-expected-error` (helper; belongs in `Matrix/Projections.lean`). -/
theorem transpose_mul_eq_zero_of_completion {m : Type*} [Fintype m] [DecidableEq m] {q r : ℕ}
    {Q : Matrix m (Fin q) ℝ} {Qp : Matrix m (Fin r) ℝ} (hQ : Qᵀ * Q = 1) (hQp : Qpᵀ * Qp = 1)
    (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1) : Qᵀ * Qp = 0 := by
  have h := congrArg (fun M => Qᵀ * M * Qp) hcomp
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one] at h
  rw [← Matrix.mul_assoc, hQ, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hQp,
    Matrix.mul_one] at h
  -- h : Qᵀ * Qp + Qᵀ * Qp = Qᵀ * Qp
  simpa using h

/-- `(PᵀQ)ᵀ(PᵀQ) = (QᵀP)(QᵀP)ᵀ`. Atlas `gn-expected-error` (helper). -/
theorem gram_transpose_mul_eq {m s q : ℕ} (P : Matrix (Fin m) (Fin s) ℝ)
    (Q : Matrix (Fin m) (Fin q) ℝ) :
    (Pᵀ * Q)ᵀ * (Pᵀ * Q) = (Qᵀ * P) * (Qᵀ * P)ᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- The Gaussian inputs of `completion_reduction` for an `m × s` standard Gaussian `Ψ` and fixed
`Q`, `Qp` with orthonormal, mutually orthogonal columns, `q + 2 ≤ s`: a.s. full column rank of
`ΨᵀQ` (`hG₁`), `E‖(ΨᵀQ)†‖_F² = q/(s−q−1)` (`hG₁m`), and integrability of the noise term
`‖(ΨᵀQ)†(ΨᵀQp)B‖_F²` (`hGi`). `ΨᵀQ = (QᵀΨ)ᵀ` with `QᵀΨ ∼ gaussianMatrix q s` (block law).
Chen–Persson, proof of `lem:completion`; Tropp–Webber 2023, proof of Thm 5.1.
Atlas `gn-expected-error` (uses `gaussian-conditioning`, `pinv-frob-moment`,
`gaussian-full-rank-ae`). -/
theorem completion_gaussian_inputs [IsProbabilityMeasure μ] {m s q rp : ℕ} {ι : Type*}
    [Fintype ι] {Ψ : Ωs → Fin m → Fin s → ℝ} (hΨ : μ.map Ψ = gaussianMatrix m s)
    (Q : Matrix (Fin m) (Fin q) ℝ) (Qp : Matrix (Fin m) (Fin rp) ℝ) (hQ : Qᵀ * Q = 1)
    (hQp : Qpᵀ * Qp = 1) (hQQp : Qᵀ * Qp = 0) (B : Matrix (Fin rp) ι ℝ) (hqs : q + 2 ≤ s) :
    (∀ᵐ ω ∂μ, IsUnit (((Matrix.of (Ψ ω))ᵀ * Q)ᵀ * ((Matrix.of (Ψ ω))ᵀ * Q))) ∧
    (∫ ω, frobSq (pinvL ((Matrix.of (Ψ ω))ᵀ * Q)) ∂μ = (q : ℝ) / ((s : ℝ) - q - 1)) ∧
    Integrable
      (fun ω => frobSq (pinvL ((Matrix.of (Ψ ω))ᵀ * Q) * ((Matrix.of (Ψ ω))ᵀ * Qp) * B)) μ := by
  have h1 : ∀ ω, frobSq (pinvL ((Matrix.of (Ψ ω))ᵀ * Q) * ((Matrix.of (Ψ ω))ᵀ * Qp) * B) =
      frobSq (Bᵀ * (Qpᵀ * Matrix.of (Ψ ω)) * pinvR (Qᵀ * Matrix.of (Ψ ω))) := by
    intro ω
    rw [← frobSq_transpose]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, pinvL_transpose,
      Matrix.mul_assoc]
  have h2 : ∀ ω, frobSq (pinvL ((Matrix.of (Ψ ω))ᵀ * Q)) =
      frobSq (pinvR (Qᵀ * Matrix.of (Ψ ω))) := by
    intro ω
    rw [← frobSq_transpose, pinvL_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [ae_isUnit_block hΨ Q hQ (by omega)] with ω h
    rwa [gram_transpose_mul_eq]
  · simp_rw [h2]
    exact integral_pinvR_block hΨ Q hQ hqs
  · simp_rw [h1]
    exact integrable_frobSq_mul_gaussian_mul_of_indepFun
      (X := fun ω => Matrix.of.symm (Qᵀ * Matrix.of (Ψ ω)))
      (Y := fun ω => Matrix.of.symm (Qpᵀ * Matrix.of (Ψ ω)))
      ((measurable_block Q).comp_aemeasurable (aemeasurable_of_map_eq_gaussianMatrix hΨ))
      (map_block_eq_gaussianMatrix hΨ Qp hQp) (indepFun_block_of_map_eq hΨ Q Qp hQ hQp hQQp)
      Bᵀ (T := fun x => pinvR (Matrix.of x)) measurable_pinvR_entry
      (integrable_pinvR_block hΨ Q hQ hqs)

/-- `completion_reduction_gaussian` together with integrability of the error
`‖A − Q(ΨᵀQ)†ΨᵀA‖_F²`. Chen–Persson, Lemma `lem:completion`. Atlas `gn-expected-error`
(uses `gaussian-conditioning`, `pinv-frob-moment`, `sketched-regression`). -/
theorem completion_reduction_gaussian_integrable [IsProbabilityMeasure μ] {m s q r : ℕ}
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix (Fin m) (Fin q) ℝ) (Qp : Matrix (Fin m) (Fin r) ℝ) (A : Matrix (Fin m) n ℝ)
    (hQ : HasOrthonormalCols Q) (hQp : HasOrthonormalCols Qp) (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1)
    (hq : 1 ≤ q) (hqs : q + 2 ≤ s)
    (Ψ : Ωs → Matrix (Fin m) (Fin s) ℝ)
    (hΨ : μ.map (fun ω => Matrix.of.symm (Ψ ω)) = gaussianMatrix m s) :
    Integrable (fun ω => frobSq (A - sketchedOutput Q (Ψ ω) A)) μ ∧
    ∫ ω, frobSq (A - sketchedOutput Q (Ψ ω) A) ∂μ
      = (1 + (q : ℝ) / (s - q - 1)) * frobSq (residual Q A) := by
  have hQQp := transpose_mul_eq_zero_of_completion hQ hQp hcomp
  obtain ⟨hG₁, hG₁m, hGi⟩ :=
    completion_gaussian_inputs hΨ Q Qp hQ hQp hQQp (Qpᵀ * residual Q A) hqs
  have hG₂ := completion_inverse_moment_factor hΨ Q Qp hQ hQp hQQp (Qpᵀ * residual Q A)
  refine ⟨?_, completion_reduction Q Qp A hQ hQp hcomp hq hqs Ψ hG₁ hG₂ hG₁m hGi⟩
  refine ((integrable_const (frobSq (residual Q A))).add hGi).congr ?_
  filter_upwards [hG₁] with ω h
  exact (frobSq_error Q Qp (Ψ ω) A hQ hcomp h).symm

/-- **Exact Gaussian completion** (Chen–Persson, Lemma `lem:completion`; Tropp–Webber 2023, proof
of Thm 5.1). Fixed `Q` (orthonormal columns, `q ≥ 1`), an orthogonal completion `Qp`
(`QQᵀ + QpQpᵀ = I`), fixed `A`, and `Ψ` an `m × s` standard Gaussian matrix with `s ≥ q + 2`:
`E‖A − Q(ΨᵀQ)†ΨᵀA‖_F² = (1 + q/(s−q−1)) ‖(I − QQᵀ)A‖_F²`.
`completion_reduction` with `hG₁`, `hG₂`, `hG₁m`, `hGi` discharged; no hypothesis remains.
Deviation from `completion_reduction`: the row type is `Fin m` (Gaussian law convention).
Atlas `gn-expected-error` (uses `gaussian-conditioning`, `pinv-frob-moment`,
`gaussian-full-rank-ae`, `sketched-regression`). -/
theorem completion_reduction_gaussian [IsProbabilityMeasure μ] {m s q r : ℕ}
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix (Fin m) (Fin q) ℝ) (Qp : Matrix (Fin m) (Fin r) ℝ) (A : Matrix (Fin m) n ℝ)
    (hQ : HasOrthonormalCols Q) (hQp : HasOrthonormalCols Qp) (hcomp : Q * Qᵀ + Qp * Qpᵀ = 1)
    (hq : 1 ≤ q) (hqs : q + 2 ≤ s)
    (Ψ : Ωs → Matrix (Fin m) (Fin s) ℝ)
    (hΨ : μ.map (fun ω => Matrix.of.symm (Ψ ω)) = gaussianMatrix m s) :
    ∫ ω, frobSq (A - sketchedOutput Q (Ψ ω) A) ∂μ
      = (1 + (q : ℝ) / (s - q - 1)) * frobSq (residual Q A) :=
  (completion_reduction_gaussian_integrable Q Qp A hQ hQp hcomp hq hqs Ψ hΨ).2

/-- **Orthonormal complement.** A matrix `Q` with orthonormal columns has a complement `Qp` with
orthonormal columns and `QQᵀ + QpQpᵀ = I` (here `Qp` has `m − q` columns). From
`exists_orthogonal_completion`. Atlas `orthonormal-completion` (helper; belongs in
`Gaussian/Invariance.lean` or `Matrix/Projections.lean`). -/
theorem exists_orthonormal_complement {m q : ℕ} (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : HasOrthonormalCols Q) :
    ∃ r : ℕ, ∃ Qp : Matrix (Fin m) (Fin r) ℝ,
      HasOrthonormalCols Qp ∧ Q * Qᵀ + Qp * Qpᵀ = 1 := by
  have hqm : q ≤ m := by simpa using card_le_of_transpose_mul_self_eq_one Q hQ
  obtain ⟨r, rfl⟩ : ∃ r, m = q + r := ⟨m - q, by omega⟩
  obtain ⟨W, hW, hWQ⟩ := exists_orthogonal_completion Q hQ (Fin.castAddEmb r)
  have hWW : W * Wᵀ = 1 := mul_eq_one_comm.mp hW
  refine ⟨r, Matrix.of fun i j => W i (Fin.natAdd q j), ?_, ?_⟩
  · ext a b
    have := congrFun (congrFun hW (Fin.natAdd q a)) (Fin.natAdd q b)
    simpa [Matrix.mul_apply, Matrix.one_apply, Fin.natAdd_inj] using this
  · ext a b
    have := congrFun (congrFun hWW a) b
    rw [Matrix.mul_apply, Fin.sum_univ_add] at this
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [← this]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.transpose_apply]
    rw [← hWQ a j, ← hWQ b j]
    rfl

end Completion

section Measurability

/-- Entries of `pinvL (f z)` are measurable when the entries of `f` are. Atlas
`gn-expected-error` (measurability helper). -/
theorem measurable_pinvL_entry_of {γ a b : Type*} [MeasurableSpace γ] [Fintype a] [Fintype b]
    [DecidableEq b] {f : γ → Matrix a b ℝ} (hf : ∀ i j, Measurable fun z => f z i j)
    (i : b) (j : a) : Measurable fun z => pinvL (f z) i j := by
  have hF : Measurable fun z => (fun i j => f z i j : a → b → ℝ) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hf i j
  have hc : Continuous fun G : a → b → ℝ => (Matrix.of G)ᵀ * Matrix.of G :=
    continuous_id.matrix_transpose.matrix_mul continuous_id
  have hdet : Measurable fun z => ((f z)ᵀ * f z).det := hc.matrix_det.measurable.comp hF
  have hadj : ∀ a' b', Measurable fun z => ((f z)ᵀ * f z).adjugate a' b' := fun a' b' =>
    (hc.matrix_adjugate.matrix_elem a' b').measurable.comp hF
  simp only [pinvL, Matrix.mul_apply, Matrix.transpose_apply, Matrix.inv_def,
    Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun l _ => ?_
  have h1 := hadj i l
  have h2 := hf j l
  fun_prop

/-- Entries of a product of entrywise-measurable matrix maps are measurable. Atlas
`gn-expected-error` (measurability helper). -/
theorem measurable_mul_entry_of {γ a b c : Type*} [MeasurableSpace γ] [Fintype b]
    {f : γ → Matrix a b ℝ} {g : γ → Matrix b c ℝ} (hf : ∀ i j, Measurable fun z => f z i j)
    (hg : ∀ i j, Measurable fun z => g z i j) (i : a) (j : c) :
    Measurable fun z => (f z * g z) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun l _ => (hf i l).mul (hg l j)

/-- `z ↦ ‖A − Q(z)(Ψ(z)ᵀQ(z))†Ψ(z)ᵀA‖_F²` is measurable for entrywise-measurable `Q`, `Ψ`.
Atlas `gn-expected-error` (measurability helper). -/
theorem measurable_frobSq_sub_sketchedOutput {γ ι : Type*} [MeasurableSpace γ] [Fintype ι]
    [DecidableEq ι] {m s q : ℕ} (A : Matrix (Fin m) ι ℝ) {Qf : γ → Matrix (Fin m) (Fin q) ℝ}
    {Ψf : γ → Matrix (Fin m) (Fin s) ℝ} (hQ : ∀ i j, Measurable fun z => Qf z i j)
    (hΨ : ∀ i j, Measurable fun z => Ψf z i j) :
    Measurable fun z => frobSq (A - sketchedOutput (Qf z) (Ψf z) A) := by
  have hΨt : ∀ i j, Measurable fun z => (Ψf z)ᵀ i j := fun i j => hΨ j i
  have hA : ∀ i j, Measurable fun _ : γ => A i j := fun _ _ => measurable_const
  have hG := measurable_mul_entry_of hΨt hQ
  have hP := measurable_pinvL_entry_of hG
  have hB := measurable_mul_entry_of hΨt hA
  have hC := measurable_mul_entry_of hP hB
  have hD := measurable_mul_entry_of hQ hC
  refine measurable_frobSq_of_entries fun i j => ?_
  simp only [sketchedOutput, sketchedCore, Matrix.sub_apply]
  exact measurable_const.sub (hD i j)

/-- `z ↦ ‖(I − Q(z)Q(z)ᵀ)A‖_F²` is measurable for entrywise-measurable `Q`. Atlas
`gn-expected-error` (measurability helper). -/
theorem measurable_frobSq_residual_of {γ ι : Type*} [MeasurableSpace γ] [Fintype ι]
    {m q : ℕ} (A : Matrix (Fin m) ι ℝ) {Qf : γ → Matrix (Fin m) (Fin q) ℝ}
    (hQ : ∀ i j, Measurable fun z => Qf z i j) :
    Measurable fun z => frobSq (residual (Qf z) A) := by
  have hQt : ∀ i j, Measurable fun z => (Qf z)ᵀ i j := fun i j => hQ j i
  have hA : ∀ i j, Measurable fun _ : γ => A i j := fun _ _ => measurable_const
  have hD := measurable_mul_entry_of hQ (measurable_mul_entry_of hQt hA)
  refine measurable_frobSq_of_entries fun i j => ?_
  simp only [residual, Matrix.sub_apply]
  exact measurable_const.sub (hD i j)

end Measurability

section GN

variable {Ωs : Type*} [MeasurableSpace Ωs] {μ : Measure Ωs} [IsProbabilityMeasure μ]
variable {m n k r r' t s q : ℕ}

/-- `completion_reduction_gaussian` on the canonical space (`Ψ = Matrix.of` under
`gaussianMatrix m s`) with the orthogonal completion chosen internally, plus integrability:
the per-`Ω` inner integral in the conditioning step of `thm:GN`. Chen–Persson,
`lem:completion`. Atlas `gn-expected-error` (uses `orthonormal-completion`). -/
theorem completion_gaussian_of_orthonormal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix (Fin m) (Fin q) ℝ) (A : Matrix (Fin m) ι ℝ) (hQ : HasOrthonormalCols Q)
    (hq : 1 ≤ q) (hqs : q + 2 ≤ s) :
    Integrable (fun y => frobSq (A - sketchedOutput Q (Matrix.of y) A)) (gaussianMatrix m s) ∧
    ∫ y, frobSq (A - sketchedOutput Q (Matrix.of y) A) ∂gaussianMatrix m s
      = (1 + (q : ℝ) / (s - q - 1)) * frobSq (residual Q A) := by
  obtain ⟨r, Qp, hQp, hcomp⟩ := exists_orthonormal_complement Q hQ
  exact completion_reduction_gaussian_integrable (μ := gaussianMatrix m s) Q Qp A hQ hQp hcomp
    hq hqs (fun y => Matrix.of y) Measure.map_id

/-- **Generalized Nyström with Gaussian sketches** (Chen–Persson, Theorem `thm:GN`; Tropp–Webber
2023, Thm 5.1). `Ω` (`n × t`) and `Ψ` (`m × s`) independent standard Gaussian matrices,
`t ≥ k + 2`, `s ≥ t + 2`; `Q ω = Qf(Ω ω)` with `q ≤ t` columns, `q ≥ 1`, `Qf` entrywise
measurable, a.s. orthonormal columns and `range(AΩ) ⊆ range(Q)` (the user's choice of
`orth(AΩ)`). Output `Â = Q(ΨᵀQ)†ΨᵀA`:
`E‖A − Â‖_F² ≤ (1 + t/(s−t−1)) (1 + k/(t−k−1)) ‖A − ⟦A⟧ₖ‖_F²`.
`gn_main` with every Gaussian and integrability hypothesis discharged: `hcond` by Fubini for
independent variables (`lintegral_of_indepFun`) and `completion_gaussian_of_orthonormal` for
each fixed `Ω`; `hYi` from `‖(I − QQᵀ)A‖_F ≤ ‖A‖_F`.
Deviations: row index types `Fin m`, `Fin n`; `q` fixed (see `RSVD.lean`); `Q` must factor
measurably through `Ω` (`hQ`, `hQf`), needed to apply Fubini.
Atlas `gn-expected-error` (uses `rsvd-expected-error`, `gaussian-conditioning`,
`pinv-frob-moment`, `gaussian-full-rank-ae`, `sketched-regression`,
`orthonormal-completion`, `hmt-9-1-frobenius`). -/
theorem gn_main_gaussian
    {A : Matrix (Fin m) (Fin n) ℝ} {U₁ : Matrix (Fin m) (Fin k) ℝ}
    {U₂ : Matrix (Fin m) (Fin r) ℝ} {V₁ : Matrix (Fin n) (Fin k) ℝ}
    {V₂ : Matrix (Fin n) (Fin r') ℝ} {S₁ : Matrix (Fin k) (Fin k) ℝ}
    {S₂ : Matrix (Fin r) (Fin r') ℝ}
    (hA : A = U₁ * S₁ * V₁ᵀ + U₂ * S₂ * V₂ᵀ) (hU₂ : HasOrthonormalCols U₂)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (hV : V₁ᵀ * V₂ = 0)
    (hkt : k + 2 ≤ t) (hts : t + 2 ≤ s) (hqt : q ≤ t) (hq : 1 ≤ q)
    (Ω : Ωs → Matrix (Fin n) (Fin t) ℝ) (Ψ : Ωs → Matrix (Fin m) (Fin s) ℝ)
    (hΩ : μ.map (fun ω => Matrix.of.symm (Ω ω)) = gaussianMatrix n t)
    (hΨ : μ.map (fun ω => Matrix.of.symm (Ψ ω)) = gaussianMatrix m s)
    (hind : IndepFun (fun ω => Matrix.of.symm (Ω ω)) (fun ω => Matrix.of.symm (Ψ ω)) μ)
    (Q : Ωs → Matrix (Fin m) (Fin q) ℝ) (Qf : (Fin n → Fin t → ℝ) → Matrix (Fin m) (Fin q) ℝ)
    (hQf : ∀ i j, Measurable fun x => Qf x i j) (hQ : ∀ ω, Q ω = Qf (Matrix.of.symm (Ω ω)))
    (hQo : ∀ᵐ ω ∂μ, HasOrthonormalCols (Q ω))
    (hQr : ∀ᵐ ω ∂μ, Q ω * ((Q ω)ᵀ * (A * Ω ω)) = A * Ω ω) :
    ∫ ω, frobSq (A - sketchedOutput (Q ω) (Ψ ω) A) ∂μ
      ≤ (1 + (t : ℝ) / (s - t - 1)) * ((1 + (k : ℝ) / (t - k - 1)) * frobSq S₂) := by
  have hQ' : Q = fun ω => Qf (Matrix.of.symm (Ω ω)) := funext hQ
  subst hQ'
  obtain ⟨hunit, hinv, hZi⟩ := rsvd_gaussian_inputs S₂ hV₁ hV₂ hV hkt Ω hΩ
  have hqs : q + 2 ≤ s := by omega
  have hc0 : 0 ≤ 1 + (q : ℝ) / (s - q - 1) := by
    have : (q : ℝ) + 2 ≤ s := by exact_mod_cast hqs
    have : 0 ≤ (q : ℝ) / (s - q - 1) := div_nonneg (Nat.cast_nonneg q) (by linarith)
    linarith
  have hXm : AEMeasurable (fun ω => Matrix.of.symm (Ω ω)) μ :=
    aemeasurable_of_map_eq_gaussianMatrix hΩ
  have hYm : AEMeasurable (fun ω => Matrix.of.symm (Ψ ω)) μ :=
    aemeasurable_of_map_eq_gaussianMatrix hΨ
  have hres : Measurable fun x => frobSq (residual (Qf x) A) :=
    measurable_frobSq_residual_of A hQf
  have hYi : Integrable (fun ω => frobSq (residual (Qf (Matrix.of.symm (Ω ω))) A)) μ := by
    refine (integrable_const (frobSq A)).mono' (hres.comp_aemeasurable hXm).aestronglyMeasurable ?_
    filter_upwards [hQo] with ω h
    rw [Real.norm_of_nonneg (frobSq_nonneg _)]
    exact frobSq_residual_le h A
  have hgm : Measurable fun p : (Fin n → Fin t → ℝ) × (Fin m → Fin s → ℝ) =>
      frobSq (A - sketchedOutput (Qf p.1) (Matrix.of p.2) A) :=
    measurable_frobSq_sub_sketchedOutput A (fun i j => (hQf i j).comp measurable_fst)
      (fun i j => by simp only [Matrix.of_apply]; fun_prop)
  have hL : ∫⁻ ω, ENNReal.ofReal
        (frobSq (A - sketchedOutput (Qf (Matrix.of.symm (Ω ω))) (Ψ ω) A)) ∂μ
      = ∫⁻ ω, ENNReal.ofReal ((1 + (q : ℝ) / (s - q - 1))
          * frobSq (residual (Qf (Matrix.of.symm (Ω ω))) A)) ∂μ := by
    refine (lintegral_of_indepFun hXm hYm hind
      (g := fun x y => ENNReal.ofReal (frobSq (A - sketchedOutput (Qf x) (Matrix.of y) A)))
      (ENNReal.measurable_ofReal.comp hgm).aemeasurable).trans ?_
    rw [hΨ, lintegral_map' ?_ hXm]
    · apply lintegral_congr_ae
      filter_upwards [hQo] with ω hω
      obtain ⟨hi, hv⟩ := completion_gaussian_of_orthonormal (s := s) _ A hω hq hqs
      rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => frobSq_nonneg _), hv]
    · exact (Measurable.lintegral_prod_right' (ENNReal.measurable_ofReal.comp hgm)).aemeasurable
  have hcond : ∫ ω, frobSq (A - sketchedOutput (Qf (Matrix.of.symm (Ω ω))) (Ψ ω) A) ∂μ
      = ∫ ω, (1 + (q : ℝ) / (s - q - 1))
          * frobSq (residual (Qf (Matrix.of.symm (Ω ω))) A) ∂μ := by
    have hLm : AEStronglyMeasurable
        (fun ω => frobSq (A - sketchedOutput (Qf (Matrix.of.symm (Ω ω))) (Ψ ω) A)) μ :=
      (hgm.comp_aemeasurable (hXm.prodMk hYm)).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => frobSq_nonneg _) hLm,
      integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun _ => mul_nonneg hc0 (frobSq_nonneg _))
        (hYi.const_mul _).aestronglyMeasurable, hL]
  exact gn_main hA hU₂ hV₁ hV₂ hV hkt hts hqt Ω Ψ _ hQo hQr hunit hinv hcond hYi hZi

end GN

end NLAlib

end
