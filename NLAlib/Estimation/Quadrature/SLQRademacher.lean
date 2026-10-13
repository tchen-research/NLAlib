import NLAlib.Estimation.Quadrature.SLQ
/-!
# Stochastic Lanczos quadrature with Rademacher probes

The deterministic quadrature error (degree `< 2q`) and the Hutchinson tail give the general
SLQ trace-estimation bound with the Hanson–Wright constant `1/(256e²)`. The polynomial
approximation is an explicit hypothesis here; the Lipschitz and analytic rates are in
`SLQLipschitz`, `SLQAnalytic`. Atlas: `slq-error`.
These are bounds for supplied orthonormal compression frames containing `K_q`.
The parameter `q` is an approximation order; no relation between the frame column count
and `q`, construction algorithm, or matvec cost is asserted.
-/

noncomputable section

open scoped Matrix
open MeasureTheory ProbabilityTheory Real

namespace NLAlib

variable {Ω n κ r : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ] [Fintype r] [DecidableEq r]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq κ] [IsProbabilityMeasure μ] in
/-- The average squared norm of Rademacher probes equals the ambient dimension almost surely:
`tr_m(I) = n` a.s. Source: Ubaru–Chen–Saad (2017) [`ucs17`], Lem. 4.2. Helper for `slq-error`. -/
theorem ae_hutchinsonEstimate_one_eq_card_of_hasLaw_rademacherVector {G : Ω → Matrix n κ ℝ}
    (hG : HasLaw (fun ω (e : n × κ) => G ω e.1 e.2) (rademacherVector (n × κ)) μ) :
    ∀ᵐ ω ∂μ, hutchinsonEstimate (1 : Matrix n n ℝ) (G ω) = Fintype.card n := by
  have hsq : ∀ᵐ ω ∂μ, ∀ e : n × κ, G ω e.1 e.2 ^ 2 = 1 :=
    (ae_all_iff).mpr fun e =>
      (ae_eq_one_or_neg_one_of_hasLaw_rademacherMeasure (hG.hasLaw_eval_rademacherMeasure e)).mono
        fun ω h => by rcases h with h | h <;> simp [h]
  filter_upwards [hsq] with ω hω
  rw [hutchinsonEstimate_one]
  have hn : ∀ k : κ, ‖WithLp.toLp 2 (fun i => G ω i k)‖ ^ 2 = Fintype.card n := by
    intro k
    rw [norm_toLp_sq_eq_dotProduct_self]
    change (∑ i : n, G ω i k * G ω i k) = Fintype.card n
    simp_rw [← sq]
    calc (∑ i : n, G ω i k ^ 2) = ∑ _i : n, (1 : ℝ) :=
        Finset.sum_congr rfl (fun i _ => hω (i, k))
      _ = Fintype.card n := by simp
  simp only [hn, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast Fintype.card_ne_zero (α := κ))

/-- General SLQ tail for independent Rademacher probes, using a polynomial approximant of
degree below `2q` and uniform error `E`: the error threshold is `η+2nE` and the tail is
`2 exp(-(m/(256e²)) min(η²/‖f(A)‖_F²,η/‖f(A)‖))`.
Source: Ubaru–Chen–Saad (2017) [`ucs17`], Thm 4.1; Chen–Trogdon–Ubaru (2021) [`ctu21`], Lem. 2.2. The approximation is an explicit premise;
the constant comes from NLAlib's proved Hanson–Wright inequality.
atlas: slq-error (partial) -/
theorem measureReal_abs_compressionQuadratureEstimate_sub_trace_gt_le_of_hasLaw_rademacherVector {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {G : Ω → Matrix n κ ℝ}
    (hG : HasLaw (fun ω (e : n × κ) => G ω e.1 e.2) (rademacherVector (n × κ)) μ)
    {Q : Ω → κ → Matrix n r ℝ} (hQ : ∀ ω k, HasOrthonormalCols (Q ω k))
    {q : ℕ} (hK : ∀ ω k, krylovSpace A (fun i => G ω i k) q ≤ LinearMap.range (Q ω k).mulVecLin)
    {f : ℝ → ℝ} {p : Polynomial ℝ} (hp : p.degree < 2 * q) {a c E : ℝ}
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a c)
    (hfp : ∀ x ∈ Set.Icc a c, |f x - p.eval x| ≤ E) {η : ℝ} (hη : 0 ≤ η) :
    μ.real {ω | η + 2 * (Fintype.card n : ℝ) * E <
      |compressionQuadratureEstimate A f (G ω) (Q ω) - (cfc f A).trace|} ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (Fintype.card κ * η ^ 2 / frobNorm (cfc f A) ^ 2)
          (Fintype.card κ * η / specNorm (cfc f A))) := by
  have hnorm := ae_hutchinsonEstimate_one_eq_card_of_hasLaw_rademacherVector hG
  have hsub : ∀ᵐ ω ∂μ, ω ∈ {ω | η + 2 * (Fintype.card n : ℝ) * E <
      |compressionQuadratureEstimate A f (G ω) (Q ω) - (cfc f A).trace|} →
      ω ∈ {ω | η ≤ |hutchinsonEstimate (cfc f A) (G ω) - (cfc f A).trace|} := by
    filter_upwards [hnorm] with ω hω
    intro hbad
    have hdet := abs_compressionQuadratureEstimate_sub_hutchinsonEstimate_le
      hA (G ω) (hQ ω) (hK ω) hp hspec hfp
    rw [hω] at hdet
    have htri := abs_sub_le (compressionQuadratureEstimate A f (G ω) (Q ω))
      (hutchinsonEstimate (cfc f A) (G ω)) (cfc f A).trace
    change η + 2 * (Fintype.card n : ℝ) * E <
      |compressionQuadratureEstimate A f (G ω) (Q ω) - (cfc f A).trace| at hbad
    change η ≤ |hutchinsonEstimate (cfc f A) (G ω) - (cfc f A).trace|
    nlinarith
  exact (ENNReal.toReal_mono (measure_ne_top μ _)
    (measure_mono_ae hsub)).trans
    (measureReal_le_abs_hutchinsonEstimate_sub_trace_le_of_hasLaw_rademacherVector (cfc f A) hG η hη)

/-- Relative-error SLQ tail for a positive semidefinite matrix function, when the explicit
polynomial approximation contributes at most half of the relative error budget.
Source: Ubaru–Chen–Saad (2017) [`ucs17`], Thm 4.1.
The coefficient `1024e²` is derived from the Hanson–Wright constant.
atlas: slq-error (partial) -/
theorem measureReal_abs_compressionQuadratureEstimate_sub_trace_gt_mul_trace_le_of_hasLaw_rademacherVector
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {f : ℝ → ℝ} (hF : (cfc f A).PosSemidef)
    (htr : 0 < (cfc f A).trace) {G : Ω → Matrix n κ ℝ}
    (hG : HasLaw (fun ω (e : n × κ) => G ω e.1 e.2) (rademacherVector (n × κ)) μ)
    {Q : Ω → κ → Matrix n r ℝ} (hQ : ∀ ω k, HasOrthonormalCols (Q ω k))
    {q : ℕ} (hK : ∀ ω k, krylovSpace A (fun i => G ω i k) q ≤ LinearMap.range (Q ω k).mulVecLin)
    {p : Polynomial ℝ} (hp : p.degree < 2 * q) {a c E : ℝ}
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a c)
    (hfp : ∀ x ∈ Set.Icc a c, |f x - p.eval x| ≤ E) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbudget : 2 * (Fintype.card n : ℝ) * E ≤ (ε / 2) * (cfc f A).trace) :
    μ.real {ω | ε * (cfc f A).trace <
      |compressionQuadratureEstimate A f (G ω) (Q ω) - (cfc f A).trace|} ≤
      2 * exp (-(Fintype.card κ * ε ^ 2 / (1024 * exp 1 ^ 2))) := by
  have hraw := measureReal_abs_compressionQuadratureEstimate_sub_trace_gt_le_of_hasLaw_rademacherVector hA hG hQ hK
    hp hspec hfp (η := (ε / 2) * (cfc f A).trace) (by positivity)
  have hsub : {ω | ε * (cfc f A).trace <
      |compressionQuadratureEstimate A f (G ω) (Q ω) - (cfc f A).trace|} ⊆
      {ω | (ε / 2) * (cfc f A).trace + 2 * (Fintype.card n : ℝ) * E <
        |compressionQuadratureEstimate A f (G ω) (Q ω) - (cfc f A).trace|} := by
    intro ω hω
    change ε * (cfc f A).trace < _ at hω
    change (ε / 2) * (cfc f A).trace + 2 * (Fintype.card n : ℝ) * E < _
    linarith
  refine ((measureReal_mono hsub).trans hraw).trans ?_
  gcongr 2 * exp ?_
  have h := mul_sq_le_min_hutchinson_exponent_of_posSemidef (κ := κ) hF htr
    (show 0 < ε / 2 by positivity) (show ε / 2 ≤ 1 by linarith)
  have hc : (0 : ℝ) ≤ 1 / (256 * exp 1 ^ 2) := by positivity
  have hh := mul_le_mul_of_nonneg_left h hc
  rw [neg_mul, neg_le_neg_iff]
  calc Fintype.card κ * ε ^ 2 / (1024 * exp 1 ^ 2) =
      (1 / (256 * exp 1 ^ 2)) * (Fintype.card κ * (ε / 2) ^ 2) := by ring
    _ ≤ _ := hh

/-- The SLQ Rademacher sample budget `m ≥ 1024e² ε⁻² log(2/δ)` gives relative error
at most `ε` with failure probability at most `δ`, provided the polynomial approximation
uses at most half the deterministic error budget.
Source: Ubaru–Chen–Saad (2017) [`ucs17`], Thm 4.1 (with the Hanson–Wright constant).
atlas: slq-error (partial) -/
theorem measureReal_abs_compressionQuadratureEstimate_sub_trace_gt_mul_trace_le_of_hasLaw_rademacherVector_of_le_card
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {f : ℝ → ℝ} (hF : (cfc f A).PosSemidef)
    (htr : 0 < (cfc f A).trace) {G : Ω → Matrix n κ ℝ}
    (hG : HasLaw (fun ω (e : n × κ) => G ω e.1 e.2) (rademacherVector (n × κ)) μ)
    {Q : Ω → κ → Matrix n r ℝ} (hQ : ∀ ω k, HasOrthonormalCols (Q ω k))
    {q : ℕ} (hK : ∀ ω k, krylovSpace A (fun i => G ω i k) q ≤ LinearMap.range (Q ω k).mulVecLin)
    {p : Polynomial ℝ} (hp : p.degree < 2 * q) {a c E : ℝ}
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a c)
    (hfp : ∀ x ∈ Set.Icc a c, |f x - p.eval x| ≤ E) {ε δ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hbudget : 2 * (Fintype.card n : ℝ) * E ≤ (ε / 2) * (cfc f A).trace)
    (hm : 1024 * exp 1 ^ 2 * log (2 / δ) / ε ^ 2 ≤ Fintype.card κ) :
    μ.real {ω | ε * (cfc f A).trace <
      |compressionQuadratureEstimate A f (G ω) (Q ω) - (cfc f A).trace|} ≤ δ := by
  refine (measureReal_abs_compressionQuadratureEstimate_sub_trace_gt_mul_trace_le_of_hasLaw_rademacherVector
    hA hF htr hG hQ hK hp hspec hfp hε hε1 hbudget).trans ?_
  have hlog : log (2 / δ) ≤ Fintype.card κ * ε ^ 2 / (1024 * exp 1 ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hm
    linarith
  calc 2 * exp (-(Fintype.card κ * ε ^ 2 / (1024 * exp 1 ^ 2))) ≤
        2 * exp (-log (2 / δ)) := by gcongr
    _ = δ := by rw [exp_neg, exp_log (by positivity)]; field_simp

end NLAlib
