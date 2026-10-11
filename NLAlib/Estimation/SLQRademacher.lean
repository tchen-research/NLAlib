import NLAlib.Estimation.SLQ

/-!
# Stochastic Lanczos quadrature with Rademacher probes

The deterministic degree-`2q-1` quadrature error and the established Hutchinson tail give
the general trace-estimation bound with the exact Hanson–Wright constant `1/(256e²)`.
The polynomial approximation premise remains explicit; concrete analytic and Lipschitz rates
belong to their scalar approximation files. Atlas `slq-error` (general transfer).
-/

noncomputable section

open scoped Matrix
open MeasureTheory ProbabilityTheory Real
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω n κ r : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ] [Fintype r] [DecidableEq r]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- A Rademacher variable has square one almost everywhere.
Source: Hutchinson 1989; helper for the general SLQ bound in `slq-error`. -/
theorem ae_sq_eq_one_of_isRademacher {g : Ω → ℝ} (hlaw : IsRademacher μ g) :
    ∀ᵐ ω ∂μ, g ω ^ 2 = 1 := by
  have hg := aemeasurable_of_isRademacher hlaw
  have hS : MeasurableSet {x : ℝ | x = 1 ∨ x = -1} :=
    (measurableSet_singleton 1).union (measurableSet_singleton (-1))
  have hpm : ∀ᵐ ω ∂μ, g ω = 1 ∨ g ω = -1 := by
    unfold IsRademacher at hlaw
    rw [← ae_map_iff hg hS]
    rw [hlaw, ae_add_measure_iff]
    constructor
    · exact Measure.ae_smul_measure ((ae_dirac_iff hS).2 (Or.inl rfl)) _
    · exact Measure.ae_smul_measure ((ae_dirac_iff hS).2 (Or.inr rfl)) _
  exact hpm.mono fun ω h => by rcases h with h | h <;> simp [h]

omit [DecidableEq κ] [IsProbabilityMeasure μ] in
/-- The average squared norm of Rademacher probes equals the ambient dimension almost surely.
Source: Ubaru–Chen–Saad 2017, Lemma 4.2; helper for `slq-error`. -/
theorem ae_hutchinsonEstimate_one_eq_card_of_isRademacher {G : Ω → n → κ → ℝ}
    (hlaw : ∀ e : n × κ, IsRademacher μ (fun ω => G ω e.1 e.2)) :
    ∀ᵐ ω ∂μ, hutchinsonEstimate (1 : Matrix n n ℝ) (G ω) = Fintype.card n := by
  have hsq : ∀ᵐ ω ∂μ, ∀ e : n × κ, G ω e.1 e.2 ^ 2 = 1 :=
    (ae_all_iff).mpr fun e => ae_sq_eq_one_of_isRademacher (hlaw e)
  filter_upwards [hsq] with ω hω
  rw [hutchinsonEstimate_one]
  have hn : ∀ k : κ, (fun i => G ω i k) ⬝ᵥ (fun i => G ω i k) = Fintype.card n := by
    intro k
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
Source: Ubaru–Chen–Saad 2017, Theorem 4.1; Chen–Trogdon–Ubaru 2021, Lemma 2.2;
operator rederivations equation `rt:slq-tail`. The approximation is an explicit premise;
the constant comes from NLAlib's proved Hanson–Wright inequality.
atlas: slq-error (partial) -/
theorem measure_abs_slqEstimate_sub_trace_gt_le_of_rademacher {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {G : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => G ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsRademacher μ (fun ω => G ω e.1 e.2))
    {Q : Ω → κ → Matrix n r ℝ} (hQ : ∀ ω k, HasOrthonormalCols (Q ω k))
    {q : ℕ} (hK : ∀ ω k, krylovSpace A (fun i => G ω i k) q ≤ LinearMap.range (Q ω k).mulVecLin)
    {f : ℝ → ℝ} {p : Polynomial ℝ} (hp : p.degree < 2 * q) {a c E : ℝ}
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a c)
    (hfp : ∀ x ∈ Set.Icc a c, |f x - p.eval x| ≤ E) {η : ℝ} (hη : 0 ≤ η) :
    (μ {ω | η + 2 * (Fintype.card n : ℝ) * E <
      |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|}).toReal ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (Fintype.card κ * η ^ 2 / frobNorm (cfc f A) ^ 2)
          (Fintype.card κ * η / specNorm (cfc f A))) := by
  have hnorm := ae_hutchinsonEstimate_one_eq_card_of_isRademacher hlaw
  have hsub : ∀ᵐ ω ∂μ, ω ∈ {ω | η + 2 * (Fintype.card n : ℝ) * E <
      |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|} →
      ω ∈ {ω | η ≤ |hutchinsonEstimate (cfc f A) (G ω) - (cfc f A).trace|} := by
    filter_upwards [hnorm] with ω hω
    intro hbad
    have hdet := abs_slqEstimate_sub_hutchinsonEstimate_le_of_degree_lt_two_mul
      hA (hQ ω) (G ω) (hK ω) hp hspec hfp
    rw [hω] at hdet
    have htri := abs_sub_le (slqEstimate A f (Q ω) (G ω))
      (hutchinsonEstimate (cfc f A) (G ω)) (cfc f A).trace
    change η + 2 * (Fintype.card n : ℝ) * E <
      |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace| at hbad
    change η ≤ |hutchinsonEstimate (cfc f A) (G ω) - (cfc f A).trace|
    nlinarith
  exact (ENNReal.toReal_mono (measure_ne_top μ _)
    (measure_mono_ae hsub)).trans
    (measure_le_abs_hutchinsonEstimate_sub_trace_le_of_rademacher (cfc f A) hind hlaw η hη)

/-- Relative-error SLQ tail for a positive semidefinite matrix function, when the explicit
polynomial approximation contributes at most half of the relative error budget.
Source: Ubaru–Chen–Saad 2017, Theorem 4.1; operator rederivations `rt:slq-relative`.
The coefficient `1024e²` is derived from the proved Hanson–Wright constant.
atlas: slq-error (partial) -/
theorem measure_abs_slqEstimate_sub_trace_gt_mul_trace_le_of_rademacher
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {f : ℝ → ℝ} (hF : (cfc f A).PosSemidef)
    (htr : 0 < (cfc f A).trace) {G : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => G ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsRademacher μ (fun ω => G ω e.1 e.2))
    {Q : Ω → κ → Matrix n r ℝ} (hQ : ∀ ω k, HasOrthonormalCols (Q ω k))
    {q : ℕ} (hK : ∀ ω k, krylovSpace A (fun i => G ω i k) q ≤ LinearMap.range (Q ω k).mulVecLin)
    {p : Polynomial ℝ} (hp : p.degree < 2 * q) {a c E : ℝ}
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a c)
    (hfp : ∀ x ∈ Set.Icc a c, |f x - p.eval x| ≤ E) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbudget : 2 * (Fintype.card n : ℝ) * E ≤ (ε / 2) * (cfc f A).trace) :
    (μ {ω | ε * (cfc f A).trace <
      |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|}).toReal ≤
      2 * exp (-(Fintype.card κ * ε ^ 2 / (1024 * exp 1 ^ 2))) := by
  have hraw := measure_abs_slqEstimate_sub_trace_gt_le_of_rademacher hA hind hlaw hQ hK
    hp hspec hfp (η := (ε / 2) * (cfc f A).trace) (by positivity)
  have hsub : {ω | ε * (cfc f A).trace <
      |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|} ⊆
      {ω | (ε / 2) * (cfc f A).trace + 2 * (Fintype.card n : ℝ) * E <
        |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|} := by
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

/-- The exact SLQ Rademacher sample budget `m ≥ 1024e² ε⁻² log(2/δ)` gives relative error
at most `ε` with failure probability at most `δ`, provided the polynomial approximation
uses at most half the deterministic error budget.
Source: operator rederivations `rt:slq-relative`; Ubaru–Chen–Saad 2017, Theorem 4.1
(NLAlib's Hanson–Wright constant).
atlas: slq-error (partial) -/
theorem measure_abs_slqEstimate_sub_trace_gt_mul_trace_le_of_card_ge_rademacher
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {f : ℝ → ℝ} (hF : (cfc f A).PosSemidef)
    (htr : 0 < (cfc f A).trace) {G : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => G ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsRademacher μ (fun ω => G ω e.1 e.2))
    {Q : Ω → κ → Matrix n r ℝ} (hQ : ∀ ω k, HasOrthonormalCols (Q ω k))
    {q : ℕ} (hK : ∀ ω k, krylovSpace A (fun i => G ω i k) q ≤ LinearMap.range (Q ω k).mulVecLin)
    {p : Polynomial ℝ} (hp : p.degree < 2 * q) {a c E : ℝ}
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a c)
    (hfp : ∀ x ∈ Set.Icc a c, |f x - p.eval x| ≤ E) {ε δ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hbudget : 2 * (Fintype.card n : ℝ) * E ≤ (ε / 2) * (cfc f A).trace)
    (hm : 1024 * exp 1 ^ 2 * log (2 / δ) / ε ^ 2 ≤ Fintype.card κ) :
    (μ {ω | ε * (cfc f A).trace <
      |slqEstimate A f (Q ω) (G ω) - (cfc f A).trace|}).toReal ≤ δ := by
  refine (measure_abs_slqEstimate_sub_trace_gt_mul_trace_le_of_rademacher
    hA hF htr hind hlaw hQ hK hp hspec hfp hε hε1 hbudget).trans ?_
  have hlog : log (2 / δ) ≤ Fintype.card κ * ε ^ 2 / (1024 * exp 1 ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hm
    linarith
  calc 2 * exp (-(Fintype.card κ * ε ^ 2 / (1024 * exp 1 ^ 2))) ≤
        2 * exp (-log (2 / δ)) := by gcongr
    _ = δ := by rw [exp_neg, exp_log (by positivity)]; field_simp

end NLAlib
