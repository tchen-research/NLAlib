import NLAlib.RandomMatrix.Covariance.FourthMomentLower

/-!
# Success probability for the fourth-moment covariance lower bound

The failure-event estimate is expressed as the positive success probability
in the source. The actual iid law supplies null measurability of the event.
Source: Tropp (2026), Theorem 3.3.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder
namespace NLAlib

variable {Ω d : Type*} [MeasurableSpace Ω] [Fintype d] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
/-- With the exact sample-size constant 26, actual iid observations preserve
their positive-definite second moment from below with probability at least
`1 - δ`, assuming only finite fourth moments and directional fourth-moment
variance control. Source: Tropp (2026), Theorem 3.3.
atlas: sample-covariance-fourth-moment-lower -/
theorem one_sub_le_measureReal_smul_le_sampleCovariance_of_hasLaw
    {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} (W : Fin N → Ω → d → ℝ)
    (μ : Measure (d → ℝ)) [IsProbabilityMeasure μ]
    (hW : ∀ i, HasLaw (W i) μ P) (hind : iIndepFun W P)
    (hd : 2 ≤ Fintype.card d)
    (hμ : MemLp (id : (d → ℝ) → d → ℝ) 4 μ)
    (K : Matrix d d ℝ) (hK : K.PosDef)
    (hsecond : (∫ x, vecMulVec x x ∂μ) = K)
    {β ε δ : ℝ} (hβ : 1 ≤ β)
    (hfourth : ∀ a : d → ℝ,
      Var[fun x => (x ⬝ᵥ a) ^ 2; μ] ≤ β ^ 2 * (∫ x, (x ⬝ᵥ a) ^ 2 ∂μ) ^ 2)
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsize : 26 * β ^ 2 * max (Fintype.card d : ℝ)
      (Real.log ((Fintype.card d : ℝ) / δ)) / ε ^ 2 ≤ (N : ℝ)) :
    1 - δ ≤ P.real {ω | (1 - ε) • K ≤ sampleCovariance (fun i => W i ω)} := by
  have hfailure := measureReal_not_smul_le_sampleCovariance_le_of_hasLaw
    W μ hW hind hd hμ K hK hsecond hβ hfourth hε hε1 hδ hδ1 hsize
  have hpi := hind.hasLaw_pi hW
  have hcont : Continuous (sampleCovariance : (Fin N → d → ℝ) → Matrix d d ℝ) := by
    change Continuous (fun x : Fin N → d → ℝ =>
      (Fintype.card (Fin N) : ℝ)⁻¹ • ∑ i, vecMulVec (x i) (star (x i)))
    fun_prop
  have hset : MeasurableSet {x : Fin N → d → ℝ |
      (1 - ε) • K ≤ sampleCovariance x} :=
    ((isClosed_setOf_le_realMatrix ((1 - ε) • K)).preimage hcont).measurableSet
  have hnull : NullMeasurableSet
      {ω | (1 - ε) • K ≤ sampleCovariance (fun i => W i ω)} P :=
    hpi.aemeasurable.nullMeasurableSet_preimage hset
  have he : P.real {ω | ¬ ((1 - ε) • K ≤ sampleCovariance (fun i => W i ω))} =
      1 - P.real {ω | (1 - ε) • K ≤ sampleCovariance (fun i => W i ω)} :=
    probReal_compl_eq_one_sub₀ hnull
  rw [he] at hfailure
  linarith

end NLAlib
