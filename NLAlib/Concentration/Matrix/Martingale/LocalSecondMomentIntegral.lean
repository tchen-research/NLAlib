import NLAlib.Concentration.Matrix.Martingale.LocalSecondMoment
import NLAlib.ForMathlib.Analysis.Matrix.QuadraticForm
import NLAlib.ForMathlib.MeasureTheory.MatrixConditionalExpectation

/-!
# Actual Bochner moments from genuine extended quadratic moment identities

Once localization supplies integrability, the original extended identities identify
matrix set integrals by complex polarization. Conditional-expectation uniqueness then
gives the actual matrix conditional second moment, rather than an assumed covariance.
-/

noncomputable section

open MeasureTheory Matrix Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

namespace NLAlib

variable {Ω n : Type*} {m mΩ : MeasurableSpace Ω} [Fintype n] [DecidableEq n] {μ : Measure Ω}

/-- Under actual integrability, the genuine extended quadratic moment identities determine
every matrix set integral. This is the complex polarization step in the supplied audit;
integrability is derived separately after localization, not imposed on the final theorem.
Source: `audit:local-moment`, `audit:combined`; atlas `matrix-freedman` (partial). -/
theorem HasLocalMatrixSecondMoment.setIntegral_sq_eq {X V : Ω → Matrix n n ℂ}
    (h : HasLocalMatrixSecondMoment μ m X V) (_hm : m ≤ mΩ)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ) (hV : Integrable V μ)
    (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (B : Set Ω) (hB : MeasurableSet[m] B) :
    (∫ ω in B, X ω ^ 2 ∂μ) = ∫ ω in B, V ω ∂μ := by
  have hXpos : ∀ᵐ ω ∂μ, (X ω ^ 2).PosSemidef := hHerm.mono fun ω hω => by
    have heq : X ω ^ 2 = (X ω)ᴴ * X ω := by rw [hω.eq, sq]
    rw [heq]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have hXI : (∫ ω in B, X ω ^ 2 ∂μ).PosSemidef :=
    (integral_nonneg_of_ae (ae_restrict_of_ae (hXpos.mono fun ω hω => hω.nonneg))).posSemidef
  have hVI : (∫ ω in B, V ω ∂μ).PosSemidef :=
    (integral_nonneg_of_ae (ae_restrict_of_ae (h.ae_posSemidef.mono fun ω hω => hω.nonneg))).posSemidef
  apply matrix_eq_of_isHermitian_of_re_dotProduct_mulVec_eq hXI.isHermitian hVI.isHermitian
  intro u
  let T := matrixRealQuadraticFormCLM u
  change T (∫ ω in B, X ω ^ 2 ∂μ) = T (∫ ω in B, V ω ∂μ)
  rw [← T.integral_comp_comm hX2.restrict, ← T.integral_comp_comm hV.restrict]
  have hqX : (fun ω => matrixVectorSqNorm (X ω) u) =ᵐ[μ] fun ω => T (X ω ^ 2) := by
    filter_upwards [hHerm] with ω hω
    exact (re_star_dotProduct_sq_mulVec_eq_sum_sq_norm_of_isHermitian _ hω u).symm
  have hX0 : 0 ≤ᵐ[μ] fun ω => T (X ω ^ 2) := by
    filter_upwards [hqX] with ω hω
    rw [← hω]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hV0 : 0 ≤ᵐ[μ] fun ω => T (V ω) :=
    h.ae_posSemidef.mono fun ω hω => hω.re_dotProduct_nonneg u
  have hExt : (∫⁻ ω in B, ENNReal.ofReal (T (X ω ^ 2)) ∂μ) =
      ∫⁻ ω in B, ENNReal.ofReal (T (V ω)) ∂μ := by
    calc
      (∫⁻ ω in B, ENNReal.ofReal (T (X ω ^ 2)) ∂μ) =
          ∫⁻ ω in B, ENNReal.ofReal (matrixVectorSqNorm (X ω) u) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_of_ae hqX] with ω hω
        rw [hω]
      _ = ∫⁻ ω in B, ENNReal.ofReal (matrixQuadraticFormReal (V ω) u) ∂μ := h.setLIntegral_eq u B hB
      _ = ∫⁻ ω in B, ENNReal.ofReal (T (V ω)) ∂μ := rfl
  have hTX := T.integrable_comp hX2
  have hTV := T.integrable_comp hV
  rw [← ofReal_integral_eq_lintegral_ofReal hTX.restrict (ae_restrict_of_ae hX0),
    ← ofReal_integral_eq_lintegral_ofReal hTV.restrict (ae_restrict_of_ae hV0)] at hExt
  have hreal := congrArg ENNReal.toReal hExt
  simpa only [ENNReal.toReal_ofReal (integral_nonneg_of_ae (ae_restrict_of_ae hX0)),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae (ae_restrict_of_ae hV0))] using hreal

/-- Once integrability is derived, the original extended local quadratic identities give
the actual Bochner conditional square. No conditional covariance equality is an input.
Source: supplied audit `audit:combined`, conditional uniqueness after polarization;
atlas `matrix-freedman` (partial). -/
theorem HasLocalMatrixSecondMoment.condExp_sq_eq_of_integrable {X V : Ω → Matrix n n ℂ}
    (h : HasLocalMatrixSecondMoment μ m X V) (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (hX2 : Integrable (fun ω => X ω ^ 2) μ) (hV : Integrable V μ)
    (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian) : μ[(fun ω => X ω ^ 2) | m] =ᵐ[μ] V := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hX2
    (fun B hB hμB => hV.integrableOn)
    (fun B hB hμB => (h.setIntegral_sq_eq hm hX2 hV hHerm B hB).symm)
  exact h.measurable.stronglyMeasurable.aestronglyMeasurable

end NLAlib
