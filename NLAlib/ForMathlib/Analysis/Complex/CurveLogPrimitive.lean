import NLAlib.ForMathlib.Analysis.Complex.PrimitiveTransport
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Exact scalar forms and principal-log quotient primitives

The native path FTC follows from the checked finite-transport theorem.
A strict target-displacement bound constructs a principal-log primitive
for the difference of inverse kernels. Reuses the deferred contour archive
CurveCauchy and CurveWindingVariation, adapted to the current native API.
-/

noncomputable section
open Set Finset Filter MeasureTheory
open scoped unitInterval Topology
namespace Complex

/-- Exact-form FTC for an actual native C1 path. A one-cell instance of the
proved finite primitive transport supplies all integrability hypotheses. -/
theorem curveIntegral_eq_sub_of_hasDerivAt {a b : ℂ} (γ : Path a b)
    {U : Set ℂ} {G g : ℂ → ℂ}
    (hG : ∀ z ∈ U, HasDerivAt G (g z) z) (hg : ContinuousOn g U)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hγU : ∀ r, γ r ∈ U) :
    curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ = G b - G a := by
  have h := primitiveSubdivisionTransport_eq_curveIntegral_of_hasDerivAt γ hγ
    (n := 1) (p := fun i => (i : ℝ)) (G := fun _ => G) (U := fun _ => U)
    (fun i _ => by exact_mod_cast Nat.le_succ i) (by simp) (by simp)
    (fun i hi => by
      change 0 ≤ (i : ℝ) ∧ (i : ℝ) ≤ 1
      exact ⟨Nat.cast_nonneg i, by exact_mod_cast hi⟩)
    (fun _ _ => hG) (fun _ _ => hg) (by
      intro i hi t ht
      have hi0 : i = 0 := by omega
      subst i
      simp only [Nat.cast_zero, zero_add, Nat.cast_one] at ht
      rw [γ.extend_apply ht]
      exact hγU ⟨t, ht⟩)
  simpa [primitiveSubdivisionTransport] using h.symm

/-- A nearby avoided target also avoids every point separated by the
strict displacement bound. -/
theorem sub_ne_zero_and_sub_ne_zero_of_norm_sub_lt {u v z : ℂ} (h : ‖u - v‖ < ‖z - u‖) :
    z - u ≠ 0 ∧ z - v ≠ 0 := by
  constructor
  · intro heq
    rw [heq, norm_zero] at h
    exact (not_lt.mpr (norm_nonneg _)) h
  · intro heq
    have hz : z = v := sub_eq_zero.mp heq
    subst z
    rw [norm_sub_rev] at h
    exact (lt_irrefl _) h

/-- A principal-log quotient is an actual primitive of the difference
of two nearby inverse kernels. The slit-plane condition is proved. -/
theorem hasDerivAt_log_div_sub_of_norm_sub_lt {u v z : ℂ} (h : ‖u - v‖ < ‖z - u‖) :
    HasDerivAt (fun z => log ((z - v) / (z - u))) ((z - v)⁻¹ - (z - u)⁻¹) z := by
  obtain ⟨hu, hv⟩ := sub_ne_zero_and_sub_ne_zero_of_norm_sub_lt h
  have hlog : (z - v) / (z - u) ∈ slitPlane := by
    have heq : (z - v) / (z - u) = 1 + (u - v) / (z - u) := by
      field_simp [hu]
      ring
    rw [heq]
    apply mem_slitPlane_of_norm_lt_one
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hu)).mpr h
  have hd := (((hasDerivAt_id z).sub_const v).div ((hasDerivAt_id z).sub_const u) hu).clog hlog
  have hd' : HasDerivAt (fun z => log ((z - v) / (z - u)))
      (((1 * (z - u) - (z - v) * 1) / (z - u) ^ 2) / ((z - v) / (z - u))) z := by
    simpa only [id_eq, Pi.div_apply] using hd
  apply hd'.congr_deriv
  field_simp [hu, hv]

end Complex
