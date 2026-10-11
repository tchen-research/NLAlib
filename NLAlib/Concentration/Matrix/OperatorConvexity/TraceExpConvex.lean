import NLAlib.Concentration.Matrix.OperatorConvexity.VariationalTraceExp
import Mathlib.Analysis.Convex.Jensen

/-!
# Convexity of the Hermitian trace exponential

The proved Gibbs variational formula expresses the trace exponential as the
greatest of affine scores. This gives finite Jensen without differentiating
matrix eigenvectors. Supports operator re-derivation `sh:convex-sampling`.
-/

noncomputable section
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
namespace NLAlib

/-- Hermitian matrices form a convex real set.
Source: closure under real scalar linear combinations; supports `srht-ose`. -/
theorem convex_set_isHermitian {d : ℕ} :
    Convex ℝ {H : Matrix (Fin d) (Fin d) ℂ | H.IsHermitian} := by
  intro H hH K hK a b ha hb _
  exact (hH.smul (.of_nonneg ha)).add (hK.smul (.of_nonneg hb))

/-- The Hermitian trace exponential is convex, using the actual proved
variational formula, with no convexity hypothesis on this function.
Source: Tropp 2015, Equation 8.1.2; operator re-derivation `sh:convex-sampling`. -/
theorem convexOn_traceExp_isHermitian {d : ℕ} [NeZero d] :
    ConvexOn ℝ {H : Matrix (Fin d) (Fin d) ℂ | H.IsHermitian} traceExp := by
  have hlog : matrixLog (1 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
    simp [matrixLog]
  have hvar : ∀ H : Matrix (Fin d) (Fin d) ℂ, H.IsHermitian →
      IsGreatest {r : ℝ | ∃ T : Matrix (Fin d) (Fin d) ℂ,
        T.PosDef ∧ r = (T * H).trace.re + (1 : Matrix (Fin d) (Fin d) ℂ).trace.re -
          relativeEntropy T 1} (traceExp H) := by
    intro H hH
    simpa only [hlog, add_zero] using
      isGreatest_variational_traceExp H 1 hH Matrix.PosDef.one
  refine ⟨convex_set_isHermitian, ?_⟩
  intro H hH K hK a b ha hb hab
  have hM : (a • H + b • K).IsHermitian :=
    (hH.smul (.of_nonneg ha)).add (hK.smul (.of_nonneg hb))
  obtain ⟨T, hT, hscore⟩ := (hvar (a • H + b • K) hM).1
  have hHscore := (hvar H hH).2 ⟨T, hT, rfl⟩
  have hKscore := (hvar K hK).2 ⟨T, hT, rfl⟩
  have heq : (T * (a • H + b • K)).trace.re +
      (1 : Matrix (Fin d) (Fin d) ℂ).trace.re - relativeEntropy T 1 =
      a * ((T * H).trace.re + (1 : Matrix (Fin d) (Fin d) ℂ).trace.re - relativeEntropy T 1) +
      b * ((T * K).trace.re + (1 : Matrix (Fin d) (Fin d) ℂ).trace.re - relativeEntropy T 1) := by
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
      Complex.add_re, Complex.smul_re, smul_eq_mul]
    have hc : (a + b) * ((1 : Matrix (Fin d) (Fin d) ℂ).trace.re - relativeEntropy T 1) =
        (1 : Matrix (Fin d) (Fin d) ℂ).trace.re - relativeEntropy T 1 := by rw [hab, one_mul]
    nlinarith only [hc]
  rw [hscore, heq]
  exact add_le_add (mul_le_mul_of_nonneg_left hHscore ha) (mul_le_mul_of_nonneg_left hKscore hb)

end NLAlib
