import NLAlib.Concentration.Matrix.Defs.Ch8Entropy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Proposition 8.4.8 — Logarithm is operator concave

Main declaration: `NLAlib.operatorConvexOn_neg_log`.

Atlas: `operator-monotone-convex`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Proposition 8.4.8, printed pp. 130–131.
-/
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NLAlib
set_option autoImplicit false

/-- The logarithm is operator concave on `(0, ∞)`, i.e. `-log` is operator convex there.

Tropp 2015, Prop. 8.4.8. Atlas: `operator-monotone-convex`. Ported from the Prove2me mission *An
Introduction to Matrix Concentration Inequalities, Ch 8*. -/
theorem NLAlib.operatorConvexOn_neg_log :
    OperatorConvexOn (Set.Ioi 0) (fun x => -Real.log x) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro d hd A H hA hH hAsp hHsp t ht₀ ht₁
  have hAp : IsStrictlyPositive A :=
    CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr
      ⟨hA, hAsp⟩
  have hHp : IsStrictlyPositive H :=
    CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mpr
      ⟨hH, hHsp⟩
  have hc := CFC.concaveOn_log.2 hAp hHp ht₀ (sub_nonneg.mpr ht₁)
    (show t + (1 - t) = 1 by ring)
  change cfc (fun x => -Real.log x) (t • A + (1 - t) • H) ≤
    t • cfc (fun x => -Real.log x) A + (1 - t) • cfc (fun x => -Real.log x) H
  simp only [cfc_neg, smul_neg, ← neg_add]
  exact neg_le_neg hc
