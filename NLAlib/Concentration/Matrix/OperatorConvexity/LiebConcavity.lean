import NLAlib.Concentration.Matrix.OperatorConvexity.EntropyJointConvex
import NLAlib.Concentration.Matrix.OperatorConvexity.VariationalTraceExp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Theorem 8.1.1 — Lieb concavity

Main declaration: `NLAlib.lieb_concavity`.

Atlas: `operator-monotone-convex`.

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorems 3.4.1 and 8.1.1, printed pp. 35 and 119; proof development Chapter 8.
-/
open scoped Matrix.Norms.L2Operator ComplexOrder
open NLAlib
set_option autoImplicit false

/-- Lieb's concavity theorem: `A ↦ traceExp (H + matrixLog A)` is concave on positive definite
matrices for fixed Hermitian `H`.

Tropp 2015, Thm 8.1.1 (= Thm 3.4.1). Atlas: `operator-monotone-convex`. Ported from the Prove2me
mission *An Introduction to Matrix Concentration Inequalities, Ch 8*. -/
theorem NLAlib.lieb_concavity {d : ℕ} [NeZero d]
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix (Fin d) (Fin d) ℂ | A.PosDef}
      (fun A => traceExp (H + matrixLog A)) := by
  have hj := convexOn_relativeEntropy (d := d)
  have hc : Convex ℝ {A : Matrix (Fin d) (Fin d) ℂ | A.PosDef} := by
    intro A hA B hB a b ha hb hab
    exact (hj.1 (show (A,A) ∈ _ from ⟨hA,hA⟩)
      (show (B,B) ∈ _ from ⟨hB,hB⟩) ha hb hab).1
  refine ⟨hc, ?_⟩
  intro A hA B hB a b ha hb hab
  obtain ⟨T,hT,hTA⟩ := (isGreatest_variational_traceExp H A hH hA).1
  obtain ⟨U,hU,hUB⟩ := (isGreatest_variational_traceExp H B hH hB).1
  have hAB := hc hA hB ha hb hab
  have hTU := hc hT hU ha hb hab
  have hentropy := hj.2 (show (T,A) ∈ _ from ⟨hT,hA⟩)
    (show (U,B) ∈ _ from ⟨hU,hB⟩) ha hb hab
  change relativeEntropy (a • T + b • U) (a • A + b • B) ≤
    a * relativeEntropy T A + b * relativeEntropy U B at hentropy
  have hmax := (isGreatest_variational_traceExp H (a • A + b • B) hH hAB).2
    ⟨a • T + b • U,hTU,rfl⟩
  have htrace (C D : Matrix (Fin d) (Fin d) ℂ) :
      (Matrix.trace (a • C + b • D)).re = a * (Matrix.trace C).re + b * (Matrix.trace D).re := by
    simp
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, htrace, htrace] at hmax
  change a * traceExp (H + matrixLog A) + b * traceExp (H + matrixLog B) ≤ _
  rw [hTA,hUB]
  nlinarith
