import NLAlib.Matrix.OperatorTheory.EntropyJointConvex
import NLAlib.Matrix.OperatorTheory.VariationalTraceExp
import NLAlib.Matrix.Functions.UnitaryCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Theorem 8.1.1 — Lieb concavity

Main declaration: `NLAlib.lieb_concavity`, over any finite index type (the `Fin d` proof is a
private step, transported by reindexing).

Atlas: `operator-monotone-convex`, `matrix-freedman` (partial).

Source: Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorems 3.4.1 and 8.1.1, printed pp. 35 and 119; proof development Chapter 8.
-/
open scoped Matrix.Norms.L2Operator ComplexOrder
open NLAlib

/-- Lieb's concavity theorem over `Fin d`, the proof step for `lieb_concavity`. -/
private theorem lieb_concavity_fin {d : ℕ} [NeZero d]
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

namespace NLAlib

/-- Lieb's concavity theorem: `A ↦ traceExp (H + matrixLog A)` is concave on positive definite
matrices for fixed Hermitian `H`, over any finite index type (the empty type included, where the
function is constant).

Tropp 2015, Thm 8.1.1 (= Thm 3.4.1); the source states it for `d × d` matrices, the general index
type is obtained by reindexing (`posDef_reindex_iff`, `matrixLog_reindex_of_isHermitian`,
`traceExp_reindex`). Ported from the Prove2me mission *An Introduction to Matrix Concentration
Inequalities, Ch 8*.
atlas: operator-monotone-convex, matrix-freedman (partial) -/
theorem lieb_concavity {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n ℂ | A.PosDef} (fun A => traceExp (H + matrixLog A)) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have : Subsingleton (Matrix n n ℂ) := ⟨fun A B => Matrix.ext fun i => isEmptyElim i⟩
    refine ⟨Set.subsingleton_of_subsingleton.convex, ?_⟩
    intro A _ B _ a b _ _ hab
    rw [Subsingleton.elim B A, Subsingleton.elim (a • A + b • A) A, smul_eq_mul, smul_eq_mul,
      ← add_mul, hab, one_mul]
  let e := Fintype.equivFin n
  have : NeZero (Fintype.card n) := ⟨Fintype.card_ne_zero⟩
  let E := reindexStarAlgEquiv e
  let L := (Matrix.reindexLinearEquiv ℝ ℂ e e).toLinearMap
  have h := (lieb_concavity_fin (E H) (hH.reindex e)).comp_linearMap L
  have hdomain : L ⁻¹' {A | A.PosDef} = {A : Matrix n n ℂ | A.PosDef} := by
    ext A
    exact posDef_reindex_iff e A
  rw [hdomain] at h
  apply h.congr
  intro A hA
  change traceExp (E H + matrixLog (E A)) = traceExp (H + matrixLog A)
  have hlog : matrixLog (E A) = E (matrixLog A) := matrixLog_reindex_of_isHermitian e A hA.1
  rw [hlog]
  have ha : E H + E (matrixLog A) = E (H + matrixLog A) := (map_add E _ _).symm
  rw [ha]
  exact traceExp_reindex e _

end NLAlib
