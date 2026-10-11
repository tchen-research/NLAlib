import NLAlib.Concentration.Matrix.Laplace.ProbabilisticLieb
import NLAlib.Concentration.Matrix.OperatorConvexity.UnitaryCalculus

/-!
# Lieb concavity and regularity for arbitrary finite matrix labels

Exact reindexing transports the existing deterministic Lieb theorem and regularity.
No new Lieb proof is needed for the generic finite-index martingale interfaces.
-/

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Equivalent finite labels preserve positive definiteness in both directions.
Source: transport of finite quadratic forms; helper for atlas `matrix-freedman`. -/
theorem posDef_reindex_iff {r : Type*} (e : n ≃ r) (A : Matrix n n ℂ) :
    (Matrix.reindex e e A).PosDef ↔ A.PosDef := by
  change (A.submatrix e.symm e.symm).PosDef ↔ A.PosDef
  constructor
  · intro h
    have h' := h.submatrix e.injective
    have heq : (A.submatrix e.symm e.symm).submatrix e e = A := by
      ext i j
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rw [heq] at h'
    exact h'
  · intro h
    exact h.submatrix e.symm.injective

/-- Equivalent finite labels commute with the matrix logarithm for Hermitian input.
Source: star-algebra transport of continuous functional calculus; helper for
operator rederivations `eq:condlieb` and atlas `matrix-freedman`. -/
theorem matrixLog_reindex_of_isHermitian {r : Type*} [Fintype r] [DecidableEq r]
    (e : n ≃ r) (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    matrixLog (Matrix.reindex e e A) = Matrix.reindex e e (matrixLog A) := by
  let E := reindexStarAlgEquiv e
  have hc : Continuous E := E.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hf : ContinuousOn Real.log (spectrum ℝ A) := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).continuousOn _
  symm
  change E (cfc Real.log A) = cfc Real.log (E A)
  exact StarAlgHomClass.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) E Real.log A
    hf hc hA (hA.reindex e)

/-- The existing positive-definite Hermitian exponential and logarithmic inverse,
transported to arbitrary finite labels, including the empty matrix.
Source: Tropp 2015, Sections 2.1.11–12; exact transport of
`posDef_matrixExp_and_matrixLog_matrixExp`. Atlas `matrix-freedman` (partial). -/
theorem posDef_matrixExp_and_matrixLog_matrixExp_finite (A : Matrix n n ℂ)
    (hA : A.IsHermitian) : (matrixExp A).PosDef ∧ matrixLog (matrixExp A) = A := by
  let e := Fintype.equivFin n
  have h := posDef_matrixExp_and_matrixLog_matrixExp (Matrix.reindex e e A) (hA.reindex e)
  rw [matrixExp_reindex e A] at h
  refine ⟨(posDef_reindex_iff e (matrixExp A)).mp h.1, ?_⟩
  have hEq := h.2
  rw [matrixLog_reindex_of_isHermitian e (matrixExp A) hA.exp] at hEq
  exact (reindexStarAlgEquiv e).injective hEq

/-- The existing Lieb concavity theorem on the actual positive-definite cone, transported
to every nonempty finite index type.
Source: Tropp 2015, Theorem 3.4.1; exact finite-label transport of `lieb_concavity`.
atlas: matrix-freedman (partial) -/
theorem lieb_concavity_finite [Nonempty n] (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n ℂ | A.PosDef} (fun A => traceExp (H + matrixLog A)) := by
  let e := Fintype.equivFin n
  let E := reindexStarAlgEquiv e
  let L := (Matrix.reindexLinearEquiv ℝ ℂ e e).toLinearMap
  have h := (lieb_concavity (E H) (hH.reindex e)).comp_linearMap L
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

/-- The existing continuity of the Lieb trace function on the positive-definite cone,
transported to arbitrary nonempty finite labels.
Source: Tropp 2015, Corollary 3.4.2; exact finite-label transport of the promoted
`continuousOn_traceExp_add_matrixLog` helper. Atlas `matrix-freedman`. -/
theorem continuousOn_traceExp_add_matrixLog_finite [Nonempty n] (H : Matrix n n ℂ) :
    ContinuousOn (fun A => traceExp (H + matrixLog A)) {A : Matrix n n ℂ | A.PosDef} := by
  let e := Fintype.equivFin n
  let E := reindexStarAlgEquiv e
  have hc : Continuous E := E.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have h := (continuousOn_traceExp_add_matrixLog (E H)).comp hc.continuousOn
    (fun A hA => (posDef_reindex_iff e A).mpr hA)
  apply h.congr
  intro A hA
  change traceExp (H + matrixLog A) = traceExp (E H + matrixLog (E A))
  have hlog : matrixLog (E A) = E (matrixLog A) := matrixLog_reindex_of_isHermitian e A hA.1
  rw [hlog]
  have ha : E H + E (matrixLog A) = E (H + matrixLog A) := (map_add E _ _).symm
  rw [ha]
  exact (traceExp_reindex e _).symm

end NLAlib
