import NLAlib.Matrix.Functions.TraceExponentialBranchRepresentation
import NLAlib.Matrix.Functions.UnitaryCalculus

/-!
# Exterior-circle representation for a Hermitian coefficient of simple spectrum

Unitary diagonalization transports the exterior-branch formula to arbitrary
Hermitian coefficient matrices with distinct eigenvalues. The first matrix
need not commute with the coefficient and can be any complex square matrix.
The resulting density is complex-valued; positivity remains a separate task.
Source: Stahl 2013, Theorem 2 and the unitary reduction in §1.3.
-/

noncomputable section

open Complex MeasureTheory Metric Filter
open scoped Topology Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A Hermitian coefficient with distinct eigenvalues has the exterior-circle
atom-plus-density representation for every complex matrix `A`. The atoms use
the diagonal of `A` in the coefficient's orthonormal eigenbasis. One fixed
circle gives the transform at every real parameter, without a commutation
assumption. No positivity of the complex-valued density is asserted.
Source: Stahl 2013, Theorem 2, unitary reduction and transform verification.
atlas: trace-exponential-stahl (partial) -/
theorem exists_exterior_branches_integral_circleDensity_eq_trace_matrixExp_sub_atoms_of_isHermitian
    (A B : Matrix n n ℂ) (hB : B.IsHermitian)
    (hsimple : Function.Injective hB.eigenvalues) :
    let E := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (star hB.eigenvectorUnitary)
    ∃ R : ℝ, 0 < R ∧ ∃ branch : n → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (branch i) {z | R < ‖z‖} ∧
        Tendsto (fun z => branch i z + (hB.eigenvalues i : ℂ) * z)
          (Bornology.cobounded ℂ) (𝓝 ((E A) i i))) ∧
      ∀ l u : ℝ, l ≤ u → (∀ i, hB.eigenvalues i ∈ Set.Icc l u) →
        ∀ r : ℝ, R < r → ∀ t : ℝ,
        IntervalIntegrable (fun s => Complex.exp (-(t : ℂ) * s) *
          traceExponentialCircleDensity branch hB.eigenvalues r s) volume l u ∧
        (∫ s in l..u, Complex.exp (-(t : ℂ) * s) *
          traceExponentialCircleDensity branch hB.eigenvalues r s) =
          Matrix.trace (matrixExp (A - (t : ℂ) • B)) -
            ∑ i, Complex.exp ((E A) i i - (t : ℂ) * hB.eigenvalues i) := by
  let E := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (star hB.eigenvectorUnitary)
  have hEB : E B = Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ)) := by
    simpa only [E, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      hB.conjStarAlgAut_star_eigenvectorUnitary
  obtain ⟨R, hR, branch, hbranch, hformula⟩ :=
    exists_exterior_branches_integral_circleDensity_eq_trace_matrixExp_sub_atoms
      hB.eigenvalues hsimple (E A)
  refine ⟨R, hR, branch, hbranch, ?_⟩
  intro l u hlu hau r hRr t
  have hpencil : E A - (t : ℂ) • Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ)) =
      E (A - (t : ℂ) • B) := by
    rw [map_sub, map_smul, hEB]
  have htrace : Matrix.trace (matrixExp
      (E A - (t : ℂ) • Matrix.diagonal (fun i => (hB.eigenvalues i : ℂ)))) =
      Matrix.trace (matrixExp (A - (t : ℂ) • B)) := by
    rw [hpencil]
    have hh := congrArg Matrix.trace
      (matrixExp_unitary_conj (star hB.eigenvectorUnitary) (A - (t : ℂ) • B))
    rw [trace_unitary_conj] at hh
    exact hh
  simpa only [htrace] using hformula l u hlu hau r hRr t

end NLAlib
