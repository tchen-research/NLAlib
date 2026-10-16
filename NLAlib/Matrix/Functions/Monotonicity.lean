import NLAlib.Matrix.Functions.UnitaryCalculus
import NLAlib.Matrix.Functions.ExtremeEigenvalues
import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# Operator monotonicity and spectral intervals

The quantifier over every matrix size follows the library's operator
convexity interface. Spectral intervals are open, and order segments stay
inside a convex spectral domain. Tropp (2022), Chapter 14.
-/

noncomputable section
open Matrix Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace NLAlib

/-- Operator monotonicity on a scalar set, in every finite matrix size.
The empty size is included. Tropp (2022), Chapter 14. -/
def OperatorMonotoneOn (I : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ),
    A.IsHermitian → B.IsHermitian → spectrum ℝ A ⊆ I → spectrum ℝ B ⊆ I →
    A ≤ B → cfc f A ≤ cfc f B

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Operator monotonicity is independent of the chosen finite index type. -/
theorem OperatorMonotoneOn.cfc_le {I : Set ℝ} {f : ℝ → ℝ}
    (hf : OperatorMonotoneOn I f) {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I) (hAB : A ≤ B) :
    cfc f A ≤ cfc f B := by
  let e := Fintype.equivFin n
  let R : Matrix n n ℂ → Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ :=
    Matrix.reindex e e
  have h := hf (Fintype.card n) (R A) (R B) (hA.reindex e) (hB.reindex e)
    (by rwa [spectrum_reindex]) (by rwa [spectrum_reindex])
    (by simpa [R, Matrix.reindex_apply, Matrix.le_iff, Matrix.submatrix_sub] using
      ((Matrix.le_iff.mp hAB).submatrix e.symm))
  rw [Matrix.le_iff, cfc_reindex_of_isHermitian e f A hA,
    cfc_reindex_of_isHermitian e f B hB] at h
  simpa [R, Matrix.reindex_apply, Matrix.le_iff, Matrix.submatrix_submatrix,
    Matrix.submatrix_sub] using h.submatrix e

/-- Matrices whose real spectrum lies in an open set form an open set. -/
theorem isOpen_setOf_real_spectrum_subset {I : Set ℝ} (hI : IsOpen I) :
    IsOpen {A : Matrix n n ℂ | spectrum ℝ A ⊆ I} := by
  rw [isOpen_iff_mem_nhds]
  intro A hA
  exact (upperHemicontinuous_spectrum ℝ (Matrix n n ℂ)).forall_isOpen A I hI hA

/-- A Hermitian matrix between two endpoints with spectra in a convex
scalar set also has its spectrum in that set. -/
theorem spectrum_subset_of_order_interval [Nonempty n] {I : Set ℝ}
    (hI : Convex ℝ I) {A B C : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian)
    (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I)
    (hAC : A ≤ C) (hCB : C ≤ B) : spectrum ℝ C ⊆ I := by
  have hmin : lambdaMin A ∈ spectrum ℝ A := by
    rw [lambdaMin, hA.spectrum_real_eq_range_eigenvalues]
    exact (Set.range_nonempty _).csInf_mem (Set.finite_range _)
  have hmax : lambdaMax B ∈ spectrum ℝ B := by
    rw [lambdaMax, hB.spectrum_real_eq_range_eigenvalues]
    exact (Set.range_nonempty _).csSup_mem (Set.finite_range _)
  have hlow : algebraMap ℝ (Matrix n n ℂ) (lambdaMin A) ≤ A := by
    apply (algebraMap_le_iff_le_spectrum hA).mpr
    intro x hx
    exact csInf_le (by rw [hA.spectrum_real_eq_range_eigenvalues]; exact (Set.finite_range _).bddBelow) hx
  have hupp : B ≤ algebraMap ℝ (Matrix n n ℂ) (lambdaMax B) := by
    apply (le_algebraMap_iff_spectrum_le hB).mpr
    intro x hx
    exact le_csSup (by rw [hB.spectrum_real_eq_range_eigenvalues]; exact (Set.finite_range _).bddAbove) hx
  intro x hx
  exact hI.ordConnected.out (hAI hmin) (hBI hmax)
    ⟨(algebraMap_le_iff_le_spectrum hC).mp (hlow.trans hAC) x hx,
      (le_algebraMap_iff_spectrum_le hC).mp (hCB.trans hupp) x hx⟩

end NLAlib
