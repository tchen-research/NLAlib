import NLAlib.Krylov.Spaces.CyclicEigenspaces
import NLAlib.ForMathlib.LinearAlgebra.MatrixScalarExtension
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Minimal polynomial degree under scalar extension

Independent columns of a Krylov matrix stay independent in an extension field.
A vector realizing the original minimal polynomial therefore gives the lower
degree bound, while the mapped annihilating polynomial gives the upper bound.
In particular the geometric companion criterion for a real matrix uses its
complex eigenspaces. Source: operator derivations, Section 6.
Atlas: `companion-matrix`.
-/

noncomputable section
open Polynomial
open scoped Matrix
namespace NLAlib

variable {K L n : Type*} [Field K] [Field L] [Algebra K L]
variable [Fintype n] [DecidableEq n]

/-- Extending the scalar field preserves the degree of a finite matrix's minimal
polynomial. No infinitude, characteristic or nonempty dimension assumption is
needed. Source: operator derivations, Section 6.
atlas: companion-matrix (partial) -/
theorem natDegree_minpoly_map_algebraMap (A : Matrix n n K) :
    (minpoly L (A.map (algebraMap K L))).natDegree = (minpoly K A).natDegree := by
  let σ : K →+* L := algebraMap K L
  let ψ : Matrix n n K →+* Matrix n n L := σ.mapMatrix
  have hcomp : (algebraMap L (Matrix n n L)).comp σ =
      ψ.comp (algebraMap K (Matrix n n K)) := by
    ext c i j
    by_cases hij : i = j <;>
      simp [ψ, hij, Matrix.algebraMap_eq_diagonal, Matrix.diagonal, Matrix.map_apply]
  have hann : aeval (A.map σ) ((minpoly K A).map σ) = 0 := by
    have h := map_aeval_eq_aeval_map hcomp (minpoly K A) A
    rw [minpoly.aeval, map_zero] at h
    exact h.symm
  have hup : (minpoly L (A.map σ)).natDegree ≤ (minpoly K A).natDegree := by
    have h := natDegree_le_of_dvd (minpoly.dvd L (A.map σ) hann)
      ((minpoly.monic A.isIntegral).map σ).ne_zero
    simpa only [(minpoly.monic A.isIntegral).natDegree_map] using h
  obtain ⟨b, hb⟩ := exists_vectorMinpoly_eq_minpoly A
  let ν := krylovGrade A b
  let M : Matrix n (Fin ν) K := fun i j => ((A ^ (j : ℕ)) *ᵥ b) i
  have hM : LinearIndependent K M.col :=
    (linearIndependent_pow_mulVec_iff_le_krylovGrade A b).mpr le_rfl
  have hML := Matrix.linearIndependent_cols_map σ hM
  have hpow (j : ℕ) : (A ^ j).map σ = (A.map σ) ^ j :=
    ψ.map_pow A j
  have hcols : (M.map σ).col =
      fun j : Fin ν => ((A.map σ) ^ (j : ℕ)) *ᵥ (σ ∘ b) := by
    funext j i
    change σ (((A ^ (j : ℕ)) *ᵥ b) i) = _
    rw [RingHom.map_mulVec, hpow]
  rw [hcols] at hML
  have hν : ν ≤ krylovGrade (A.map σ) (σ ∘ b) :=
    (linearIndependent_pow_mulVec_iff_le_krylovGrade (A.map σ) (σ ∘ b)).mp hML
  have hνμ : (minpoly K A).natDegree = ν := by
    rw [← hb, natDegree_vectorMinpoly]
  apply le_antisymm hup
  rw [hνμ]
  exact hν.trans (krylovGrade_le_natDegree_minpoly (A.map σ) (σ ∘ b))

/-- Every actual eigenvalue has a one-dimensional eigenspace exactly when the
minimal polynomial has full degree over a splitting field. Non-eigenvalues have
zero eigenspaces, so the preceding at-most-one interface is equivalent.
Source: Horn–Johnson (2013), Theorem 3.3.14.
atlas: companion-matrix (partial) -/
theorem natDegree_minpoly_eq_card_iff_eigenvalue_finrank_eq_one
    (A : Matrix n n K) (hsplit : A.charpoly.Splits) :
    (minpoly K A).natDegree = Fintype.card n ↔
      ∀ μ : K, Module.End.HasEigenvalue (Matrix.toLin' A) μ →
        Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) μ) = 1 := by
  rw [natDegree_minpoly_eq_card_iff_finrank_eigenspace_le_one A hsplit]
  constructor
  · intro h μ hμ
    have hpos := Module.End.pos_finrank_genEigenspace_of_hasEigenvalue hμ
      (by norm_num : 0 < (1 : ℕ))
    exact le_antisymm (h μ) (by exact hpos)
  · intro h μ
    by_cases hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ
    · exact (h μ hμ).le
    · have hbot : Module.End.eigenspace (Matrix.toLin' A) μ = ⊥ :=
        not_ne_iff.mp hμ
      rw [hbot]
      simp

/-- For a real matrix, geometric nonderogatoriness uses the eigenspaces of its
complexification, including repeated nonreal eigenvalues. Real eigenspaces alone
would give an incorrect criterion. Source: operator derivations, Section 6.
atlas: companion-matrix (partial) -/
theorem natDegree_minpoly_real_eq_card_iff_complex_eigenvalue_finrank_eq_one
    (A : Matrix n n ℝ) :
    (minpoly ℝ A).natDegree = Fintype.card n ↔
      ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ →
        Module.finrank ℂ (Module.End.eigenspace
          (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ) = 1 := by
  rw [← natDegree_minpoly_map_algebraMap (L := ℂ) A]
  exact natDegree_minpoly_eq_card_iff_eigenvalue_finrank_eq_one _
    (IsAlgClosed.splits _)

end NLAlib
