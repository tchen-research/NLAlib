import NLAlib.Matrix.Spectral.EigenvectorPairing
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Diagonalizable matrices and eigenvector bases

The matrix definition is equivalent to a full independent eigenvector family
and to the spanning-eigenspace criterion. Source: Horn–Johnson (2013),
Definitions 1.3.6 and 1.4.4 and Theorems 1.3.7, 1.3.9 and 1.4.10;
atlas `diagonalizable-def`.
-/

noncomputable section
open scoped Matrix
open Module
open Module.End
open Polynomial

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- A matrix is diagonalizable if an invertible eigenvector matrix
intertwines it with a diagonal matrix. Source: Horn–Johnson (2013),
Definition 1.3.6; `isDiagonalizable_iff_exists_similarity` gives the usual
`A = V Λ V⁻¹` form.
atlas: diagonalizable-def (partial) -/
def IsDiagonalizable (A : Matrix n n K) : Prop :=
  ∃ (V : Matrix n n K) (d : n → K), IsUnit V ∧ A * V = V * Matrix.diagonal d

/-- The intertwining definition equals the usual invertible diagonal
similarity. Source: Horn–Johnson (2013), Definition 1.3.6.
atlas: diagonalizable-def -/
theorem isDiagonalizable_iff_exists_similarity (A : Matrix n n K) :
    IsDiagonalizable A ↔ ∃ (V : Matrix n n K) (d : n → K),
      IsUnit V ∧ A = V * Matrix.diagonal d * V⁻¹ := by
  constructor
  · rintro ⟨V, d, hV, hAV⟩
    refine ⟨V, d, hV, ?_⟩
    have hdet := V.isUnit_iff_isUnit_det.mp hV
    calc
      A = A * (V * V⁻¹) := by rw [Matrix.mul_nonsing_inv V hdet, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hAV]
  · rintro ⟨V, d, hV, hA⟩
    refine ⟨V, d, hV, ?_⟩
    rw [hA, Matrix.mul_assoc, Matrix.nonsing_inv_mul V (V.isUnit_iff_isUnit_det.mp hV),
      Matrix.mul_one]

/-- Diagonalizability is equivalent to a full independent family of
eigenvectors. Source: Horn–Johnson (2013), Theorem 1.3.7; finite index types
are arbitrary and may be empty.
atlas: diagonalizable-def -/
theorem isDiagonalizable_iff_exists_independent_eigenvectors (A : Matrix n n K) :
    IsDiagonalizable A ↔ ∃ (v : n → n → K) (d : n → K),
      LinearIndependent K v ∧ ∀ j, A *ᵥ v j = d j • v j := by
  constructor
  · rintro ⟨V, d, hV, hAV⟩
    refine ⟨Matrix.col V, d, Matrix.linearIndependent_cols_iff_isUnit.mpr hV, ?_⟩
    intro j
    funext i
    have h := congrArg (fun M : Matrix n n K => M i j) hAV
    rw [Matrix.mul_diagonal] at h
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Matrix.col_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h
  · rintro ⟨v, d, hv, hAv⟩
    let V : Matrix n n K := fun i j => v j i
    refine ⟨V, d, Matrix.linearIndependent_cols_iff_isUnit.mp hv, ?_⟩
    ext i j
    rw [Matrix.mul_diagonal]
    change (∑ k, A i k * v j k) = v j i * d j
    simpa only [Matrix.mulVec, dotProduct,
      Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun (hAv j) i

/-- A full eigenvector basis is equivalent to diagonalizability.
Horn–Johnson (2013), Theorem 1.3.7.
atlas: diagonalizable-def (partial) -/
theorem isDiagonalizable_iff_exists_eigenbasis (A : Matrix n n K) :
    IsDiagonalizable A ↔ ∃ (b : Basis n K (n → K)) (d : n → K),
      ∀ j, A *ᵥ b j = d j • b j := by
  rw [isDiagonalizable_iff_exists_independent_eigenvectors]
  constructor
  · rintro ⟨v, d, hv, hAv⟩
    let b := basisOfLinearIndependentOfCardEqFinrank' v hv
      (Module.finrank_fintype_fun_eq_card K).symm
    refine ⟨b, d, ?_⟩
    simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank'] using hAv
  · rintro ⟨b, d, hAv⟩
    exact ⟨b, d, b.linearIndependent, hAv⟩

/-- A full list of distinct eigenvalues makes a matrix diagonalizable.
Source: Horn–Johnson (2013), Theorem 1.3.9; eigenvectors at distinct
eigenvalues are independent by Mathlib's eigenspace theorem.
atlas: diagonalizable-def -/
theorem isDiagonalizable_of_distinct_eigenvalues {A : Matrix n n K} (d : n → K)
    (hd : Function.Injective d) (hroots : ∀ j, d j ∈ spectrum K A) :
    IsDiagonalizable A := by
  classical
  choose v hv hAv using fun j => exists_mulVec_eq_smul_of_mem_spectrum (hroots j)
  apply (isDiagonalizable_iff_exists_independent_eigenvectors A).mpr
  refine ⟨v, d, Module.End.eigenvectors_linearIndependent' A.toLin' d hd v ?_, hAv⟩
  intro j
  exact ⟨Module.End.mem_eigenspace_iff.mpr (hAv j), hv j⟩

/-- Eigenvectors spanning the whole space characterize diagonalizability.
Source: Horn–Johnson (2013), Theorem 1.3.7; the reverse direction collects
bases of the independent eigenspaces.
atlas: diagonalizable-def (partial) -/
theorem isDiagonalizable_iff_iSup_eigenspace_eq_top (A : Matrix n n K) :
    IsDiagonalizable A ↔ (⨆ μ : K, Module.End.eigenspace A.toLin' μ) = ⊤ := by
  classical
  constructor
  · intro hA
    obtain ⟨b, d, hb⟩ := (isDiagonalizable_iff_exists_eigenbasis A).mp hA
    apply (Submodule.eq_top_iff_forall_basis_mem b).mpr
    intro j
    exact Submodule.mem_iSup_of_mem (d j) (Module.End.mem_eigenspace_iff.mpr (hb j))
  · intro hspan
    have hsum : DirectSum.IsInternal (fun μ : K => Module.End.eigenspace A.toLin' μ) :=
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
        (Module.End.eigenspaces_iSupIndep A.toLin') hspan
    let c := hsum.collectedBasis (fun μ => Module.finBasis K (Module.End.eigenspace A.toLin' μ))
    let : Fintype (Σ μ : K, Fin (Module.finrank K (Module.End.eigenspace A.toLin' μ))) :=
      FiniteDimensional.fintypeBasisIndex c
    have hcCard : Fintype.card (Σ μ : K, Fin (Module.finrank K (Module.End.eigenspace A.toLin' μ))) =
        Fintype.card n := by
      rw [← Module.finrank_eq_card_basis c, Module.finrank_fintype_fun_eq_card]
    let e := Fintype.equivOfCardEq hcCard
    let b : Basis n K (n → K) := c.reindex e
    apply (isDiagonalizable_iff_exists_eigenbasis A).mpr
    refine ⟨b, fun j => (e.symm j).1, fun j => ?_⟩
    change A.toLin' (b j) = (e.symm j).1 • b j
    apply Module.End.mem_eigenspace_iff.mp
    simpa only [b, Basis.reindex_apply] using
      hsum.collectedBasis_mem (fun μ => Module.finBasis K (Module.End.eigenspace A.toLin' μ)) (e.symm j)

/-- Semisimplicity implies diagonalizability over an algebraically closed
field. Source: Horn–Johnson (2013), Definition 1.4.4 and Theorem 1.4.10;
this bridges the matrix predicate with Mathlib's semisimple endomorphism API.
atlas: diagonalizable-def (partial) -/
theorem isDiagonalizable_of_isSemisimple [IsAlgClosed K] {A : Matrix n n K}
    (hA : Module.End.IsSemisimple A.toLin') : IsDiagonalizable A :=
  (isDiagonalizable_iff_iSup_eigenspace_eq_top A).mpr hA.iSup_eigenspace_eq_top

/-- A diagonalizable matrix induces a semisimple endomorphism over any field.
Source: Horn–Johnson (2013), Definition 1.4.4 and Theorem 1.4.10; the distinct
linear eigenvalue factors give a squarefree annihilating polynomial.
atlas: diagonalizable-def (partial) -/
theorem IsDiagonalizable.isSemisimple {A : Matrix n n K} (hA : IsDiagonalizable A) :
    Module.End.IsSemisimple A.toLin' := by
  classical
  obtain ⟨b, d, hb⟩ := (isDiagonalizable_iff_exists_eigenbasis A).mp hA
  let s : Finset K := Finset.univ.image d
  let p : K[X] := ∏ μ ∈ s, (Polynomial.X - Polynomial.C μ)
  have hp : Squarefree p := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro α hα β hβ hαβ
      exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hαβ))).isRelPrime
    · intro μ hμ
      exact (Polynomial.irreducible_X_sub_C μ).squarefree
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp
  apply b.ext
  intro j
  have heval : p.eval (d j) = 0 := by
    change (∏ μ ∈ s, (Polynomial.X - Polynomial.C μ)).eval (d j) = 0
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    simp
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hb j), heval, zero_smul]
  rfl

/-- Over an algebraically closed field the matrix diagonalizability
predicate is equivalent to Mathlib's semisimplicity. Source: Horn–Johnson
(2013), Definition 1.4.4 and Theorem 1.4.10.
atlas: diagonalizable-def (partial) -/
theorem isDiagonalizable_iff_isSemisimple [IsAlgClosed K] (A : Matrix n n K) :
    IsDiagonalizable A ↔ Module.End.IsSemisimple A.toLin' :=
  ⟨IsDiagonalizable.isSemisimple, isDiagonalizable_of_isSemisimple⟩

/-- A diagonalizable matrix's geometric and algebraic multiplicities agree
at every scalar. Source: Horn–Johnson (2013), Theorem 1.4.10; a scalar
outside the spectrum has both multiplicities zero.
atlas: diagonalizable-def (partial) -/
theorem IsDiagonalizable.finrank_eigenspace_eq_rootMultiplicity {A : Matrix n n K}
    (hA : IsDiagonalizable A) (μ : K) :
    Module.finrank K (Module.End.eigenspace A.toLin' μ) = A.charpoly.rootMultiplicity μ := by
  have hm := LinearMap.finrank_maxGenEigenspace_eq A.toLin' μ
  have heq : Module.End.maxGenEigenspace A.toLin' μ = Module.End.eigenspace A.toLin' μ :=
    hA.isSemisimple.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  rw [heq] at hm
  simpa only [Matrix.charpoly_toLin'] using hm

/-- Over an algebraically closed field diagonalizability is equivalent to
equality of all geometric and algebraic multiplicities. Source: Horn–Johnson
(2013), Theorem 1.4.10; empty spectra and zero multiplicities are included.
atlas: diagonalizable-def -/
theorem isDiagonalizable_iff_finrank_eigenspace_eq_rootMultiplicity [IsAlgClosed K]
    (A : Matrix n n K) : IsDiagonalizable A ↔
      ∀ μ : K, Module.finrank K (Module.End.eigenspace A.toLin' μ) =
        A.charpoly.rootMultiplicity μ := by
  constructor
  · exact fun hA μ => hA.finrank_eigenspace_eq_rootMultiplicity μ
  · intro hmult
    have heq (μ : K) : Module.End.eigenspace A.toLin' μ =
        Module.End.maxGenEigenspace A.toLin' μ := by
      apply Submodule.eq_of_le_of_finrank_eq Module.End.eigenspace_le_maxGenEigenspace
      rw [hmult μ, LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin']
    apply (isDiagonalizable_iff_iSup_eigenspace_eq_top A).mpr
    simpa only [heq] using Module.End.iSup_maxGenEigenspace_eq_top A.toLin'

end NLAlib
