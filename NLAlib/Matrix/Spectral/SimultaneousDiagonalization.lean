import NLAlib.Matrix.Spectral.Diagonalizable
import Mathlib.LinearAlgebra.Eigenspace.Pi

/-!
# Simultaneous diagonalization of commuting families

Joint eigenspaces of arbitrary commuting diagonalizable families span the
finite-dimensional space. Collecting their bases produces one similarity
matrix for the entire family, without requiring a finite family index.
Source: Horn–Johnson (2013), Theorems 1.3.21 and 2.4.8.1;
atlas `simultaneous-diagonalization`.
-/

noncomputable section
open scoped Matrix
open Module

namespace NLAlib

variable {n ι : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- A commuting family of diagonalizable matrices has a common eigenbasis.
Source: Horn–Johnson (2013), Theorem 1.3.21; the family index may be infinite
or empty, and any field is allowed when each matrix is diagonalizable there.
atlas: simultaneous-diagonalization (partial) -/
theorem exists_common_eigenbasis_of_commute (A : ι → Matrix n n K)
    (hdiag : ∀ i, IsDiagonalizable (A i))
    (hcomm : Pairwise fun i j => Commute (A i) (A j)) :
    ∃ (b : Basis n K (n → K)) (d : ι → n → K),
      ∀ i j, A i *ᵥ b j = d i j • b j := by
  classical
  let f (i : ι) : Module.End K (n → K) := (A i).toLin'
  have hfc : Pairwise fun i j => Commute (f i) (f j) := by
    intro i j hij
    exact (hcomm hij).map Matrix.toLinAlgEquiv'.toRingHom
  have hgen (i : ι) (μ : K) : (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    (hdiag i).isSemisimple.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hsp (i : ι) : (⨆ μ : K, (f i).maxGenEigenspace μ) = ⊤ := by
    simp only [hgen]
    exact (isDiagonalizable_iff_iSup_eigenspace_eq_top (A i)).mp (hdiag i)
  let W (χ : ι → K) : Submodule K (n → K) := ⨅ i, (f i).eigenspace (χ i)
  have hspan : (⨆ χ : ι → K, W χ) = ⊤ := by
    simpa only [hgen] using
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
        f hfc hsp
  have hind : iSupIndep W := by
    have hmap (i j : ι) (μ : K) : Set.MapsTo (f i)
        ((f j).maxGenEigenspace μ) ((f j).maxGenEigenspace μ) := by
      apply Module.End.mapsTo_maxGenEigenspace_of_comm
      rcases eq_or_ne i j with rfl | hij
      · exact Commute.refl _
      · exact (hfc hij).symm
    simpa only [hgen] using
      Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f hmap
  have hsum : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hspan
  let c := hsum.collectedBasis (fun χ => Module.finBasis K (W χ))
  let : Fintype (Σ χ : ι → K, Fin (Module.finrank K (W χ))) :=
    FiniteDimensional.fintypeBasisIndex c
  have hcCard : Fintype.card (Σ χ : ι → K, Fin (Module.finrank K (W χ))) =
      Fintype.card n := by
    rw [← Module.finrank_eq_card_basis c, Module.finrank_fintype_fun_eq_card]
  let e := Fintype.equivOfCardEq hcCard
  let b : Basis n K (n → K) := c.reindex e
  refine ⟨b, fun i j => (e.symm j).1 i, fun i j => ?_⟩
  have hb : b j ∈ W (e.symm j).1 := by
    simpa only [b, Basis.reindex_apply] using
      hsum.collectedBasis_mem (fun χ => Module.finBasis K (W χ)) (e.symm j)
  exact Module.End.mem_eigenspace_iff.mp
    ((iInf_le (fun k => (f k).eigenspace ((e.symm j).1 k)) i) hb)

/-- A commuting diagonalizable family shares one invertible eigenvector
matrix. Source: Horn–Johnson (2013), Theorem 1.3.21; real diagonalizable
families are handled over the real field directly.
atlas: simultaneous-diagonalization (partial) -/
theorem exists_simultaneous_diagonalization_of_commute (A : ι → Matrix n n K)
    (hdiag : ∀ i, IsDiagonalizable (A i))
    (hcomm : Pairwise fun i j => Commute (A i) (A j)) :
    ∃ (V : Matrix n n K) (d : ι → n → K), IsUnit V ∧
      ∀ i, A i * V = V * Matrix.diagonal (d i) := by
  obtain ⟨b, d, hb⟩ := exists_common_eigenbasis_of_commute A hdiag hcomm
  let V : Matrix n n K := fun i j => b j i
  refine ⟨V, d, Matrix.linearIndependent_cols_iff_isUnit.mp b.linearIndependent, ?_⟩
  intro i
  ext j k
  rw [Matrix.mul_diagonal]
  change (∑ l, A i j l * b k l) = b k j * d i k
  simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_comm] using
    congrFun (hb i k) j

/-- Simultaneously diagonalized matrices commute. Source: Horn–Johnson
(2013), Theorem 1.3.12; repeated diagonal values require no exception.
atlas: simultaneous-diagonalization (partial) -/
theorem commute_of_simultaneous_diagonalization {A B V : Matrix n n K}
    {a b : n → K} (hV : IsUnit V) (hA : A * V = V * Matrix.diagonal a)
    (hB : B * V = V * Matrix.diagonal b) : Commute A B := by
  apply hV.mul_right_cancel
  change (A * B) * V = (B * A) * V
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc,
    Matrix.mul_assoc, hA, ← Matrix.mul_assoc B V, hB, Matrix.mul_assoc,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg (fun d : n → K => V * Matrix.diagonal d)
    (funext fun i => mul_comm (a i) (b i))

/-- A diagonalizable family commutes exactly when it has one common
diagonalizing similarity. Source: Horn–Johnson (2013), Theorems 1.3.12
and 1.3.21; no finiteness assumption on the family is imposed.
atlas: simultaneous-diagonalization (partial) -/
theorem pairwise_commute_iff_exists_simultaneous_diagonalization
    (A : ι → Matrix n n K) (hdiag : ∀ i, IsDiagonalizable (A i)) :
    (Pairwise fun i j => Commute (A i) (A j)) ↔
      ∃ (V : Matrix n n K) (d : ι → n → K), IsUnit V ∧
        ∀ i, A i * V = V * Matrix.diagonal (d i) := by
  constructor
  · exact exists_simultaneous_diagonalization_of_commute A hdiag
  · rintro ⟨V, d, hV, hAV⟩ i j hij
    exact commute_of_simultaneous_diagonalization hV (hAV i) (hAV j)

end NLAlib
