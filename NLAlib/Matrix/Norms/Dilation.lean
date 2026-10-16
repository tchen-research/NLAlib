import NLAlib.Matrix.Functions.DilationIdentities
import NLAlib.Matrix.Norms.Reindex

/-!
# Dilation norm on arbitrary finite coordinate labels

The existing finite-dimensional dilation theorem transports through ordinary
row and column equivalences, retaining its exact spectral norm.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- The Hermitian dilation commutes with arbitrary row and column reindexing. -/
theorem dilation_reindex {m n p q : Type*} (A : Matrix m n ℂ)
    (em : m ≃ p) (en : n ≃ q) :
    dilation (A.reindex em en) =
      (dilation A).reindex (em.sumCongr en) (em.sumCongr en) := by
  ext (a | a) (b | b) <;>
    simp [dilation, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]

open scoped Matrix.Norms.L2Operator in
/-- Hermitian dilation preserves the spectral norm on arbitrary nonempty finite
row and column labels. Source: Tropp 2015, equations (2.1.27)–(2.1.28). -/
theorem specNorm_dilation {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n] (A : Matrix m n ℂ) :
    specNorm (dilation A) = specNorm A := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  haveI : NeZero (Fintype.card m) := ⟨Fintype.card_ne_zero⟩
  haveI : NeZero (Fintype.card n) := ⟨Fintype.card_ne_zero⟩
  have h := (dilation_identities (A.reindex em en)).2.2.2
  simp only [← specNorm_eq_norm, dilation_reindex, specNorm_reindex] at h
  exact h

end NLAlib
