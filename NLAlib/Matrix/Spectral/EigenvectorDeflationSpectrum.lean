import NLAlib.Matrix.Spectral.EigenvectorDeflation
import NLAlib.Matrix.Spectral.GeneralizedEigenPairing

/-!
# Characteristic factors of isolated eigenlines

The distinguished invariant line contributes one linear characteristic
factor. Algebraic simplicity excludes that eigenvalue from the remaining
principal block. Source: Horn–Johnson (2013), Lemma 1.4.11 and Lemma 6.3.10;
atlas `left-right-eigenvectors` and `simple-eigenvalue-perturbation`.
-/

noncomputable section
open Polynomial
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- An isolated coordinate contributes exactly one characteristic linear
factor. Source: Horn–Johnson (2013), Theorem 1.4.7; the remaining block is
the principal submatrix on all other coordinates, including an empty block. -/
theorem charpoly_eq_X_sub_C_mul_submatrix_of_isolated_coordinate
    (M : Matrix n n K) (i : n) (μ : K)
    (hcol : ∀ j, M j i = if j = i then μ else 0)
    (hrow : ∀ j, M i j = if j = i then μ else 0) :
    M.charpoly = (X - C μ) *
      (M.submatrix (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val)).charpoly := by
  classical
  let L := {j : n // j = i}
  let R := {j : n // j ≠ i}
  let : Unique L := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  let e : L ⊕ R ≃ n := Equiv.sumCompl (fun j => j = i)
  let B : Matrix R R K := M.submatrix Subtype.val Subtype.val
  have hblock : M.submatrix e e = Matrix.fromBlocks (Matrix.diagonal (fun _ : L => μ)) 0 0 B := by
    ext a b
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have ha : a.val = i := a.property
        have hb : b.val = i := b.property
        change M a.val b.val = Matrix.diagonal (fun _ : L => μ) a b
        rw [ha, hb, hcol]
        simp only [ite_true, Matrix.diagonal_apply, Subsingleton.elim a b, ite_true]
      | inr b =>
        have ha : a.val = i := a.property
        have hb : b.val ≠ i := b.property
        change M a.val b.val = 0
        rw [ha, hrow]
        exact if_neg hb
    | inr a =>
      cases b with
      | inl b =>
        have ha : a.val ≠ i := a.property
        have hb : b.val = i := b.property
        change M a.val b.val = 0
        rw [hb, hcol]
        exact if_neg ha
      | inr b => rfl
  calc
    M.charpoly = (M.submatrix e e).charpoly := (Matrix.charpoly_reindex e.symm M).symm
    _ = (X - C μ) * B.charpoly := by
      rw [hblock, Matrix.charpoly_fromBlocks_zero₂₁, Matrix.charpoly_diagonal]
      simp only [Fintype.prod_unique]

/-- Algebraic simplicity excludes the isolated eigenvalue from the remaining
principal block. Source: Horn–Johnson (2013), Lemma 6.3.10.
atlas: simple-eigenvalue-perturbation (partial) -/
theorem not_mem_spectrum_submatrix_of_isolated_coordinate_of_simple
    (M : Matrix n n K) (i : n) (μ : K)
    (hcol : ∀ j, M j i = if j = i then μ else 0)
    (hrow : ∀ j, M i j = if j = i then μ else 0)
    (hμ : M.charpoly.rootMultiplicity μ = 1) :
    μ ∉ spectrum K
      (M.submatrix (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val)) := by
  classical
  let B := M.submatrix (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val)
  have hfactor : M.charpoly = (X - C μ) * B.charpoly :=
    charpoly_eq_X_sub_C_mul_submatrix_of_isolated_coordinate M i μ hcol hrow
  have hprod : (X - C μ) * B.charpoly ≠ 0 := hfactor ▸ M.charpoly_monic.ne_zero
  rw [hfactor, Polynomial.rootMultiplicity_mul hprod] at hμ
  simp only [Polynomial.rootMultiplicity_X_sub_C] at hμ
  have hB : B.charpoly.rootMultiplicity μ = 0 := Nat.add_eq_left.mp hμ
  intro hspec
  have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hspec
  have hpos := Polynomial.rootMultiplicity_pos'.mpr ⟨B.charpoly_monic.ne_zero, hroot⟩
  rw [hB] at hpos
  exact (Nat.lt_irrefl 0) hpos

/-- A simple eigenvalue admits a left–right normalized isolated similarity,
and the remaining principal block excludes that eigenvalue. Source:
Horn–Johnson (2013), Lemmas 1.4.11 and 6.3.10; the distinguished coordinate
can be relabeled as the first coordinate of the scalar/direct-sum split.
atlas: left-right-eigenvectors (partial), simple-eigenvalue-perturbation (partial) -/
theorem exists_simple_eigenvalue_isolated_similarity [IsAlgClosed K]
    {A : Matrix n n K} {x y : n → K} {μ : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hμ : A.charpoly.rootMultiplicity μ = 1) :
    ∃ (S : Matrix n n K) (i : n), IsUnit S ∧ Matrix.col S i = x ∧
      (∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) ∧
      (∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0) ∧
      (∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) ∧
      μ ∉ spectrum K ((S⁻¹ * A * S).submatrix
        (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val)) := by
  have hpair := dotProduct_ne_zero_of_simple_eigenvalue hx hy hAx hyA hμ
  obtain ⟨S, i, hS, hcol, hrow, hright, hleft, hproj⟩ :=
    exists_isolated_eigenvector_similarity hAx hyA hpair
  have hchar : (S⁻¹ * A * S).charpoly = A.charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv S (S.isUnit_iff_isUnit_det.mp hS), Matrix.one_mul]
  exact ⟨S, i, hS, hcol, hrow, hright, hleft,
    not_mem_spectrum_submatrix_of_isolated_coordinate_of_simple (S⁻¹ * A * S) i μ
      hright hleft (by simpa only [hchar] using hμ)⟩

end NLAlib
