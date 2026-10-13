import NLAlib.Matrix.Spectral.EigenvectorDeflationSpectrum

/-!
# Block coordinates for a paired eigenline and its perturbation

The distinguished coordinate and its complement give the scalar/block
split used by the Schur-complement eigenvalue equation. The leading perturbed
entry is the normalized left–right pairing. Source: Horn–Johnson (2013),
Lemmas 6.3.10 and Theorem 6.3.12; atlas `simple-eigenvalue-perturbation`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

omit [Fintype n] in
/-- Splitting an isolated coordinate from its complement gives a scalar/direct-sum block matrix. Source: Horn–Johnson (2013), Lemma 6.3.10;
the two subtype blocks are the distinguished coordinate and all others. -/
theorem submatrix_eq_fromBlocks_of_isolated_coordinate (M : Matrix n n K) (i : n) (μ : K)
    (hcol : ∀ j, M j i = if j = i then μ else 0)
    (hrow : ∀ j, M i j = if j = i then μ else 0) :
    M.submatrix (Equiv.sumCompl (fun j => j = i)) (Equiv.sumCompl (fun j => j = i)) =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : {j : n // j = i} => μ)) 0 0
        (M.submatrix (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val)) := by
  classical
  let : Unique {j : n // j = i} := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  ext a b
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change M a.val b.val = Matrix.diagonal (fun _ : {j : n // j = i} => μ) a b
      rw [a.property, b.property, hcol]
      simp only [ite_true, Matrix.diagonal_apply, Subsingleton.elim a b, ite_true]
    | inr b =>
      change M a.val b.val = 0
      rw [a.property, hrow]
      exact if_neg b.property
  | inr a =>
    cases b with
    | inl b =>
      change M a.val b.val = 0
      rw [b.property, hcol]
      exact if_neg a.property
    | inr b => rfl

omit [Fintype n] in
/-- Any perturbation matrix decomposes into its leading scalar, row,
column and trailing block in the isolated-coordinate split.
Horn–Johnson (2013), proof of Theorem 6.3.12. -/
theorem submatrix_eq_fromBlocks_scalar_row_col (F : Matrix n n K) (i : n) :
    F.submatrix (Equiv.sumCompl (fun j => j = i)) (Equiv.sumCompl (fun j => j = i)) =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : {j : n // j = i} => F i i))
        (Matrix.replicateRow {j : n // j = i} (fun j : {j : n // j ≠ i} => F i j.val))
        (Matrix.replicateCol {j : n // j = i} (fun j : {j : n // j ≠ i} => F j.val i))
        (F.submatrix (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val)) := by
  classical
  let : Unique {j : n // j = i} := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  ext a b
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change F a.val b.val = Matrix.diagonal (fun _ : {j : n // j = i} => F i i) a b
      rw [a.property, b.property]
      simp only [Matrix.diagonal_apply, Subsingleton.elim a b, ite_true]
    | inr b =>
      change F a.val b.val = F i b.val
      rw [a.property]
  | inr a =>
    cases b with
    | inl b =>
      change F a.val b.val = F a.val i
      rw [b.property]
    | inr b => rfl

/-- Nonsingular similarity preserves the characteristic polynomial.
Source: Horn–Johnson (2013), §1.3; this is the cyclic characteristic identity. -/
theorem charpoly_nonsing_inv_mul_mul_eq (A S : Matrix n n K) (hS : IsUnit S) :
    (S⁻¹ * A * S).charpoly = A.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv S (S.isUnit_iff_isUnit_det.mp hS), Matrix.one_mul]

/-- Nonsingular similarity preserves spectral membership.
Source: Horn–Johnson (2013), §1.3; root multiplicities are preserved as well. -/
theorem mem_spectrum_nonsing_inv_mul_mul_iff (A S : Matrix n n K) (hS : IsUnit S) (μ : K) :
    μ ∈ spectrum K (S⁻¹ * A * S) ↔ μ ∈ spectrum K A := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly,
    charpoly_nonsing_inv_mul_mul_eq A S hS]

/-- The leading conjugated perturbation entry is exactly the normalized
left–right perturbation pairing. Source: Horn–Johnson (2013), Theorem 6.3.12;
for complex left columns use their conjugate row in the hypotheses. -/
theorem nonsing_inv_mul_mul_apply_eq_dotProduct_mulVec_div
    (S E : Matrix n n K) (i : n) (x y : n → K)
    (hcol : Matrix.col S i = x) (hrow : ∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) :
    (S⁻¹ * E * S) i i = (y ⬝ᵥ (E *ᵥ x)) / (y ⬝ᵥ x) := by
  rw [Matrix.mul_assoc]
  change (fun j => S⁻¹ i j) ⬝ᵥ (E *ᵥ Matrix.col S i) = _
  rw [hcol]
  have hrowfun : (fun j => S⁻¹ i j) = (y ⬝ᵥ x)⁻¹ • y := by
    funext j
    simp only [hrow, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hrowfun, smul_dotProduct, smul_eq_mul, div_eq_mul_inv, mul_comm]

end NLAlib
