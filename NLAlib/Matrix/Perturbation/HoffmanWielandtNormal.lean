import NLAlib.Matrix.Spectral.NormalSpectral
import NLAlib.Matrix.Subspaces.ComplexProjectionBounds
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Hoffman–Wielandt for complex normal matrices

The squared overlaps of two unitary eigenbases are doubly stochastic.
Birkhoff's theorem selects a permutation with cost no greater than the
Frobenius residual cost. Source: Horn–Johnson (2013), Theorem 6.3.5;
atlas `hoffman-wielandt-normal`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.Frobenius

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Squared complex unitary entries form a doubly stochastic matrix.
Source: Horn–Johnson (2013), proof of Theorem 6.3.5; row and column norm
identities apply without a nonempty-shape hypothesis. -/
theorem norm_sq_entries_mem_doublyStochastic (U : Matrix.unitaryGroup n ℂ) :
    (Matrix.of fun i j => ‖(U : Matrix n n ℂ) i j‖ ^ 2) ∈ doublyStochastic ℝ n := by
  have hrow : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self U
  have hcol : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun _ _ => sq_nonneg _, ?_, ?_⟩
  · intro i
    have h := congrArg (fun M : Matrix n n ℂ => (M i i).re) hrow
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.re_sum, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.one_re, Matrix.one_apply_eq, Matrix.of_apply] using h
  · intro j
    have h := congrArg (fun M : Matrix n n ℂ => (M j j).re) hcol
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.re_sum, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.one_re, Matrix.one_apply_eq, Matrix.of_apply] using h

/-- A doubly stochastic matching cost dominates some permutation cost.
Source: Birkhoff's theorem and Horn–Johnson (2013), proof of Theorem 6.3.5;
the cost array is arbitrary real data, including signed costs. -/
theorem exists_perm_sum_le_doublyStochastic_cost (C : Matrix n n ℝ)
    {W : Matrix n n ℝ} (hW : W ∈ doublyStochastic ℝ n) :
    ∃ σ : Equiv.Perm n, (∑ i, C i (σ i)) ≤ ∑ i, ∑ j, W i j * C i j := by
  let f : Matrix n n ℝ →ₗ[ℝ] ℝ :=
    { toFun X := ∑ i, ∑ j, X i j * C i j
      map_add' X Y := by simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' c X := by
        simp only [RingHom.id_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc,
          Finset.mul_sum] }
  have hconv : W ∈ convexHull ℝ {σ.permMatrix ℝ | σ : Equiv.Perm n} := by
    rwa [← doublyStochastic_eq_convexHull_permMatrix]
  obtain ⟨P, ⟨σ, rfl⟩, hP⟩ := (f.concaveOn convex_univ).exists_le_of_mem_convexHull
    (Set.subset_univ _) hconv
  refine ⟨σ, ?_⟩
  simpa [f, Equiv.Perm.permMatrix, Equiv.toPEquiv_apply] using hP

/-- For any two unitary diagonalizations there is a matching of their
diagonal eigenvalues with squared error at most the squared Frobenius matrix
error. Source: Horn–Johnson (2013), Theorem 6.3.5; arbitrary eigenvalue orders,
repeated eigenvalues and empty matrices are included.
atlas: hoffman-wielandt-normal (partial) -/
theorem exists_perm_sum_sq_le_frobenius_norm_sq_of_unitary_diagonalizations
    (U V : Matrix.unitaryGroup n ℂ) (a b : n → ℂ) {A B : Matrix n n ℂ}
    (hA : A = (U : Matrix n n ℂ) * Matrix.diagonal a * (U : Matrix n n ℂ)ᴴ)
    (hB : B = (V : Matrix n n ℂ) * Matrix.diagonal b * (V : Matrix n n ℂ)ᴴ) :
    ∃ σ : Equiv.Perm n, (∑ i, ‖a i - b (σ i)‖ ^ 2) ≤ ‖A - B‖ ^ 2 := by
  let C : Matrix.unitaryGroup n ℂ := star U * V
  have hUU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self U
  have hUUt : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self U
  have hVV : (V : Matrix n n ℂ) * (V : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self V
  have hVVt : (V : Matrix n n ℂ)ᴴ * (V : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self V
  have hC : (C : Matrix n n ℂ) = (U : Matrix n n ℂ)ᴴ * (V : Matrix n n ℂ) := rfl
  have hAU : (U : Matrix n n ℂ)ᴴ * A = Matrix.diagonal a * (U : Matrix n n ℂ)ᴴ := by
    rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUUt, Matrix.one_mul]
  have hBV : B * (V : Matrix n n ℂ) = (V : Matrix n n ℂ) * Matrix.diagonal b := by
    rw [hB, Matrix.mul_assoc, hVVt, Matrix.mul_one]
  have hres : (U : Matrix n n ℂ)ᴴ * (A - B) * (V : Matrix n n ℂ) =
      Matrix.diagonal a * (C : Matrix n n ℂ) - (C : Matrix n n ℂ) * Matrix.diagonal b := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hAU,
      Matrix.mul_assoc (Matrix.diagonal a) (U : Matrix n n ℂ)ᴴ,
      Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ B, hBV,
      ← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (V : Matrix n n ℂ), ← hC]
  have hinv : ‖(U : Matrix n n ℂ)ᴴ * (A - B) * (V : Matrix n n ℂ)‖ ^ 2 = ‖A - B‖ ^ 2 := by
    have hUt : (U : Matrix n n ℂ)ᴴᴴ * (U : Matrix n n ℂ)ᴴ = 1 := by
      simpa only [Matrix.conjTranspose_conjTranspose] using hUU
    have hVt : (V : Matrix n n ℂ)ᴴᴴ * (V : Matrix n n ℂ)ᴴ = 1 := by
      simpa only [Matrix.conjTranspose_conjTranspose] using hVV
    have hh := frobenius_norm_sq_mul_conjTranspose_right_of_conjTranspose_mul_eq_one
      hVt ((U : Matrix n n ℂ)ᴴ * (A - B))
    simpa only [Matrix.conjTranspose_conjTranspose,
      frobenius_norm_sq_mul_left_of_conjTranspose_mul_eq_one hUt] using hh
  have hcost : (∑ i, ∑ j, ‖(C : Matrix n n ℂ) i j‖ ^ 2 * ‖a i - b j‖ ^ 2) =
      ‖A - B‖ ^ 2 := by
    rw [← hinv, hres, frobenius_norm_sq_eq_sum_norm_sq]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    have heq : a i * (C : Matrix n n ℂ) i j - (C : Matrix n n ℂ) i j * b j =
        (a i - b j) * (C : Matrix n n ℂ) i j := by ring
    rw [heq, norm_mul, mul_pow, mul_comm]
  obtain ⟨σ, hσ⟩ := exists_perm_sum_le_doublyStochastic_cost
    (Matrix.of fun i j => ‖a i - b j‖ ^ 2) (norm_sq_entries_mem_doublyStochastic C)
  exact ⟨σ, hσ.trans_eq hcost⟩

/-- Hoffman–Wielandt for arbitrary complex normal matrices: complete
characteristic eigenvalue lists admit a matching with Frobenius error bound.
Source: Horn–Johnson (2013), Theorem 6.3.5; the accompanying polynomial
identities certify multiplicities, including repeated and absent eigenvalues.
atlas: hoffman-wielandt-normal -/
theorem exists_eigenvalue_lists_perm_sum_sq_le_frobenius_norm_sq_of_normal
    {A B : Matrix n n ℂ} (hA : A * Aᴴ = Aᴴ * A) (hB : B * Bᴴ = Bᴴ * B) :
    ∃ (a b : n → ℂ) (σ : Equiv.Perm n),
      A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (a i)) ∧
      B.charpoly = ∏ i, (Polynomial.X - Polynomial.C (b i)) ∧
      (∑ i, ‖a i - b (σ i)‖ ^ 2) ≤ ‖A - B‖ ^ 2 := by
  obtain ⟨U, a, hUa⟩ := exists_unitary_diagonalization_of_normal hA
  obtain ⟨V, b, hVb⟩ := exists_unitary_diagonalization_of_normal hB
  obtain ⟨σ, hσ⟩ := exists_perm_sum_sq_le_frobenius_norm_sq_of_unitary_diagonalizations U V a b hUa hVb
  have hchar (W : Matrix.unitaryGroup n ℂ) (d : n → ℂ) :
      ((W : Matrix n n ℂ) * Matrix.diagonal d * (W : Matrix n n ℂ)ᴴ).charpoly =
        ∏ i, (Polynomial.X - Polynomial.C (d i)) := by
    have hWW : (W : Matrix n n ℂ)ᴴ * (W : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self W
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hWW, Matrix.one_mul,
      Matrix.charpoly_diagonal]
  exact ⟨a, b, σ, hUa ▸ hchar U a, hVb ▸ hchar V b, hσ⟩

end NLAlib
