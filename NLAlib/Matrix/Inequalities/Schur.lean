import NLAlib.Matrix.Inequalities.MajorizationHLP
import NLAlib.Matrix.Functions.PolynomialCalculus
import NLAlib.Matrix.Functions.CFCTrace
/-!
# Schur's diagonal majorization and Peierls' inequality

For a Hermitian matrix over `𝕜` (`ℝ` or `ℂ`) the squared moduli of the entries of its
eigenvector unitary form a doubly stochastic matrix (`norm_sq_entries_mem_doublyStochastic_of_hasOrthonormalCols`), so
the real diagonal `Re aᵢᵢ` is a doubly stochastic image of the spectrum and is majorized by it
(`majorized_diagonal_eigenvalues`, Schur's theorem); every diagonal entry lies between the
extreme eigenvalues (`re_diagonal_mem_Icc_eigenvalues₀`). Peierls' convex trace inequality
(`sum_convex_diagonal_le_trace_cfc`) is stated for real symmetric matrices.
Source: Horn–Johnson (2013), Theorem 4.3.45 and Corollary 4.3.46; Marshall–Olkin–Arnold (2011),
9.B.1. Atlas: `schur-horn`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared entry moduli `‖pᵢⱼ‖²` of a square matrix with orthonormal columns form a
doubly stochastic matrix. Horn–Johnson 2013, proof of Theorem 4.3.45. -/
theorem norm_sq_entries_mem_doublyStochastic_of_hasOrthonormalCols {P : Matrix n n 𝕜} (hP : HasOrthonormalCols P) :
    (Matrix.of fun i j => ‖P i j‖ ^ 2) ∈ doublyStochastic ℝ n := by
  have hPP : P * Pᴴ = 1 := mul_eq_one_comm.mp hP
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => sq_nonneg _, ?_, ?_⟩
  · intro i
    have h := congrArg (fun M : Matrix n n 𝕜 => RCLike.re (M i i)) hPP
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      RCLike.star_def, RCLike.mul_conj, map_sum, ← RCLike.ofReal_pow, RCLike.ofReal_re, RCLike.one_re] at h
    simpa only [Matrix.of_apply] using h
  · intro j
    have h := congrArg (fun M : Matrix n n 𝕜 => RCLike.re (M j j)) (show Pᴴ * P = 1 from hP)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      RCLike.star_def, RCLike.conj_mul, map_sum, ← RCLike.ofReal_pow, RCLike.ofReal_re, RCLike.one_re] at h
    simpa only [Matrix.of_apply] using h

/-- The eigenvector unitary of a Hermitian matrix has orthonormal columns. -/
theorem hasOrthonormalCols_eigenvectorUnitary {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    HasOrthonormalCols (hA.eigenvectorUnitary : Matrix n n 𝕜) := by
  rw [HasOrthonormalCols, ← Matrix.star_eq_conjTranspose]
  exact Unitary.coe_star_mul_self hA.eigenvectorUnitary

/-- Real form: the squared entries of a real orthogonal matrix form a doubly stochastic matrix.
Horn–Johnson 2013, proof of Theorem 4.3.45. -/
theorem sq_entries_mem_doublyStochastic {P : Matrix n n ℝ} (hP : HasOrthonormalCols P) :
    (Matrix.of fun i j => P i j ^ 2) ∈ doublyStochastic ℝ n := by
  simpa only [Real.norm_eq_abs, sq_abs] using norm_sq_entries_mem_doublyStochastic_of_hasOrthonormalCols hP

/-- The real diagonal `Re aᵢᵢ` of a Hermitian matrix is the doubly stochastic image of its
eigenvalues under the squared moduli of the eigenvector unitary. Horn–Johnson 2013, proof of
Theorem 4.3.45. -/
theorem re_diagonal_eq_norm_sq_eigenvectorUnitary_mulVec {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    (fun i => RCLike.re (A i i)) =
      (Matrix.of fun i j => ‖(hA.eigenvectorUnitary : Matrix n n 𝕜) i j‖ ^ 2) *ᵥ
        hA.eigenvalues := by
  let U : Matrix n n 𝕜 := hA.eigenvectorUnitary
  have hs : A = U * Matrix.diagonal (fun i => (hA.eigenvalues i : 𝕜)) * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, U] using hA.spectral_theorem
  funext i
  calc
    RCLike.re (A i i) =
        RCLike.re ((U * Matrix.diagonal (fun j => (hA.eigenvalues j : 𝕜)) * Uᴴ) i i) :=
      congrArg (fun M : Matrix n n 𝕜 => RCLike.re (M i i)) hs
    _ = _ := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, RCLike.star_def, map_sum,
        Matrix.mulVec, dotProduct, Matrix.of_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_right_comm, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
        RCLike.ofReal_re]

/-- **Schur's theorem.** The real diagonal of a Hermitian matrix is majorized by its spectrum
(`Majorized` sorts intrinsically; arbitrary finite indices, repeated eigenvalues and empty
shapes are included). Over `ℝ` the diagonal is `Matrix.diag A` (`RCLike.re_to_real`).
Horn–Johnson 2013, Theorem 4.3.45.
atlas: schur-horn -/
theorem majorized_diagonal_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    Majorized (fun i => RCLike.re (A i i)) hA.eigenvalues := by
  rw [re_diagonal_eq_norm_sq_eigenvectorUnitary_mulVec hA]
  exact majorized_mulVec_of_doublyStochastic hA.eigenvalues
    (norm_sq_entries_mem_doublyStochastic_of_hasOrthonormalCols (hasOrthonormalCols_eigenvectorUnitary hA))

/-- Every real diagonal entry of a Hermitian matrix lies between its smallest and largest
eigenvalues. Horn–Johnson 2013, Corollary 4.3.46. -/
theorem re_diagonal_mem_Icc_eigenvalues₀ {A : Matrix n n 𝕜} (hA : A.IsHermitian) (i : n)
    (hcard : 0 < Fintype.card n) :
    RCLike.re (A i i) ∈ Set.Icc
      (hA.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt hcard (by decide)⟩)
      (hA.eigenvalues₀ ⟨0, hcard⟩) := by
  let D := Matrix.of fun i j => ‖(hA.eigenvectorUnitary : Matrix n n 𝕜) i j‖ ^ 2
  have hD := norm_sq_entries_mem_doublyStochastic_of_hasOrthonormalCols (hasOrthonormalCols_eigenvectorUnitary hA)
  rw [mem_doublyStochastic_iff_sum] at hD
  have hrow : ∑ j, D i j = 1 := hD.2.1 i
  have hnonneg : ∀ j, 0 ≤ D i j := fun j => hD.1 i j
  have heq := congrFun (re_diagonal_eq_norm_sq_eigenvectorUnitary_mulVec hA) i
  change RCLike.re (A i i) = ∑ j, D i j * hA.eigenvalues j at heq
  rw [heq]
  constructor
  · calc
      _ = ∑ j, D i j * hA.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_lt hcard (by decide)⟩ := by
        rw [← Finset.sum_mul, hrow, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
        (hA.eigenvalues₀_antitone (by exact Nat.le_pred_of_lt (Fin.isLt _))) (hnonneg j)
  · calc
      _ ≤ ∑ j, D i j * hA.eigenvalues₀ ⟨0, hcard⟩ := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hA.eigenvalues₀_antitone (by exact Nat.zero_le _)) (hnonneg j)
      _ = _ := by rw [← Finset.sum_mul, hrow, one_mul]

/-- **Peierls' inequality.** For a real symmetric `A` and a convex `φ`,
`∑ᵢ φ(aᵢᵢ) ≤ tr φ(A)`; no integrability or smoothness hypothesis. Horn–Johnson 2013,
Theorem 4.3.45; Marshall–Olkin–Arnold 2011, 9.B.1.
atlas: schur-horn -/
theorem sum_convex_diagonal_le_trace_cfc {A : Matrix n n ℝ} (hA : A.IsHermitian) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) : (∑ i, φ (A i i)) ≤ (cfc φ A).trace := by
  have ht := re_trace_cfc_eq_sum_eigenvalues hA φ
  simp only [RCLike.re_to_real] at ht
  rw [ht]
  have h := (majorized_diagonal_eigenvalues hA).sum_convex_le hφ
  simpa only [RCLike.re_to_real] using h

end NLAlib
