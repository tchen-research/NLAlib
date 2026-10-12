import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Complex.Basic

/-!
# Transport of Hermitian eigenvalue lists

Sorted eigenvalue lists `eigenvalues₀` depend only on the characteristic polynomial: equal
matrices (`eigenvalues₀_eq_of_matrix_eq`), matrices with equal characteristic polynomials
(`eigenvalues₀_eq_of_charpoly_eq`), relabelled matrices (`eigenvalues₀_reindex`) and the
complexification of a real symmetric matrix (`eigenvalues₀_map_ofReal`) have the same sorted
spectrum, independently of the Hermitian witnesses. This is the basic transport interface used
in Gram decomposition, singular-value and congruence arguments.
Source: Horn–Johnson 2013, §4.1.
-/

noncomputable section

namespace NLAlib

/-- Equal Hermitian matrices have equal sorted eigenvalue lists.
Mathlib's spectral definition and proof irrelevance; helper for
`singular-value-interlacing` and congruence spectrum comparisons. -/
theorem eigenvalues₀_eq_of_matrix_eq {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [RCLike 𝕜] {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : hA.eigenvalues₀ = hB.eigenvalues₀ := by
  subst B
  rfl

/-- Hermitian matrices (over `ℝ` or `ℂ`) with equal characteristic polynomials have the same
sorted eigenvalue list. Horn–Johnson 2013, Section 4.1. -/
theorem eigenvalues₀_eq_of_charpoly_eq {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A.charpoly = B.charpoly) : hA.eigenvalues₀ = hB.eigenvalues₀ := by
  apply List.ofFn_inj.mp
  rw [← hA.sort_roots_charpoly_eq_eigenvalues₀,
    ← hB.sort_roots_charpoly_eq_eigenvalues₀, h]

/-- Sorted eigenvalues are invariant under equivalent labels, with the canonical
dimension cast. Horn–Johnson 2013, permutation similarity; multiplicities included.
-/
theorem eigenvalues₀_reindex {n p : Type*} [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (e : n ≃ p) (i : Fin (Fintype.card n)) :
    (hA.reindex e).eigenvalues₀ (Fin.cast (Fintype.card_congr e) i) = hA.eigenvalues₀ i := by
  have hl : List.ofFn (hA.reindex e).eigenvalues₀ = List.ofFn hA.eigenvalues₀ := by
    rw [← (hA.reindex e).sort_roots_charpoly_eq_eigenvalues₀,
      ← hA.sort_roots_charpoly_eq_eigenvalues₀, Matrix.charpoly_reindex]
  have hc := List.ofFn_congr (Fintype.card_congr e) hA.eigenvalues₀
  have hf := List.ofFn_inj.mp (hl.trans hc)
  simpa only [Fin.cast] using congrFun hf (Fin.cast (Fintype.card_congr e) i)

/-- Complexification preserves the full ordered spectrum of a real
symmetric matrix. Horn–Johnson 2013, Section 4.1; eigenvalues have exactly
their original multiplicities. -/
theorem eigenvalues₀_map_ofReal {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (hC : (A.map Complex.ofReal).IsHermitian) :
    hC.eigenvalues₀ = hA.eigenvalues₀ := by
  have hmap : (A.map Complex.ofReal).charpoly = A.charpoly.map Complex.ofRealHom :=
    Matrix.charpoly_map A Complex.ofRealHom
  apply List.ofFn_inj.mp
  rw [← hC.sort_roots_charpoly_eq_eigenvalues₀,
    ← hA.sort_roots_charpoly_eq_eigenvalues₀, hmap,
    hA.splits_charpoly.roots_map]
  simp only [Multiset.map_map, Function.comp_def, RCLike.re_to_real]
  rfl

end NLAlib
