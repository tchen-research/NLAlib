import NLAlib.Matrix.Structured.KroneckerNormRank
import NLAlib.Matrix.Spectral.SingularValueSpectrum
/-!
# Singular-value multisets of rectangular Kronecker products

The full domain-side singular-value list is the pairwise product of the two
domain-side lists. Each list includes its domain zero padding. This is a faithful
multiplicity-aware formulation for arbitrary rectangular shapes: unlike the
unqualified thin-list formula, it includes the necessary extra zero singular values.
Source: Horn–Johnson 1991, Theorem 4.2.15; the operator derivation manuscript,
Section 4, rectangular zero-multiplicity correction. Atlas: `kronecker-spectral`.
-/

noncomputable section
open scoped Matrix Kronecker

namespace NLAlib

/-- Tensoring two SVD factorizations gives a full orthogonal factorization of the
Kronecker product. Horn–Johnson 1991, Theorem 4.2.15. The rectangular middle
factor need not be sorted in the lexicographic product-coordinate order.
atlas: kronecker-spectral (partial) -/
theorem IsSVD.kronecker_factorization {m n p q : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {B : Matrix (Fin p) (Fin q) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}
    {P : Matrix (Fin p) (Fin p) ℝ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hA : IsSVD A U V) (hB : IsSVD B P Q) :
    A ⊗ₖ B = (U ⊗ₖ P) *
      ((rectDiag (singularValues A) : Matrix (Fin m) (Fin n) ℝ) ⊗ₖ
        (rectDiag (singularValues B) : Matrix (Fin p) (Fin q) ℝ)) * (V ⊗ₖ Q)ᵀ := by
  conv_lhs => rw [hA.eq, hB.eq]
  rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul, Matrix.kroneckerMap_transpose]

/-- The domain-side multiset of native singular values is the square-root Gram
spectrum, including every domain zero. Horn–Johnson 2013, Section 2.6.
-/
theorem multiset_toEuclideanLin_singularValues_eq_sqrt_eigenvalues {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) :
    (Finset.univ : Finset (Fin (Fintype.card n))).val.map
      (fun i : Fin (Fintype.card n) => A.toEuclideanLin.singularValues (i : ℕ)) =
    (Finset.univ : Finset n).val.map
      (fun i => Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)) := by
  have hG := Matrix.isHermitian_conjTranspose_mul_self A
  have hs : (fun i : Fin (Fintype.card n) => A.toEuclideanLin.singularValues (i : ℕ)) =
      fun i => Real.sqrt (hG.eigenvalues₀ i) := by
    funext i
    rw [← singularValues_eq_linearMap, ← sq_singularValues_eq_eigenvalues₀ A i,
      Real.sqrt_sq (singularValues_nonneg A _)]
  rw [hs]
  have he : (Finset.univ : Finset n).val.map hG.eigenvalues =
      (Finset.univ : Finset (Fin (Fintype.card n))).val.map hG.eigenvalues₀ := by
    simpa using hG.roots_charpoly_eq_eigenvalues.symm.trans hG.roots_charpoly_eq_eigenvalues₀
  simpa only [Multiset.map_map, Function.comp_def] using
    (congrArg (Multiset.map Real.sqrt) he).symm

private theorem map_product_maps {α β γ δ ζ : Type*} (s : Multiset α) (t : Multiset β)
    (f : α → γ) (g : β → δ) (h : γ × δ → ζ) :
    ((s.map f) ×ˢ (t.map g)).map h = (s ×ˢ t).map (fun ij => h (f ij.1, g ij.2)) := by
  simp only [SProd.sprod, Multiset.product, Multiset.map_bind, Multiset.bind_map,
    Multiset.map_map, Function.comp_def]

/-- The singular values of a rectangular Kronecker product are all pairwise
products of the two native domain-side singular-value lists, with multiplicities.
Horn–Johnson 1991, Theorem 4.2.15. Domain lists have `card n`, `card q`, and
`card n * card q` entries; each includes its full domain-side zero padding.
This covers empty dimensions and the additional rectangular zeros automatically.
atlas: kronecker-spectral (partial) -/
theorem multiset_toEuclideanLin_singularValues_kronecker {m n p q : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q] [DecidableEq n] [DecidableEq q]
    (A : Matrix m n ℝ) (B : Matrix p q ℝ) :
    (Finset.univ : Finset (Fin (Fintype.card (n × q)))).val.map
      (fun i : Fin (Fintype.card (n × q)) => (A ⊗ₖ B).toEuclideanLin.singularValues (i : ℕ)) =
    (((Finset.univ : Finset (Fin (Fintype.card n))).val.map
      (fun i : Fin (Fintype.card n) => A.toEuclideanLin.singularValues (i : ℕ))) ×ˢ
      ((Finset.univ : Finset (Fin (Fintype.card q))).val.map
      (fun i : Fin (Fintype.card q) => B.toEuclideanLin.singularValues (i : ℕ)))).map (fun xy => xy.1 * xy.2) := by
  classical
  let hA := Matrix.isHermitian_conjTranspose_mul_self A
  let hB := Matrix.isHermitian_conjTranspose_mul_self B
  let hT := Matrix.isHermitian_conjTranspose_mul_self (A ⊗ₖ B)
  have hGram : (A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = (Aᴴ * A) ⊗ₖ (Bᴴ * B) := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  have heig : (Finset.univ : Finset (n × q)).val.map hT.eigenvalues =
      (Finset.univ : Finset (n × q)).val.map
        (fun ij => hA.eigenvalues ij.1 * hB.eigenvalues ij.2) := by
    have hc : hT.eigenvalues = (isHermitian_kronecker hA hB).eigenvalues := by
      rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
      rw [hGram]
    rw [hc]
    exact multiset_eigenvalues_kronecker hA hB
  rw [multiset_toEuclideanLin_singularValues_eq_sqrt_eigenvalues,
    multiset_toEuclideanLin_singularValues_eq_sqrt_eigenvalues,
    multiset_toEuclideanLin_singularValues_eq_sqrt_eigenvalues,
    map_product_maps]
  have hsqrt := congrArg (Multiset.map Real.sqrt) heig
  simp only [Multiset.map_map, Function.comp_def] at hsqrt
  calc
    _ = (Finset.univ : Finset (n × q)).val.map
        (fun ij => Real.sqrt (hA.eigenvalues ij.1 * hB.eigenvalues ij.2)) := hsqrt
    _ = (Finset.univ : Finset (n × q)).val.map
        (fun ij => Real.sqrt (hA.eigenvalues ij.1) * Real.sqrt (hB.eigenvalues ij.2)) := by
      congr 1
      funext ij
      rw [Real.sqrt_mul (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A ij.1)]
    _ = _ := by rw [← Finset.product_val, Finset.univ_product_univ]

end NLAlib
