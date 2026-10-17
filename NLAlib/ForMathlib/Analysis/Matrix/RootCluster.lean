import NLAlib.ForMathlib.Analysis.Matrix.Charpoly
import NLAlib.ForMathlib.Analysis.Complex.Polynomial.RootCluster
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Analytic sums of separated characteristic roots

For an affine matrix pencil whose spectrum avoids the real axis at a given
parameter, the sum of its upper-half-plane eigenvalues is analytic locally.
Characteristic roots retain their algebraic multiplicities; individual
eigenvalues may collide within the selected half-plane.
-/

noncomputable section

open Complex Polynomial
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A full indexed family of distinct spectral points gives exactly the
characteristic-root multiset, with no further roots or hidden multiplicities. -/
theorem roots_charpoly_eq_map_of_injective_mem_spectrum
    (M : Matrix n n ℂ) (ev : n → ℂ) (hev : Function.Injective ev)
    (hmem : ∀ i, ev i ∈ spectrum ℂ M) :
    M.charpoly.roots = Finset.univ.val.map ev := by
  classical
  let S : Finset ℂ := Finset.univ.map ⟨ev, hev⟩
  have hroots : M.charpoly.roots = S.val := by
    apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
    · intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
      exact (Matrix.mem_spectrum_iff_isRoot_charpoly.mp (hmem i)).eq_zero
    · simp [S, Matrix.charpoly_natDegree_eq_dim]
    · exact M.charpoly_monic.ne_zero
  simpa [S] using hroots

/-- Selecting characteristic roots by a predicate agrees with selecting a
complete indexed list of distinct eigenvalues. -/
theorem sum_filter_roots_charpoly_eq_sum_ite_of_injective_mem_spectrum
    (M : Matrix n n ℂ) (ev : n → ℂ) (hev : Function.Injective ev)
    (hmem : ∀ i, ev i ∈ spectrum ℂ M) (p : ℂ → Prop) [DecidablePred p] :
    (M.charpoly.roots.filter p).sum = ∑ i, if p (ev i) then ev i else 0 := by
  classical
  rw [roots_charpoly_eq_map_of_injective_mem_spectrum M ev hev hmem]
  rw [Multiset.filter_map]
  change (∑ i ∈ Finset.univ.filter (fun i => p (ev i)), ev i) = _
  rw [Finset.sum_filter]

/-- An affine complex matrix pencil has an analytic sum of its upper
characteristic roots wherever its spectrum is disjoint from the real axis.
No normality, eigenvalue labelling, or simplicity assumption is required. -/
theorem analyticAt_sum_filter_roots_charpoly_affine_upper
    (A E : Matrix n n ℂ) (u : ℂ)
    (hreal : ∀ z ∈ spectrum ℂ (A + u • E), z.im ≠ 0) :
    AnalyticAt ℂ (fun v : ℂ => ((A + v • E).charpoly.roots.filter
      (fun z => 0 < z.im)).sum) u := by
  classical
  let a : Fin (Fintype.card n + 1) → ℂ → ℂ := fun i v => (A + v • E).charpoly.coeff i
  let q : Fin (Fintype.card n + 1) → ℂ[X] := fun i => X ^ (i : ℕ)
  have hP (v : ℂ) : ∑ i, a i v • q i = (A + v • E).charpoly := by
    dsimp [a, q]
    change (∑ i : Fin (Fintype.card n + 1),
      (fun k : ℕ => (A + v • E).charpoly.coeff k • (X : ℂ[X]) ^ k) i) = _
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      (A + v • E).charpoly.coeff k • (X : ℂ[X]) ^ k)]
    simpa only [Polynomial.smul_eq_C_mul] using
      ((A + v • E).charpoly.as_sum_range_C_mul_X_pow'
        (by rw [Matrix.charpoly_natDegree_eq_dim]; omega)).symm
  have hset (v : ℂ) : {z | z ∈ (∑ i, a i v • q i).roots} =
      spectrum ℂ (A + v • E) := by
    ext z
    rw [hP]
    exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).trans
      (Matrix.mem_spectrum_iff_isRoot_charpoly).symm
  have hroots : UpperHemicontinuousAt
      (fun v => {z | z ∈ (∑ i, a i v • q i).roots}) u := by
    simp only [hset]
    exact (upperHemicontinuous_spectrum ℂ (Matrix n n ℂ)).upperHemicontinuousAt _ |>.comp
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have h := Polynomial.analyticAt_sum_filter_roots_upper_of_upperHemicontinuous q a
    (fun i => Matrix.analyticAt_charpoly_coeff_affine A E i u)
    (by rw [hP]; exact (Matrix.charpoly_monic _).ne_zero) hroots
    (fun z hz => hreal z (by rw [← hset u]; exact hz))
  simpa only [hP] using h

end Matrix
