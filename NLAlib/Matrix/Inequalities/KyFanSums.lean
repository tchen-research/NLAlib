import NLAlib.Matrix.Spectral.Eigenframes
import NLAlib.Matrix.Inequalities.KyFanNorms
import NLAlib.Matrix.Inequalities.MajorizationProperties
/-!
# Ky Fan sum inequalities and spectral majorization

An optimizing frame for the sum splits into two admissible traces. This proves
the full eigenvalue and singular-value prefix majorization conclusions.
Source: Fan (1949), Theorem 1; Horn–Johnson (2013), Corollary 4.3.39.
Atlas: `ky-fan-maximum-principle`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- The trace is the full sum of the decreasing eigenvalue list. -/
theorem trace_eq_sum_eigenvalues₀ {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) : A.trace = ∑ i, hA.eigenvalues₀ i := by
  calc
    A.trace = ∑ i, hA.eigenvalues i := hA.trace_eq_sum_eigenvalues
    _ = ∑ i, hA.eigenvalues₀ i := sum_eigenvalues_eq_sum_sorted hA id

/-- Every top eigenvalue sum of a sum is bounded by the sum of the two top
eigenvalue sums. Fan (1949), Theorem 1, including empty and full prefixes.
atlas: ky-fan-maximum-principle -/
theorem eigenvaluePrefix_add_le {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (A + B).IsHermitian) {k : ℕ} (hk : k ≤ Fintype.card n) :
    eigenvaluePrefix hAB k ≤ eigenvaluePrefix hA k + eigenvaluePrefix hB k := by
  let Q := topEigenframe hAB hk
  have hQ : HasOrthonormalCols Q := hasOrthonormalCols_topEigenframe hAB hk
  have ht : (Qᵀ * (A + B) * Q).trace = eigenvaluePrefix hAB k := by
    rw [compression_topEigenframe_eq_diagonal hAB hk, Matrix.trace_diagonal,
      eigenvaluePrefix_eq_sum_castLE hAB hk]
    rfl
  rw [← ht, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  have h1 := trace_compression_le_eigenvaluePrefix hA hQ
  have h2 := trace_compression_le_eigenvaluePrefix hB hQ
  simp only [RCLike.re_to_real, Matrix.conjTranspose_eq_transpose_of_trivial,
    Fintype.card_fin] at h1 h2
  exact add_le_add h1 h2

/-- The spectrum of a real symmetric sum is majorized by the coordinatewise
sum of the two decreasing spectra. Equality of totals follows from trace.
Fan (1949), Theorem 1; Horn–Johnson (2013), Corollary 4.3.39.
atlas: ky-fan-maximum-principle -/
theorem majorized_eigenvalues₀_add {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Majorized (hA.add hB).eigenvalues₀ (hA.eigenvalues₀ + hB.eigenvalues₀) := by
  constructor
  · intro k hk
    have hkN : k ≤ Fintype.card n := by simpa using hk
    change sumLargest (hA.add hB).eigenvalues₀ k ≤
      sumLargest (fun i => hA.eigenvalues₀ i + hB.eigenvalues₀ i) k
    rw [sumLargest_eq_prefix_of_antitone _ (hA.add hB).eigenvalues₀_antitone,
      sumLargest_eq_prefix_of_antitone _ (hA.eigenvalues₀_antitone.add hB.eigenvalues₀_antitone)]
    rw [sum_fin_ite_lt_eq_sum_castLE hkN, sum_fin_ite_lt_eq_sum_castLE hkN]
    simp only [Finset.sum_add_distrib]
    exact eigenvaluePrefix_add_le hA hB (hA.add hB) hkN
  · rw [← trace_eq_sum_eigenvalues₀ (hA.add hB)]
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [← trace_eq_sum_eigenvalues₀ hA, ← trace_eq_sum_eigenvalues₀ hB, Matrix.trace_add]

/-- Singular values of a sum are weakly majorized by the coordinatewise sum
of its two decreasing singular-value lists, for arbitrary finite matrix indices.
Fan (1949), Theorem 1; includes empty matrix shapes.
atlas: ky-fan-maximum-principle -/
theorem weaklyMajorized_singularValues_add {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (A B : Matrix m n ℝ) :
    WeaklyMajorized
      (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues (A + B) i)
      (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
        singularValues A i + singularValues B i) := by
  intro k hk
  have hkN : k ≤ min (Fintype.card m) (Fintype.card n) := by simpa using hk
  have hantiA : Antitone (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
      singularValues A i) := fun i j hij => singularValues_antitone _ hij
  have hantiB : Antitone (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
      singularValues B i) := fun i j hij => singularValues_antitone _ hij
  have hantiAB : Antitone (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
      singularValues (A + B) i) := fun i j hij => singularValues_antitone _ hij
  rw [sumLargest_eq_prefix_of_antitone _ hantiAB,
    sumLargest_eq_prefix_of_antitone _ (hantiA.add hantiB)]
  rw [sum_fin_ite_lt_eq_sum_range hkN (fun i => singularValues (A + B) i),
    sum_fin_ite_lt_eq_sum_range hkN (fun i => singularValues A i + singularValues B i)]
  rw [Finset.sum_add_distrib]
  exact kyFanNorm_add_le A B k

end NLAlib
