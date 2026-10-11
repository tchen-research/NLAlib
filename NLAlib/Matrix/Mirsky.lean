import NLAlib.Matrix.RealDilationSpectrum
import NLAlib.Matrix.Lidskii
import NLAlib.Matrix.MajorizationProperties

/-!
# Rectangular Mirsky weak majorization

Selecting a top dilation slot for a positive singular-value increment and its
reversed bottom slot for a negative increment turns indexed Lidskii into the
full rectangular Mirsky inequality. Source: Bhatia 1997, Theorem IV.3.4;
the matrix-toolkit operator manuscript, equations (19)–(20). Atlas: `lidskii`.
-/
noncomputable section
open scoped Matrix
namespace NLAlib

private theorem eigenvaluePrefix_realDilation {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hk : k ≤ min m n) :
    eigenvaluePrefix (isHermitian_realDilation A) (k := k) (by simp; omega) =
      ∑ i : Fin k, singularValues A i := by
  apply Finset.sum_congr rfl
  intro i _
  have hi := eigenvalues₀_realDilation A (Fin.castLE (by omega : k ≤ m + n) i)
  have him : (i : ℕ) < m := lt_of_lt_of_le i.isLt (hk.trans (min_le_left m n))
  simpa [realDilationSpectrum, him, Fin.cast, Fin.castLE] using hi

/-- Every selected sum of absolute rectangular singular-value increments is
bounded by the same-sized top singular-value sum of the perturbation.
Bhatia 1997, Theorem IV.3.4; includes arbitrary subsets, multiplicities, empty
shapes and zero singular values. -/
theorem sum_abs_singularValues_add_sub_le_sum_prefix {m n : ℕ}
    (A E : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin (min m n))) :
    (∑ i ∈ S, |singularValues (A + E) i - singularValues A i|) ≤
      ∑ j : Fin S.card, singularValues E j := by
  classical
  let δ : Fin (min m n) → ℝ := fun i => singularValues (A + E) i - singularValues A i
  let f₀ : Fin (min m n) → Fin (m + n) := fun i =>
    if 0 ≤ δ i then Fin.castLE (by omega : min m n ≤ m + n) i else
      (Fin.castLE (by omega : min m n ≤ m + n) i).rev
  have hf₀ : Function.Injective f₀ := by
    intro i j hij
    have hv := congrArg Fin.val hij
    dsimp [f₀] at hv
    split_ifs at hv <;> simp only [Fin.val_castLE, Fin.val_rev] at hv
    all_goals
      have hi := i.isLt
      have hj := j.isLt
      apply Fin.ext
      omega
  let f : Fin (min m n) ↪ Fin (Fintype.card (Fin m ⊕ Fin n)) :=
    ⟨fun i => Fin.cast (by simp) (f₀ i), fun i j hij => hf₀ (Fin.ext (congrArg (fun k : Fin (Fintype.card (Fin m ⊕ Fin n)) => k.val) hij))⟩
  have hspectrum (C : Matrix (Fin m) (Fin n) ℝ) (i : Fin (min m n)) :
      (isHermitian_realDilation C).eigenvalues₀ (f i) =
        if 0 ≤ δ i then singularValues C i else -singularValues C i := by
    change (isHermitian_realDilation C).eigenvalues₀
      (Fin.cast (by simp) (if 0 ≤ δ i then Fin.castLE (by omega : min m n ≤ m + n) i
        else (Fin.castLE (by omega : min m n ≤ m + n) i).rev)) =
          if 0 ≤ δ i then singularValues C i else -singularValues C i
    split_ifs
    · exact eigenvalues₀_realDilation_top C i
    · exact eigenvalues₀_realDilation_bottom C i
  have hdiff (i : Fin (min m n)) :
      ((isHermitian_realDilation A).add (isHermitian_realDilation E)).eigenvalues₀ (f i) -
        (isHermitian_realDilation A).eigenvalues₀ (f i) = |δ i| := by
    rw [eigenvalues₀_eq_of_eq (realDilation_add A E).symm _ (isHermitian_realDilation (A + E))]
    rw [hspectrum, hspectrum]
    split_ifs with hi
    · exact (abs_of_nonneg hi).symm
    · dsimp [δ]
      rw [abs_of_neg (lt_of_not_ge hi)]
      ring
  have h := sum_eigenvalues₀_add_le_sum_add_eigenvaluePrefix
    (isHermitian_realDilation A) (isHermitian_realDilation E) (S.map f)
  have hcard : S.card ≤ min m n := by simpa using Finset.card_le_univ S
  have hprefix : eigenvaluePrefix (isHermitian_realDilation E) (k := (S.map f).card)
      (by simpa using Finset.card_le_univ (S.map f)) =
        ∑ j : Fin S.card, singularValues E j := by
    simpa only [Finset.card_map] using eigenvaluePrefix_realDilation E hcard
  rw [hprefix, Finset.sum_map, Finset.sum_map] at h
  have hdiffsum :
      (∑ i ∈ S, ((isHermitian_realDilation A).add (isHermitian_realDilation E)).eigenvalues₀ (f i)) -
        (∑ i ∈ S, (isHermitian_realDilation A).eigenvalues₀ (f i)) = ∑ i ∈ S, |δ i| := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => hdiff i
  change (∑ i ∈ S, |δ i|) ≤ _
  linarith

/-- Rectangular Mirsky: the entire absolute singular-value difference vector is
weakly majorized by the perturbation singular list. Bhatia 1997, Theorem IV.3.4.
The vector has the actual thin rectangular dimension, with rank-deficient zeros;
its coordinatewise differences are not assumed already sorted.
atlas: lidskii (partial) -/
theorem weaklyMajorized_abs_singularValues_add_sub {m n : ℕ}
    (A E : Matrix (Fin m) (Fin n) ℝ) :
    WeaklyMajorized (fun i : Fin (min m n) =>
      |singularValues (A + E) i - singularValues A i|)
      (fun i : Fin (min m n) => singularValues E i) := by
  classical
  rw [weaklyMajorized_iff_sum_le]
  intro S
  have hcard : S.card ≤ min m n := by simpa using Finset.card_le_univ S
  rw [sumLargest_eq_prefix_of_antitone _ (fun i j hij => singularValues_antitone E hij),
    sum_fin_ite_lt_eq_sum_castLE hcard]
  exact sum_abs_singularValues_add_sub_le_sum_prefix A E S

/-- Rectangular Mirsky on arbitrary finite real matrix row and column indices,
using Mathlib's actual native singular values. Bhatia 1997, Theorem IV.3.4.
All finite shapes, empty dimensions and padded singular zeros are included.
atlas: lidskii (partial) -/
theorem weaklyMajorized_abs_toEuclideanLin_singularValues_add_sub {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A E : Matrix m n ℝ) :
    WeaklyMajorized (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
      |(A + E).toEuclideanLin.singularValues i - A.toEuclideanLin.singularValues i|)
      (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => E.toEuclideanLin.singularValues i) := by
  classical
  have h := weaklyMajorized_abs_singularValues_add_sub
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
    (E.reindex (Fintype.equivFin m) (Fintype.equivFin n))
  have hadd : A.reindex (Fintype.equivFin m) (Fintype.equivFin n) +
      E.reindex (Fintype.equivFin m) (Fintype.equivFin n) =
      (A + E).reindex (Fintype.equivFin m) (Fintype.equivFin n) := rfl
  rw [hadd] at h
  simpa only [singularValues_reindex_eq_toEuclideanLin_singularValues] using h

end NLAlib
