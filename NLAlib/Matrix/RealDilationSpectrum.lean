import NLAlib.Matrix.RealDilation
import Mathlib.Data.Fin.Rev

/-!
# Decreasing eigenvalues of real rectangular dilation

The sorted dilation list is the row-side padded singular list followed by the
reversed negative column-side padded list. This single formula handles tall,
wide and empty matrices. Source: Bhatia 1997, Section III.4; supports `lidskii`.
-/
noncomputable section
open scoped Matrix
namespace NLAlib

/-- The decreasing paired spectrum of the real dilation: padded positive values,
then reversed padded negative values. Bhatia 1997, Section III.4. -/
def realDilationSpectrum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Fin (m + n) → ℝ :=
  fun k => if (k : ℕ) < m then singularValues A k else -singularValues A (m + n - 1 - k)

/-- The explicit paired list decreases, including all the rectangular zeros.
Bhatia 1997, Section III.4; no positive-rank hypothesis is needed. -/
theorem realDilationSpectrum_antitone {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Antitone (realDilationSpectrum A) := by
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  simp only [realDilationSpectrum]
  split_ifs with hj hi hi
  · exact singularValues_antitone A hij'
  · omega
  · exact (neg_nonpos.mpr (singularValues_nonneg A _)).trans (singularValues_nonneg A _)
  · exact neg_le_neg (singularValues_antitone A (by omega))

private def dilationOrderingEquiv (m n : ℕ) : Fin m ⊕ Fin n ≃ Fin (m + n) :=
  (Equiv.sumCongr (Equiv.refl (Fin m)) (Fin.revPerm (n := n))).trans finSumFinEquiv

private theorem diagonal_reindex_dilationOrdering {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (Matrix.diagonal (Sum.elim (fun i : Fin m => singularValues A i)
      (fun j : Fin n => -singularValues A j))).reindex
        (dilationOrderingEquiv m n) (dilationOrderingEquiv m n) =
      Matrix.diagonal (realDilationSpectrum A) := by
  rw [Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  congr 1
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp [dilationOrderingEquiv, realDilationSpectrum, i.isLt]
  · simp [dilationOrderingEquiv, realDilationSpectrum, Fin.val_rev]
    apply congrArg (singularValues A)
    have hj := j.isLt
    omega
/-- Every sorted eigenvalue of the actual real dilation equals the corresponding
explicit paired singular value. Bhatia 1997, Section III.4; all rectangular
shapes, multiplicities and zero padding are included. -/
theorem eigenvalues₀_realDilation {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (k : Fin (m + n)) :
    (isHermitian_realDilation A).eigenvalues₀ (Fin.cast (by simp) k) = realDilationSpectrum A k := by
  classical
  obtain ⟨P, hP, hHP⟩ := exists_realDilation_orthogonal_diagonalization A
  have hc : (realDilation A).charpoly = (Matrix.diagonal (realDilationSpectrum A)).charpoly := by
    rw [hHP, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc Pᵀ P, hP, Matrix.one_mul]
    calc
      _ = ((Matrix.diagonal (Sum.elim (fun i : Fin m => singularValues A i)
        (fun j : Fin n => -singularValues A j))).reindex
          (dilationOrderingEquiv m n) (dilationOrderingEquiv m n)).charpoly :=
        (Matrix.charpoly_reindex (dilationOrderingEquiv m n) _).symm
      _ = _ := congrArg Matrix.charpoly (diagonal_reindex_dilationOrdering A)
  have hsort := (isHermitian_realDilation A).sort_roots_charpoly_eq_eigenvalues₀
  rw [hc, Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at hsort
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map,
    Function.comp_def, RCLike.re_to_real] at hsort
  have hl : List.ofFn (isHermitian_realDilation A).eigenvalues₀ =
      List.ofFn (realDilationSpectrum A) := by
    rw [← hsort]
    simp_rw [Fin.univ_val_map, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact (realDilationSpectrum_antitone A).sortedGE_ofFn
  have hv := congrArg (fun l : List ℝ => l.getD k 0) hl
  simpa using hv

/-- The top thin slots of real dilation are the ordered singular values.
Bhatia 1997, Section III.4; singular zeros cause no exceptions. -/
theorem eigenvalues₀_realDilation_top {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin (min m n)) :
    (isHermitian_realDilation A).eigenvalues₀
      (Fin.cast (by simp) (Fin.castLE (by omega : min m n ≤ m + n) i)) = singularValues A i := by
  rw [eigenvalues₀_realDilation]
  simp [realDilationSpectrum, show (i : ℕ) < m from lt_of_lt_of_le i.isLt (min_le_left m n)]

/-- The reversed bottom thin slots of real dilation are the negative singular values.
Bhatia 1997, Section III.4; all empty and rank-deficient cases are included. -/
theorem eigenvalues₀_realDilation_bottom {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin (min m n)) :
    (isHermitian_realDilation A).eigenvalues₀
      (Fin.cast (by simp) ((Fin.castLE (by omega : min m n ≤ m + n) i).rev)) =
      -singularValues A i := by
  rw [eigenvalues₀_realDilation]
  have hm : ¬ (((Fin.castLE (by omega : min m n ≤ m + n) i).rev : Fin (m + n)) : ℕ) < m := by
    simp only [Fin.val_rev, Fin.val_castLE]
    have hin := lt_of_lt_of_le i.isLt (min_le_right m n)
    omega
  simp only [realDilationSpectrum]
  rw [if_neg hm]
  have hi : m + n - 1 - ((Fin.castLE (by omega : min m n ≤ m + n) i).rev : Fin (m + n)).val = i.val := by
    simp only [Fin.val_rev, Fin.val_castLE]
    have hlt := i.isLt
    omega
  rw [hi]
end NLAlib
