import NLAlib.Matrix.Inequalities.Mirsky
/-!
# Mirsky inequalities with arbitrary zero padding

Every finite selection of natural singular indices obeys the exact Mirsky bound,
even when the selection contains indices beyond both dimensions. Source:
Bhatia 1997, Theorem IV.3.4; supports the complete `lidskii` interface.
-/
noncomputable section
open scoped Matrix
namespace NLAlib

/-- Every finite selection of zero-padded natural singular indices obeys Mirsky's
absolute-difference sum bound. Bhatia 1997, Theorem IV.3.4; all padding indices,
empty selections, empty shapes and rank-deficient zeros are covered. -/
theorem sum_abs_singularValues_add_sub_le_sum_range {m n : ℕ}
    (A E : Matrix (Fin m) (Fin n) ℝ) (S : Finset ℕ) :
    (∑ i ∈ S, |singularValues (A + E) i - singularValues A i|) ≤
      ∑ j ∈ Finset.range S.card, singularValues E j := by
  classical
  let T := S.filter fun k => k < min m n
  let e : {k // k ∈ T} ↪ Fin (min m n) :=
    ⟨fun k => ⟨k.val, (Finset.mem_filter.mp k.property).2⟩,
      fun i j hij => Subtype.ext (congrArg (fun k : Fin (min m n) => k.val) hij)⟩
  let I := T.attach.map e
  have hT : (∑ i ∈ T, |singularValues (A + E) i - singularValues A i|) =
      ∑ i ∈ S, |singularValues (A + E) i - singularValues A i| := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hkT
    have hge : min m n ≤ k := by
      simpa only [T, Finset.mem_filter, hk, true_and, not_lt] using hkT
    rw [singularValues_eq_zero_of_min_le _ hge,
      singularValues_eq_zero_of_min_le _ hge]
    simp
  have hI : (∑ i ∈ I, |singularValues (A + E) i - singularValues A i|) =
      ∑ i ∈ T, |singularValues (A + E) i - singularValues A i| := by
    simp only [I, Finset.sum_map]
    change (∑ i ∈ T.attach, |singularValues (A + E) i.val - singularValues A i.val|) = _
    exact Finset.sum_attach T (fun i => |singularValues (A + E) i - singularValues A i|)
  have hcard : I.card ≤ S.card := by
    simp only [I, Finset.card_map, Finset.card_attach]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  calc
    _ = ∑ i ∈ I, |singularValues (A + E) i - singularValues A i| := hT.symm.trans hI.symm
    _ ≤ ∑ j ∈ Finset.range I.card, singularValues E j := by
      simpa only [Fin.sum_univ_eq_sum_range] using
        sum_abs_singularValues_add_sub_le_sum_prefix A E I
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hcard)
      (fun j _ _ => singularValues_nonneg E j)

/-- Mirsky's finite-selection inequality on arbitrary finite real matrix row and
column indices, with every natural zero-padding index included.
Bhatia 1997, Theorem IV.3.4. -/
theorem sum_abs_toEuclideanLin_singularValues_add_sub_le_sum_range {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A E : Matrix m n ℝ) (S : Finset ℕ) :
    (∑ i ∈ S, |(A + E).toEuclideanLin.singularValues i - A.toEuclideanLin.singularValues i|) ≤
      ∑ j ∈ Finset.range S.card, E.toEuclideanLin.singularValues j := by
  classical
  have h := sum_abs_singularValues_add_sub_le_sum_range
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
    (E.reindex (Fintype.equivFin m) (Fintype.equivFin n)) S
  have hadd : A.reindex (Fintype.equivFin m) (Fintype.equivFin n) +
      E.reindex (Fintype.equivFin m) (Fintype.equivFin n) =
      (A + E).reindex (Fintype.equivFin m) (Fintype.equivFin n) := rfl
  rw [hadd] at h
  simpa only [singularValues_reindex_eq_toEuclideanLin_singularValues] using h

/-- Mirsky weak majorization on any finite zero-padded length, without a dimension
bound on that length. Bhatia 1997, Theorem IV.3.4; native arbitrary finite indices. -/
theorem weaklyMajorized_abs_toEuclideanLin_singularValues_add_sub_padded {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A E : Matrix m n ℝ) (d : ℕ) :
    WeaklyMajorized (fun i : Fin d =>
      |(A + E).toEuclideanLin.singularValues i - A.toEuclideanLin.singularValues i|)
      (fun i : Fin d => E.toEuclideanLin.singularValues i) := by
  classical
  rw [weaklyMajorized_iff_sum_le]
  intro S
  let e : Fin d ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have h := sum_abs_toEuclideanLin_singularValues_add_sub_le_sum_range A E (S.map e)
  simp only [Finset.sum_map, e, Function.Embedding.coeFn_mk, Finset.card_map] at h
  have hcard : S.card ≤ d := by simpa using Finset.card_le_univ S
  rw [sumLargest_eq_prefix_of_antitone _ (fun i j hij => E.toEuclideanLin.singularValues_antitone hij),
    sum_fin_ite_lt_eq_sum_castLE hcard]
  simp only [Fin.val_castLE]
  rw [Fin.sum_univ_eq_sum_range]
  exact h

end NLAlib
