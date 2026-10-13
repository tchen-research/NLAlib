import NLAlib.Matrix.Spectral.RealDilationSpectrum
import NLAlib.Matrix.Inequalities.Lidskii
/-!
# Singular-value majorization (Mirsky)

Mirsky's weak majorization `|σ(A + E) − σ(A)| ≺_w σ(E)` (Bhatia 1997, Theorem IV.3.4):
selecting a top dilation slot for a positive singular-value increment and its reversed bottom
slot for a negative increment turns indexed Lidskii into the rectangular inequality, on
`Fin (min (card m) (card n))` (`weaklyMajorized_abs_singularValues_add_sub`) and on any
zero-padded length (`weaklyMajorized_abs_singularValues_add_sub_padded`,
`sum_abs_singularValues_add_sub_le_sum_range`). Real matrices: the dilation spectrum
(`Spectral/RealDilationSpectrum`) is stated over `ℝ`. Atlas: `weyl-mirsky`.
-/
noncomputable section
open scoped Matrix
namespace NLAlib

private theorem eigenvaluePrefix_realDilation {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hk : k ≤ min m n) :
    eigenvaluePrefix (isHermitian_dilation A) k = ∑ i : Fin k, singularValues A i := by
  rw [eigenvaluePrefix_eq_sum_castLE _ (by simp; omega)]
  apply Finset.sum_congr rfl
  intro i _
  have hi := eigenvalues₀_dilation A (Fin.castLE (by omega : k ≤ m + n) i)
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
      (isHermitian_dilation C).eigenvalues₀ (f i) =
        if 0 ≤ δ i then singularValues C i else -singularValues C i := by
    change (isHermitian_dilation C).eigenvalues₀
      (Fin.cast (by simp) (if 0 ≤ δ i then Fin.castLE (by omega : min m n ≤ m + n) i
        else (Fin.castLE (by omega : min m n ≤ m + n) i).rev)) =
          if 0 ≤ δ i then singularValues C i else -singularValues C i
    split_ifs
    · exact eigenvalues₀_dilation_top C i
    · exact eigenvalues₀_dilation_bottom C i
  have hdiff (i : Fin (min m n)) :
      ((isHermitian_dilation A).add (isHermitian_dilation E)).eigenvalues₀ (f i) -
        (isHermitian_dilation A).eigenvalues₀ (f i) = |δ i| := by
    rw [eigenvalues₀_eq_of_matrix_eq _ (isHermitian_dilation (A + E)) (dilation_add A E).symm]
    rw [hspectrum, hspectrum]
    split_ifs with hi
    · exact (abs_of_nonneg hi).symm
    · dsimp [δ]
      rw [abs_of_neg (lt_of_not_ge hi)]
      ring
  have h := sum_eigenvalues₀_add_le_sum_add_eigenvaluePrefix
    (isHermitian_dilation A) (isHermitian_dilation E) (S.map f)
  have hcard : S.card ≤ min m n := by simpa using Finset.card_le_univ S
  have hprefix : eigenvaluePrefix (isHermitian_dilation E) (S.map f).card =
        ∑ j : Fin S.card, singularValues E j := by
    simpa only [Finset.card_map] using eigenvaluePrefix_realDilation E hcard
  rw [hprefix, Finset.sum_map, Finset.sum_map] at h
  have hdiffsum :
      (∑ i ∈ S, ((isHermitian_dilation A).add (isHermitian_dilation E)).eigenvalues₀ (f i)) -
        (∑ i ∈ S, (isHermitian_dilation A).eigenvalues₀ (f i)) = ∑ i ∈ S, |δ i| := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => hdiff i
  change (∑ i ∈ S, |δ i|) ≤ _
  linarith

/-- `Fin` step of `weaklyMajorized_abs_singularValues_add_sub`. -/
private theorem weaklyMajorized_abs_singularValues_add_sub_fin {m n : ℕ}
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

/-- Rectangular Mirsky: the entire absolute singular-value difference vector is
weakly majorized by the perturbation singular list, on arbitrary finite real matrix row and
column indices. Bhatia 1997, Theorem IV.3.4. The vector has the thin rectangular
dimension `min (card m) (card n)`, with rank-deficient zeros; its coordinatewise differences are
not assumed already sorted. Empty dimensions are included.
atlas: weyl-mirsky -/
theorem weaklyMajorized_abs_singularValues_add_sub {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A E : Matrix m n ℝ) :
    WeaklyMajorized (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
      |singularValues (A + E) i - singularValues A i|)
      (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues E i) := by
  classical
  have h := weaklyMajorized_abs_singularValues_add_sub_fin
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
    (E.reindex (Fintype.equivFin m) (Fintype.equivFin n))
  have hadd : A.reindex (Fintype.equivFin m) (Fintype.equivFin n) +
      E.reindex (Fintype.equivFin m) (Fintype.equivFin n) =
      (A + E).reindex (Fintype.equivFin m) (Fintype.equivFin n) := rfl
  rw [hadd] at h
  simp only [singularValues_reindex] at h
  exact h

/-! ### Zero-padded index forms -/


/-- `Fin` step of `sum_abs_singularValues_add_sub_le_sum_range`. -/
private theorem sum_abs_singularValues_add_sub_le_sum_range_fin {m n : ℕ}
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
    rw [singularValues_eq_zero_of_min_le _ (by simpa only [Fintype.card_fin] using hge),
      singularValues_eq_zero_of_min_le _ (by simpa only [Fintype.card_fin] using hge)]
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

/-- Every finite selection of zero-padded natural singular indices obeys Mirsky's
absolute-difference sum bound, on arbitrary finite real matrix row and column indices.
Bhatia 1997, Theorem IV.3.4; all padding indices, empty selections, empty shapes and
rank-deficient zeros are covered.
atlas: weyl-mirsky -/
theorem sum_abs_singularValues_add_sub_le_sum_range {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A E : Matrix m n ℝ) (S : Finset ℕ) :
    (∑ i ∈ S, |singularValues (A + E) i - singularValues A i|) ≤
      ∑ j ∈ Finset.range S.card, singularValues E j := by
  classical
  have h := sum_abs_singularValues_add_sub_le_sum_range_fin
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
    (E.reindex (Fintype.equivFin m) (Fintype.equivFin n)) S
  have hadd : A.reindex (Fintype.equivFin m) (Fintype.equivFin n) +
      E.reindex (Fintype.equivFin m) (Fintype.equivFin n) =
      (A + E).reindex (Fintype.equivFin m) (Fintype.equivFin n) := rfl
  rw [hadd] at h
  simp only [singularValues_reindex] at h
  exact h

/-- Mirsky weak majorization on any finite zero-padded length, without a dimension
bound on that length. Bhatia 1997, Theorem IV.3.4; arbitrary finite indices.
atlas: weyl-mirsky -/
theorem weaklyMajorized_abs_singularValues_add_sub_padded {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A E : Matrix m n ℝ) (d : ℕ) :
    WeaklyMajorized (fun i : Fin d =>
      |singularValues (A + E) i - singularValues A i|)
      (fun i : Fin d => singularValues E i) := by
  classical
  rw [weaklyMajorized_iff_sum_le]
  intro S
  let e : Fin d ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have h := sum_abs_singularValues_add_sub_le_sum_range A E (S.map e)
  simp only [Finset.sum_map, e, Function.Embedding.coeFn_mk, Finset.card_map] at h
  have hcard : S.card ≤ d := by simpa using Finset.card_le_univ S
  rw [sumLargest_eq_prefix_of_antitone _ (fun i j hij => singularValues_antitone E hij),
    sum_fin_ite_lt_eq_sum_castLE hcard]
  simp only [Fin.val_castLE]
  rw [Fin.sum_univ_eq_sum_range]
  exact h

end NLAlib
