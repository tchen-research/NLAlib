import NLAlib.Probability.Free.WordWickCutBound
import Mathlib.Data.List.TakeDrop

/-!
# The actual homogeneous Wick operator estimate

The exact normal-order cuts are reindexed by a prefix and a reversed suffix.
Each cut has the same actual coefficient ℓ² mass, and the native row bound
gives the degree-plus-one homogeneous estimate without a dimension factor.
This is the homogeneous ingredient in Lemma 4.5 of arXiv:2406.11453v2.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace NLAlib

variable {ι : Type*}

private def wordCutEquiv (m j : ℕ) (hj : j ≤ m) :
    (List.Vector ι j × List.Vector ι (m - j)) ≃ List.Vector ι m where
  toFun uv := ⟨uv.1.toList ++ uv.2.toList.reverse, by simp; omega⟩
  invFun w := (⟨w.toList.take j, by simp [Nat.min_eq_left hj]⟩,
    ⟨(w.toList.drop j).reverse, by simp⟩)
  left_inv uv := by
    rcases uv with ⟨u, v⟩
    apply Prod.ext <;> apply Subtype.ext
    · change (u.toList ++ v.toList.reverse).take j = u.toList
      have hu : u.toList.length = j := by simp
      exact List.take_left' hu
    · change ((u.toList ++ v.toList.reverse).drop j).reverse = v.toList
      have hu : u.toList.length = j := by simp
      rw [List.drop_left' hu, List.reverse_reverse]
  right_inv w := by
    apply Subtype.ext
    change w.toList.take j ++ ((w.toList.drop j).reverse).reverse = w.toList
    rw [List.reverse_reverse, List.take_append_drop]

private theorem wordCutEquiv_take (m j : ℕ) (hj : j ≤ m)
    (u : List.Vector ι j) (v : List.Vector ι (m - j)) :
    ((wordCutEquiv (ι := ι) m j hj) (u, v)).toList.take j = u.toList := by
  change (u.toList ++ v.toList.reverse).take j = _
  have hu : u.toList.length = j := by simp
  exact List.take_left' hu

private theorem wordCutEquiv_drop_reverse (m j : ℕ) (hj : j ≤ m)
    (u : List.Vector ι j) (v : List.Vector ι (m - j)) :
    (((wordCutEquiv (ι := ι) m j hj) (u, v)).toList.drop j).reverse = v.toList := by
  change ((u.toList ++ v.toList.reverse).drop j).reverse = _
  have hu : u.toList.length = j := by simp
  rw [List.drop_left' hu, List.reverse_reverse]

private theorem norm_sum_wordWick_normal_cut_le [Fintype ι] (m j : ℕ) (hj : j ≤ m)
    (a : List.Vector ι m → ℂ) :
    ‖∑ w, a w • (wordCreationProduct (w.toList.take j) *
      star (wordCreationProduct (w.toList.drop j).reverse))‖ ≤
        Real.sqrt (∑ w, ‖a w‖ ^ 2) := by
  let e := wordCutEquiv (ι := ι) m j hj
  have he : (∑ w, a w • (wordCreationProduct (w.toList.take j) *
      star (wordCreationProduct (w.toList.drop j).reverse))) =
      wordWickCutOperator j (m - j) (fun u v => a (e (u, v))) := by
    rw [wordWickCutOperator, ← Fintype.sum_prod_type']
    symm
    apply Fintype.sum_equiv e
    intro uv
    rcases uv with ⟨u, v⟩
    dsimp only [e]
    simp only [wordCutEquiv_take, wordCutEquiv_drop_reverse]
  rw [he]
  convert! norm_wordWickCutOperator_le j (m - j) (fun u v => a (e (u, v))) using 1
  congr 1
  rw [← Fintype.sum_prod_type']
  exact (e.sum_comp (fun w => ‖a w‖ ^ 2)).symm

/-- The genuine homogeneous Wick estimate: the actual operator norm is
at most degree plus one times the actual Euclidean coefficient norm. The
alphabet may be empty; degree zero includes the unique empty word. -/
theorem norm_sum_wordWickOperator_le [Fintype ι] (m : ℕ)
    (a : List.Vector ι m → ℂ) :
    ‖∑ w, a w • wordWickOperator w.toList‖ ≤
      (m + 1 : ℝ) * Real.sqrt (∑ w, ‖a w‖ ^ 2) := by
  have hsum : (∑ w, a w • wordWickOperator w.toList) =
      ∑ j ∈ Finset.range (m + 1), ∑ w, a w •
        (wordCreationProduct (w.toList.take j) *
          star (wordCreationProduct (w.toList.drop j).reverse)) := by
    have hlen (w : List.Vector ι m) : w.toList.length = m := by simp
    simp_rw [wordWickOperator_eq_sum_cuts, hlen, Finset.smul_sum]
    exact Finset.sum_comm
  rw [hsum]
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1),
        ‖∑ w, a w • (wordCreationProduct (w.toList.take j) *
          star (wordCreationProduct (w.toList.drop j).reverse))‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (m + 1), Real.sqrt (∑ w, ‖a w‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_sum_wordWick_normal_cut_le m j
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) a
    _ = _ := by simp

end NLAlib
