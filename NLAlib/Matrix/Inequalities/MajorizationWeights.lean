import NLAlib.Matrix.Spectral.EckartYoung
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.Monovary
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Finite weight budgets and doubly stochastic comparisons

Signed versions of the finite top-coordinate budget and rearrangement inequality,
and scalar Jensen for doubly stochastic matrices. These are the finite-dimensional
foundations of `majorization-def`, Ky Fan principles, Schur–Horn and Lidskii.
Source: Marshall–Olkin–Arnold (2011), Chapters 1–4.
-/

noncomputable section
open scoped BigOperators Matrix

namespace NLAlib

/-- A prefix of a finite coordinate list has the prescribed cardinality, also at
the empty and full endpoints. Majorization weight-budget helper. -/
theorem card_filter_fin_lt {m k : ℕ} (hk : k ≤ m) :
    ((Finset.univ : Finset (Fin m)).filter fun i => i.val < k).card = k := by
  classical
  by_cases hkm : k < m
  · have he : ((Finset.univ : Finset (Fin m)).filter fun i => i.val < k) =
        Finset.Iio (⟨k, hkm⟩ : Fin m) := by ext i; simp; rfl
    rw [he, Fin.card_Iio]
  · have hkm : k = m := by omega
    subst k
    simp

/-- The signed finite weight budget: decreasing real entries paired with weights
in `[0,1]` of exact integer total `k` cannot exceed the top-`k` sum.
Marshall–Olkin–Arnold (2011), majorization prefix criterion. -/
theorem sum_mul_le_sum_ite_lt_of_antitone_of_sum_eq {m k : ℕ}
    (a w : Fin m → ℝ) (ha : Antitone a) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∀ i, w i ≤ 1) (hk : k ≤ m) (hbudget : ∑ i, w i = (k : ℝ)) :
    (∑ i, a i * w i) ≤ ∑ i : Fin m, if i.val < k then a i else 0 := by
  classical
  cases m with
  | zero => simp
  | succ m =>
    let c : ℝ := a (Fin.last m)
    have hshift (i : Fin (m + 1)) : 0 ≤ a i - c :=
      sub_nonneg.mpr (ha (Fin.le_last i))
    have hanti : Antitone (fun i => a i - c) := fun i j hij => sub_le_sub_right (ha hij) c
    have h := sum_mul_le_sum_ite_lt_of_antitone (fun i => a i - c) w
      hshift hanti hw0 hw1 hbudget.le
    have hleft : (∑ i, (a i - c) * w i) = (∑ i, a i * w i) - c * k := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hbudget]
    have hright : (∑ i : Fin (m + 1), if i.val < k then a i - c else 0) =
        (∑ i : Fin (m + 1), if i.val < k then a i else 0) - c * k := by
      rw [← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_const,
        card_filter_fin_lt hk, ← Finset.sum_filter]
      simp [nsmul_eq_mul, mul_comm]
    rw [hleft, hright] at h
    linarith

/-- Signed rearrangement for a doubly stochastic matrix, with decreasing lists.
This follows from Birkhoff and Mathlib's rearrangement inequality, without a
nonnegativity restriction on either list. Marshall–Olkin–Arnold (2011), §2.B. -/
theorem sum_mul_mulVec_le_of_doublyStochastic {n : ℕ}
    (a b : Fin n → ℝ) (ha : Antitone a) (hb : Antitone b)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : D ∈ doublyStochastic ℝ (Fin n)) :
    (∑ i, a i * (D *ᵥ b) i) ≤ ∑ i, a i * b i := by
  classical
  have hab : Monovary a b := by
    rw [monovary_iff_forall_mul_nonneg]
    intro i j
    rcases le_total i j with hij | hji
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (ha hij))
        (sub_nonpos.mpr (hb hij))
    · exact mul_nonneg (sub_nonneg.mpr (ha hji)) (sub_nonneg.mpr (hb hji))
  obtain ⟨w, hw0, hw1, hwD⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hD
  rw [← hwD, Matrix.sum_mulVec]
  simp_rw [Matrix.smul_mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ σ : Equiv.Perm (Fin n), ∑ i, a i * (w σ * (σ.permMatrix ℝ *ᵥ b) i)) =
        ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i, a i * b (σ i) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [Matrix.permMatrix_mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Function.comp_apply]
      ring
    _ ≤ ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i, a i * b i := by
      apply Finset.sum_le_sum
      intro σ _
      apply mul_le_mul_of_nonneg_left _ (hw0 σ)
      simpa only [smul_eq_mul] using hab.sum_smul_comp_perm_le_sum_smul (σ := σ)
    _ = ∑ i, a i * b i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Scalar Jensen summed across a doubly stochastic matrix.
Marshall–Olkin–Arnold (2011), convex-function majorization criterion. -/
theorem sum_convex_mulVec_le_of_doublyStochastic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) {D : Matrix ι ι ℝ} (hD : D ∈ doublyStochastic ℝ ι)
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) :
    (∑ i, φ ((D *ᵥ y) i)) ≤ ∑ i, φ (y i) := by
  calc
    (∑ i, φ ((D *ᵥ y) i)) ≤ ∑ i, ∑ j, D i j * φ (y j) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Matrix.mulVec, dotProduct, smul_eq_mul] using
        hφ.map_sum_le (fun j _ => nonneg_of_mem_doublyStochastic hD)
          (sum_row_of_mem_doublyStochastic hD i) (fun j _ => Set.mem_univ (y j))
    _ = ∑ j, φ (y j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic hD j, one_mul]

end NLAlib
