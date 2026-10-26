import NLAlib.Matrix.Structured.ProfileRearrangement
import NLAlib.Matrix.Inequalities.Majorization
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Rearrangement from the actual profile envelopes

The maximum row Euclidean norm and the logarithmically weighted decreasing
row maxima supply all hypotheses of the finite profile rearrangement theorem.
One simultaneous row/column permutation then gives both entry envelopes.
Source: Latała--van Handel--Youssef 2018, Lemma 3.10.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace NLAlib

variable {ι : Type*} [Fintype ι]

/-- Largest row Euclidean norm of a finite real variance profile. -/
def profileMaxRowEnergy (A : Matrix ι ι ℝ) : ℝ :=
  ‖fun i => Real.sqrt (∑ j, A i j ^ 2)‖

/-- Largest logarithmically weighted row maximum after sorting the row
maxima in decreasing order. The Pi norm is the finite maximum, including
the zero value in the empty-dimensional case. -/
def profileLogRowMaximum (A : Matrix ι ι ℝ) : ℝ :=
  ‖fun i : Fin (Fintype.card ι) =>
    ‖A (sortingEquiv (fun j => ‖A j‖) i)‖ * Real.sqrt (Real.log (i.val + 1))‖

/-- The row-energy envelope is nonnegative, including empty profiles. -/
theorem profileMaxRowEnergy_nonneg (A : Matrix ι ι ℝ) : 0 ≤ profileMaxRowEnergy A :=
  norm_nonneg _

/-- The sorted logarithmic row-maximum envelope is nonnegative. -/
theorem profileLogRowMaximum_nonneg (A : Matrix ι ι ℝ) : 0 ≤ profileLogRowMaximum A :=
  norm_nonneg _

/-- Every row's squared Euclidean norm is bounded by the actual maximum
row-energy envelope, without an auxiliary bound hypothesis. -/
theorem sum_row_sq_le_profileMaxRowEnergy_sq (A : Matrix ι ι ℝ) (i : ι) :
    ∑ j, A i j ^ 2 ≤ profileMaxRowEnergy A ^ 2 := by
  have hn : 0 ≤ ∑ j, A i j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hbound : Real.sqrt (∑ j, A i j ^ 2) ≤ profileMaxRowEnergy A := by
    have h := norm_le_pi_norm (fun i => Real.sqrt (∑ j, A i j ^ 2)) i
    simpa only [profileMaxRowEnergy, Real.norm_of_nonneg (Real.sqrt_nonneg _)] using h
  nlinarith [Real.sq_sqrt hn, Real.sqrt_nonneg (∑ j, A i j ^ 2),
    profileMaxRowEnergy_nonneg A]

/-- Symmetry converts the actual maximum row-energy envelope into the
column-energy bound required by the heavy-neighbor construction. -/
theorem sum_column_sq_le_profileMaxRowEnergy_sq (A : Matrix ι ι ℝ) (hA : A.IsSymm) (j : ι) :
    ∑ i, A i j ^ 2 ≤ profileMaxRowEnergy A ^ 2 := by
  simpa only [hA.apply] using sum_row_sq_le_profileMaxRowEnergy_sq A j

/-- Every entry in the initially sorted profile satisfies the actual
logarithmic row-maximum envelope. -/
theorem entry_mul_sqrt_log_le_profileLogRowMaximum (A : Matrix ι ι ℝ)
    (i j : Fin (Fintype.card ι)) :
    A (sortingEquiv (fun j => ‖A j‖) i) (sortingEquiv (fun j => ‖A j‖) j) *
      Real.sqrt (Real.log (i.val + 1)) ≤ profileLogRowMaximum A := by
  let e := sortingEquiv (fun j => ‖A j‖)
  have hentry : A (e i) (e j) ≤ ‖A (e i)‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (A (e i)) (e j))
  have hbound := norm_le_pi_norm
    (fun l : Fin (Fintype.card ι) => ‖A (e l)‖ * Real.sqrt (Real.log (l.val + 1))) i
  have hweighted : ‖A (e i)‖ * Real.sqrt (Real.log (i.val + 1)) ≤ profileLogRowMaximum A := by
    simpa only [profileLogRowMaximum, Real.norm_of_nonneg (by positivity :
      0 ≤ ‖A (e i)‖ * Real.sqrt (Real.log (i.val + 1)))] using hbound
  exact (mul_le_mul_of_nonneg_right hentry (Real.sqrt_nonneg _)).trans hweighted

/-- One actual permutation gives both row and cross-entry bounds in terms of
the profile's own maximum row energy and sorted logarithmic row maxima.
All counting bounds follow from these quantities; none are assumed.
Source: Latała--van Handel--Youssef 2018, Lemma 3.10. -/
theorem exists_equiv_entry_le_profile_envelopes
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (hA0 : ∀ i j, 0 ≤ A i j) :
    ∃ e : Fin (Fintype.card ι) ≃ ι, ∀ k,
      (∀ i j, profileCutoff k ≤ i.val →
        A (e i) (e j) ≤ profileLogRowMaximum A /
          Real.sqrt (Real.log (profilePreviousCutoff k))) ∧
      (∀ i j, profileNeighborCutoff k ≤ i.val → j.val < profileCutoff k →
        A (e i) (e j) ≤ profileMaxRowEnergy A / Real.sqrt (profilePreviousCutoff k)) := by
  classical
  let e₀ := sortingEquiv (fun j => ‖A j‖)
  let B : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ :=
    Matrix.of fun i j => A (e₀ i) (e₀ j)
  have hcol (j : Fin (Fintype.card ι)) : ∑ i, B i j ^ 2 ≤ profileMaxRowEnergy A ^ 2 := by
    change (∑ i, (fun l => A l (e₀ j) ^ 2) (e₀ i)) ≤ _
    rw [e₀.sum_comp (fun l : ι => A l (e₀ j) ^ 2)]
    exact sum_column_sq_le_profileMaxRowEnergy_sq A hA (e₀ j)
  obtain ⟨e, he⟩ := exists_equiv_entry_le_div_sqrt_log_and_div_sqrt B
    (profileMaxRowEnergy_nonneg A) (fun i j => hA0 (e₀ i) (e₀ j)) hcol
    (entry_mul_sqrt_log_le_profileLogRowMaximum A)
  refine ⟨e.trans e₀, ?_⟩
  simpa only [Equiv.trans_apply, B, Matrix.of_apply] using he

end NLAlib
