import NLAlib.Probability.Free.WordCreationRows
import NLAlib.Probability.Free.WordMatrixAmplification

/-!
# Contractive partial creation rows and coefficient blocks

Restricting a native fixed-length creation row to injected coordinates is
contractive. Rectangular scalar coefficients can therefore use the existing
native matrix amplification after padding on the disjoint union of indices.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical InnerProduct

namespace NLAlib

variable {ι D : Type*} [Fintype ι] [Fintype D]
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W
local notation "K" => PiLp 2 (fun _ : D => W)

/-- The actual creation row reading precisely an injected set of coordinates. -/
def wordCreationRowAlong (m : ℕ) (e : List.Vector ι m ↪ D) : K →L[ℂ] W :=
  ∑ w, (wordCreationProduct w.toList).comp (PiLp.proj 2 (fun _ : D => W) (e w))

omit [Fintype D] in
/-- The finite column formula for a partial creation row. -/
@[simp]
theorem wordCreationRowAlong_apply (m : ℕ) (e : List.Vector ι m ↪ D) (x : K) :
    wordCreationRowAlong m e x = ∑ w, wordCreationProduct w.toList (x (e w)) := by
  simp [wordCreationRowAlong, ContinuousLinearMap.comp_apply]

/-- Every partial creation row is contractive, including an empty row. -/
theorem norm_wordCreationRowAlong_le_one (m : ℕ) (e : List.Vector ι m ↪ D) :
    ‖wordCreationRowAlong m e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  have hsq : ‖wordCreationRowAlong m e x‖ ^ 2 = ∑ w, ‖x (e w)‖ ^ 2 := by
    rw [wordCreationRowAlong_apply]
    simpa only [wordPrefixIsometry_apply] using
      (orthogonalFamily_wordPrefixIsometry (ι := ι) m).norm_sum
        (fun w => x (e w)) Finset.univ
  have hle : ∑ w : List.Vector ι m, ‖x (e w)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ = ∑ d ∈ Finset.univ.map e, ‖x d‖ ^ 2 := by simp
      _ ≤ ∑ d : D, ‖x d‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (wordCreationRowAlong m e x), norm_nonneg x]

omit [Fintype D] in
/-- A single injected coordinate recovers its whole-word creation operator. -/
theorem wordCreationRowAlong_apply_single (m : ℕ) (e : List.Vector ι m ↪ D)
    (w : List.Vector ι m) (x : W) :
    wordCreationRowAlong m e (PiLp.single 2 (e w) x) = wordCreationProduct w.toList x := by
  rw [wordCreationRowAlong_apply, Finset.sum_eq_single w]
  · simp
  · intro v _ hvw
    simp [e.injective.ne hvw]
  · simp

/-- The native adjoint of a partial row recovers annihilation in each
injected coordinate. This is an identity of the actual Hilbert operators. -/
theorem wordCreationRowAlong_adjoint_apply (m : ℕ) (e : List.Vector ι m ↪ D)
    (x : W) (w : List.Vector ι m) :
    (wordCreationRowAlong m e).adjoint x (e w) = star (wordCreationProduct w.toList) x := by
  apply ext_inner_left ℂ
  intro z
  have h := ContinuousLinearMap.adjoint_inner_right (wordCreationRowAlong m e)
    (PiLp.single 2 (e w) z) x
  rw [wordCreationRowAlong_apply_single, PiLp.inner_apply, Finset.sum_eq_single (e w)] at h
  · simpa only [PiLp.single_eq_same, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right] using h
  · intro d _ hd
    simp [hd]
  · simp

end NLAlib
