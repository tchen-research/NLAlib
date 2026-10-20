import NLAlib.Matrix.Functions.ResolventWordDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform analytic domination for actual ordered inverse words

Prerequisite for `independent-sum-spectrum-universality`.
These estimates justify the existing resampling derivative
formula; sharp covariance estimates continue to use the actual ordered words.

Source: Brailovskaya–van Handel, arXiv:2201.05142v3, Sections 6.3–6.4.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "E" => ((n × n) ⊕ (n × n)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

/-- Actual fixed coefficient mass after inserting one inverse direction. -/
theorem prod_norm_snd_resolventWordInsert {m : ℕ}
    (w : Fin m → ℂ × M) (i : Fin m) (H : M) :
    (∏ j, ‖(resolventWordInsert w i H j).2‖) = ‖H‖ * ∏ j, ‖(w j).2‖ := by
  rw [Fin.prod_univ_succAbove _ i.castSucc]
  simp only [resolventWordInsert, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]

omit [Fintype n] [DecidableEq n] in
/-- The original nonreal shift bound is unchanged by a real direction insertion. -/
theorem inv_abs_im_le_resolventWordInsert {m : ℕ}
    (w : Fin m → ℂ × M) {c : ℝ} (hc : ∀ i, |(w i).1.im|⁻¹ ≤ c)
    (i : Fin m) (H : M) : ∀ j, |(resolventWordInsert w i H j).1.im|⁻¹ ≤ c := by
  intro j
  refine Fin.succAboveCases i.castSucc ?_ (fun k => ?_) j
  · simpa only [resolventWordInsert, Fin.insertNth_apply_same] using hc i
  · simpa only [resolventWordInsert, Fin.insertNth_apply_succAbove] using hc k

/-- Uniform primitive domination, including zero word length and empty matrices. -/
theorem norm_hermitianCoordinateResolventWord_le {m : ℕ} (A : M)
    (hA : A.IsHermitian) (w : Fin m → ℂ × M)
    (hw : ∀ i, (w i).1.im ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    (hcb : ∀ i, |(w i).1.im|⁻¹ ≤ c) (y : E) :
    ‖hermitianCoordinateResolventWord A w y‖ ≤ c ^ m * ∏ i, ‖(w i).2‖ := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    let := hn
    have hz : hermitianCoordinateResolventWord A w y = 0 := Subsingleton.elim _ _
    rw [hz, norm_zero]
    positivity
  | inr hn =>
    let := hn
    calc
      _ ≤ ((((List.ofFn w).map
          (fun b => hermitianCoordinateResolvent A b.1 y * b.2)).map norm).prod) :=
        List.norm_prod_le _
      _ = ∏ i : Fin m, ‖hermitianCoordinateResolvent A (w i).1 y * (w i).2‖ := by
        simp only [List.map_ofFn, List.prod_ofFn, Function.comp_apply]
      _ ≤ ∏ i : Fin m, c * ‖(w i).2‖ := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro i _
        have hr : ‖hermitianCoordinateResolvent A (w i).1 y‖ ≤ c := by
          simpa only [specNorm_eq_norm] using
            (specNorm_hermitianCoordinateResolvent_le A hA (w i).1 (hw i) y).trans (hcb i)
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))
      _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]

/-- Uniform first derivative domination follows from the actual insertion identity. -/
theorem norm_fderiv_hermitianCoordinateResolventWord_le {m : ℕ} (A : M)
    (hA : A.IsHermitian) (w : Fin m → ℂ × M)
    (hw : ∀ i, (w i).1.im ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    (hcb : ∀ i, |(w i).1.im|⁻¹ ≤ c) (y : E) :
    ‖fderiv ℝ (hermitianCoordinateResolventWord A w) y‖ ≤
      (m : ℝ) * c ^ (m + 1) * (∏ i, ‖(w i).2‖) * ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  rw [fderiv_hermitianCoordinateResolventWord_apply A hA w hw]
  calc
    _ ≤ ∑ i : Fin m, ‖hermitianCoordinateResolventWord A
        (resolventWordInsert w i (L h)) y‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin m, c ^ (m + 1) * ‖L h‖ * ∏ i, ‖(w i).2‖ := by
      apply Finset.sum_le_sum
      intro i _
      convert! norm_hermitianCoordinateResolventWord_le A hA
        (resolventWordInsert w i (L h)) (im_ne_zero_resolventWordInsert w hw i (L h))
        hc (inv_abs_im_le_resolventWordInsert w hcb i (L h)) y using 1
      rw [prod_norm_snd_resolventWordInsert]
      ring
    _ = (m : ℝ) * c ^ (m + 1) * (∏ i, ‖(w i).2‖) * ‖L h‖ := by simp; ring
    _ ≤ ((m : ℝ) * c ^ (m + 1) * (∏ i, ‖(w i).2‖)) * (‖L‖ * ‖h‖) :=
      mul_le_mul_of_nonneg_left ((L).le_opNorm h) (by positivity)
    _ = _ := by ring

/-- Uniform Hessian domination from the genuine double-insertion formula. -/
theorem norm_iteratedFDeriv_two_hermitianCoordinateResolventWord_le {m : ℕ} (A : M)
    (hA : A.IsHermitian) (w : Fin m → ℂ × M)
    (hw : ∀ i, (w i).1.im ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    (hcb : ∀ i, |(w i).1.im|⁻¹ ≤ c) (y : E) :
    ‖iteratedFDeriv ℝ 2 (hermitianCoordinateResolventWord A w) y‖ ≤
      (m : ℝ) * (m + 1) * c ^ (m + 2) * (∏ i, ‖(w i).2‖) * ‖L‖ ^ 2 := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro h
  rw [iteratedFDeriv_two_hermitianCoordinateResolventWord_apply A hA w hw]
  have hb (i : Fin m) (j : Fin (m + 1)) :
      ‖hermitianCoordinateResolventWord A
        (resolventWordInsert (resolventWordInsert w i (L (h 1))) j (L (h 0))) y‖ ≤
        c ^ (m + 2) * (∏ i, ‖(w i).2‖) * ‖L (h 0)‖ * ‖L (h 1)‖ := by
    have hw1 := im_ne_zero_resolventWordInsert w hw i (L (h 1))
    have hc1 := inv_abs_im_le_resolventWordInsert w hcb i (L (h 1))
    convert! norm_hermitianCoordinateResolventWord_le A hA _
      (im_ne_zero_resolventWordInsert _ hw1 j (L (h 0))) hc
      (inv_abs_im_le_resolventWordInsert _ hc1 j (L (h 0))) y using 1
    rw [prod_norm_snd_resolventWordInsert, prod_norm_snd_resolventWordInsert]
    ring
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin (m + 1),
        ‖hermitianCoordinateResolventWord A
          (resolventWordInsert (resolventWordInsert w i (L (h 1))) j (L (h 0))) y‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _ : Fin m, ∑ _ : Fin (m + 1),
        c ^ (m + 2) * (∏ i, ‖(w i).2‖) * ‖L (h 0)‖ * ‖L (h 1)‖ := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ = (m : ℝ) * (m + 1) * c ^ (m + 2) * (∏ i, ‖(w i).2‖) *
        ‖L (h 0)‖ * ‖L (h 1)‖ := by simp; ring
    _ ≤ (m : ℝ) * (m + 1) * c ^ (m + 2) * (∏ i, ‖(w i).2‖) *
        (‖L‖ * ‖h 0‖) * (‖L‖ * ‖h 1‖) := by
      gcongr <;> exact (L).le_opNorm _
    _ = _ := by simp [Fin.prod_univ_succ]; ring

/-- Pointwise cubic domination keeps actual reconstructed directions. -/
theorem norm_iteratedFDeriv_three_hermitianCoordinateResolventWord_apply_le {m : ℕ} (A : M)
    (hA : A.IsHermitian) (w : Fin m → ℂ × M)
    (hw : ∀ i, (w i).1.im ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    (hcb : ∀ i, |(w i).1.im|⁻¹ ≤ c) (y : E) (h : Fin 3 → E) :
    ‖iteratedFDeriv ℝ 3 (hermitianCoordinateResolventWord A w) y h‖ ≤
      (m : ℝ) * (m + 1) * (m + 2) * c ^ (m + 3) *
        (∏ i, ‖(w i).2‖) * ‖L (h 0)‖ * ‖L (h 1)‖ * ‖L (h 2)‖ := by
  rw [iteratedFDeriv_three_hermitianCoordinateResolventWord_apply A hA w hw]
  have hb (i : Fin m) (j : Fin (m + 1)) (k : Fin (m + 2)) :
      ‖hermitianCoordinateResolventWord A
        (resolventWordInsert
          (resolventWordInsert (resolventWordInsert w i (L (h 2))) j (L (h 1)))
            k (L (h 0))) y‖ ≤
        c ^ (m + 3) * (∏ i, ‖(w i).2‖) *
          ‖L (h 0)‖ * ‖L (h 1)‖ * ‖L (h 2)‖ := by
    have hw1 := im_ne_zero_resolventWordInsert w hw i (L (h 2))
    have hc1 := inv_abs_im_le_resolventWordInsert w hcb i (L (h 2))
    have hw2 := im_ne_zero_resolventWordInsert _ hw1 j (L (h 1))
    have hc2 := inv_abs_im_le_resolventWordInsert _ hc1 j (L (h 1))
    convert! norm_hermitianCoordinateResolventWord_le A hA _
      (im_ne_zero_resolventWordInsert _ hw2 k (L (h 0))) hc
      (inv_abs_im_le_resolventWordInsert _ hc2 k (L (h 0))) y using 1
    rw [prod_norm_snd_resolventWordInsert, prod_norm_snd_resolventWordInsert,
      prod_norm_snd_resolventWordInsert]
    ring
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin (m + 1), ∑ k : Fin (m + 2),
        ‖hermitianCoordinateResolventWord A
          (resolventWordInsert
            (resolventWordInsert (resolventWordInsert w i (L (h 2))) j (L (h 1)))
              k (L (h 0))) y‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ _ : Fin m, ∑ _ : Fin (m + 1), ∑ _ : Fin (m + 2),
        c ^ (m + 3) * (∏ i, ‖(w i).2‖) *
          ‖L (h 0)‖ * ‖L (h 1)‖ * ‖L (h 2)‖ := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ => hb i j k
    _ = (m : ℝ) * (m + 1) * (m + 2) * c ^ (m + 3) * (∏ i, ‖(w i).2‖) *
        ‖L (h 0)‖ * ‖L (h 1)‖ * ‖L (h 2)‖ := by simp; ring

/-- Uniform third derivative domination from the actual ordered cubic words. -/
theorem norm_iteratedFDeriv_three_hermitianCoordinateResolventWord_le {m : ℕ} (A : M)
    (hA : A.IsHermitian) (w : Fin m → ℂ × M)
    (hw : ∀ i, (w i).1.im ≠ 0) {c : ℝ} (hc : 0 ≤ c)
    (hcb : ∀ i, |(w i).1.im|⁻¹ ≤ c) (y : E) :
    ‖iteratedFDeriv ℝ 3 (hermitianCoordinateResolventWord A w) y‖ ≤
      (m : ℝ) * (m + 1) * (m + 2) * c ^ (m + 3) *
        (∏ i, ‖(w i).2‖) * ‖L‖ ^ 3 := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro h
  have hb := norm_iteratedFDeriv_three_hermitianCoordinateResolventWord_apply_le
    A hA w hw hc hcb y h
  calc
    _ ≤ (m : ℝ) * (m + 1) * (m + 2) * c ^ (m + 3) * (∏ i, ‖(w i).2‖) *
        ‖L (h 0)‖ * ‖L (h 1)‖ * ‖L (h 2)‖ := hb
    _ ≤ (m : ℝ) * (m + 1) * (m + 2) * c ^ (m + 3) * (∏ i, ‖(w i).2‖) *
        (‖L‖ * ‖h 0‖) * (‖L‖ * ‖h 1‖) * (‖L‖ * ‖h 2‖) := by
      gcongr <;> exact (L).le_opNorm _
    _ = _ := by simp [Fin.prod_univ_succ]; ring

end NLAlib
