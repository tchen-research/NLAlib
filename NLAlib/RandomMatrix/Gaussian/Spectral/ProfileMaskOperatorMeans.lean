import NLAlib.RandomMatrix.Gaussian.Moments.ProfileBlockMaximum
import NLAlib.RandomMatrix.Gaussian.Basic.ProfileMasks
import NLAlib.RandomMatrix.Gaussian.Spectral.VarianceProfileWeakBound
import NLAlib.Matrix.Structured.ProfileMaskBounds
import NLAlib.Matrix.Norms.FiniteBlockSupport

/-!
# Operator means of the three rearranged Gaussian profile parts

The diagonal masks are bounded by their actual finite block maxima. The weak
Gaussian-process estimate controls the rapidly decaying remainder. Together
they give the sharp two-profile upper mean bound for a rearranged profile.
Source: Latała--van Handel--Youssef (2018), Section 3.2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {n : ℕ}

/-- The first diagonal mask has a dimension-free actual Gaussian operator
mean bound. -/
theorem integral_specNorm_symmetricGaussianMatrix_profileFirstPart_le
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA0 : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ a ^ 2)
    (hthreshold : ∀ k i j, profileCutoff k ≤ i.val →
      A i j ≤ b / Real.sqrt (Real.log (profilePreviousCutoff k))) :
    (∫ G, specNorm (symmetricGaussianMatrix (profileFirstPart A) G)
      ∂gaussianMatrix (Fin n) (Fin n)) ≤ 224 * (a + b) := by
  have hpoint (G : Matrix (Fin n) (Fin n) ℝ) :
      specNorm (symmetricGaussianMatrix (profileFirstPart A) G) ≤
        ⨆ t : Fin (n + 1), specNorm (symmetricGaussianMatrix (profileBlockPart A t.val) G) := by
    have hmax (t : Fin (n + 1)) :
        specNorm (symmetricGaussianMatrix (profileBlockPart A t.val) G) ≤
          ⨆ t : Fin (n + 1), specNorm (symmetricGaussianMatrix (profileBlockPart A t.val) G) :=
      le_ciSup (f := fun t : Fin (n + 1) =>
        specNorm (symmetricGaussianMatrix (profileBlockPart A t.val) G))
        (Set.finite_range _).bddAbove t
    rw [symmetricGaussianMatrix_profileFirstPart]
    apply specNorm_profileFirstPart_le _ ((specNorm_nonneg _).trans (hmax 0))
    intro t ht _
    rw [← symmetricGaussianMatrix_profileBlockPart]
    exact hmax ⟨t, Nat.lt_succ_of_le ht⟩
  let f : Fin (n + 1) → Matrix (Fin n) (Fin n) ℝ → ℝ := fun t G =>
    specNorm (symmetricGaussianMatrix (profileBlockPart A t.val) G)
  have hInt : Integrable (fun G => ⨆ t, f t G) (gaussianMatrix (Fin n) (Fin n)) :=
    integrable_iSup_of_integrable_finite f fun t =>
      integrable_specNorm_symmetricGaussianMatrix_of_finite_profile (profileBlockPart A t.val)
  have hmono := integral_mono
    (f := fun G => specNorm (symmetricGaussianMatrix (profileFirstPart A) G))
    (g := fun G => ⨆ t, f t G)
    (integrable_specNorm_symmetricGaussianMatrix_of_finite_profile (profileFirstPart A)) hInt hpoint
  exact hmono.trans (integral_iSup_specNorm_symmetricGaussianMatrix_profileBlockPart_le
    A A hA (fun _ _ => le_rfl) ha hb hA0 hrow hthreshold)

/-- The second diagonal mask has the same actual Gaussian operator mean bound,
including the removed overlap with the first mask. -/
theorem integral_specNorm_symmetricGaussianMatrix_profileSecondPart_le
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA0 : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ a ^ 2)
    (hthreshold : ∀ k i j, profileCutoff k ≤ i.val →
      A i j ≤ b / Real.sqrt (Real.log (profilePreviousCutoff k))) :
    (∫ G, specNorm (symmetricGaussianMatrix (profileSecondPart A) G)
      ∂gaussianMatrix (Fin n) (Fin n)) ≤ 224 * (a + b) := by
  have hpoint (G : Matrix (Fin n) (Fin n) ℝ) :
      specNorm (symmetricGaussianMatrix (profileSecondPart A) G) ≤
        ⨆ t : Fin (n + 1), specNorm (symmetricGaussianMatrix
          (profileBlockPart (profileSecondPart A) t.val) G) := by
    have hmax (t : Fin (n + 1)) :
        specNorm (symmetricGaussianMatrix (profileBlockPart (profileSecondPart A) t.val) G) ≤
          ⨆ t : Fin (n + 1), specNorm (symmetricGaussianMatrix
            (profileBlockPart (profileSecondPart A) t.val) G) :=
      le_ciSup (f := fun t : Fin (n + 1) =>
        specNorm (symmetricGaussianMatrix (profileBlockPart (profileSecondPart A) t.val) G))
        (Set.finite_range _).bddAbove t
    rw [symmetricGaussianMatrix_profileSecondPart]
    apply specNorm_profileSecondPart_le _ ((specNorm_nonneg _).trans (hmax 0))
    intro t ht _
    rw [← symmetricGaussianMatrix_profileSecondPart, ← symmetricGaussianMatrix_profileBlockPart]
    exact hmax ⟨t, Nat.lt_succ_of_le ht⟩
  let f : Fin (n + 1) → Matrix (Fin n) (Fin n) ℝ → ℝ := fun t G =>
    specNorm (symmetricGaussianMatrix (profileBlockPart (profileSecondPart A) t.val) G)
  have hInt : Integrable (fun G => ⨆ t, f t G) (gaussianMatrix (Fin n) (Fin n)) :=
    integrable_iSup_of_integrable_finite f fun t =>
      integrable_specNorm_symmetricGaussianMatrix_of_finite_profile
        (profileBlockPart (profileSecondPart A) t.val)
  have hmono := integral_mono
    (f := fun G => specNorm (symmetricGaussianMatrix (profileSecondPart A) G))
    (g := fun G => ⨆ t, f t G)
    (integrable_specNorm_symmetricGaussianMatrix_of_finite_profile (profileSecondPart A)) hInt hpoint
  exact hmono.trans (integral_iSup_specNorm_symmetricGaussianMatrix_profileBlockPart_le
    A (profileSecondPart A) (isSymm_profile_parts A hA).2.1
    (fun i j => (profile_parts_sq_le A i j).2.1) ha hb hA0 hrow hthreshold)

/-- The rapidly decaying residual mask has actual expected Gaussian spectral
norm bounded by `3400` times the original maximum row-energy bound. -/
theorem integral_specNorm_symmetricGaussianMatrix_profileRemainderPart_le
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) {a : ℝ} (ha : 0 ≤ a)
    (hA0 : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ a ^ 2)
    (hcross : ∀ k i j, profileNeighborCutoff k ≤ i.val → j.val < profileCutoff k →
      A i j ≤ a / Real.sqrt (profilePreviousCutoff k)) :
    (∫ G, specNorm (symmetricGaussianMatrix (profileRemainderPart A) G)
      ∂gaussianMatrix (Fin n) (Fin n)) ≤ 3400 * a := by
  classical
  have hentry (i j : Fin n) : A i j ≤ a := by
    have h := (Finset.single_le_sum (fun l _ => sq_nonneg (A i l))
      (Finset.mem_univ j)).trans (hrow i)
    nlinarith [hA0 i j]
  have hnonneg (i j : Fin n) : 0 ≤ profileRemainderPart A i j := by
    unfold profileRemainderPart
    split_ifs
    · exact hA0 i j
    · exact le_rfl
  have hcap (i j : Fin n) : |profileRemainderPart A i j| * Real.log (i.val + 2) ≤ 16 * a := by
    rw [abs_of_nonneg (hnonneg i j)]
    have hw := profileRemainderPart_mul_log_le_eight_mul A hA ha hA0 hentry hcross i j
    by_cases hi : i.val = 0
    · have hr : profileRemainderPart A i j ≤ a := by
        unfold profileRemainderPart
        split_ifs
        · exact hentry i j
        · exact ha
      have hlog : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      simp only [hi, Nat.cast_zero, zero_add]
      nlinarith [mul_le_mul_of_nonneg_left hlog (hnonneg i j)]
    · have hi' : (1 : ℝ) ≤ i.val := by exact_mod_cast (by omega : 1 ≤ i.val)
      have hlog : Real.log (i.val + 2 : ℝ) ≤ 2 * Real.log (i.val + 1 : ℝ) := by
        calc
          _ ≤ Real.log ((i.val + 1 : ℝ) ^ 2) :=
            Real.log_le_log (by positivity) (by nlinarith)
          _ = _ := Real.log_pow _ _
      nlinarith [mul_le_mul_of_nonneg_left hlog (hnonneg i j)]
  have h := integral_specNorm_symmetricGaussianMatrix_le_log_envelope
    (profileRemainderPart A) (isSymm_profile_parts A hA).2.2 a (16 * a) ha (by positivity)
    (fun i => (Finset.sum_le_sum fun j _ => (profile_parts_sq_le A i j).2.2).trans (hrow i)) hcap
  nlinarith

/-- The three explicit profile masks give a universal operator mean bound for
every profile satisfying the constructed row and heavy-neighbor inequalities.
All three component expectations are actual Gaussian matrix expectations. -/
theorem integral_specNorm_symmetricGaussianMatrix_le_of_profile_rearrangement
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA0 : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ a ^ 2)
    (hthreshold : ∀ k i j, profileCutoff k ≤ i.val →
      A i j ≤ b / Real.sqrt (Real.log (profilePreviousCutoff k)))
    (hcross : ∀ k i j, profileNeighborCutoff k ≤ i.val → j.val < profileCutoff k →
      A i j ≤ a / Real.sqrt (profilePreviousCutoff k)) :
    (∫ G, specNorm (symmetricGaussianMatrix A G) ∂gaussianMatrix (Fin n) (Fin n)) ≤
      4096 * (a + b) := by
  have hdecomp (G : Matrix (Fin n) (Fin n) ℝ) :
      symmetricGaussianMatrix A G =
        symmetricGaussianMatrix (profileFirstPart A) G +
        symmetricGaussianMatrix (profileSecondPart A) G +
        symmetricGaussianMatrix (profileRemainderPart A) G := by
    rw [symmetricGaussianMatrix_profileFirstPart, symmetricGaussianMatrix_profileSecondPart,
      symmetricGaussianMatrix_profileRemainderPart]
    exact (profileFirstPart_add_secondPart_add_remainderPart _).symm
  have hF := integrable_specNorm_symmetricGaussianMatrix_of_finite_profile (profileFirstPart A)
  have hS := integrable_specNorm_symmetricGaussianMatrix_of_finite_profile (profileSecondPart A)
  have hW := integrable_specNorm_symmetricGaussianMatrix_of_finite_profile (profileRemainderPart A)
  have hpoint (G : Matrix (Fin n) (Fin n) ℝ) :
      specNorm (symmetricGaussianMatrix A G) ≤
        specNorm (symmetricGaussianMatrix (profileFirstPart A) G) +
        specNorm (symmetricGaussianMatrix (profileSecondPart A) G) +
        specNorm (symmetricGaussianMatrix (profileRemainderPart A) G) := by
    rw [hdecomp G]
    exact specNorm_add_add_le (symmetricGaussianMatrix (profileFirstPart A) G)
      (symmetricGaussianMatrix (profileSecondPart A) G)
      (symmetricGaussianMatrix (profileRemainderPart A) G)
  have htotal := integral_mono
    (f := fun G => specNorm (symmetricGaussianMatrix A G))
    (g := fun G => specNorm (symmetricGaussianMatrix (profileFirstPart A) G) +
      specNorm (symmetricGaussianMatrix (profileSecondPart A) G) +
      specNorm (symmetricGaussianMatrix (profileRemainderPart A) G))
    (integrable_specNorm_symmetricGaussianMatrix_of_finite_profile A) ((hF.add hS).add hW) hpoint
  have hFS : Integrable (fun G =>
      specNorm (symmetricGaussianMatrix (profileFirstPart A) G) +
      specNorm (symmetricGaussianMatrix (profileSecondPart A) G))
      (gaussianMatrix (Fin n) (Fin n)) := hF.add hS
  rw [integral_add hFS hW, integral_add hF hS] at htotal
  have hfirst := integral_specNorm_symmetricGaussianMatrix_profileFirstPart_le
    A hA ha hb hA0 hrow hthreshold
  have hsecond := integral_specNorm_symmetricGaussianMatrix_profileSecondPart_le
    A hA ha hb hA0 hrow hthreshold
  have hrem := integral_specNorm_symmetricGaussianMatrix_profileRemainderPart_le
    A hA ha hA0 hrow hcross
  linarith

end NLAlib
