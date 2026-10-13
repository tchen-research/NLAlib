import NLAlib.Polynomial.BestApproximation.GapNormal
import NLAlib.Polynomial.BestApproximation.GapProperness
import NLAlib.ForMathlib.Analysis.PeakComparison
import NLAlib.ForMathlib.LinearAlgebra.Matrix.ContinuousEquiv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Global comparison of the actual interpolation peaks

The concrete Jacobian, normalized positive normal, smooth peak charts, and
quantitative boundary estimates discharge every hypothesis of the global
proper-map comparison. No comparison or smoothness premise is assumed.
Source: focused reroutes, the Bernstein–Erdős peak comparison.
-/

noncomputable section

open Set Finset
open scoped Matrix

namespace NLAlib

/-- The equal-peak configuration compares to every actual canonical node grid
through a finite convex combination of its gap peaks.
Source: focused reroutes, the proper peak-difference inverse and positive normal.
Helper for the universal sharp Lebesgue lower bound. -/
theorem exists_equal_interpolation_peaks_with_convex_combination {n : ℕ} (hn : 0 < n) :
    ∃ t ∈ interiorNodeSimplex n,
      (∀ i, interpolationGapPeak n t i = interpolationGapPeak n t 0) ∧
      ∀ u ∈ interiorNodeSimplex n, ∃ w : Fin (n + 1) → ℝ,
        (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
        interpolationGapPeak n t 0 = ∑ i, w i * interpolationGapPeak n u i := by
  classical
  let M : Fin (n + 1) → (Fin n → ℝ) → ℝ := fun i t => interpolationGapPeak n t i
  let L : Fin (n + 1) → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ := fun i t =>
    ∑ j, interpolationGapJacobian n t i j • ContinuousLinearMap.proj j
  have hM : ∀ i t, t ∈ interiorNodeSimplex n → HasFDerivAt (M i) (L i t) t :=
    fun i t ht => hasFDerivAt_interpolationGapPeak_jacobian hn ht i
  have hΓ : ∀ t ∈ interiorNodeSimplex n,
      ∃ e : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ),
        HasStrictFDerivAt (interpolationPeakDifference n) (e : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) t := by
    intro t ht
    let A : Matrix (Fin n) (Fin n) ℝ :=
      fun i j => interpolationGapJacobian n t i.succ j - interpolationGapJacobian n t 0 j
    obtain ⟨e, he⟩ := exists_continuousLinearEquiv_apply_eq_mulVec A
      (det_interpolationGapJacobian_difference_ne_zero hn ht)
    have heL : (e : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) =
        ContinuousLinearMap.pi (fun i => L i.succ t - L 0 t) := by
      ext v i
      change (e v) i = (ContinuousLinearMap.pi (fun i => L i.succ t - L 0 t)) v i
      rw [he]
      simp only [ContinuousLinearMap.pi_apply, sub_apply, L,
        _root_.sum_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply,
        Matrix.mulVec, dotProduct, A, sub_mul, sum_sub_distrib]
    have hd : HasFDerivAt (interpolationPeakDifference n)
        (ContinuousLinearMap.pi (fun i => L i.succ t - L 0 t)) t := by
      apply hasFDerivAt_pi.mpr
      intro i
      exact (hM i.succ t ht).sub (hM 0 t ht)
    have hc : ContDiffAt ℝ 1 (interpolationPeakDifference n) t :=
      contDiffAt_pi.mpr (fun i => (contDiffAt_interpolationGapPeak hn ht i.succ).sub
        (contDiffAt_interpolationGapPeak hn ht 0))
    refine ⟨e, ?_⟩
    rw [heL]
    exact hc.hasStrictFDerivAt' hd one_ne_zero
  let D : (Fin n → ℝ) → (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) := fun t =>
    if ht : t ∈ interiorNodeSimplex n then (hΓ t ht).choose else ContinuousLinearEquiv.refl ℝ _
  have hD : ∀ t ∈ interiorNodeSimplex n,
      HasStrictFDerivAt (interpolationPeakDifference n) (D t : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) t := by
    intro t ht
    simpa only [D, dif_pos ht] using (hΓ t ht).choose_spec
  have hW : ∀ t ∈ interiorNodeSimplex n, ∃ w : Fin (n + 1) → ℝ,
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ ∀ v, ∑ i, w i * L i t v = 0 := by
    intro t ht
    obtain ⟨w, hw, hs, hk⟩ := exists_pos_vecMul_interpolationGapJacobian_eq_zero hn ht
    refine ⟨w, fun i => (hw i).le, hs, fun v => ?_⟩
    simp only [L, _root_.sum_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
    simp_rw [mul_sum, ← mul_assoc]
    rw [sum_comm]
    apply sum_eq_zero
    intro j hj
    rw [← sum_mul]
    have he : (∑ i, w i * interpolationGapJacobian n t i j) = 0 := congrFun hk j
    rw [he, zero_mul]
  let W : (Fin n → ℝ) → Fin (n + 1) → ℝ := fun t =>
    if ht : t ∈ interiorNodeSimplex n then (hW t ht).choose else fun _ => 0
  have hWspec : ∀ t ∈ interiorNodeSimplex n,
      (∀ i, 0 ≤ W t i) ∧ (∑ i, W t i = 1) ∧ ∀ v, ∑ i, W t i * L i t v = 0 := by
    intro t ht
    simpa only [W, dif_pos ht] using (hW t ht).choose_spec
  have hc : ContinuousOn (interpolationPeakDifference n) (interiorNodeSimplex n) := by
    intro t ht
    exact (hD t ht).hasFDerivAt.continuousAt.continuousWithinAt
  let : Nonempty (interiorNodeSimplex n) := (nonempty_interiorNodeSimplex n).to_subtype
  let : PreconnectedSpace (interiorNodeSimplex n) :=
    Subtype.preconnectedSpace (convex_interiorNodeSimplex n).isPreconnected
  exact exists_equal_peaks_with_convex_combination (isOpen_interiorNodeSimplex n) hM hD
    (isProperMap_interpolationPeakDifference hc)
    (fun t ht => (hWspec t ht).1) (fun t ht => (hWspec t ht).2.1)
    (fun t ht => (hWspec t ht).2.2)

end NLAlib
