import NLAlib.ForMathlib.Analysis.CStarAlgebra.CStarMatrixPiLp
import NLAlib.ForMathlib.Analysis.NormSumSq

/-!
# The dimension bound from actual operator-matrix entries

A native C*-matrix of Hilbert operators with entry norms bounded by `r`
has norm at most `card D * r`. The actual finite Hilbert direct-sum action
and finite Cauchy--Schwarz retain one dimension factor, including empty D.
This is the operator-norm part of Lemma 4.6 of arXiv:2406.11453v2.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace CStarMatrix

variable {D H : Type*} [Fintype D] [DecidableEq D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The norm of an actual operator-valued C*-matrix is bounded by one
dimension factor times any common nonnegative bound on its entry norms. -/
theorem norm_le_card_mul_of_forall_norm_entry_le
    (M : CStarMatrix D D (H →L[ℂ] H)) {r : ℝ} (hr : 0 ≤ r)
    (hM : ∀ i j, ‖M i j‖ ≤ r) : ‖M‖ ≤ (Fintype.card D : ℝ) * r := by
  rw [← norm_toPiLpStarAlgHom M]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hr)
  intro x
  have hrow (i : D) : ‖∑ j, M i j (x j)‖ ^ 2 ≤
      (Fintype.card D : ℝ) * r ^ 2 * ‖x‖ ^ 2 := by
    calc
      _ ≤ (Fintype.card D : ℝ) * ∑ j, ‖M i j (x j)‖ ^ 2 := by
        simpa only [Finset.card_univ] using
          NLAlib.norm_sum_sq_le_card_mul_sum_norm_sq Finset.univ (fun j => M i j (x j))
      _ ≤ (Fintype.card D : ℝ) * ∑ j, (r * ‖x j‖) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (norm_nonneg _)
          (((M i j).le_opNorm (x j)).trans
            (mul_le_mul_of_nonneg_right (hM i j) (norm_nonneg _))) 2
      _ = _ := by
        simp only [mul_pow, ← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2]
        ring
  have hsq : ‖toPiLpStarAlgHom (D := D) (H := H) M x‖ ^ 2 ≤
      ((Fintype.card D : ℝ) * r * ‖x‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [toPiLpStarAlgHom_apply]
    calc
      _ ≤ ∑ _i : D, (Fintype.card D : ℝ) * r ^ 2 * ‖x‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => hrow i)
      _ = _ := by simp; ring
  have hright : 0 ≤ (Fintype.card D : ℝ) * r * ‖x‖ := by positivity
  nlinarith [norm_nonneg (toPiLpStarAlgHom (D := D) (H := H) M x)]

end CStarMatrix
