import NLAlib.Matrix.Norms.EntryBounds
import NLAlib.Matrix.Basic.NormalizedTrace
import NLAlib.Matrix.Norms.Schatten

/-!
# Absolute trace bounded by the nuclear norm

A singular-value decomposition and the diagonal bounds for the intervening
unitary matrix prove the trace bound over both real and complex scalars.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

open scoped Matrix.Norms.L2Operator in
/-- The absolute trace of a real or complex square matrix is at most its
nuclear norm, including empty dimensions and rank-deficient matrices. -/
theorem norm_trace_le_nuclearNorm {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    (A : Matrix n n 𝕜) : ‖A.trace‖ ≤ nuclearNorm A := by
  classical
  obtain ⟨U,V,h⟩ := exists_isSVD A
  let Q := Vᴴ * U
  have hQ : Qᴴ * Q = 1 := by
    dsimp [Q]
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [←Matrix.mul_assoc V Vᴴ,h.mul_conjTranspose_right,Matrix.one_mul,h.conjTranspose_mul_left]
  have hspec : specNorm Q ≤ 1 := by
    have hb : specNorm Q ^ 2 ≤ 1 := by
      have heq : specNorm (Qᴴ*Q) = specNorm Q ^ 2 := by
        simpa only [specNorm,pow_two] using Matrix.l2_opNorm_conjTranspose_mul_self Q
      rw [←heq,hQ]
      exact specNorm_one_le
    nlinarith [specNorm_nonneg Q]
  have htrace : A.trace = ∑ i : Fin (Fintype.card n), (singularValues A i : 𝕜) * Q i i := by
    conv_lhs => rw [h.eq,Matrix.trace_mul_cycle]
    change (Q * (rectDiag (singularValues A) : Matrix (Fin (Fintype.card n))
      (Fin (Fintype.card n)) 𝕜)).trace = _
    simp [Matrix.trace,Matrix.mul_apply,rectDiag_apply_ofReal,Fin.val_inj,mul_comm]
  rw [htrace]
  calc
    _ ≤ ∑ i : Fin (Fintype.card n), ‖(singularValues A i : 𝕜) * Q i i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (Fintype.card n), singularValues A i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,RCLike.norm_ofReal,abs_of_nonneg (singularValues_nonneg A i)]
      have hi : ‖Q i i‖ ≤ 1 := (norm_apply_le_specNorm Q i i).trans hspec
      nlinarith [singularValues_nonneg A i]
    _ = nuclearNorm A := by
      rw [nuclearNorm_eq_sum_range,min_self,Fin.sum_univ_eq_sum_range (singularValues A)]

/-- The norm of the normalized trace is the ordinary trace norm divided by
the matrix dimension, with the same zero convention for empty matrices. -/
theorem norm_normalizedTrace {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
    (A : Matrix n n 𝕜) :
    ‖normalizedTrace A‖ = ‖A.trace‖ / (Fintype.card n : ℝ) := by
  simp [normalizedTrace,norm_mul,norm_inv,RCLike.norm_natCast,div_eq_mul_inv,mul_comm]

/-- The normalized trace is bounded by the nuclear norm divided by dimension. -/
theorem norm_normalizedTrace_le_nuclearNorm_div_card {𝕜 n : Type*} [RCLike 𝕜]
    [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) :
    ‖normalizedTrace A‖ ≤ nuclearNorm A / (Fintype.card n : ℝ) := by
  rw [norm_normalizedTrace]
  exact div_le_div_of_nonneg_right (norm_trace_le_nuclearNorm A) (Nat.cast_nonneg _)

end NLAlib
