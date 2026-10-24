/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Sketching.Properties.ObliviousSubspaceInjection.Basic
import NLAlib.Matrix.Subspaces.RangeProjector

/-!
# Deterministic inverse bounds under a subspace injection

A lower embedding on an orthonormal frame gives full row rank of its transposed sketch and
the Frobenius bound required for the OSI cross residual. The proof sums the lower bound over
columns and uses the contraction of the actual Moore–Penrose range projector.
Source: Camaño–Epperly–Meyer–Tropp (2025), proof of Lemma 2.1;
`NLA-lib/NLAlib` commit `6a845a2ec27f37c1a98118c107a06a13ce45273d`,
`Regression/Embedding.lean` (Apache-2.0), adapted to native pseudoinverse notation.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib
variable {𝕜 k n r t : Type*} [RCLike 𝕜] [Fintype k] [Fintype n] [Fintype r]
  [Fintype t] [DecidableEq k] [DecidableEq r]

private theorem frobSq_eq_sum_norm_col {a b : Type*} [Fintype a] [Fintype b]
    (M : Matrix a b 𝕜) : frobSq M = ∑ j, ‖WithLp.toLp 2 (M.col j)‖ ^ 2 := by
  rw [frobSq_eq_sum_norm_sq, Finset.sum_comm]
  simp only [EuclideanSpace.norm_sq_eq, Matrix.col_apply]

omit [DecidableEq k] in
private theorem frame_lower {S : Matrix k n 𝕜} {Q : Matrix n r 𝕜} {α : ℝ}
    (h : IsSubspaceInjection S Q α) (hQ : HasOrthonormalCols Q) (x : r → 𝕜) :
    α * ‖WithLp.toLp 2 x‖ ^ 2 ≤ ‖WithLp.toLp 2 ((S * Q) *ᵥ x)‖ ^ 2 := by
  have he : ‖WithLp.toLp 2 (Q *ᵥ x)‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 := by
    rw [norm_toLp_sq_eq_re_star_dotProduct,
      star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ,
      norm_toLp_sq_eq_re_star_dotProduct]
  simpa only [Matrix.mulVec_mulVec, he] using h x

omit [DecidableEq k] in
/-- A positive lower embedding gives full row rank of the head sketch's adjoint.
This is the rank clause in Camaño–Epperly–Meyer–Tropp (2025), Lemma 2.1. -/
theorem IsSubspaceInjection.rank_conjTranspose_mul_eq_card {S : Matrix k n 𝕜}
    {Q : Matrix n r 𝕜} {α : ℝ} (h : IsSubspaceInjection S Q α)
    (hQ : HasOrthonormalCols Q) (hα : 0 < α) :
    ((S * Q)ᴴ).rank = Fintype.card r := by
  have hinj : Function.Injective (S * Q).mulVecLin := by
    intro x y hxy
    have hz : (S * Q) *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub]
      exact sub_eq_zero.mpr hxy
    have hb := frame_lower h hQ (x - y)
    rw [hz, WithLp.toLp_zero, norm_zero, zero_pow two_ne_zero] at hb
    have hs : ‖WithLp.toLp 2 (x - y)‖ ^ 2 ≤ 0 :=
      (mul_le_mul_iff_right₀ hα).mp (by simpa only [mul_zero] using hb)
    have hn : ‖WithLp.toLp 2 (x - y)‖ = 0 := by
      nlinarith [norm_nonneg (WithLp.toLp 2 (x - y))]
    exact sub_eq_zero.mp ((WithLp.toLp_eq_zero 2).mp (norm_eq_zero.mp hn))
  rw [Matrix.rank_conjTranspose, Matrix.rank,
    LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]

/-- Under a lower embedding, every right-hand side obeys the inverse Frobenius estimate.
The general Moore–Penrose inverse is used, with no assumed inverse norm certificate.
Camaño–Epperly–Meyer–Tropp (2025), proof of Lemma 2.1. -/
theorem IsSubspaceInjection.frobSq_mul_moorePenroseInverse_conjTranspose_le
    {S : Matrix k n 𝕜} {Q : Matrix n r 𝕜} {α : ℝ}
    (h : IsSubspaceInjection S Q α) (hQ : HasOrthonormalCols Q) (hα : 0 < α)
    (Z : Matrix t k 𝕜) :
    frobSq (Z * moorePenroseInverse ((S * Q)ᴴ)) ≤ frobSq Z / α := by
  let A := S * Q
  let C := moorePenroseInverse A * Zᴴ
  have hlower : α * frobSq C ≤ frobSq (A * C) := by
    rw [frobSq_eq_sum_norm_col, frobSq_eq_sum_norm_col, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      simpa only [col_mul_eq_mulVec_col, A] using frame_lower h hQ (C.col j)
  have hP : specNorm (rangeProjector A) ≤ 1 :=
    (rangeProjector_isHermitian A).specNorm_le_one_of_isIdempotentElem
      (rangeProjector_isIdempotentElem A)
  have hcon : frobSq (A * C) ≤ frobSq Z := by
    calc
      frobSq (A * C) = frobSq (rangeProjector A * Zᴴ) := by
        change frobSq (A * (moorePenroseInverse A * Zᴴ)) =
          frobSq ((A * moorePenroseInverse A) * Zᴴ)
        exact congrArg frobSq (Matrix.mul_assoc A (moorePenroseInverse A) Zᴴ).symm
      _ ≤ specNorm (rangeProjector A) ^ 2 * frobSq Zᴴ :=
        frobSq_mul_le_specNorm_sq_mul_frobSq _ _
      _ ≤ 1 ^ 2 * frobSq Zᴴ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (specNorm_nonneg _) hP 2) (frobSq_nonneg _)
      _ = frobSq Z := by rw [one_pow, one_mul, frobSq_conjTranspose]
  have he : frobSq C = frobSq (Z * moorePenroseInverse ((S * Q)ᴴ)) := by
    rw [← frobSq_conjTranspose (Z * moorePenroseInverse ((S * Q)ᴴ)),
      Matrix.conjTranspose_mul, ← moorePenroseInverse_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  rw [he] at hlower
  exact (le_div_iff₀ hα).mpr (by simpa only [mul_comm] using hlower.trans hcon)

end NLAlib
