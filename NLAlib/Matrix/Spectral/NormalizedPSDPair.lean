import NLAlib.Matrix.Spectral.CommutingHermitian
import NLAlib.Matrix.Basic.GramVanishing
import Mathlib.Analysis.Matrix.Spectrum
/-!+# Arbitrary-rank normalized positive semidefinite pairs

Whiten the positive spectral coordinates of the sum, leaving its common
kernel unchanged. The transformed summands add to a projection and commute.
One common unitary eigenbasis therefore gives normalized diagonal pairs.
No nonsingularity assumption is made on either matrix or their sum.
-/
noncomputable section
open Matrix
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- PSD summands of a real diagonal projection commute, over either field. -/
theorem commute_of_posSemidef_add_eq_diagonal_projection_ofReal
    {A B : Matrix n n 𝕜} {p : n → ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : A + B = diagonal (fun i => (p i : 𝕜)))
    (hp : ∀ i, p i = 0 ∨ p i = 1) : Commute A B := by
  have hAP : A * diagonal (fun i => (p i : 𝕜)) = A := by
    ext i j
    rw [Matrix.mul_diagonal]
    rcases hp j with hj | hj
    · have he := congrArg (fun M : Matrix n n 𝕜 => M j j) hAB
      simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, hj, RCLike.ofReal_zero] at he
      have hz : A j j = 0 := le_antisymm (by
        calc
          A j j ≤ A j j + B j j := le_add_of_nonneg_right (hB.diag_nonneg (i := j))
          _ = 0 := he) (hA.diag_nonneg (i := j))
      rw [hj, RCLike.ofReal_zero, mul_zero,
        apply_eq_zero_of_posSemidef_of_apply_self_eq_zero hA hz i]
    · rw [hj, RCLike.ofReal_one, mul_one]
  have hPA : diagonal (fun i => (p i : 𝕜)) * A = A := by
    have hd : (diagonal (fun i => (p i : 𝕜)))ᴴ = diagonal (fun i => (p i : 𝕜)) := by simp
    simpa only [Matrix.conjTranspose_mul, hd, hA.isHermitian.eq] using
      congrArg Matrix.conjTranspose hAP
  change A * B = B * A
  have hl : A * A + A * B = A := by rw [← Matrix.mul_add, hAB, hAP]
  have hr : A * A + B * A = A := by rw [← Matrix.add_mul, hAB, hPA]
  exact add_left_cancel (hl.trans hr.symm)

open scoped Matrix.Norms.L2Operator in
/-- Every PSD pair has an invertible normalized diagonal congruence, with
diagonal sums exactly zero or one. Zero sums are precisely the common
kernel coordinates. Horn–Johnson (2013), §7.6; supports arbitrary-rank GSVD. -/
theorem exists_normalized_psd_pair_congruence {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ (X : Matrix n n 𝕜) (a b : n → ℝ), IsUnit X ∧
      Xᴴ * A * X = diagonal (fun i => (a i : 𝕜)) ∧
      Xᴴ * B * X = diagonal (fun i => (b i : 𝕜)) ∧
      (∀ i, 0 ≤ a i) ∧ (∀ i, 0 ≤ b i) ∧
      ∀ i, a i + b i = 0 ∨ a i + b i = 1 := by
  classical
  let hC := (hA.add hB).isHermitian
  let U : Matrix n n 𝕜 := hC.eigenvectorUnitary
  let c := hC.eigenvalues
  have hc : ∀ i, 0 ≤ c i := (hA.add hB).eigenvalues_nonneg
  have hUt : Uᴴ * U = 1 := Unitary.coe_star_mul_self hC.eigenvectorUnitary
  have hU : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr
    (Matrix.isUnit_det_of_left_inverse hUt)
  have hCU : Uᴴ * (A + B) * U = diagonal (fun i => (c i : 𝕜)) := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Unitary.coe_star, Matrix.conjTranspose_conjTranspose, Function.comp_def, U, c]
      using hC.conjStarAlgAut_star_eigenvectorUnitary
  let t : n → ℝ := fun i => if c i = 0 then 1 else (Real.sqrt (c i))⁻¹
  have ht : ∀ i, t i ≠ 0 := by
    intro i
    dsimp only [t]
    split_ifs with hi
    · exact one_ne_zero
    · exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hc i) (Ne.symm hi)))
  let D : Matrix n n 𝕜 := diagonal (fun i => (t i : 𝕜))
  have hD : Dᴴ = D := by simp [D]
  let R : Matrix n n 𝕜 := U * D
  have hR : IsUnit R := hU.mul (Matrix.isUnit_diagonal.mpr
    (Pi.isUnit_iff.mpr fun i => isUnit_iff_ne_zero.mpr (by exact_mod_cast ht i)))
  let A' := Rᴴ * A * R
  let B' := Rᴴ * B * R
  have hA' : A'.PosSemidef := hA.conjTranspose_mul_mul_same R
  have hB' : B'.PosSemidef := hB.conjTranspose_mul_mul_same R
  let p : n → ℝ := fun i => t i * c i * t i
  have hsum : A' + B' = diagonal (fun i => (p i : 𝕜)) := by
    calc
      A' + B' = Rᴴ * (A + B) * R := by simp only [Matrix.mul_add, Matrix.add_mul, A', B']
      _ = D * (Uᴴ * (A + B) * U) * D := by
        simp only [R, Matrix.conjTranspose_mul, hD, Matrix.mul_assoc]
      _ = diagonal (fun i => (p i : 𝕜)) := by
        rw [hCU, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        simp only [p, map_mul]
  have hp : ∀ i, p i = 0 ∨ p i = 1 := by
    intro i
    by_cases hi : c i = 0
    · exact Or.inl (by simp [p, hi])
    · right
      have hs : Real.sqrt (c i) ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hc i) (Ne.symm hi))
      dsimp only [p, t]
      rw [if_neg hi]
      field_simp
      exact (Real.sq_sqrt (hc i)).symm
  obtain ⟨V, a, b, hV, hVA, hVB⟩ := exists_unitary_congruence_diagonal_of_commute
    hA'.isHermitian hB'.isHermitian
    (commute_of_posSemidef_add_eq_diagonal_projection_ofReal hA' hB' hsum hp)
  have hVu : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).mpr
    (Matrix.isUnit_det_of_left_inverse hV.conjTranspose_mul_self)
  have ha : ∀ i, 0 ≤ a i := by
    have hpos := hA'.conjTranspose_mul_mul_same V
    rw [hVA] at hpos
    intro i
    have hi : (0 : 𝕜) ≤ (a i : 𝕜) := by simpa using hpos.diag_nonneg (i := i)
    exact_mod_cast hi
  have hb : ∀ i, 0 ≤ b i := by
    have hpos := hB'.conjTranspose_mul_mul_same V
    rw [hVB] at hpos
    intro i
    have hi : (0 : 𝕜) ≤ (b i : 𝕜) := by simpa using hpos.diag_nonneg (i := i)
    exact_mod_cast hi
  refine ⟨R * V, a, b, hR.mul hVu, ?_, ?_, ha, hb, ?_⟩
  · simpa only [A', Matrix.conjTranspose_mul, Matrix.mul_assoc] using hVA
  · simpa only [B', Matrix.conjTranspose_mul, Matrix.mul_assoc] using hVB
  · have hP : (A' + B') * (A' + B') = A' + B' := by
      rw [hsum, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rcases hp i with hi | hi <;> simp [hi]
    have hVV : V * Vᴴ = 1 := mul_eq_one_comm.mp hV.conjTranspose_mul_self
    have hVsum : Vᴴ * (A' + B') * V = diagonal (fun i => ((a i + b i : ℝ) : 𝕜)) := by
      rw [Matrix.mul_add, Matrix.add_mul, hVA, hVB, Matrix.diagonal_add]
      simp only [map_add]
    have he : (Vᴴ * (A' + B') * V) * (Vᴴ * (A' + B') * V) = Vᴴ * (A' + B') * V := by
      calc
        _ = Vᴴ * ((A' + B') * (V * Vᴴ) * (A' + B')) * V := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hVV, Matrix.mul_one, hP]
    rw [hVsum, Matrix.diagonal_mul_diagonal] at he
    intro i
    have hi := congrArg (fun M : Matrix n n 𝕜 => M i i) he
    simp only [Matrix.diagonal_apply_eq] at hi
    have hir : (a i + b i) * (a i + b i) = a i + b i := by exact_mod_cast hi
    have hz : (a i + b i) * (a i + b i - 1) = 0 := by nlinarith [hir]
    rcases mul_eq_zero.mp hz with hh | hh
    · exact Or.inl hh
    · exact Or.inr (sub_eq_zero.mp hh)

end NLAlib
