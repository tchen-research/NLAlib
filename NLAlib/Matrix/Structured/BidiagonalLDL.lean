import NLAlib.Matrix.Structured.BidiagonalDarboux

/-! # Entries of a bidiagonal LDL transpose product

The symmetric tridiagonal product has diagonal `d_i+e_(i-1)^2*d_(i-1)`
and neighboring entries `e_i*d_i`. The first diagonal omits its predecessor.
Source: Gautschi (2004), Theorem 1.33; supports the kernel polynomial factorization.
-/

noncomputable section
open Matrix
open scoped Matrix
namespace NLAlib
variable {𝕜 : Type*} [CommRing 𝕜]

/-- The entry formula for a unit lower bidiagonal LDL transpose product. -/
theorem darbouxLowerMatrix_mul_diagonal_mul_transpose_apply {n : ℕ}
    (d e : ℕ → 𝕜) (i j : Fin n) :
    (darbouxLowerMatrix n e * diagonal (fun k : Fin n => d k.val) *
      (darbouxLowerMatrix n e)ᵀ) i j =
    if i.val = j.val then d i.val +
      (if i.val = 0 then 0 else e (i.val - 1) ^ 2 * d (i.val - 1))
    else if i.val + 1 = j.val then e i.val * d i.val
    else if j.val + 1 = i.val then e j.val * d j.val else 0 := by
  rw [Matrix.mul_assoc, darbouxLowerMatrix_mul_apply]
  simp only [diagonal_mul, transpose_apply, darbouxLowerMatrix, Matrix.add_apply,
    Matrix.one_apply, Matrix.of_apply]
  simp only [Fin.ext_iff]
  by_cases hij : i.val = j.val
  · have heq : i = j := Fin.ext hij
    subst j
    by_cases hi : i.val = 0
    · simp [hi]
    · have hp : 0 < i.val := by omega
      have hprev : i.val - 1 + 1 = i.val := by omega
      have hne : i.val ≠ i.val - 1 := by omega
      simp only [ite_true, dif_pos hp, if_neg hi,
        if_neg (show i.val + 1 ≠ i.val by omega), if_neg hne, if_pos hprev]
      ring
  · by_cases hsup : i.val + 1 = j.val
    · simp only [if_neg hij, if_neg (Ne.symm hij), if_pos hsup]
      by_cases hi : 0 < i.val
      · simp only [dif_pos hi, if_neg (show j.val ≠ i.val - 1 by omega),
          if_neg (show i.val - 1 + 1 ≠ j.val by omega)]
        ring
      · simp [hi, mul_comm]
    · by_cases hsub : j.val + 1 = i.val
      · have hi : 0 < i.val := by omega
        have hprev : i.val - 1 = j.val := by omega
        simp only [if_neg hij, if_neg (Ne.symm hij), if_neg hsup,
          if_pos hsub, dif_pos hi, hprev, ite_true,
          if_neg (show j.val + 1 ≠ j.val by omega)]
        ring
      · simp only [if_neg hij, if_neg (Ne.symm hij), if_neg hsup, if_neg hsub]
        by_cases hi : 0 < i.val
        · simp only [dif_pos hi, if_neg (show j.val ≠ i.val - 1 by omega),
            if_neg (show i.val - 1 + 1 ≠ j.val by omega)]
          ring
        · simp [hi]

end NLAlib
