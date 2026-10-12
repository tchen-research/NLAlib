import NLAlib.Matrix.Subspaces.PrincipalAngleDefinitions
/-!
# The largest principal angle

At positive frame width the operator sine norm is the sine of the last
angle, equivalently the square root of one minus the smallest overlap
singular value squared. Stewart–Sun §I.5.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The sines of the ordered principal angles increase. Stewart–Sun §I.5. -/
theorem sin_principalAngles_monotone {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    Monotone (fun i => Real.sin (principalAnglesFintype P Q i)) := by
  intro i j hij
  change Real.sin (principalAnglesFintype P Q i) ≤ Real.sin (principalAnglesFintype P Q j)
  rw [sin_principalAngles, sin_principalAngles]
  apply Real.sqrt_le_sqrt
  have horder := singularValues_antitone
    ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n)) hij
  have hi := overlap_singularValues_mem_Icc hP hQ i
  have hj := overlap_singularValues_mem_Icc hP hQ j
  nlinarith [hi.1, hj.1]

/-- The actual sine matrix norm is the sine of its last ordered angle.
Stewart–Sun §I.5; the explicit positive width prevents an undefined last index.
atlas: principal-angles-def (partial) -/
theorem specNorm_sinePrincipalAngles_eq_sin_last {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) (hn : 0 < Fintype.card n) :
    specNorm (sinePrincipalAngles P Q) =
      Real.sin (principalAnglesFintype P Q ⟨Fintype.card n-1, by omega⟩) := by
  let last : Fin (Fintype.card n) := ⟨Fintype.card n-1, by omega⟩
  have hl : 0 ≤ Real.sin (principalAnglesFintype P Q last) := by
    rw [sin_principalAngles]
    exact Real.sqrt_nonneg _
  rw [sinePrincipalAngles, specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg hl).2
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Real.sin (principalAnglesFintype P Q i) by
      rw [sin_principalAngles]; exact Real.sqrt_nonneg _)]
    apply sin_principalAngles_monotone hP hQ
    change i.val ≤ Fintype.card n-1
    omega
  · have hh := norm_le_pi_norm (fun i => Real.sin (principalAnglesFintype P Q i)) last
    rw [Real.norm_eq_abs, abs_of_nonneg hl] at hh
    exact hh

/-- The sine-angle operator norm is the square root of one minus the last
overlap singular value square. Stewart–Sun §I.5, with positive frame width.
atlas: principal-angles-def (partial) -/
theorem specNorm_sinePrincipalAngles_eq_sqrt_one_sub_last_sq {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) (hn : 0 < Fintype.card n) :
    specNorm (sinePrincipalAngles P Q) = Real.sqrt (1-singularValues
      ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n)) (Fintype.card n-1)^2) := by
  rw [specNorm_sinePrincipalAngles_eq_sin_last hP hQ hn, sin_principalAngles]

end NLAlib
