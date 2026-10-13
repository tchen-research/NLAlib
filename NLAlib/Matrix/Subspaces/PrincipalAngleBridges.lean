import NLAlib.Matrix.Subspaces.PrincipalAngleToolkit
import NLAlib.Matrix.Spectral.SigmaMinTransport
/-!
# Principal-angle bridges to variational minima and tangent ratios

The largest-sine formula holds also for unequal frame widths (through the
projResidual Gram identity `transpose_residual_mul_residual_eq_one_sub_overlap`). For equal widths the actual largest tangent has the exact
sine ratio. These results connect the first-course principal-angle API to
the native singular spectrum. Source: Stewart--Sun, Section I.5;
Golub--Van Loan, Theorem 2.5.1. Atlas: `principal-angles-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-- **Singular-value characterisation of `sin θ_max`.** With nonempty right frame, its residual
norm squared is one minus the squared variational smallest overlap singular value:
`‖(I − PPᵀ)Q‖₂² = 1 − σ_min(PᵀQ)²`. The widths may differ, and wide overlaps include their
kernel zeros (`σ_min = 0` when `Q` is wider than `P`). `Nonempty p` is needed: for an empty
frame both norms are `0`. Golub–Van Loan 2013, Thm 2.5.1; Stewart--Sun, Theorem I.5.5.
atlas: principal-angles-def (partial) -/
theorem specNorm_residual_sq_eq_one_sub_sigmaMin_sq [Nonempty p]
    {P : Matrix m n ℝ} {Q : Matrix m p ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) :
    specNorm (projResidual P Q) ^ 2 = 1 - sigmaMin (Pᵀ * Q) ^ 2 := by
  let C := Pᵀ * Q
  let en := Fintype.equivFin n
  let ep := Fintype.equivFin p
  let CF := C.reindex en ep
  have hp : 0 < Fintype.card p := Fintype.card_pos
  let last : Fin (Fintype.card p) := ⟨Fintype.card p - 1, by omega⟩
  have hNorm : specNorm CF ≤ 1 := by
    rw [specNorm_reindex]
    have hh := specNorm_mul_le Pᵀ Q
    rw [specNorm_transpose] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_right (specNorm_le_one_of_orthonormal hP)
      (specNorm_nonneg Q)).trans (by simpa using specNorm_le_one_of_orthonormal hQ))
  have hBounds (i : ℕ) : 0 ≤ singularValues CF i ∧ singularValues CF i ≤ 1 :=
    ⟨singularValues_nonneg CF i, (singularValues_le_specNorm CF i).trans hNorm⟩
  have hLast : 0 ≤ 1 - singularValues CF last ^ 2 := by
    have hb := hBounds last
    nlinarith
  have hPi : ‖(fun i : Fin (Fintype.card p) => singularValues CF i ^ 2 - 1)‖ =
      1 - singularValues CF last ^ 2 := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg hLast).2
      intro i
      have hb := hBounds i
      have hl := hBounds last
      rw [Real.norm_eq_abs, abs_of_nonpos (by nlinarith [hb.1, hb.2])]
      have hOrder := singularValues_antitone CF (show i.val ≤ last.val by
        dsimp only [last]
        omega)
      nlinarith
    · have hh := norm_le_pi_norm
        (fun i : Fin (Fintype.card p) => singularValues CF i ^ 2 - 1) last
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)] at hh
      linarith
  have hGramNorm := specNorm_gram_sub_one_eq_norm_singularValues_sq_sub_one CF
  have hGramTransport : CFᵀ * CF - 1 = (Cᵀ * C - 1).reindex ep ep := by
    simp only [CF, Matrix.reindex_apply, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
    change _ = (Cᵀ * C).submatrix ep.symm ep.symm -
      (1 : Matrix p p ℝ).submatrix ep.symm ep.symm
    rw [Matrix.submatrix_one_equiv]
  rw [hGramTransport, specNorm_reindex, specNorm_sub_comm, hPi] at hGramNorm
  have hSigma : sigmaMin C = singularValues CF last := by
    rw [sigmaMin_eq_singularValues_last C hp, ← singularValues_reindex C en ep]
  have hResidual := specNorm_sq_eq_specNorm_transpose_mul_self (projResidual P Q)
  rw [transpose_residual_mul_residual_eq_one_sub_overlap hP hQ] at hResidual
  exact hResidual.trans (hGramNorm.trans (by rw [hSigma]))

/-- At positive width and invertible overlap, the norm of the genuine
tangent matrix is the tangent of the last principal angle. Stewart--Sun,
Theorem I.5.5; supports `principal-angles-def`. -/
theorem specNorm_tangentPrincipalAngles_eq_tan_last {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q)
    (hC : IsUnit (Pᵀ * Q)) (hn : 0 < Fintype.card n) :
    specNorm (tangentPrincipalAngles P Q) =
      Real.tan (principalAnglesFintype P Q ⟨Fintype.card n - 1, by omega⟩) := by
  let last : Fin (Fintype.card n) := ⟨Fintype.card n - 1, by omega⟩
  let e := Fintype.equivFin n
  let C := (Pᵀ * Q).reindex e e
  have hUnit : IsUnit C := hC.map (Matrix.reindexRingEquiv ℝ e).toMonoidHom
  have hRank : C.rank = Fintype.card n := by
    simpa only [Fintype.card_fin] using Matrix.rank_of_isUnit C hUnit
  have hSigma : 0 < singularValues C last := (singularValues_pos_iff C last).mpr (by
    rw [hRank]
    exact last.isLt)
  have hAngleLast : principalAnglesFintype P Q last < Real.pi / 2 :=
    Real.arccos_lt_pi_div_two.mpr hSigma
  have hRangeLast := principalAngles_mem_Icc hP hQ last
  have hTanLast : 0 ≤ Real.tan (principalAnglesFintype P Q last) :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hRangeLast.1 hRangeLast.2
  rw [tangentPrincipalAngles, specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg hTanLast).2
    intro i
    have hRange := principalAngles_mem_Icc hP hQ i
    have hOrder := principalAngles_monotone P Q (show i ≤ last by
      change i.val ≤ Fintype.card n - 1
      omega)
    have hAngle : principalAnglesFintype P Q i < Real.pi / 2 := hOrder.trans_lt hAngleLast
    have hTan : 0 ≤ Real.tan (principalAnglesFintype P Q i) :=
      Real.tan_nonneg_of_nonneg_of_le_pi_div_two hRange.1 hRange.2
    rw [Real.norm_eq_abs, abs_of_nonneg hTan]
    exact Real.strictMonoOn_tan.monotoneOn
      ⟨by linarith [Real.pi_pos, hRange.1], hAngle⟩
      ⟨by linarith [Real.pi_pos, hRangeLast.1], hAngleLast⟩ hOrder
  · have hh := norm_le_pi_norm (fun i => Real.tan (principalAnglesFintype P Q i)) last
    rwa [Real.norm_eq_abs, abs_of_nonneg hTanLast] at hh

/-- For equal-width orthonormal frames with invertible overlap, the actual
residual-times-overlap-inverse norm has squared sine ratio. Empty frames
give zero on both sides. Stewart--Sun, Theorem I.5.5;
supports `principal-angles-def`. -/
theorem specNorm_residual_mul_inv_sq_eq_div_residual_sq {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) (hC : IsUnit (Pᵀ * Q)) :
    specNorm (projResidual P Q * (Pᵀ * Q)⁻¹) ^ 2 =
      specNorm (projResidual P Q) ^ 2 / (1 - specNorm (projResidual P Q) ^ 2) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hR : projResidual P Q = 0 := Subsingleton.elim _ _
    simp [hR, specNorm_zero]
  · have hn : 0 < Fintype.card n := Fintype.card_pos
    let last : Fin (Fintype.card n) := ⟨Fintype.card n - 1, by omega⟩
    have hSin : specNorm (projResidual P Q) = Real.sin (principalAnglesFintype P Q last) :=
      (specNorm_sinePrincipalAngles_eq_residual hP hQ).symm.trans
        (specNorm_sinePrincipalAngles_eq_sin_last hP hQ hn)
    have hTan : specNorm (projResidual P Q * (Pᵀ * Q)⁻¹) =
        Real.tan (principalAnglesFintype P Q last) :=
      (specNorm_tangentPrincipalAngles_eq_residual_mul_inv hP hQ hC).symm.trans
        (specNorm_tangentPrincipalAngles_eq_tan_last hP hQ hC hn)
    rw [hSin, hTan, Real.tan_eq_sin_div_cos, div_pow]
    congr 1
    nlinarith [Real.sin_sq_add_cos_sq (principalAnglesFintype P Q last)]

end NLAlib
