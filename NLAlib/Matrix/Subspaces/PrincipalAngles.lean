import NLAlib.Matrix.Subspaces.PrincipalAngleBridges
/-!
# Principal (canonical) angles between subspaces

For `Q : n × k` with orthonormal columns (the reference subspace `range Q`) and a block
`X : n × k'`, the largest principal angle `θ_max` between `range Q` and `range X` enters NLAlib
through its sine and tangent, defined as spectral norms so that the projection API applies:

* `NLAlib.sinThetaMax Q X = ‖(I − QQᵀ) X‖₂ = ‖residual Q X‖₂` (meaningful for orthonormal `X`);
* `NLAlib.tanThetaMax Q X = ‖(I − QQᵀ) X (QᵀX)⁻¹‖₂` (square `QᵀX`; meaningful when `QᵀX` is
  invertible, junk value `0` otherwise because Mathlib's inverse of a singular matrix is `0`);
  this form needs no orthonormality of `X`, and depends only on `range X`
  (`tanThetaMax_mul_right`, `tanThetaMax_eq_of_range_eq`);
* `NLAlib.principalAngles Q Q' i = arccos σ_i(QᵀQ')` (zero-indexed, nondecreasing in `i`).

Proved: basis independence in both arguments (`sinThetaMax_congr_left/right`,
`tanThetaMax_congr_left`, `tanThetaMax_eq_of_range_eq`), the complement forms
`sin θ_max = ‖Q⊥ᵀ X‖₂` and `tan θ_max = ‖Q⊥ᵀ X (QᵀX)⁻¹‖₂`, `0 ≤ sin θ_max ≤ 1`, and the
Frobenius identity `‖sin Θ‖_F² = k' − ‖QᵀQ'‖_F²`. Proved also: the singular-value
characterisation, symmetry, the projector-difference form, and the `sin`–`tan` relation.

Deviation from the atlas notes: basis independence in this layer-0 file uses
`mul_transpose_eq_of_range_eq` (Projections) instead of `transpose_mul_mul_eq_of_range_le`
(Krylov/Block, layer 1, not importable here). The single-vector `tanSqAngle` of
`Krylov/Ritz.lean` is the `k = 1` case of `tanThetaMax` squared (bridge in
`Krylov/PowerMethod.lean`).

Source: Stewart–Sun (1990) [`ss90`], §I.5 (Def I.5.3, Thm I.5.5); Golub–Van Loan (2013)
[`gvl13`], §2.5.3 (Thm 2.5.1), §6.4.3; Bhatia (1997) [`bhatia97`], §VII.1; Saad (2011)
[`saad11`], §5.2 (the `tan` form).
Atlas: `principal-angles-def`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {n k k' : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  [Fintype k'] [DecidableEq k']

/-! ### Definitions -/

/-- The sine of the largest principal angle between `range Q` and `range X`:
`sin θ_max = ‖(I − QQᵀ) X‖₂`, for `Q` and `X` with orthonormal columns. With `X` orthonormal
and `k' ≤ k` columns this is `√(1 − σ_min(QᵀX)²)` (`sq_sinThetaMax_eq_one_sub_sq_sigmaMin`).
Source: Golub–Van Loan (2013) [`gvl13`], Thm 2.5.1; Stewart–Sun (1990) [`ss90`], Thm I.5.5.
atlas: principal-angles-def (partial) -/
def sinThetaMax (Q : Matrix n k ℝ) (X : Matrix n k' ℝ) : ℝ := specNorm (residual Q X)

/-- The tangent of the largest principal angle between `range Q` (`Q` orthonormal) and
`range X` (`X` any block with the same number of columns and `QᵀX` invertible):
`tan θ_max = ‖(I − QQᵀ) X (QᵀX)⁻¹‖₂`; with an orthonormal complement `Q⊥` this is
`‖Q⊥ᵀ X (QᵀX)⁻¹‖₂` (`tanThetaMax_eq_specNorm_transpose_mul_mul`). Junk value `0` when `QᵀX` is
singular (the angle is `π/2`). Source: Saad (2011) [`saad11`], §5.2 (proof of Thm 5.2);
Golub–Van Loan (2013) [`gvl13`], §8.2.4. Alternative: a definition via `tan ∘ principalAngles`
would need `Fin` indices and the SVD; this one is index-free and basis-independent in `X`.
atlas: principal-angles-def (partial) -/
def tanThetaMax (Q : Matrix n k ℝ) (X : Matrix n k ℝ) : ℝ :=
  specNorm (residual Q X * (Qᵀ * X)⁻¹)

omit [Fintype k] [DecidableEq k] [Fintype k'] [DecidableEq k'] in
/-- The principal angles `θ_i = arccos σ_i(QᵀQ')` between `range Q` and `range Q'` (both with
orthonormal columns), zero-indexed and nondecreasing in `i` (the singular values are
nonincreasing); there are `min k k'` of them, and `θ_i = π/2` (`σ_i = 0`) past that index.
Source: Golub–Van Loan (2013) [`gvl13`], §6.4.3; Stewart–Sun (1990) [`ss90`], Def I.5.3.
atlas: principal-angles-def (partial) -/
def principalAngles {r r' : ℕ} (Q : Matrix n (Fin r) ℝ) (Q' : Matrix n (Fin r') ℝ) (i : ℕ) :
    ℝ :=
  Real.arccos (singularValues (Qᵀ * Q') i)

omit [Fintype k'] [DecidableEq k'] [DecidableEq n] [DecidableEq k] in
/-- The finite-index angle representation is exactly the standard natural
index principal angle after normalizing the frame's columns to `Fin`.
This is equality of the actual arccos singular values. Stewart--Sun,
Definition I.5.3; supports `principal-angles-def`. -/
theorem principalAnglesFintype_eq_principalAngles (Q Q' : Matrix n k ℝ)
    (i : Fin (Fintype.card k)) :
    principalAnglesFintype Q Q' i =
      principalAngles (Q.submatrix id (Fintype.equivFin k).symm)
        (Q'.submatrix id (Fintype.equivFin k).symm) i := by
  unfold principalAnglesFintype principalAngles
  apply congrArg Real.arccos
  apply congrArg (fun C : Matrix (Fin (Fintype.card k)) (Fin (Fintype.card k)) ℝ =>
    singularValues C i)
  rw [Matrix.transpose_submatrix, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
  rfl

/-! ### Elementary properties -/

omit [DecidableEq k] in
/-- `sin θ_max ≥ 0`. Atlas `principal-angles-def` (helper). -/
theorem sinThetaMax_nonneg (Q : Matrix n k ℝ) (X : Matrix n k' ℝ) : 0 ≤ sinThetaMax Q X :=
  specNorm_nonneg _

/-- `tan θ_max ≥ 0`. Atlas `principal-angles-def` (helper). -/
theorem tanThetaMax_nonneg (Q : Matrix n k ℝ) (X : Matrix n k ℝ) : 0 ≤ tanThetaMax Q X :=
  specNorm_nonneg _

/-- `sin θ_max ≤ 1` for `Q`, `Q'` with orthonormal columns. Source: Golub–Van Loan (2013)
[`gvl13`], §2.5.3. Atlas `principal-angles-def` (helper). -/
theorem sinThetaMax_le_one {Q : Matrix n k ℝ} {Q' : Matrix n k' ℝ} (hQ : HasOrthonormalCols Q)
    (hQ' : HasOrthonormalCols Q') : sinThetaMax Q Q' ≤ 1 :=
  (specNorm_sub_mul_transpose_mul_le hQ Q').trans (specNorm_le_one_of_orthonormal hQ')

omit [Fintype k'] [DecidableEq k'] in
/-- The residual depends only on the range of the orthonormal frame: if `range Q = range P`
then `(I − QQᵀ) X = (I − PPᵀ) X`. Helper for `principal-angles-def` (belongs in
`NLAlib.Matrix.Subspaces.Projections`). -/
theorem residual_eq_of_range_eq {k₂ : Type*} [Fintype k₂] [DecidableEq k₂] {Q : Matrix n k ℝ}
    {P : Matrix n k₂ ℝ} (hQ : HasOrthonormalCols Q) (hP : HasOrthonormalCols P)
    (h : LinearMap.range Q.mulVecLin = LinearMap.range P.mulVecLin) (X : Matrix n k' ℝ) :
    residual Q X = residual P X := by
  rw [residual_eq_one_sub_mul, residual_eq_one_sub_mul, mul_transpose_eq_of_range_eq hQ hP h]

/-- Right multiplication by a square orthogonal matrix preserves the spectral norm:
`‖Y W‖₂ = ‖Y‖₂` for `WᵀW = I`. Helper for `principal-angles-def` (belongs in
`NLAlib.Matrix.Norms.Core`). -/
theorem specNorm_mul_of_transpose_mul_self_eq_one {W : Matrix k k ℝ} (hW : Wᵀ * W = 1)
    (Y : Matrix k' k ℝ) : specNorm (Y * W) = specNorm Y := by
  have hW' : W * Wᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl k)).1 hW
  calc specNorm (Y * W) = specNorm (Y * W)ᵀ := (specNorm_transpose _).symm
    _ = specNorm (Wᵀ * Yᵀ) := by rw [Matrix.transpose_mul]
    _ = specNorm Yᵀ := specNorm_transpose_mul_of_eq_mul hW (by
          rw [← Matrix.mul_assoc, hW', Matrix.one_mul])
    _ = specNorm Y := specNorm_transpose _

/-! ### Basis independence -/

/-- `sin θ_max` depends only on `range Q`. Source: Stewart–Sun (1990) [`ss90`], §I.5.
atlas: principal-angles-def (partial) -/
theorem sinThetaMax_congr_left {k₂ : Type*} [Fintype k₂] [DecidableEq k₂] {Q : Matrix n k ℝ}
    {P : Matrix n k₂ ℝ} (hQ : HasOrthonormalCols Q) (hP : HasOrthonormalCols P)
    (h : LinearMap.range Q.mulVecLin = LinearMap.range P.mulVecLin) (X : Matrix n k' ℝ) :
    sinThetaMax Q X = sinThetaMax P X := by
  rw [sinThetaMax, sinThetaMax, residual_eq_of_range_eq hQ hP h]

omit [DecidableEq k] in
/-- Monotonicity behind `sinThetaMax_congr_right`: if `Y`, `Z` have orthonormal columns and
`range Z ⊆ range Y`, then `‖(I − QQᵀ)Z‖₂ ≤ ‖(I − QQᵀ)Y‖₂`, since `Z = Y (YᵀZ)` with
`‖YᵀZ‖₂ ≤ 1`. Helper for `principal-angles-def`. -/
theorem sinThetaMax_le_of_range_le {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (Q : Matrix n k ℝ) {Y : Matrix n a ℝ} {Z : Matrix n b ℝ}
    (hY : HasOrthonormalCols Y) (hZ : HasOrthonormalCols Z)
    (hle : LinearMap.range Z.mulVecLin ≤ LinearMap.range Y.mulVecLin) :
    sinThetaMax Q Z ≤ sinThetaMax Q Y := by
  have hZY : Y * (Yᵀ * Z) = Z := mul_transpose_mul_eq_of_range_le hY hle
  have hU : (Yᵀ * Z)ᵀ * (Yᵀ * Z) = 1 := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Y, Matrix.mul_assoc Y, hZY]
    exact hZ
  calc sinThetaMax Q Z = specNorm (residual Q Y * (Yᵀ * Z)) := by
        rw [sinThetaMax, residual_mul, hZY]
    _ ≤ specNorm (residual Q Y) * specNorm (Yᵀ * Z) := specNorm_mul_le _ _
    _ ≤ specNorm (residual Q Y) * 1 :=
        mul_le_mul_of_nonneg_left (specNorm_le_one_of_orthonormal hU) (specNorm_nonneg _)
    _ = sinThetaMax Q Y := mul_one _

omit [DecidableEq k] in
/-- `sin θ_max` depends only on `range Q'` among orthonormal frames: if `Q'`, `Q''` have
orthonormal columns and the same range then `‖(I − QQᵀ)Q'‖₂ = ‖(I − QQᵀ)Q''‖₂`. Proof:
`Q'' = Q' (Q'ᵀQ'')` with `‖Q'ᵀQ''‖₂ ≤ 1`, and symmetrically. Source: Stewart–Sun (1990)
[`ss90`], §I.5.
atlas: principal-angles-def (partial) -/
theorem sinThetaMax_congr_right {k₂ : Type*} [Fintype k₂] [DecidableEq k₂] (Q : Matrix n k ℝ)
    {Q' : Matrix n k' ℝ} {Q'' : Matrix n k₂ ℝ} (hQ' : HasOrthonormalCols Q')
    (hQ'' : HasOrthonormalCols Q'')
    (h : LinearMap.range Q'.mulVecLin = LinearMap.range Q''.mulVecLin) :
    sinThetaMax Q Q' = sinThetaMax Q Q'' :=
  le_antisymm (sinThetaMax_le_of_range_le Q hQ'' hQ' h.le)
    (sinThetaMax_le_of_range_le Q hQ' hQ'' h.ge)

/-- `tan θ_max` is invariant under a change of basis of `range X`: `tan θ_max(Q, X R) =
tan θ_max(Q, X)` for invertible `R`, since `(I − QQᵀ) X R (QᵀXR)⁻¹ = (I − QQᵀ) X (QᵀX)⁻¹`. In
particular `X` need not be orthonormalised. Source: Saad (2011) [`saad11`], §5.2.
atlas: principal-angles-def (partial) -/
theorem tanThetaMax_mul_right (Q : Matrix n k ℝ) (X : Matrix n k ℝ) {R : Matrix k k ℝ}
    (hR : IsUnit R) : tanThetaMax Q (X * R) = tanThetaMax Q X := by
  have hR' : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).1 hR)
  rw [tanThetaMax, tanThetaMax, ← residual_mul, ← Matrix.mul_assoc, Matrix.mul_inv_rev,
    Matrix.mul_assoc, ← Matrix.mul_assoc R, hR', Matrix.one_mul]

omit [Fintype n] [DecidableEq n] in
/-- If `range Y ⊆ range X` then `Y = X R` for some `R`. Helper for `principal-angles-def`
(belongs in `NLAlib.Matrix.Subspaces.Projections`). -/
theorem exists_eq_mul_of_range_le {a b : Type*} [Fintype a] [Fintype b] {X : Matrix n a ℝ}
    {Y : Matrix n b ℝ} (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range X.mulVecLin) :
    ∃ R : Matrix a b ℝ, Y = X * R := by
  have hc : ∀ j, ∃ z : a → ℝ, X *ᵥ z = Y.col j := fun j =>
    h (Matrix.range_mulVecLin Y ▸ Submodule.subset_span ⟨j, rfl⟩)
  choose z hz using hc
  refine ⟨Matrix.of fun i j => z j i, ?_⟩
  ext i j
  have hij := congrFun (hz j) i
  simp only [Matrix.mulVec, dotProduct, Matrix.col_apply] at hij
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact hij.symm

/-- `tan θ_max` depends only on `range X`: if `range X = range Y` and `QᵀX` is invertible,
then `tan θ_max(Q, X) = tan θ_max(Q, Y)` (and `QᵀY` is invertible too). Source: Saad (2011)
[`saad11`], §5.2.
atlas: principal-angles-def (partial) -/
theorem tanThetaMax_eq_of_range_eq (Q : Matrix n k ℝ) {X Y : Matrix n k ℝ}
    (h : LinearMap.range X.mulVecLin = LinearMap.range Y.mulVecLin) (hX : IsUnit (Qᵀ * X)) :
    tanThetaMax Q X = tanThetaMax Q Y := by
  obtain ⟨R, hR⟩ := exists_eq_mul_of_range_le h.ge
  obtain ⟨R', hR'⟩ := exists_eq_mul_of_range_le h.le
  -- `Qᵀ X = Qᵀ Y R'`, so `det (Qᵀ Y) ≠ 0`; then `Qᵀ Y = Qᵀ X R`, so `det R ≠ 0`
  have hdX := (Matrix.isUnit_iff_isUnit_det _).1 hX
  have hdY : IsUnit (Qᵀ * Y).det := by
    rw [hR', ← Matrix.mul_assoc, Matrix.det_mul] at hdX
    exact isUnit_of_mul_isUnit_left hdX
  have hdR : IsUnit R.det := by
    have := hdY
    rw [hR, ← Matrix.mul_assoc, Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_right this
  rw [hR, tanThetaMax_mul_right Q X ((Matrix.isUnit_iff_isUnit_det R).2 hdR)]

/-- `tan θ_max` depends only on `range Q` among orthonormal frames with the same index type:
if `range Q = range P` then `tan θ_max(Q, X) = tan θ_max(P, X)`. Proof: `P = Q W` with `W = QᵀP`
orthogonal, so the inverse picks up a right factor `W`. Source: Saad (2011) [`saad11`], §5.2.
atlas: principal-angles-def (partial) -/
theorem tanThetaMax_congr_left {Q P : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (hP : HasOrthonormalCols P) (h : LinearMap.range Q.mulVecLin = LinearMap.range P.mulVecLin)
    (X : Matrix n k ℝ) : tanThetaMax Q X = tanThetaMax P X := by
  have hPQ : Q * (Qᵀ * P) = P := mul_transpose_mul_eq_of_range_le hQ h.ge
  set W := Qᵀ * P with hWdef
  have hW : Wᵀ * W = 1 := by
    rw [hWdef, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← hWdef, hPQ]
    exact hP
  have hW' : W * Wᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl k)).1 hW
  have hPt : Pᵀ * X = Wᵀ * (Qᵀ * X) := by
    rw [← hPQ, Matrix.transpose_mul, Matrix.mul_assoc]
  have hWinv : Wᵀ⁻¹ = W := Matrix.inv_eq_left_inv hW'
  rw [tanThetaMax, tanThetaMax, hPt, Matrix.mul_inv_rev, hWinv, ← residual_eq_of_range_eq hQ hP h,
    ← Matrix.mul_assoc, specNorm_mul_of_transpose_mul_self_eq_one hW]

/-! ### Complement forms -/

omit [DecidableEq k] in
/-- With an orthonormal complement `Q⊥` (`Q⊥ᵀQ⊥ = I`, `QQᵀ + Q⊥Q⊥ᵀ = I`):
`sin θ_max = ‖Q⊥ᵀ X‖₂`. Source: Golub–Van Loan (2013) [`gvl13`], Thm 2.5.1; Stewart–Sun (1990)
[`ss90`], Thm I.5.5.
atlas: principal-angles-def (partial) -/
theorem sinThetaMax_eq_specNorm_transpose_mul {r : Type*} [Fintype r] [DecidableEq r]
    (Q : Matrix n k ℝ) {Qp : Matrix n r ℝ} (hQp : HasOrthonormalCols Qp)
    (hc : Q * Qᵀ + Qp * Qpᵀ = 1) (X : Matrix n k' ℝ) :
    sinThetaMax Q X = specNorm (Qpᵀ * X) := by
  have hres : residual Q X = Qp * (Qpᵀ * X) := by
    rw [residual_eq_one_sub_mul, ← hc, add_sub_cancel_left, Matrix.mul_assoc]
  have hQp' : Qpᵀ * Qp = 1 := hQp
  rw [sinThetaMax, hres]
  refine (specNorm_transpose_mul_of_eq_mul hQp' ?_).symm.trans ?_
  · rw [← Matrix.mul_assoc Qpᵀ, hQp', Matrix.one_mul]
  · rw [← Matrix.mul_assoc Qpᵀ, hQp', Matrix.one_mul]

/-- With an orthonormal complement `Q⊥`: `tan θ_max = ‖Q⊥ᵀ X (QᵀX)⁻¹‖₂`, the form of Saad and
Golub–Van Loan. Source: Saad (2011) [`saad11`], §5.2; Golub–Van Loan (2013) [`gvl13`], §8.2.4.
atlas: principal-angles-def (partial) -/
theorem tanThetaMax_eq_specNorm_transpose_mul_mul {r : Type*} [Fintype r] [DecidableEq r]
    (Q : Matrix n k ℝ) {Qp : Matrix n r ℝ} (hQp : HasOrthonormalCols Qp)
    (hc : Q * Qᵀ + Qp * Qpᵀ = 1) (X : Matrix n k ℝ) :
    tanThetaMax Q X = specNorm (Qpᵀ * X * (Qᵀ * X)⁻¹) := by
  have hres : residual Q X = Qp * (Qpᵀ * X) := by
    rw [residual_eq_one_sub_mul, ← hc, add_sub_cancel_left, Matrix.mul_assoc]
  have hQp' : Qpᵀ * Qp = 1 := hQp
  rw [tanThetaMax, hres, Matrix.mul_assoc Qp]
  refine (specNorm_transpose_mul_of_eq_mul hQp' ?_).symm.trans ?_
  · rw [← Matrix.mul_assoc Qpᵀ, hQp', Matrix.one_mul]
  · rw [← Matrix.mul_assoc Qpᵀ, hQp', Matrix.one_mul, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- Frobenius form: `‖sin Θ‖_F² = ‖(I − QQᵀ) Q'‖_F² = k' − ‖QᵀQ'‖_F²` for `Q'` with `k'`
orthonormal columns. Source: Stewart–Sun (1990) [`ss90`], §I.5; Golub–Van Loan (2013)
[`gvl13`], §2.5.3.
atlas: principal-angles-def (partial) -/
theorem frobSq_residual_eq_card_sub {Q : Matrix n k ℝ} {Q' : Matrix n k' ℝ}
    (hQ : HasOrthonormalCols Q) (hQ' : HasOrthonormalCols Q') :
    frobSq (residual Q Q') = Fintype.card k' - frobSq (Qᵀ * Q') := by
  have hQ'' : Q'ᵀ * Q' = 1 := hQ'
  rw [frobSq_residual_eq_sub hQ, frobSq, frobInner_eq_trace, hQ'', Matrix.trace_one]

/-! ### Singular values, symmetry, projectors, `sin`–`tan` -/

/--
**Singular-value characterisation.** For `Q`, `Q'` with orthonormal columns and `k'` nonempty,
`sin² θ_max = ‖(I − QQᵀ)Q'‖₂² = 1 − σ_min(QᵀQ')²` (`sigmaMin` is the infimum of `‖QᵀQ' x‖` over
unit `x`, the smallest of the `k'` singular values when `k' ≤ k`, and `0` when `k' > k`).
Source: Golub–Van Loan (2013) [`gvl13`], Thm 2.5.1; Stewart–Sun (1990) [`ss90`], Thm I.5.5.
Proof sketch: for unit `x`, `‖(I − QQᵀ)Q'x‖² = ‖Q'x‖² − ‖QᵀQ'x‖² = 1 − ‖QᵀQ'x‖²`
(`mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols`, Pythagoras); take the supremum over
the unit sphere (`specNorm` as `sup ‖Mx‖`, e.g. via `specNorm_le_iff_abs_dotProduct_mulVec_le`
on `Mᵀ M`) and compare with `sigmaMin` (an infimum over the same sphere). `Nonempty k'` is
needed: for empty `k'` both norms are `0`.
atlas: principal-angles-def (partial) -/
theorem sq_sinThetaMax_eq_one_sub_sq_sigmaMin [Nonempty k'] {Q : Matrix n k ℝ}
    {Q' : Matrix n k' ℝ} (hQ : HasOrthonormalCols Q) (hQ' : HasOrthonormalCols Q') :
    sinThetaMax Q Q' ^ 2 = 1 - sigmaMin (Qᵀ * Q') ^ 2 := by
  exact specNorm_residual_sq_eq_one_sub_sigmaMin_sq hQ hQ'

/--
**Principal angles from the SVD.** For `Q : n × r`, `Q' : n × r'` with orthonormal columns and
`0 < r' ≤ r`: `sin θ_max = √(1 − σ_{r'−1}(QᵀQ')²)`, `σ` the zero-indexed singular values.
Source: Golub–Van Loan (2013) [`gvl13`], §6.4.3 and Thm 2.5.1; Stewart–Sun (1990) [`ss90`],
Def I.5.3. Proof sketch: `sq_sinThetaMax_eq_one_sub_sq_sigmaMin` and
`σ_min(M) = σ_{r'−1}(M)` for `M : r × r'` with `r' ≤ r` (Courant–Fischer for `MᵀM`, the bridge
`singularValues` = `√` eigenvalues of `MᵀM`, `NLAlib.Matrix.Spectral.SVD`).
atlas: principal-angles-def (partial) -/
theorem sinThetaMax_eq_sqrt_one_sub_sq_singularValues {r r' : ℕ} {Q : Matrix n (Fin r) ℝ}
    {Q' : Matrix n (Fin r') ℝ} (hQ : HasOrthonormalCols Q) (hQ' : HasOrthonormalCols Q')
    (hr' : 0 < r') (hrr : r' ≤ r) :
    sinThetaMax Q Q' = √(1 - singularValues (Qᵀ * Q') (r' - 1) ^ 2) := by
  have _ := hrr
  let : Nonempty (Fin r') := ⟨⟨0, hr'⟩⟩
  have h := sq_sinThetaMax_eq_one_sub_sq_sigmaMin hQ hQ'
  rw [sigmaMin_eq_singularValues_last _ hr'] at h
  rw [← h, Real.sqrt_sq (sinThetaMax_nonneg Q Q')]

/-- `sin θ_max` is the sine of the largest principal angle: `‖(I − QQᵀ)Q'‖₂ = sin θ_{r'−1}` for
`0 < r' ≤ r`. Source: Golub–Van Loan (2013) [`gvl13`], §6.4.3; Stewart–Sun (1990) [`ss90`],
Def I.5.3 and Thm I.5.5.
atlas: principal-angles-def (partial) -/
theorem sinThetaMax_eq_sin_principalAngles {r r' : ℕ} {Q : Matrix n (Fin r) ℝ}
    {Q' : Matrix n (Fin r') ℝ} (hQ : HasOrthonormalCols Q) (hQ' : HasOrthonormalCols Q')
    (hr' : 0 < r') (hrr : r' ≤ r) :
    sinThetaMax Q Q' = Real.sin (principalAngles Q Q' (r' - 1)) := by
  rw [principalAngles, Real.sin_arccos,
    sinThetaMax_eq_sqrt_one_sub_sq_singularValues hQ hQ' hr' hrr]

/--
**Symmetry for equal dimensions.** For `Q`, `Q'` with orthonormal columns indexed by the same
`k`: `θ_max(range Q, range Q') = θ_max(range Q', range Q)`, i.e.
`‖(I − QQᵀ)Q'‖₂ = ‖(I − Q'Q'ᵀ)Q‖₂`. Source: Stewart–Sun (1990) [`ss90`], Thm I.5.5;
Golub–Van Loan (2013) [`gvl13`], Thm 2.5.1. Proof sketch: by
`sq_sinThetaMax_eq_one_sub_sq_sigmaMin` both sides are `1 − σ_min²` of `QᵀQ'` and of
`Q'ᵀQ = (QᵀQ')ᵀ`; a square matrix and its transpose have the same smallest singular value
(`MᵀM` and `MMᵀ` have the same eigenvalues). False for unequal dimensions (a line inside a
plane has `θ = 0` one way and `π/2` the other).
atlas: principal-angles-def (partial) -/
theorem sinThetaMax_comm {Q Q' : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (hQ' : HasOrthonormalCols Q') : sinThetaMax Q Q' = sinThetaMax Q' Q := by
  exact specNorm_residual_comm hQ hQ'

/--
**Projector form.** For `Q`, `Q'` with orthonormal columns indexed by the same `k`:
`sin θ_max = ‖QQᵀ − Q'Q'ᵀ‖₂`. Source: Golub–Van Loan (2013) [`gvl13`], Thm 2.5.1; Stewart–Sun
(1990) [`ss90`], Thm I.5.5. Proof sketch: `P − P' = P(I − P') − (I − P)P'`, the two terms have
orthogonal ranges and co-ranges, so `‖P − P'‖ = max(‖(I − P)P'‖, ‖P(I − P')‖)`
(`specNorm_add_sq_le_of_mul_transpose_eq_zero` for `≤`, compression for `≥`), and both are
`sin θ_max` by `sinThetaMax_comm`.
atlas: principal-angles-def (partial) -/
theorem sinThetaMax_eq_specNorm_sub {Q Q' : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (hQ' : HasOrthonormalCols Q') : sinThetaMax Q Q' = specNorm (Q * Qᵀ - Q' * Q'ᵀ) := by
  exact (specNorm_sub_frame_projector_eq_residual hQ hQ').symm

/--
**`QᵀQ'` is invertible iff `θ_max < π/2`.** For `Q`, `Q'` with orthonormal columns indexed by
the same `k`: `sin θ_max < 1 ↔ IsUnit (QᵀQ')`. Source: Golub–Van Loan (2013) [`gvl13`],
§2.5.3. Proof sketch: by `sq_sinThetaMax_eq_one_sub_sq_sigmaMin` (`k` nonempty; the empty case
is trivial), `sin θ_max < 1 ↔ σ_min(QᵀQ') > 0 ↔` `QᵀQ'` injective `↔` invertible (square).
atlas: principal-angles-def (partial) -/
theorem sinThetaMax_lt_one_iff_isUnit {Q Q' : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (hQ' : HasOrthonormalCols Q') : sinThetaMax Q Q' < 1 ↔ IsUnit (Qᵀ * Q') := by
  rcases isEmpty_or_nonempty k with hk | hk
  · have hR : residual Q Q' = 0 := Subsingleton.elim _ _
    have hUnit := isUnit_of_subsingleton (Qᵀ * Q')
    exact ⟨fun _ => hUnit, fun _ => by simp [sinThetaMax, hR, specNorm_zero]⟩
  · have hEq := sq_sinThetaMax_eq_one_sub_sq_sigmaMin hQ hQ'
    have hNonneg := sinThetaMax_nonneg Q Q'
    have hBound := sinThetaMax_le_one hQ hQ'
    have hSigma := sigmaMin_nonneg (Qᵀ * Q')
    rw [← sigmaMin_pos_iff_isUnit_of_nonempty]
    constructor <;> intro h <;> nlinarith

/--
**`tan² = sin²/(1 − sin²)`.** For `Q`, `Q'` with orthonormal columns indexed by the same `k`
and `QᵀQ'` invertible: `tan² θ_max = sin² θ_max/(1 − sin² θ_max)`. Source: Golub–Van Loan
(2013) [`gvl13`], §2.5.3 and §8.2.4; Stewart–Sun (1990) [`ss90`], §I.5. Proof sketch: with
`C = QᵀQ'` and `S = (I − QQᵀ)Q'`, `CᵀC + SᵀS = I`; for `v = Cw`,
`‖S C⁻¹ v‖²/‖v‖² = t/(1 − t)` with `t = ‖Sw‖²/‖w‖²`, which is increasing in `t`; the maximum
of `t` is `sin² θ_max`. (When `QᵀQ'` is singular, `tan` has the junk value `0`.)
atlas: principal-angles-def (partial) -/
theorem sq_tanThetaMax_eq_div {Q Q' : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (hQ' : HasOrthonormalCols Q') (hC : IsUnit (Qᵀ * Q')) :
    tanThetaMax Q Q' ^ 2 = sinThetaMax Q Q' ^ 2 / (1 - sinThetaMax Q Q' ^ 2) := by
  exact specNorm_residual_mul_inv_sq_eq_div_residual_sq hQ hQ' hC

end NLAlib
