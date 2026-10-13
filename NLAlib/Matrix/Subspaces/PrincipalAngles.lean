import NLAlib.Matrix.Subspaces.PrincipalAngleBridges
/-!
# Principal (canonical) angles between subspaces

For `Q : n × k` with orthonormal columns (the reference subspace `range Q`) and a block
`X : n × k'`, the directed gap from `range X` to `range Q` and the equal-width principal-angle tangent
are defined through spectral norms so that the projection API applies:

* `NLAlib.directedSubspaceGap Q X = ‖(I − QQᵀ) X‖₂ = ‖projResidual Q X‖₂` (meaningful for orthonormal `X`);
* `NLAlib.overlapTangentNorm Q X = ‖(I − QQᵀ) X (QᵀX)⁻¹‖₂` (square `QᵀX`; meaningful when `QᵀX` is
  invertible, junk value `0` otherwise because Mathlib's inverse of a singular matrix is `0`);
  this form needs no orthonormality of `X`, and depends only on `range X`
  (`overlapTangentNorm_mul_right`, `overlapTangentNorm_eq_of_range_eq`);
* the equal-width principal angles are `principalAnglesFintype` (`PrincipalAngleDefinitions`);
  `directedSubspaceGap_eq_sin_principalAngles` identifies `sin θ_max` with the sine of the last one.

Proved: basis independence in both arguments (`directedSubspaceGap_congr_left/right`,
`overlapTangentNorm_congr_left`, `overlapTangentNorm_eq_of_range_eq`), the complement forms
`sin θ_max = ‖Q⊥ᵀ X‖₂` and `tan θ_max = ‖Q⊥ᵀ X (QᵀX)⁻¹‖₂`, `0 ≤ directedSubspaceGap Q X ≤ 1`, and the
Frobenius identity `‖sin Θ‖_F² = k' − ‖QᵀQ'‖_F²`. Proved also: the singular-value
characterisation (`specNorm_residual_sq_eq_one_sub_singularValues_last_sq`), symmetry
(`specNorm_residual_comm`), the projector-difference form
(`specNorm_sub_frame_projector_eq_residual`), and the `sin`–`tan` relation; these are stated
for `residual` and apply to `directedSubspaceGap` by unfolding.

Deviation from the atlas notes: basis independence in this layer-0 file uses
`mul_conjTranspose_eq_of_range_eq` (Projections) instead of `transpose_mul_mul_eq_of_range_le`
(Krylov/Block, layer 1, not importable here). The single-vector `overlapTangentSq` of
`Krylov/Ritz.lean` is the `k = 1` case of `overlapTangentNorm` squared (bridge in
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

/-- The directed gap from the source subspace `range X` to the target subspace
`range Q`, represented by orthonormal frames: `‖(I − QQᴴ) X‖₂`. For arbitrary
blocks this definition is the residual norm. With orthonormal source and target
it lies in `[0, 1]` and depends only on their ranges. It is generally asymmetric
for unequal widths: a source contained in its target has gap zero, while the
reverse gap can be one. For equal widths it is the sine of the largest
principal angle (`directedSubspaceGap_eq_sin_principalAngles`).
Source: Stewart–Sun (1990), §I.5; Golub–Van Loan (2013), §2.5.3.
atlas: principal-angles-def (partial) -/
def directedSubspaceGap {𝕜 : Type*} [RCLike 𝕜]
    (Q : Matrix n k 𝕜) (X : Matrix n k' 𝕜) : ℝ := specNorm (projResidual Q X)

/-- The tangent of the largest principal angle between `range Q` (`Q` orthonormal) and
`range X` (`X` any block with the same number of columns and `QᵀX` invertible):
`tan θ_max = ‖(I − QQᵀ) X (QᵀX)⁻¹‖₂`; with an orthonormal complement `Q⊥` this is
`‖Q⊥ᵀ X (QᵀX)⁻¹‖₂` (`overlapTangentNorm_eq_specNorm_transpose_mul_mul`). Junk value `0` when `QᵀX` is
singular (the angle is `π/2`). Source: Saad (2011) [`saad11`], §5.2 (proof of Thm 5.2);
Golub–Van Loan (2013) [`gvl13`], §8.2.4. Alternative: a definition via
`tan ∘ principalAnglesFintype` would need the SVD; this one is index-free and basis-independent in `X`.
atlas: principal-angles-def (partial) -/
def overlapTangentNorm (Q : Matrix n k ℝ) (X : Matrix n k ℝ) : ℝ :=
  specNorm (projResidual Q X * (Qᵀ * X)⁻¹)

/-- The finite tangent of the largest principal angle from a block to an
orthonormal reference frame, with an explicit transverse-overlap certificate.
The block may have any basis of its range; an orthogonal block has singular
overlap and cannot satisfy the domain requirement. Source: Saad (2011), §5.2. -/
def tanThetaMax (Q : Matrix n k ℝ) (X : Matrix n k ℝ)
    (_hQ : HasOrthonormalCols Q) (_hC : IsUnit (Qᵀ * X)) : ℝ :=
  overlapTangentNorm Q X

/-- On its explicit geometric domain, the largest-angle tangent is the
residual-times-inverse overlap norm. -/
theorem tanThetaMax_eq_overlapTangentNorm (Q : Matrix n k ℝ) (X : Matrix n k ℝ)
    (hQ : HasOrthonormalCols Q) (hC : IsUnit (Qᵀ * X)) :
    tanThetaMax Q X hQ hC = overlapTangentNorm Q X := rfl

/-- Singular overlap makes the total algebraic inverse-overlap norm zero.
This is a totalization convention, not a finite tangent at a right angle. -/
theorem overlapTangentNorm_eq_zero_of_not_isUnit (Q X : Matrix n k ℝ)
    (hC : ¬ IsUnit (Qᵀ * X)) : overlapTangentNorm Q X = 0 := by
  have hd : ¬ IsUnit (Qᵀ * X).det :=
    (Matrix.isUnit_iff_isUnit_det (Qᵀ * X)).not.mp hC
  rw [overlapTangentNorm, Matrix.nonsing_inv_apply_not_isUnit (Qᵀ * X) hd,
    Matrix.mul_zero, specNorm_zero]

/-! ### Elementary properties -/

omit [DecidableEq k] in
/-- The directed subspace gap is nonnegative. Atlas `principal-angles-def` (helper). -/
theorem directedSubspaceGap_nonneg {𝕜 : Type*} [RCLike 𝕜]
    (Q : Matrix n k 𝕜) (X : Matrix n k' 𝕜) : 0 ≤ directedSubspaceGap Q X :=
  specNorm_nonneg _

/-- `tan θ_max ≥ 0`. Atlas `principal-angles-def` (helper). -/
theorem overlapTangentNorm_nonneg (Q : Matrix n k ℝ) (X : Matrix n k ℝ) : 0 ≤ overlapTangentNorm Q X :=
  specNorm_nonneg _

/-- The directed gap is at most one for `Q`, `Q'` with orthonormal columns. Source: Golub–Van Loan (2013)
[`gvl13`], §2.5.3. Atlas `principal-angles-def` (helper). -/
theorem directedSubspaceGap_le_one {𝕜 : Type*} [RCLike 𝕜]
    {Q : Matrix n k 𝕜} {Q' : Matrix n k' 𝕜} (hQ : HasOrthonormalCols Q)
    (hQ' : HasOrthonormalCols Q') : directedSubspaceGap Q Q' ≤ 1 :=
  (specNorm_sub_mul_conjTranspose_mul_le hQ Q').trans (specNorm_le_one_of_orthonormal hQ')

omit [Fintype k'] [DecidableEq k'] in
/-- The residual depends only on the range of the orthonormal frame: if `range Q = range P`
then `(I − QQᵀ) X = (I − PPᵀ) X`. Helper for `principal-angles-def` (belongs in
`NLAlib.Matrix.Subspaces.Projections`). -/
theorem residual_eq_of_range_eq {k₂ : Type*} [Fintype k₂] [DecidableEq k₂] {Q : Matrix n k ℝ}
    {P : Matrix n k₂ ℝ} (hQ : HasOrthonormalCols Q) (hP : HasOrthonormalCols P)
    (h : LinearMap.range Q.mulVecLin = LinearMap.range P.mulVecLin) (X : Matrix n k' ℝ) :
    projResidual Q X = projResidual P X := by
  rw [residual_eq_one_sub_mul, residual_eq_one_sub_mul, mul_conjTranspose_eq_of_range_eq hQ hP h]

/-! ### Basis independence -/

/-- The directed gap depends only on the target range `range Q`. Source: Stewart–Sun (1990) [`ss90`], §I.5.
atlas: principal-angles-def (partial) -/
theorem directedSubspaceGap_congr_left {k₂ : Type*} [Fintype k₂] [DecidableEq k₂] {Q : Matrix n k ℝ}
    {P : Matrix n k₂ ℝ} (hQ : HasOrthonormalCols Q) (hP : HasOrthonormalCols P)
    (h : LinearMap.range Q.mulVecLin = LinearMap.range P.mulVecLin) (X : Matrix n k' ℝ) :
    directedSubspaceGap Q X = directedSubspaceGap P X := by
  rw [directedSubspaceGap, directedSubspaceGap, residual_eq_of_range_eq hQ hP h]

omit [DecidableEq k] in
/-- Monotonicity behind `directedSubspaceGap_congr_right`: if `Y`, `Z` have orthonormal columns and
`range Z ⊆ range Y`, then `‖(I − QQᵀ)Z‖₂ ≤ ‖(I − QQᵀ)Y‖₂`, since `Z = Y (YᵀZ)` with
`‖YᵀZ‖₂ ≤ 1`. Helper for `principal-angles-def`. -/
theorem directedSubspaceGap_le_of_range_le {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (Q : Matrix n k ℝ) {Y : Matrix n a ℝ} {Z : Matrix n b ℝ}
    (hY : HasOrthonormalCols Y) (hZ : HasOrthonormalCols Z)
    (hle : LinearMap.range Z.mulVecLin ≤ LinearMap.range Y.mulVecLin) :
    directedSubspaceGap Q Z ≤ directedSubspaceGap Q Y := by
  have hZY : Y * (Yᵀ * Z) = Z := mul_conjTranspose_mul_eq_of_range_le hY hle
  have hU : (Yᵀ * Z)ᵀ * (Yᵀ * Z) = 1 := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Y, Matrix.mul_assoc Y, hZY]
    exact hZ
  calc directedSubspaceGap Q Z = specNorm (projResidual Q Y * (Yᵀ * Z)) := by
        rw [directedSubspaceGap, residual_mul, hZY]
    _ ≤ specNorm (projResidual Q Y) * specNorm (Yᵀ * Z) := specNorm_mul_le _ _
    _ ≤ specNorm (projResidual Q Y) * 1 :=
        mul_le_mul_of_nonneg_left (specNorm_le_one_of_orthonormal hU) (specNorm_nonneg _)
    _ = directedSubspaceGap Q Y := mul_one _

omit [DecidableEq k] in
/-- The directed gap depends only on the source range `range Q'` among orthonormal frames: if `Q'`, `Q''` have
orthonormal columns and the same range then `‖(I − QQᵀ)Q'‖₂ = ‖(I − QQᵀ)Q''‖₂`. Proof:
`Q'' = Q' (Q'ᵀQ'')` with `‖Q'ᵀQ''‖₂ ≤ 1`, and symmetrically. Source: Stewart–Sun (1990)
[`ss90`], §I.5.
atlas: principal-angles-def (partial) -/
theorem directedSubspaceGap_congr_right {k₂ : Type*} [Fintype k₂] [DecidableEq k₂] (Q : Matrix n k ℝ)
    {Q' : Matrix n k' ℝ} {Q'' : Matrix n k₂ ℝ} (hQ' : HasOrthonormalCols Q')
    (hQ'' : HasOrthonormalCols Q'')
    (h : LinearMap.range Q'.mulVecLin = LinearMap.range Q''.mulVecLin) :
    directedSubspaceGap Q Q' = directedSubspaceGap Q Q'' :=
  le_antisymm (directedSubspaceGap_le_of_range_le Q hQ'' hQ' h.le)
    (directedSubspaceGap_le_of_range_le Q hQ' hQ'' h.ge)

/-- `tan θ_max` is invariant under a change of basis of `range X`: `tan θ_max(Q, X R) =
tan θ_max(Q, X)` for invertible `R`, since `(I − QQᵀ) X R (QᵀXR)⁻¹ = (I − QQᵀ) X (QᵀX)⁻¹`. In
particular `X` need not be orthonormalised. Source: Saad (2011) [`saad11`], §5.2.
atlas: principal-angles-def (partial) -/
theorem overlapTangentNorm_mul_right (Q : Matrix n k ℝ) (X : Matrix n k ℝ) {R : Matrix k k ℝ}
    (hR : IsUnit R) : overlapTangentNorm Q (X * R) = overlapTangentNorm Q X := by
  have hR' : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).1 hR)
  rw [overlapTangentNorm, overlapTangentNorm, ← residual_mul, ← Matrix.mul_assoc, Matrix.mul_inv_rev,
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
theorem overlapTangentNorm_eq_of_range_eq (Q : Matrix n k ℝ) {X Y : Matrix n k ℝ}
    (h : LinearMap.range X.mulVecLin = LinearMap.range Y.mulVecLin) (hX : IsUnit (Qᵀ * X)) :
    overlapTangentNorm Q X = overlapTangentNorm Q Y := by
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
  rw [hR, overlapTangentNorm_mul_right Q X ((Matrix.isUnit_iff_isUnit_det R).2 hdR)]

/-- `tan θ_max` depends only on `range Q` among orthonormal frames with the same index type:
if `range Q = range P` then `tan θ_max(Q, X) = tan θ_max(P, X)`. Proof: `P = Q W` with `W = QᵀP`
orthogonal, so the inverse picks up a right factor `W`. Source: Saad (2011) [`saad11`], §5.2.
atlas: principal-angles-def (partial) -/
theorem overlapTangentNorm_congr_left {Q P : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (hP : HasOrthonormalCols P) (h : LinearMap.range Q.mulVecLin = LinearMap.range P.mulVecLin)
    (X : Matrix n k ℝ) : overlapTangentNorm Q X = overlapTangentNorm P X := by
  have hPQ : Q * (Qᵀ * P) = P := mul_conjTranspose_mul_eq_of_range_le hQ h.ge
  set W := Qᵀ * P with hWdef
  have hW : Wᵀ * W = 1 := by
    rw [hWdef, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← hWdef, hPQ]
    exact hP
  have hW' : W * Wᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl k)).1 hW
  have hPt : Pᵀ * X = Wᵀ * (Qᵀ * X) := by
    rw [← hPQ, Matrix.transpose_mul, Matrix.mul_assoc]
  have hWinv : Wᵀ⁻¹ = W := Matrix.inv_eq_left_inv hW'
  rw [overlapTangentNorm, overlapTangentNorm, hPt, Matrix.mul_inv_rev, hWinv, ← residual_eq_of_range_eq hQ hP h,
    ← Matrix.mul_assoc]
  have hWt : Wᵀᵀ * Wᵀ = 1 := by rw [Matrix.transpose_transpose]; exact hW'
  conv_rhs => rw [← Matrix.transpose_transpose W]
  exact (specNorm_mul_transpose_right_of_hasOrthonormalCols hWt _).symm

/-- Equal-width orthonormal frames have symmetric directed gaps, equal to the
sine of their largest principal angle. This statement does not extend to
unequal-dimensional subspaces. Source: Stewart–Sun (1990), §I.5. -/
theorem directedSubspaceGap_comm {𝕜 : Type*} [RCLike 𝕜] {Q X : Matrix n k 𝕜}
    (hQ : HasOrthonormalCols Q) (hX : HasOrthonormalCols X) :
    directedSubspaceGap Q X = directedSubspaceGap X Q :=
  specNorm_residual_comm hQ hX

/-- Containment of the source range in the target range makes the directed gap
zero. This permits different frame widths. -/
theorem directedSubspaceGap_eq_zero_of_range_le {𝕜 : Type*} [RCLike 𝕜]
    {Q : Matrix n k 𝕜} (hQ : HasOrthonormalCols Q) (X : Matrix n k' 𝕜)
    (h : LinearMap.range X.mulVecLin ≤ LinearMap.range Q.mulVecLin) :
    directedSubspaceGap Q X = 0 := by
  rw [directedSubspaceGap, projResidual, mul_conjTranspose_mul_eq_of_range_le hQ h,
    sub_self, specNorm_zero]

/-! ### Complement forms -/

omit [DecidableEq k] in
/-- With an orthonormal complement `Q⊥` (`Q⊥ᵀQ⊥ = I`, `QQᵀ + Q⊥Q⊥ᵀ = I`):
`sin θ_max = ‖Q⊥ᵀ X‖₂`. Source: Golub–Van Loan (2013) [`gvl13`], Thm 2.5.1; Stewart–Sun (1990)
[`ss90`], Thm I.5.5.
atlas: principal-angles-def (partial) -/
theorem directedSubspaceGap_eq_specNorm_transpose_mul {r : Type*} [Fintype r] [DecidableEq r]
    (Q : Matrix n k ℝ) {Qp : Matrix n r ℝ} (hQp : HasOrthonormalCols Qp)
    (hc : Q * Qᵀ + Qp * Qpᵀ = 1) (X : Matrix n k' ℝ) :
    directedSubspaceGap Q X = specNorm (Qpᵀ * X) := by
  have hres : projResidual Q X = Qp * (Qpᵀ * X) := by
    rw [residual_eq_one_sub_mul, Matrix.conjTranspose_eq_transpose_of_trivial, ← hc,
      add_sub_cancel_left, Matrix.mul_assoc]
  have hQp' : Qpᵀ * Qp = 1 := hQp
  rw [directedSubspaceGap, hres]
  refine (specNorm_conjTranspose_mul_of_eq_mul hQp' ?_).symm.trans ?_
  · rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.mul_assoc Qpᵀ, hQp', Matrix.one_mul]
  · rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.mul_assoc Qpᵀ, hQp', Matrix.one_mul]

/-- With an orthonormal complement `Q⊥`: `tan θ_max = ‖Q⊥ᵀ X (QᵀX)⁻¹‖₂`, the form of Saad and
Golub–Van Loan. Source: Saad (2011) [`saad11`], §5.2; Golub–Van Loan (2013) [`gvl13`], §8.2.4.
atlas: principal-angles-def (partial) -/
theorem overlapTangentNorm_eq_specNorm_transpose_mul_mul {r : Type*} [Fintype r] [DecidableEq r]
    (Q : Matrix n k ℝ) {Qp : Matrix n r ℝ} (hQp : HasOrthonormalCols Qp)
    (hc : Q * Qᵀ + Qp * Qpᵀ = 1) (X : Matrix n k ℝ) :
    overlapTangentNorm Q X = specNorm (Qpᵀ * X * (Qᵀ * X)⁻¹) := by
  have hres : projResidual Q X = Qp * (Qpᵀ * X) := by
    rw [residual_eq_one_sub_mul, Matrix.conjTranspose_eq_transpose_of_trivial, ← hc,
      add_sub_cancel_left, Matrix.mul_assoc]
  have hQp' : Qpᵀ * Qp = 1 := hQp
  rw [overlapTangentNorm, hres, Matrix.mul_assoc Qp]
  refine (specNorm_conjTranspose_mul_of_eq_mul hQp' ?_).symm.trans ?_
  · rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.mul_assoc Qpᵀ, hQp', Matrix.one_mul]
  · rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.mul_assoc Qpᵀ, hQp', Matrix.one_mul,
      Matrix.mul_assoc]

omit [DecidableEq n] in
/-- Frobenius form: `‖sin Θ‖_F² = ‖(I − QQᵀ) Q'‖_F² = k' − ‖QᵀQ'‖_F²` for `Q'` with `k'`
orthonormal columns. Source: Stewart–Sun (1990) [`ss90`], §I.5; Golub–Van Loan (2013)
[`gvl13`], §2.5.3.
atlas: principal-angles-def (partial) -/
theorem frobSq_residual_eq_card_sub {Q : Matrix n k ℝ} {Q' : Matrix n k' ℝ}
    (hQ : HasOrthonormalCols Q) (hQ' : HasOrthonormalCols Q') :
    frobSq (projResidual Q Q') = Fintype.card k' - frobSq (Qᵀ * Q') := by
  have hQ'' : Q'ᵀ * Q' = 1 := hQ'
  rw [frobSq_residual_eq_sub hQ, Matrix.conjTranspose_eq_transpose_of_trivial, frobSq,
      frobInner_eq_trace, RCLike.re_to_real,
      Matrix.conjTranspose_eq_transpose_of_trivial, hQ'', Matrix.trace_one]

/-! ### Singular values, symmetry, projectors, `sin`–`tan` -/

/--
**Principal angles from the SVD.** For `Q : n × r`, `Q' : n × r'` with orthonormal columns and
`0 < r' ≤ r`: `sin θ_max = √(1 − σ_{r'−1}(QᵀQ')²)`, `σ` the zero-indexed singular values.
Source: Golub–Van Loan (2013) [`gvl13`], §6.4.3 and Thm 2.5.1; Stewart–Sun (1990) [`ss90`],
Def I.5.3. Proof: `specNorm_residual_sq_eq_one_sub_singularValues_last_sq` and
`σ_min(M) = σ_{r'−1}(M)` for `M : r × r'` with `r' ≤ r` (Courant–Fischer for `MᵀM`, the bridge
`singularValues` = `√` eigenvalues of `MᵀM`, `NLAlib.Matrix.Spectral.SVD`).
atlas: principal-angles-def (partial) -/
theorem directedSubspaceGap_eq_sqrt_one_sub_sq_singularValues {r r' : ℕ} {Q : Matrix n (Fin r) ℝ}
    {Q' : Matrix n (Fin r') ℝ} (hQ : HasOrthonormalCols Q) (hQ' : HasOrthonormalCols Q')
    (hr' : 0 < r') (hrr : r' ≤ r) :
    directedSubspaceGap Q Q' = √(1 - singularValues (Qᵀ * Q') (r' - 1) ^ 2) := by
  have _ := hrr
  let : Nonempty (Fin r') := ⟨⟨0, hr'⟩⟩
  have h : directedSubspaceGap Q Q' ^ 2 = 1 - singularValues (Qᵀ * Q') (Fintype.card (Fin r') - 1) ^ 2 :=
    specNorm_residual_sq_eq_one_sub_singularValues_last_sq hQ hQ'
  rw [Fintype.card_fin] at h
  rw [← h, Real.sqrt_sq (directedSubspaceGap_nonneg Q Q')]

omit [Fintype k'] [DecidableEq k'] in
/-- `sin θ_max` is the sine of the largest principal angle: for frames `Q`, `Q'` of the same
positive width, `‖(I − QQᵀ)Q'‖₂ = sin θ_last`, `θ` the ordered principal angles
`principalAnglesFintype Q Q'`. (For unequal widths `0 < r' ≤ r` use
`directedSubspaceGap_eq_sqrt_one_sub_sq_singularValues`.) Source: Golub–Van Loan (2013) [`gvl13`],
§6.4.3; Stewart–Sun (1990) [`ss90`], Def I.5.3 and Thm I.5.5.
atlas: principal-angles-def (partial) -/
theorem directedSubspaceGap_eq_sin_principalAngles {Q Q' : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (hQ' : HasOrthonormalCols Q') (hk : 0 < Fintype.card k) :
    directedSubspaceGap Q Q' =
      Real.sin (principalAnglesFintype Q Q' ⟨Fintype.card k - 1, by omega⟩) := by
  rw [directedSubspaceGap, ← specNorm_sinePrincipalAngles_eq_residual hQ hQ',
    specNorm_sinePrincipalAngles_eq_sin_last hQ hQ' hk]

/--
**`QᵀQ'` is invertible iff `θ_max < π/2`.** For `Q`, `Q'` with orthonormal columns indexed by
the same `k`: `sin θ_max < 1 ↔ IsUnit (QᵀQ')`. Source: Golub–Van Loan (2013) [`gvl13`],
§2.5.3. Proof: by `specNorm_residual_sq_eq_one_sub_singularValues_last_sq` (`k` nonempty; the empty case
is trivial), `sin θ_max < 1 ↔ σ_min(QᵀQ') > 0 ↔` `QᵀQ'` injective `↔` invertible (square).
atlas: principal-angles-def (partial) -/
theorem directedSubspaceGap_lt_one_iff_isUnit {Q Q' : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (hQ' : HasOrthonormalCols Q') : directedSubspaceGap Q Q' < 1 ↔ IsUnit (Qᵀ * Q') := by
  rcases isEmpty_or_nonempty k with hk | hk
  · have hR : projResidual Q Q' = 0 := Subsingleton.elim _ _
    have hUnit := isUnit_of_subsingleton (Qᵀ * Q')
    exact ⟨fun _ => hUnit, fun _ => by simp [directedSubspaceGap, hR, specNorm_zero]⟩
  · have hEq : directedSubspaceGap Q Q' ^ 2 = 1 - singularValues (Qᵀ * Q') (Fintype.card k - 1) ^ 2 :=
      specNorm_residual_sq_eq_one_sub_singularValues_last_sq hQ hQ'
    have hNonneg := directedSubspaceGap_nonneg Q Q'
    have hBound := directedSubspaceGap_le_one hQ hQ'
    have hSigma := singularValues_nonneg (Qᵀ * Q') (Fintype.card k - 1)
    rw [← singularValues_last_pos_iff_isUnit]
    constructor <;> intro h <;> nlinarith

/--
**`tan² = sin²/(1 − sin²)`.** For `Q`, `Q'` with orthonormal columns indexed by the same `k`
and `QᵀQ'` invertible: `tan² θ_max = sin² θ_max/(1 − sin² θ_max)`. Source: Golub–Van Loan
(2013) [`gvl13`], §2.5.3 and §8.2.4; Stewart–Sun (1990) [`ss90`], §I.5. Proof sketch: with
`C = QᵀQ'` and `S = (I − QQᵀ)Q'`, `CᵀC + SᵀS = I`; for `v = Cw`,
`‖S C⁻¹ v‖²/‖v‖² = t/(1 − t)` with `t = ‖Sw‖²/‖w‖²`, which is increasing in `t`; the maximum
of `t` is `sin² θ_max`. (When `QᵀQ'` is singular, `tan` has the junk value `0`.)
atlas: principal-angles-def (partial) -/
theorem sq_overlapTangentNorm_eq_div {Q Q' : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    (hQ' : HasOrthonormalCols Q') (hC : IsUnit (Qᵀ * Q')) :
    overlapTangentNorm Q Q' ^ 2 = directedSubspaceGap Q Q' ^ 2 / (1 - directedSubspaceGap Q Q' ^ 2) := by
  exact specNorm_residual_mul_inv_sq_eq_div_residual_sq hQ hQ' hC

/-- The geometric tangent satisfies the sine–tangent identity on the explicitly
transverse domain. Source: Stewart–Sun (1990), §I.5. -/
theorem sq_tanThetaMax_eq_div {Q Q' : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (hQ' : HasOrthonormalCols Q')
    (hC : IsUnit (Qᵀ * Q')) :
    tanThetaMax Q Q' hQ hC ^ 2 = directedSubspaceGap Q Q' ^ 2 /
      (1 - directedSubspaceGap Q Q' ^ 2) :=
  sq_overlapTangentNorm_eq_div hQ hQ' hC

/-- For positive equal width, the domain-safe tangent is the tangent of the
largest principal angle. Both orthonormality and transversality are explicit.
Source: Stewart–Sun (1990), Theorem I.5.5. -/
theorem tanThetaMax_eq_tan_principalAngles {Q X : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) (hX : HasOrthonormalCols X)
    (hC : IsUnit (Qᵀ * X)) (hk : 0 < Fintype.card k) :
    tanThetaMax Q X hQ hC =
      Real.tan (principalAnglesFintype Q X ⟨Fintype.card k - 1, by omega⟩) := by
  change specNorm (projResidual Q X * (Qᵀ * X)⁻¹) = _
  rw [← specNorm_tangentPrincipalAngles_eq_residual_mul_inv hQ hX hC]
  exact specNorm_tangentPrincipalAngles_eq_tan_last hQ hX hC hk

end NLAlib
