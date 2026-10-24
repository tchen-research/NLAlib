import NLAlib.LowRank.Cholesky.HistoryDeterminant
import NLAlib.Matrix.Factorizations.EliminationProjector
import NLAlib.Matrix.Basic.OrderedPrincipalMinors
import NLAlib.Matrix.Factorizations.ProjectionPivoting

/-! # Actual adaptive histories of an orthogonal projector

Every projector history has determinant-over-falling-factorial probability.
This specializes the existing real and complex Cholesky laws, rather than
postulating a separate pivot distribution. It is the QR projection-DPP law.
Source: Epperly 2025, Theorem 3.3; projection specialization of the
Dereziński–Warmuth determinant law.
-/

noncomputable section
open scoped Matrix ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem eq_re_det_div_descFactorial {𝕜 : Type*} [RCLike 𝕜]
    {P : Matrix n n 𝕜} (hs : P.IsHermitian) (hp : IsIdempotentElem P)
    {t : ℕ} (h : Fin t → n) (ht : t ≤ P.rank) (w : ℝ)
    (hw : w * choleskyHistoryTraceProduct P h = RCLike.re (P.submatrix h h).det) :
    w = RCLike.re (P.submatrix h h).det / (P.rank.descFactorial t : ℝ) := by
  have hPSD := hs.posSemidef_of_isIdempotentElem hp
  have htpos : 0 < choleskyHistoryTraceProduct P h := by
    apply eliminationTraceProduct_pos hPSD
    simpa only [List.length_ofFn] using ht
  by_cases hz : RCLike.re (P.submatrix h h).det = 0
  · have hwz : w = 0 := (mul_eq_zero.mp (hw.trans hz)).resolve_right htpos.ne'
    rw [hwz, hz, zero_div]
  · have hprod : eliminationPivotProduct P (List.ofFn h) ≠ 0 := by
      rw [← det_submatrix_eq_eliminationPivotProduct hPSD]
      intro hd
      exact hz (by rw [hd, map_zero])
    have htrace := eliminationTraceProduct_eq_descFactorial_of_projector hs hp (List.ofFn h) hprod
    simp only [List.length_ofFn] at htrace
    change choleskyHistoryTraceProduct P h = _ at htrace
    have hfpos : (0 : ℝ) < P.rank.descFactorial t := htrace ▸ htpos
    apply (eq_div_iff hfpos.ne').mpr
    rwa [htrace] at hw

/-- The actual real adaptive pivot-history weight of a projector is its
selected principal determinant divided by the falling factorial of the rank.
Every history is included, including zero-probability repeated pivots. -/
theorem choleskyHistoryWeight_projector {P : Matrix n n ℝ}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) {t : ℕ} (h : Fin t → n)
    (ht : t ≤ P.rank) :
    choleskyHistoryWeight P t h = (P.submatrix h h).det / (P.rank.descFactorial t : ℝ) := by
  exact eq_re_det_div_descFactorial hs hp h ht _
    (choleskyHistoryWeight_mul_traceProduct_eq_det
      (hs.posSemidef_of_isIdempotentElem hp) h)

/-- The actual complex adaptive pivot-history weight of a projector has
the same determinant formula. No complex matrix is replaced by its real part. -/
theorem complexCholeskyHistoryWeight_projector {P : Matrix n n ℂ}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) {t : ℕ} (h : Fin t → n)
    (ht : t ≤ P.rank) :
    complexCholeskyHistoryWeight P t h =
      (P.submatrix h h).det.re / (P.rank.descFactorial t : ℝ) := by
  exact eq_re_det_div_descFactorial hs hp h ht _
    (complexCholeskyHistoryWeight_mul_traceProduct_eq_re_det
      (hs.posSemidef_of_isIdempotentElem hp) h)

private theorem sum_re_det_submatrix_image_eq {𝕜 : Type*} [RCLike 𝕜]
    (P : Matrix n n 𝕜) (t : ℕ) (S : Finset n) :
    (∑ h : Fin t → n, if Finset.univ.image h = S then RCLike.re (P.submatrix h h).det else 0) =
      (t.factorial : ℝ) * (if S ∈ (Finset.univ : Finset n).powersetCard t then
        RCLike.re (P.submatrix (Subtype.val : S → n) Subtype.val).det else 0) := by
  classical
  let f : Finset n → ℝ := fun T => if T = S then
    RCLike.re (P.submatrix (Subtype.val : T → n) Subtype.val).det else 0
  calc
    _ = ∑ h : Fin t → n, if Function.Injective h then f (Finset.univ.image h) else 0 := by
      apply Finset.sum_congr rfl
      intro h _
      by_cases hh : Function.Injective h
      · rw [if_pos hh, det_submatrix_eq_det_image_of_injective P h hh]
      · rw [if_neg hh, det_submatrix_eq_zero_of_not_injective P h hh, map_zero]
        split_ifs <;> rfl
    _ = _ := by
      rw [Finset.sum_injective_image_eq_factorial_nsmul]
      simp only [f, Finset.sum_ite_eq', nsmul_eq_mul]

private theorem pmf_map_image_toReal {𝕜 : Type*} [RCLike 𝕜]
    (P : Matrix n n 𝕜) (t : ℕ) (p : PMF (Fin t → n))
    (hp : ∀ h, (p h).toReal = RCLike.re (P.submatrix h h).det / (t.factorial : ℝ))
    (S : Finset n) :
    ((p.map (fun h => Finset.univ.image h)) S).toReal =
      if S ∈ (Finset.univ : Finset n).powersetCard t then
        RCLike.re (P.submatrix (Subtype.val : S → n) Subtype.val).det else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (fun h _ => by
    split_ifs
    · exact p.apply_ne_top h
    · exact ENNReal.zero_ne_top)]
  calc
    _ = ∑ h : Fin t → n, if Finset.univ.image h = S then
        RCLike.re (P.submatrix h h).det / (t.factorial : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro h _
      by_cases he : Finset.univ.image h = S
      · rw [if_pos he.symm, if_pos he, hp]
      · rw [if_neg (Ne.symm he), if_neg he, ENNReal.toReal_zero]
    _ = (∑ h : Fin t → n, if Finset.univ.image h = S then
        RCLike.re (P.submatrix h h).det else 0) / (t.factorial : ℝ) := by
      simp only [ite_div, zero_div, Finset.sum_div]
    _ = _ := by
      rw [sum_re_det_submatrix_image_eq]
      exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero t))

/-- Forgetting the order of a complete real projector pivot history gives
exactly its projection-DPP principal-minor mass on each subset.
Epperly 2025, Theorem 3.3.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem choleskyHistoryPMF_projector_image_toReal [Nonempty n] {P : Matrix n n ℝ}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) (S : Finset n) :
    (((choleskyHistoryPMF P (hs.posSemidef_of_isIdempotentElem hp) P.rank).map
      (fun h => Finset.univ.image h)) S).toReal =
      if S ∈ (Finset.univ : Finset n).powersetCard P.rank then
        (P.submatrix (Subtype.val : S → n) Subtype.val).det else 0 := by
  refine pmf_map_image_toReal P P.rank _ ?_ S
  intro h
  simp only [choleskyHistoryPMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (choleskyHistoryWeight_nonneg
      (hs.posSemidef_of_isIdempotentElem hp) _ h)]
  rw [choleskyHistoryWeight_projector hs hp h le_rfl, Nat.descFactorial_self]
  rfl

/-- Forgetting order gives the same projection-DPP law for actual complex
adaptive histories, with nonnegative real principal Gram determinants.
Epperly 2025, Theorem 3.3.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem complexCholeskyHistoryPMF_projector_image_toReal [Nonempty n] {P : Matrix n n ℂ}
    (hs : P.IsHermitian) (hp : IsIdempotentElem P) (S : Finset n) :
    (((complexCholeskyHistoryPMF P (hs.posSemidef_of_isIdempotentElem hp) P.rank).map
      (fun h => Finset.univ.image h)) S).toReal =
      if S ∈ (Finset.univ : Finset n).powersetCard P.rank then
        (P.submatrix (Subtype.val : S → n) Subtype.val).det.re else 0 := by
  refine pmf_map_image_toReal P P.rank _ ?_ S
  intro h
  simp only [complexCholeskyHistoryPMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (complexCholeskyHistoryWeight_nonneg
      (hs.posSemidef_of_isIdempotentElem hp) _ h)]
  rw [complexCholeskyHistoryWeight_projector hs hp h le_rfl, Nat.descFactorial_self]
  rfl

/-- The actual real projection-DPP image mass at any explicitly supplied
time equal to the projector rank. This avoids transporting dependent history
types at a frame-width specialization. -/
theorem choleskyHistoryPMF_projector_image_toReal_of_rank_eq [Nonempty n]
    {P : Matrix n n ℝ} (hs : P.IsHermitian) (hp : IsIdempotentElem P)
    {t : ℕ} (ht : P.rank = t) (S : Finset n) :
    (((choleskyHistoryPMF P (hs.posSemidef_of_isIdempotentElem hp) t).map
      (fun h => Finset.univ.image h)) S).toReal =
      if S.card = t then (P.submatrix (Subtype.val : S → n) Subtype.val).det else 0 := by
  subst t
  simpa only [Finset.mem_powersetCard, Finset.subset_univ, true_and] using
    choleskyHistoryPMF_projector_image_toReal hs hp S

/-- The same explicitly sized projection-DPP image mass for the actual
complex history law. -/
theorem complexCholeskyHistoryPMF_projector_image_toReal_of_rank_eq [Nonempty n]
    {P : Matrix n n ℂ} (hs : P.IsHermitian) (hp : IsIdempotentElem P)
    {t : ℕ} (ht : P.rank = t) (S : Finset n) :
    (((complexCholeskyHistoryPMF P (hs.posSemidef_of_isIdempotentElem hp) t).map
      (fun h => Finset.univ.image h)) S).toReal =
      if S.card = t then (P.submatrix (Subtype.val : S → n) Subtype.val).det.re else 0 := by
  subst t
  simpa only [Finset.mem_powersetCard, Finset.subset_univ, true_and] using
    complexCholeskyHistoryPMF_projector_image_toReal hs hp S

/-- A positive real history weight before the input rank has a nonzero
chronological pivot product. Consequently none of its active pivots uses
the zero-column or absorbed fallback. -/
theorem eliminationPivotProduct_ne_zero_of_choleskyHistoryWeight_pos
    {A : Matrix n n ℝ} (hA : A.PosSemidef) {t : ℕ} (h : Fin t → n)
    (ht : t ≤ A.rank) (hw : 0 < choleskyHistoryWeight A t h) :
    eliminationPivotProduct A (List.ofFn h) ≠ 0 := by
  have hp := mul_pos hw (choleskyHistoryTraceProduct_pos hA h ht)
  rw [choleskyHistoryWeight_mul_traceProduct_eq_det hA h,
    det_submatrix_eq_eliminationPivotProduct hA] at hp
  exact hp.ne'

/-- The same nonzero chronological-pivot assertion for the actual complex
history law, obtained from its real nonnegative weights. -/
theorem eliminationPivotProduct_ne_zero_of_complexCholeskyHistoryWeight_pos
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {t : ℕ} (h : Fin t → n)
    (ht : t ≤ A.rank) (hw : 0 < complexCholeskyHistoryWeight A t h) :
    eliminationPivotProduct A (List.ofFn h) ≠ 0 := by
  have hp := mul_pos hw (choleskyHistoryTraceProduct_pos hA h ht)
  rw [complexCholeskyHistoryWeight_mul_traceProduct_eq_re_det hA h,
    det_submatrix_eq_eliminationPivotProduct hA] at hp
  intro hz
  simp only [hz, Complex.zero_re, lt_self_iff_false] at hp

/-- On every positive-weight real prefix, the actual QR normalization is
exactly frame width minus prefix length. Epperly 2025, Theorem 3.3. -/
theorem frobSq_projectionPivotResidual_of_choleskyHistoryWeight_pos
    {d : Type*} [Fintype d] [DecidableEq d] {Q : Matrix n d ℝ}
    (hQ : HasOrthonormalCols Q) {t : ℕ} (h : Fin t → n) (ht : t ≤ Fintype.card d)
    (hw : 0 < choleskyHistoryWeight (Q * Qᴴ) t h) :
    frobSq (projectionPivotResidual Q (List.ofFn h)) = ((Fintype.card d - t : ℕ) : ℝ) := by
  have hprod := eliminationPivotProduct_ne_zero_of_choleskyHistoryWeight_pos
    (Matrix.posSemidef_self_mul_conjTranspose Q) h
    (by rwa [Matrix.rank_self_mul_conjTranspose, hQ.rank_eq_card]) hw
  simpa only [List.length_ofFn] using
    frobSq_projectionPivotResidual_eq_card_sub_length hQ (List.ofFn h) hprod

/-- The same exact active-prefix normalization for complex adaptive QR. -/
theorem frobSq_projectionPivotResidual_of_complexCholeskyHistoryWeight_pos
    {d : Type*} [Fintype d] [DecidableEq d] {Q : Matrix n d ℂ}
    (hQ : HasOrthonormalCols Q) {t : ℕ} (h : Fin t → n) (ht : t ≤ Fintype.card d)
    (hw : 0 < complexCholeskyHistoryWeight (Q * Qᴴ) t h) :
    frobSq (projectionPivotResidual Q (List.ofFn h)) = ((Fintype.card d - t : ℕ) : ℝ) := by
  have hprod := eliminationPivotProduct_ne_zero_of_complexCholeskyHistoryWeight_pos
    (Matrix.posSemidef_self_mul_conjTranspose Q) h
    (by rwa [Matrix.rank_self_mul_conjTranspose, hQ.rank_eq_card]) hw
  simpa only [List.length_ofFn] using
    frobSq_projectionPivotResidual_eq_card_sub_length hQ (List.ofFn h) hprod

/-- Every positive-weight real prefix shorter than the frame width uses
exactly the source QR probability `columnNormSq/(k-t)`.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem choleskyPivotProbability_projection_frame_of_history_pos
    {d : Type*} [Fintype d] [DecidableEq d] {Q : Matrix n d ℝ}
    (hQ : HasOrthonormalCols Q) {t : ℕ} (h : Fin t → n) (ht : t < Fintype.card d)
    (hw : 0 < choleskyHistoryWeight (Q * Qᴴ) t h) (i : n) :
    choleskyPivotProbability (partialCholeskyResidual (Q * Qᴴ) h) i =
      ‖WithLp.toLp 2 ((projectionPivotResidual Q (List.ofFn h)).col i)‖ ^ 2 /
        ((Fintype.card d - t : ℕ) : ℝ) := by
  have hprod := eliminationPivotProduct_ne_zero_of_choleskyHistoryWeight_pos
    (Matrix.posSemidef_self_mul_conjTranspose Q) h
    (by rw [Matrix.rank_self_mul_conjTranspose, hQ.rank_eq_card]; exact ht.le) hw
  simpa only [List.length_ofFn, eliminationListResidual_ofFn_eq_partialCholeskyResidual] using
    choleskyPivotProbability_projectionPivotResidual_eq_div_card_sub_length hQ (List.ofFn h)
      hprod (by simpa only [List.length_ofFn] using ht) i

/-- Every positive-weight complex prefix uses the same normalized squared
column rule, with the actual native complex residual and no fallback.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem choleskyPivotProbability_complexProjection_frame_of_history_pos
    {d : Type*} [Fintype d] [DecidableEq d] {Q : Matrix n d ℂ}
    (hQ : HasOrthonormalCols Q) {t : ℕ} (h : Fin t → n) (ht : t < Fintype.card d)
    (hw : 0 < complexCholeskyHistoryWeight (Q * Qᴴ) t h) (i : n) :
    choleskyPivotProbability (complexCholeskyResidualHistory (Q * Qᴴ) t h) i =
      ‖WithLp.toLp 2 ((projectionPivotResidual Q (List.ofFn h)).col i)‖ ^ 2 /
        ((Fintype.card d - t : ℕ) : ℝ) := by
  have hprod := eliminationPivotProduct_ne_zero_of_complexCholeskyHistoryWeight_pos
    (Matrix.posSemidef_self_mul_conjTranspose Q) h
    (by rw [Matrix.rank_self_mul_conjTranspose, hQ.rank_eq_card]; exact ht.le) hw
  simpa only [List.length_ofFn, eliminationListResidual_ofFn_eq_complexCholeskyResidualHistory] using
    choleskyPivotProbability_projectionPivotResidual_eq_div_card_sub_length hQ (List.ofFn h)
      hprod (by simpa only [List.length_ofFn] using ht) i

end NLAlib
