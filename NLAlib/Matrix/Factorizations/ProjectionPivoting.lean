import NLAlib.Matrix.Factorizations.EliminationProjector
import NLAlib.Matrix.Subspaces.OrthogonalProducts
import NLAlib.Matrix.Factorizations.CholeskyPivotProbability

/-! # Adaptive QR residuals in projector coordinates

The native elimination process on `Q Qᴴ` is exactly column pivoting of
`Qᴴ`: its diagonal pivot masses are residual column norm squares and its
Schur update is normalized orthogonalization of that column. No singular
vector selector or extra probabilistic state is introduced.
Source: Epperly 2025, Theorem 3.3.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 n d : Type*} [RCLike 𝕜] [Fintype n] [Fintype d]
  [DecidableEq n] [DecidableEq d]

/-- The adaptive QR residual after a chronological pivot list, expressed
through the actual Schur-elimination residual of its row Gram projector. -/
def projectionPivotResidual (Q : Matrix n d 𝕜) (l : List n) : Matrix d n 𝕜 :=
  Qᴴ * eliminationListResidual (Q * Qᴴ) l

omit [DecidableEq n] in
/-- The adaptive QR residual starts at the actual adjoint input frame.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem projectionPivotResidual_nil {Q : Matrix n d 𝕜} (hQ : HasOrthonormalCols Q) :
    projectionPivotResidual Q [] = Qᴴ := by
  change Qᴴ * (Q * Qᴴ) = Qᴴ
  rw [← Matrix.mul_assoc, hQ.conjTranspose_mul_self, Matrix.one_mul]

/-- The QR residual Gram matrix is the actual elimination residual. This
identifies all pivot probabilities and retains zero/repeated pivots. -/
theorem projectionPivotResidual_conjTranspose_mul_self {Q : Matrix n d 𝕜}
    (hQ : HasOrthonormalCols Q) (l : List n) :
    (projectionPivotResidual Q l)ᴴ * projectionPivotResidual Q l =
      eliminationListResidual (Q * Qᴴ) l := by
  let K := Q * Qᴴ
  let R := eliminationListResidual K l
  have hK : K.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self Q
  have hKp : IsIdempotentElem K := hQ.isIdempotentElem_mul_conjTranspose
  have hR : R.IsHermitian :=
    (posSemidef_eliminationListResidual (hK.posSemidef_of_isIdempotentElem hKp) l).isHermitian
  have hRR : R * R = R := isIdempotentElem_eliminationListResidual_of_projector hK hKp l
  have hRK : R * K = R := eliminationListResidual_mul_of_mul_eq hKp l
  change (Qᴴ * R)ᴴ * (Qᴴ * R) = R
  rw [Matrix.conjTranspose_mul, hR.eq, Matrix.conjTranspose_conjTranspose]
  calc
    _ = (R * K) * R := by simp only [K, Matrix.mul_assoc]
    _ = R := by rw [hRK, hRR]

/-- Each elimination pivot diagonal is exactly its QR residual column norm
square, in the native Euclidean norm. -/
theorem norm_projectionPivotResidual_col_sq {Q : Matrix n d 𝕜}
    (hQ : HasOrthonormalCols Q) (l : List n) (i : n) :
    ‖WithLp.toLp 2 ((projectionPivotResidual Q l).col i)‖ ^ 2 =
      RCLike.re (eliminationListResidual (Q * Qᴴ) l i i) := by
  rw [norm_toLp_sq_eq_re_star_dotProduct, ← conjTranspose_mul_self_apply,
    projectionPivotResidual_conjTranspose_mul_self hQ l]

/-- The Frobenius normalization of adaptive QR is the real trace used by
the native adaptive pivot law. -/
theorem frobSq_projectionPivotResidual {Q : Matrix n d 𝕜}
    (hQ : HasOrthonormalCols Q) (l : List n) :
    frobSq (projectionPivotResidual Q l) =
      RCLike.re (eliminationListResidual (Q * Qᴴ) l).trace := by
  rw [frobSq_eq_re_trace_conjTranspose_mul_self,
    projectionPivotResidual_conjTranspose_mul_self hQ l]

/-- At every nonabsorbed state, the native Cholesky pivot law is exactly
the adaptive QR squared-column-norm law. -/
theorem choleskyPivotProbability_projectionPivotResidual {Q : Matrix n d 𝕜}
    (hQ : HasOrthonormalCols Q) (l : List n)
    (ht : frobSq (projectionPivotResidual Q l) ≠ 0) (i : n) :
    choleskyPivotProbability (eliminationListResidual (Q * Qᴴ) l) i =
      ‖WithLp.toLp 2 ((projectionPivotResidual Q l).col i)‖ ^ 2 /
        frobSq (projectionPivotResidual Q l) := by
  rw [frobSq_projectionPivotResidual hQ l] at ht
  rw [choleskyPivotProbability, if_neg ht, norm_projectionPivotResidual_col_sq hQ l,
    frobSq_projectionPivotResidual hQ l]

/-- The actual next QR residual is normalized orthogonalization against its
selected residual column. The formula is total even for a zero column.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem projectionPivotResidual_append_singleton {Q : Matrix n d 𝕜}
    (hQ : HasOrthonormalCols Q) (l : List n) (i : n) :
    let M := projectionPivotResidual Q l
    let u := M.col i
    projectionPivotResidual Q (l ++ [i]) =
      (1 - (((‖WithLp.toLp 2 u‖ ^ 2 : ℝ) : 𝕜))⁻¹ •
        Matrix.vecMulVec u (star u)) * M := by
  let R := eliminationListResidual (Q * Qᴴ) l
  let M := projectionPivotResidual Q l
  have hPSD := posSemidef_eliminationListResidual (Matrix.posSemidef_self_mul_conjTranspose Q) l
  have hGram : Mᴴ * M = R := projectionPivotResidual_conjTranspose_mul_self hQ l
  have hrow : star (M.col i) ᵥ* M = fun j => R i j := by
    funext j
    exact congrFun (congrFun hGram i) j
  have hcol : Qᴴ *ᵥ (fun j => R j i) = M.col i := by
    funext j
    rfl
  have hnorm : ((‖WithLp.toLp 2 (M.col i)‖ ^ 2 : ℝ) : 𝕜) = R i i := by
    rw [norm_projectionPivotResidual_col_sq hQ l]
    exact (diag_eq_ofReal_re_of_posSemidef hPSD i).symm
  change Qᴴ * eliminationListResidual (Q * Qᴴ) (l ++ [i]) = _
  rw [eliminationListResidual_append_singleton]
  change Qᴴ * eliminationStep R i =
    (1 - (((‖WithLp.toLp 2 (M.col i)‖ ^ 2 : ℝ) : 𝕜))⁻¹ •
      Matrix.vecMulVec (M.col i) (star (M.col i))) * M
  rw [hnorm, eliminationStep, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_vecMulVec,
    hcol, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.vecMulVec_mul, hrow]
  rfl

/-- On a history of nonzero chronological pivots, the actual QR residual
normalizer is the original frame width minus the number of selected pivots.
This is the source's `k-t` denominator, proved from exact rank drop. -/
theorem frobSq_projectionPivotResidual_eq_card_sub_length {Q : Matrix n d 𝕜}
    (hQ : HasOrthonormalCols Q) (l : List n)
    (hl : eliminationPivotProduct (Q * Qᴴ) l ≠ 0) :
    frobSq (projectionPivotResidual Q l) = ((Fintype.card d - l.length : ℕ) : ℝ) := by
  rw [frobSq_projectionPivotResidual hQ l,
    trace_eq_rank_of_isIdempotentElem _ (isIdempotentElem_eliminationListResidual_of_projector
      (Matrix.isHermitian_mul_conjTranspose_self Q) (hQ.isIdempotentElem_mul_conjTranspose) l), RCLike.natCast_re]
  have h := rank_eliminationListResidual_add_length_eq_of_pivotProduct_ne_zero (Q * Qᴴ) l hl
  rw [Matrix.rank_self_mul_conjTranspose, hQ.rank_eq_card] at h
  congr 1
  omega

/-- Before the last active pivot, the literal native pivot probability is
the squared residual column norm divided by `k-t`. No fallback is used on a
supported prefix. -/
theorem choleskyPivotProbability_projectionPivotResidual_eq_div_card_sub_length
    {Q : Matrix n d 𝕜} (hQ : HasOrthonormalCols Q) (l : List n)
    (hl : eliminationPivotProduct (Q * Qᴴ) l ≠ 0) (ht : l.length < Fintype.card d) (i : n) :
    choleskyPivotProbability (eliminationListResidual (Q * Qᴴ) l) i =
      ‖WithLp.toLp 2 ((projectionPivotResidual Q l).col i)‖ ^ 2 /
        ((Fintype.card d - l.length : ℕ) : ℝ) := by
  have hnorm := frobSq_projectionPivotResidual_eq_card_sub_length hQ l hl
  have hn : frobSq (projectionPivotResidual Q l) ≠ 0 := by
    rw [hnorm]
    exact_mod_cast (Nat.sub_pos_of_lt ht).ne'
  rw [choleskyPivotProbability_projectionPivotResidual hQ l hn i, hnorm]

/-- The source coordinate projector onto the already selected directions,
defined from the actual QR residual. It is total on arbitrary histories. -/
def projectionPivotProjector (Q : Matrix n d 𝕜) (l : List n) : Matrix d d 𝕜 :=
  1 - projectionPivotResidual Q l * (projectionPivotResidual Q l)ᴴ

/-- The residual row Gram is an orthogonal projector at every history,
including zero or repeated pivot labels. -/
theorem projectionPivotResidual_mul_conjTranspose_projector {Q : Matrix n d 𝕜}
    (hQ : HasOrthonormalCols Q) (l : List n) :
    (projectionPivotResidual Q l * (projectionPivotResidual Q l)ᴴ).IsHermitian ∧
      IsIdempotentElem (projectionPivotResidual Q l * (projectionPivotResidual Q l)ᴴ) := by
  let M := projectionPivotResidual Q l
  let R := eliminationListResidual (Q * Qᴴ) l
  have hGram : Mᴴ * M = R := projectionPivotResidual_conjTranspose_mul_self hQ l
  have hRR : R * R = R := isIdempotentElem_eliminationListResidual_of_projector
    (Matrix.isHermitian_mul_conjTranspose_self Q) (hQ.isIdempotentElem_mul_conjTranspose) l
  refine ⟨Matrix.isHermitian_mul_conjTranspose_self M, ?_⟩
  change (M * Mᴴ) * (M * Mᴴ) = M * Mᴴ
  calc
    _ = (M * (Mᴴ * M)) * Mᴴ := by simp only [Matrix.mul_assoc]
    _ = (M * R) * Mᴴ := by rw [hGram]
    _ = _ := by
      have hMR : M * R = M := by
        change (Qᴴ * R) * R = Qᴴ * R
        rw [Matrix.mul_assoc, hRR]
      rw [hMR]

/-- The actual selected-direction projector is Hermitian and idempotent,
and its complement is exactly the QR residual row Gram.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem projectionPivotProjector_certificate {Q : Matrix n d 𝕜}
    (hQ : HasOrthonormalCols Q) (l : List n) :
    (projectionPivotProjector Q l).IsHermitian ∧
      IsIdempotentElem (projectionPivotProjector Q l) ∧
      projectionPivotResidual Q l * (projectionPivotResidual Q l)ᴴ =
        1 - projectionPivotProjector Q l := by
  have h := projectionPivotResidual_mul_conjTranspose_projector hQ l
  refine ⟨?_, ?_, ?_⟩
  · exact Matrix.isHermitian_one.sub h.1
  · exact (one_sub_projector_isHermitian_isIdempotentElem h.1 h.2).2
  · unfold projectionPivotProjector
    abel

/-- A supported prefix selects exactly one new direction per pivot. Together
with the projector certificate and the norm identity this gives all source
QR invariants at every active prefix.
atlas: adaptive-pivoting-projection-dpp (partial) -/
theorem rank_projectionPivotProjector_eq_length {Q : Matrix n d 𝕜}
    (hQ : HasOrthonormalCols Q) (l : List n)
    (hl : eliminationPivotProduct (Q * Qᴴ) l ≠ 0) :
    (projectionPivotProjector Q l).rank = l.length := by
  have hCert := projectionPivotProjector_certificate hQ l
  have hRank := rank_eliminationListResidual_add_length_eq_of_pivotProduct_ne_zero (Q * Qᴴ) l hl
  rw [Matrix.rank_self_mul_conjTranspose, hQ.rank_eq_card] at hRank
  have ht := congrArg RCLike.re (trace_eq_rank_of_isIdempotentElem
    (projectionPivotProjector Q l) hCert.2.1)
  have hM : RCLike.re (projectionPivotResidual Q l * (projectionPivotResidual Q l)ᴴ).trace =
      frobSq (projectionPivotResidual Q l) := by
    rw [frobSq_eq_re_trace_conjTranspose_mul_self, Matrix.trace_mul_comm]
  simp only [projectionPivotProjector, Matrix.trace_sub, Matrix.trace_one, map_sub,
    RCLike.natCast_re, hM, frobSq_projectionPivotResidual_eq_card_sub_length hQ l hl] at ht
  have hlen : l.length ≤ Fintype.card d := by omega
  rw [Nat.cast_sub hlen] at ht
  change (Fintype.card d : ℝ) - ((Fintype.card d : ℝ) - (l.length : ℝ)) =
    ((projectionPivotProjector Q l).rank : ℝ) at ht
  exact_mod_cast (by linarith : ((projectionPivotProjector Q l).rank : ℝ) = l.length)

end NLAlib
