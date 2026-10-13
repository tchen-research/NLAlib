import NLAlib.Matrix.Perturbation.InversePerturbationBounds
import NLAlib.Matrix.Basic.LeastSquares
import Mathlib.Tactic.FieldSimp

/-!
# Full-column-rank least-squares geometry

Actual Moore–Penrose solutions, their unique minimizing property, and
Neumann stability of full column rank. Higham, Theorem 20.1; Wedin §5.
Supports atlas `least-squares-perturbation`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace RealInnerProductSpace
namespace NLAlib
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] in
/-- Rectangular Euclidean matrix action is bounded by the spectral norm.
Mathlib's operator-norm inequality; supports least-squares perturbation. -/
theorem norm_toEuclideanLin_apply_le (A : Matrix m n ℝ) (x : EuclideanSpace ℝ n) :
    ‖A.toEuclideanLin x‖ ≤ specNorm A * ‖x‖ :=
  A.l2_opNorm_mulVec x

omit [Fintype m] [DecidableEq m] in
/-- Euclidean action transports rectangular matrix multiplication.
Mathlib's matrix action; supports least-squares perturbation. -/
theorem toEuclideanLin_mul_apply (A : Matrix m n ℝ) (B : Matrix n p ℝ)
    (x : EuclideanSpace ℝ p) :
    (A*B).toEuclideanLin x = A.toEuclideanLin (B.toEuclideanLin x) := by
  apply (WithLp.equiv 2 (m → ℝ)).injective
  change (A*B)*ᵥx.ofLp = A*ᵥ(B*ᵥx.ofLp)
  rw [Matrix.mulVec_mulVec]

/-- The identity matrix acts identically on Euclidean vectors.
Mathlib's matrix action; supports least-squares perturbation. -/
@[simp] theorem toEuclideanLin_one_apply (x : EuclideanSpace ℝ n) :
    (1 : Matrix n n ℝ).toEuclideanLin x = x := by
  apply (WithLp.equiv 2 (n → ℝ)).injective
  simp

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- Full column rank makes the ordinary matrix action injective.
Rank-nullity; supports least-squares perturbation, including empty columns. -/
theorem mulVec_injective_of_rank_eq_card {A : Matrix m n ℝ}
    (hA : A.rank = Fintype.card n) : Function.Injective A.mulVecLin := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply (rank_eq_card_iff_forall_mulVec_eq_zero A).mp hA
  change A*ᵥ(x-y)=0
  rw [Matrix.mulVec_sub]
  exact sub_eq_zero.mpr hxy

omit [DecidableEq m] in
/-- Full column rank gives the literal Moore–Penrose left inverse.
Penrose identities and rank-nullity; supports least-squares perturbation. -/
theorem moorePenroseInverse_mul_eq_one_of_rank_eq_card {A : Matrix m n ℝ}
    (hA : A.rank = Fintype.card n) : moorePenroseInverse A * A = 1 := by
  have hG := isUnit_transpose_mul_self_of_rank_eq hA
  rw [moorePenroseInverse_eq_pinvL A hG]
  exact pinvL_mul hG

omit [DecidableEq m] in
/-- A literal matrix left inverse forces full column rank.
Rank monotonicity; supports least-squares perturbation. -/
theorem rank_eq_card_of_left_inverse {A : Matrix m n ℝ} {L : Matrix n m ℝ}
    (hL : L*A=1) : A.rank = Fintype.card n := by
  apply le_antisymm (Matrix.rank_le_card_width A)
  have h := Matrix.rank_mul_le_right L A
  simpa only [hL, Matrix.rank_one] using h

omit [DecidableEq m] in
/-- Any left inverse recovers the Moore–Penrose inverse after composing with
the orthogonal range projector. Penrose identities; supports least-squares perturbation. -/
theorem moorePenroseInverse_eq_left_inverse_mul_projector
    {A : Matrix m n ℝ} {L : Matrix n m ℝ} (hL : L*A=1) :
    moorePenroseInverse A = L*(A*moorePenroseInverse A) := by
  rw [← Matrix.mul_assoc, hL, Matrix.one_mul]

/-- Neumann perturbations of full-column-rank matrices retain full column rank.
Higham, Theorem 20.1; the proof constructs a genuine left inverse. -/
theorem rank_add_eq_card_of_pinv_mul_specNorm_lt_one {A E : Matrix m n ℝ}
    (hA : A.rank = Fintype.card n)
    (hE : specNorm (moorePenroseInverse A)*specNorm E < 1) :
    (A+E).rank=Fintype.card n := by
  have hF : specNorm (moorePenroseInverse A*E) < 1 :=
    (specNorm_mul_le _ _).trans_lt hE
  have hU : IsUnit (1+moorePenroseInverse A*E) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_specNorm_lt_one
      (F := -(moorePenroseInverse A*E)) (by simpa only [specNorm_neg] using hF)
  apply rank_eq_card_of_left_inverse (L := (1+moorePenroseInverse A*E)⁻¹*moorePenroseInverse A)
  rw [Matrix.mul_assoc, Matrix.mul_add,
    moorePenroseInverse_mul_eq_one_of_rank_eq_card hA,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)]

/-- The perturbed Moore–Penrose norm has the same denominator as the
Neumann left inverse. Higham, Theorem 20.1. -/
theorem specNorm_pinv_add_le_of_rank_eq_card {A E : Matrix m n ℝ}
    (hA : A.rank = Fintype.card n)
    (hE : specNorm (moorePenroseInverse A)*specNorm E < 1) :
    specNorm (moorePenroseInverse (A+E)) ≤
      specNorm (moorePenroseInverse A)/(1-specNorm (moorePenroseInverse A)*specNorm E) := by
  have hF : specNorm (moorePenroseInverse A*E) < 1 :=
    (specNorm_mul_le _ _).trans_lt hE
  have hU : IsUnit (1+moorePenroseInverse A*E) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_specNorm_lt_one
      (F := -(moorePenroseInverse A*E)) (by simpa only [specNorm_neg] using hF)
  have hL : ((1+moorePenroseInverse A*E)⁻¹*moorePenroseInverse A)*(A+E)=1 := by
    rw [Matrix.mul_assoc, Matrix.mul_add, moorePenroseInverse_mul_eq_one_of_rank_eq_card hA,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)]
  have hP : specNorm ((A+E)*moorePenroseInverse (A+E)) ≤ 1 :=
    Matrix.IsHermitian.specNorm_le_one_of_isIdempotentElem
      (mul_moorePenroseInverse_isHermitian _) (mul_moorePenroseInverse_isIdempotentElem _)
  rw [moorePenroseInverse_eq_left_inverse_mul_projector hL]
  calc
    _ ≤ specNorm ((1+moorePenroseInverse A*E)⁻¹*moorePenroseInverse A)*
        specNorm ((A+E)*moorePenroseInverse (A+E)) := specNorm_mul_le _ _
    _ ≤ specNorm ((1+moorePenroseInverse A*E)⁻¹*moorePenroseInverse A)*1 :=
      mul_le_mul_of_nonneg_left hP (specNorm_nonneg _)
    _ ≤ (1-specNorm (moorePenroseInverse A*E))⁻¹*specNorm (moorePenroseInverse A) := by
      rw [mul_one]
      exact (specNorm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (specNorm_inv_one_add_le hF) (specNorm_nonneg _))
    _ ≤ specNorm (moorePenroseInverse A)/(1-specNorm (moorePenroseInverse A)*specNorm E) := by
      rw [mul_comm, ← div_eq_mul_inv]
      apply (div_le_div_iff₀ (sub_pos.mpr hF) (sub_pos.mpr hE)).mpr
      exact mul_le_mul_of_nonneg_left (sub_le_sub_left (specNorm_mul_le _ _) 1)
        (specNorm_nonneg _)

/-- Transposition is the adjoint of real Euclidean matrix action.
Mathlib's adjoint transport; supports least-squares perturbation. -/
theorem inner_toEuclideanLin_eq_inner_transpose (A : Matrix m n ℝ)
    (x : EuclideanSpace ℝ n) (y : EuclideanSpace ℝ m) :
    inner ℝ (A.toEuclideanLin x) y =
      inner ℝ x (Aᵀ.toEuclideanLin y) := by
  have h : Aᵀ.toEuclideanLin = A.toEuclideanLin.adjoint := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rw [h, LinearMap.adjoint_inner_right]

/-- The actual Moore–Penrose residual satisfies the normal equation at every
rank. Higham, Theorem 20.1; supports least-squares perturbation. -/
theorem transpose_apply_pinv_residual_eq_zero (A : Matrix m n ℝ)
    (b : EuclideanSpace ℝ m) :
    Aᵀ.toEuclideanLin (b-A.toEuclideanLin ((moorePenroseInverse A).toEuclideanLin b))=0 := by
  have h : Aᵀ*(1-A*moorePenroseInverse A)=0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, transpose_mul_mul_moorePenroseInverse, sub_self]
  have hv := congrArg (fun M : Matrix n m ℝ => M.toEuclideanLin b) h
  simpa only [toEuclideanLin_mul_apply, map_sub, LinearMap.sub_apply,
    toEuclideanLin_one_apply, map_zero, LinearMap.zero_apply] using hv

/-- Pythagoras splits every least-squares objective into its Moore–Penrose
minimum and the squared fitted error. Higham, Theorem 20.1. -/
theorem norm_pinv_residual_sq_add_eq (A : Matrix m n ℝ)
    (b : EuclideanSpace ℝ m) (z : EuclideanSpace ℝ n) :
    ‖b-A.toEuclideanLin z‖^2 =
      ‖b-A.toEuclideanLin ((moorePenroseInverse A).toEuclideanLin b)‖^2 +
      ‖A.toEuclideanLin (z-(moorePenroseInverse A).toEuclideanLin b)‖^2 := by
  let x := (moorePenroseInverse A).toEuclideanLin b
  let r := b-A.toEuclideanLin x
  have hi : inner ℝ r (A.toEuclideanLin (z-x))=0 := by
    rw [real_inner_comm, inner_toEuclideanLin_eq_inner_transpose,
      transpose_apply_pinv_residual_eq_zero, inner_zero_right]
  have he : b-A.toEuclideanLin z = r-A.toEuclideanLin (z-x) := by
    dsimp [r]
    rw [map_sub]
    abel
  rw [he]
  have h := norm_sub_sq_eq_norm_sq_add_norm_sq_real hi
  simpa only [pow_two] using h

/-- Full-column-rank Moore–Penrose solutions are unique least-squares
minimizers. Higham, Theorem 20.1; arbitrary finite indices. -/
theorem pinv_least_squares_unique {A : Matrix m n ℝ}
    (hA : A.rank=Fintype.card n) (b : EuclideanSpace ℝ m) :
    (∀ z : EuclideanSpace ℝ n,
      ‖b-A.toEuclideanLin ((moorePenroseInverse A).toEuclideanLin b)‖ ≤
        ‖b-A.toEuclideanLin z‖) ∧
    (∀ z : EuclideanSpace ℝ n,
      (∀ w : EuclideanSpace ℝ n, ‖b-A.toEuclideanLin z‖ ≤ ‖b-A.toEuclideanLin w‖) →
        z=(moorePenroseInverse A).toEuclideanLin b) := by
  let x := (moorePenroseInverse A).toEuclideanLin b
  have hmin (z : EuclideanSpace ℝ n) : ‖b-A.toEuclideanLin x‖ ≤ ‖b-A.toEuclideanLin z‖ := by
    have h := norm_pinv_residual_sq_add_eq A b z
    have hn := sq_nonneg ‖A.toEuclideanLin (z-x)‖
    have h1 := norm_nonneg (b-A.toEuclideanLin x)
    have h2 := norm_nonneg (b-A.toEuclideanLin z)
    nlinarith
  refine ⟨hmin, ?_⟩
  intro z hz
  have hn := le_antisymm (hz x) (hmin z)
  have he := norm_pinv_residual_sq_add_eq A b z
  have hzero : A.toEuclideanLin (z-x)=0 := by
    apply norm_eq_zero.mp
    have hs : ‖A.toEuclideanLin (z-x)‖^2=0 := by
      change ‖b-A.toEuclideanLin z‖^2 = ‖b-A.toEuclideanLin x‖^2+_ at he
      rw [hn] at he
      linarith
    nlinarith [norm_nonneg (A.toEuclideanLin (z-x))]
  have hleft := moorePenroseInverse_mul_eq_one_of_rank_eq_card hA
  have hv := congrArg (fun v => (moorePenroseInverse A).toEuclideanLin v) hzero
  rw [← toEuclideanLin_mul_apply, hleft, toEuclideanLin_one_apply, map_zero] at hv
  exact sub_eq_zero.mp hv

end NLAlib
