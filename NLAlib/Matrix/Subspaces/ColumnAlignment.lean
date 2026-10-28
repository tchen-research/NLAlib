import NLAlib.Matrix.Subspaces.OrderedFrames
import NLAlib.Matrix.Subspaces.ProjectionGaps

/-!
# Sign alignment from ordered flag projectors

Real unit columns can be aligned by a sign. Their distance is bounded by the
Frobenius distance of their line projectors. Adjacent leading flag differences
therefore control each ordered column, including the final column.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {m : Type*} [Fintype m]

/-- Two real unit columns admit a sign alignment controlled by the line-projector
distance. The statement includes orthogonal columns. -/
theorem exists_sign_frobNorm_sub_le_projector {U W : Matrix m (Fin 1) ℝ}
    (hU : HasOrthonormalCols U) (hW : HasOrthonormalCols W) :
    ∃ s : ℝ, s ^ 2 = 1 ∧ frobNorm (W - s • U) ≤ frobNorm (U * Uᵀ - W * Wᵀ) := by
  have hu : frobSq U = 1 := by simpa using frobSq_frame_eq_card hU
  have hw : frobSq W = 1 := by simpa using frobSq_frame_eq_card hW
  have hun : frobNorm U = 1 := by nlinarith [frobNorm_sq U, frobNorm_nonneg U]
  have hwn : frobNorm W = 1 := by nlinarith [frobNorm_sq W, frobNorm_nonneg W]
  have hc := abs_frobInner_le_frobNorm_mul_frobNorm W U
  rw [hun, hwn, mul_one] at hc
  have ho : frobSq (Uᵀ * W) = frobInner W U ^ 2 := by
    simp only [frobSq_eq_sum_sq, Fin.sum_univ_one, Matrix.mul_apply,
      Matrix.transpose_apply, frobInner_eq_sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hp : frobSq (U * Uᵀ - W * Wᵀ) = 2 - 2 * frobInner W U ^ 2 := by
    change frobSq (Uᴴ * W) = _ at ho
    change frobSq (U * Uᴴ - W * Wᴴ) = _
    rw [frobSq_sub, frobSq_mul_left_of_orthonormal hU,
      frobSq_mul_left_of_orthonormal hW, frobSq_conjTranspose, frobSq_conjTranspose,
      hu, hw, frobInner_frame_projectors_eq_frobSq_overlap, ho]
    ring
  let s : ℝ := if 0 ≤ frobInner W U then 1 else -1
  have hs : s ^ 2 = 1 := by dsimp [s]; split_ifs <;> norm_num
  have hsc : s * frobInner W U = |frobInner W U| := by
    dsimp [s]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  have hd : frobSq (W - s • U) = 2 - 2 * |frobInner W U| := by
    rw [frobSq_sub, frobSq_smul, frobInner_smul_right, hu, hw, hs]
    nlinarith [hsc]
  refine ⟨s, hs, ?_⟩
  have hcc : frobInner W U ^ 2 ≤ |frobInner W U| := by
    nlinarith [sq_abs (frobInner W U), abs_nonneg (frobInner W U)]
  have h1 := frobNorm_sq (W - s • U)
  have h2 := frobNorm_sq (U * Uᵀ - W * Wᵀ)
  rw [hd] at h1
  rw [hp] at h2
  nlinarith [frobNorm_nonneg (W - s • U), frobNorm_nonneg (U * Uᵀ - W * Wᵀ)]

omit [Fintype m] in
/-- The difference of successive leading projectors is the next line projector. -/
theorem headColumns_projector_succ_sub {n : ℕ} (Q : Matrix m (Fin n) ℝ) (j : Fin n) :
    headColumns Q (show j.val + 1 ≤ n by omega) *
        (headColumns Q (show j.val + 1 ≤ n by omega))ᵀ -
      headColumns Q j.isLt.le * (headColumns Q j.isLt.le)ᵀ =
        Q.submatrix id (fun _ : Fin 1 => j) * (Q.submatrix id (fun _ : Fin 1 => j))ᵀ := by
  ext a b
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    headColumns, Matrix.submatrix_apply, id_eq, Fin.sum_univ_one]
  rw [Fin.sum_univ_castSucc]
  have he : (∑ i : Fin j.val, Q a (Fin.castLE (by omega) i.castSucc) *
      Q b (Fin.castLE (by omega) i.castSucc)) =
      ∑ i : Fin j.val, Q a (Fin.castLE j.isLt.le i) * Q b (Fin.castLE j.isLt.le i) := rfl
  rw [he]
  have hj : Fin.castLE (show j.val + 1 ≤ n by omega) (Fin.last j.val) = j := Fin.ext rfl
  rw [hj]
  ring

/-- Uniform control of all leading flag projectors gives a simultaneous sign
alignment of the entire ordered frame. -/
theorem exists_signs_frobNorm_sub_le_of_head_projectors {n : ℕ}
    {Q W : Matrix m (Fin n) ℝ} (hQ : HasOrthonormalCols Q) (hW : HasOrthonormalCols W)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hgap : ∀ j (hj : j ≤ n), frobNorm
      (headColumns Q hj * (headColumns Q hj)ᵀ -
        headColumns W hj * (headColumns W hj)ᵀ) ≤ ε) :
    ∃ s : Fin n → ℝ, (∀ i, s i ^ 2 = 1) ∧
      frobNorm (W - Q * Matrix.diagonal s) ≤ Real.sqrt n * (2 * ε) := by
  have hcols (j : Fin n) := exists_sign_frobNorm_sub_le_projector
    (hQ.submatrix_cols (⟨fun _ : Fin 1 => j, fun _ _ _ => Subsingleton.elim _ _⟩))
    (hW.submatrix_cols (⟨fun _ : Fin 1 => j, fun _ _ _ => Subsingleton.elim _ _⟩))
  choose s hs hd using hcols
  have hb (j : Fin n) :
      frobNorm ((W - Q * Matrix.diagonal s).submatrix id (fun _ : Fin 1 => j)) ≤ 2 * ε := by
    have he : (W - Q * Matrix.diagonal s).submatrix id (fun _ : Fin 1 => j) =
        W.submatrix id (fun _ : Fin 1 => j) - s j • Q.submatrix id (fun _ : Fin 1 => j) := by
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.mul_diagonal,
        Matrix.smul_apply, smul_eq_mul, id_eq]
      ring
    rw [he]
    apply (hd j).trans
    change frobNorm (Q.submatrix id (fun _ : Fin 1 => j) *
      (Q.submatrix id (fun _ : Fin 1 => j))ᵀ - W.submatrix id (fun _ : Fin 1 => j) *
      (W.submatrix id (fun _ : Fin 1 => j))ᵀ) ≤ _
    rw [← headColumns_projector_succ_sub Q j, ← headColumns_projector_succ_sub W j]
    let P := fun (Z : Matrix m (Fin n) ℝ) (i : ℕ) (hi : i ≤ n) =>
      headColumns Z hi * (headColumns Z hi)ᵀ
    change frobNorm ((P Q (j.val+1) _ - P Q j.val _) -
      (P W (j.val+1) _ - P W j.val _)) ≤ _
    rw [show (P Q (j.val+1) _ - P Q j.val _) - (P W (j.val+1) _ - P W j.val _) =
      (P Q (j.val+1) _ - P W (j.val+1) _) - (P Q j.val _ - P W j.val _) by abel]
    exact (frobNorm_sub_le _ _).trans (by linarith [hgap (j.val+1) (by omega), hgap j.val j.isLt.le])
  refine ⟨s, hs, ?_⟩
  have hf : frobNorm (W - Q * Matrix.diagonal s) ^ 2 ≤ (n : ℝ) * (2 * ε) ^ 2 := by
    rw [frobNorm_sq, frobSq_eq_sum_frobSq_col]
    calc
      _ ≤ ∑ j : Fin n, (2 * ε) ^ 2 := Finset.sum_le_sum fun j _ => by
        rw [← frobNorm_sq]
        exact pow_le_pow_left₀ (frobNorm_nonneg _) (hb j) 2
      _ = _ := by simp
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hp : 0 ≤ Real.sqrt n * (2 * ε) := by positivity
  nlinarith [frobNorm_nonneg (W - Q * Matrix.diagonal s)]

end NLAlib
