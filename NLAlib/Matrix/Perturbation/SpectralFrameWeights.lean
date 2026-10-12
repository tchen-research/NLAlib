import NLAlib.Matrix.Spectral.Eigenframes
import NLAlib.Matrix.Perturbation.SpectralWeightGap
import NLAlib.Matrix.Subspaces.ProjectionGaps
/-!
# Actual overlap weights in a sorted eigenframe

Overlap row squares lie in `[0,1]`, have exactly the selected frame width as
total mass, and express compression traces and residual squares. This connects
the finite signed weight budget to actual population eigenspace perturbation.
Source: Yu–Wang–Samworth, Theorem 2, trace proof.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib

variable {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq m] [DecidableEq n] [DecidableEq r]

omit [Fintype n] [DecidableEq m] in
/-- Each overlap row has squared Euclidean length at most one for two
orthonormal frames. Yu–Wang–Samworth, Theorem 2, projection weights. -/
theorem sum_sq_overlap_row_le_one {U : Matrix m n ℝ} {Q : Matrix m r ℝ}
    (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q) (i : n) :
    (∑ j, (Uᵀ*Q) i j^2) ≤ 1 := by
  let u : m → ℝ := fun s => U s i
  have hcol : u ⬝ᵥ u=1 := by
    have hh := congrArg (fun T : Matrix n n ℝ => T i i) hU
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, u, dotProduct] using hh
  have hb := transpose_mulVec_dotProduct_self_le hQ u
  rw [hcol] at hb
  have heq : (∑ j, (Uᵀ*Q) i j^2)=(Qᵀ*ᵥu) ⬝ᵥ (Qᵀ*ᵥu) := by
    simp only [dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, u, ← sq]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [heq]
  exact hb

omit [DecidableEq n] in
/-- In a complete orthonormal frame, the overlap row squares have total
mass equal to the other frame's width. Yu–Wang–Samworth trace budget. -/
theorem sum_sum_sq_overlap_eq_card {U : Matrix m n ℝ} {Q : Matrix m r ℝ}
    (hUc : U*Uᵀ=1) (hQ : HasOrthonormalCols Q) :
    (∑ i, ∑ j, (Uᵀ*Q) i j^2)=(Fintype.card r : ℝ) := by
  have hUt : Uᵀᵀ*Uᵀ=1 := by simpa only [Matrix.transpose_transpose] using hUc
  rw [← frobSq_eq_sum_sq, frobSq_mul_left_of_orthonormal hUt, frobSq_frame_eq_card hQ]

omit [DecidableEq m] [DecidableEq r] in
/-- A spectral diagonalization turns an actual compression trace into
its eigenvalue-weighted overlap row squares. Yu–Wang–Samworth trace proof. -/
theorem trace_compression_eq_sum_mul_overlap_row_sq {A : Matrix m m ℝ}
    (U : Matrix m n ℝ) (Q : Matrix m r ℝ) (a : n → ℝ)
    (hA : A=U*Matrix.diagonal a*Uᵀ) :
    (Qᵀ*A*Q).trace=∑ i, a i*∑ j, (Uᵀ*Q) i j^2 := by
  let W := Uᵀ*Q
  have heq : Qᵀ*A*Q=Wᵀ*Matrix.diagonal a*W := by
    rw [hA]
    simp only [W, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [heq, Matrix.trace_mul_cycle, Matrix.trace_mul_comm (W*Wᵀ) (Matrix.diagonal a)]
  rw [Matrix.trace]
  change (∑ i, (Matrix.diagonal a*(W*Wᵀ)) i i)=_
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ← sq, W]

omit [DecidableEq m] in
/-- A selected column prefix has the corresponding prefix of overlap
weights as its overlap Frobenius square. Yu–Wang–Samworth trace budget. -/
theorem frobSq_prefix_transpose_mul_eq_sum_overlap_row_sq {N k : ℕ}
    (hk : k ≤ N) (U : Matrix m (Fin N) ℝ) (Q : Matrix m (Fin k) ℝ) :
    frobSq ((U.submatrix id (Fin.castLE hk))ᵀ*Q)=
      ∑ i : Fin k, ∑ j, (Uᵀ*Q) (Fin.castLE hk i) j^2 := by
  have heq : (U.submatrix id (Fin.castLE hk))ᵀ*Q=(Uᵀ*Q).submatrix (Fin.castLE hk) id := by
    rw [Matrix.transpose_submatrix]
    simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using
      Matrix.submatrix_mul_equiv Uᵀ Q (Fin.castLE hk) (Equiv.refl m) id
  rw [heq, frobSq_eq_sum_sq]
  rfl

variable {A : Matrix m m ℝ}

/-- The whole sorted spectral frame is complete, including dimension zero.
Yu–Wang–Samworth trace proof; equal cardinality supplies the reverse Gram identity. -/
theorem sortedEigenframe_mul_transpose_eq_one (hA : A.IsHermitian) :
    sortedEigenframe hA*(sortedEigenframe hA)ᵀ=1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (m := Fin (Fintype.card m)) (n := m) (R := ℝ)
    (A := (sortedEigenframe hA)ᵀ) (B := sortedEigenframe hA) (eq := by simp)).mp
      (hasOrthonormalCols_sortedEigenframe hA)

/-- The real symmetric matrix is diagonalized by its actual sorted frame.
Yu–Wang–Samworth trace proof, with the signed decreasing eigenvalue list. -/
theorem eq_sortedEigenframe_mul_diagonal_mul_transpose (hA : A.IsHermitian) :
    A=sortedEigenframe hA*Matrix.diagonal hA.eigenvalues₀*(sortedEigenframe hA)ᵀ := by
  let U := sortedEigenframe hA
  have hu : U*Uᵀ=1 := sortedEigenframe_mul_transpose_eq_one hA
  have heq : U*(Uᵀ*A*U)*Uᵀ=A := by
    calc
      _ = (U*Uᵀ)*A*(U*Uᵀ) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hu, Matrix.one_mul, Matrix.mul_one]
  calc
    A=U*(Uᵀ*A*U)*Uᵀ := heq.symm
    _ = _ := by rw [compression_sortedEigenframe_eq_diagonal]

/-- The named top frame attains the actual Ky Fan trace sum.
Yu–Wang–Samworth, Theorem 2, spectral projector optimality. -/
theorem trace_topEigenframe_compression_eq_prefix (hA : A.IsHermitian)
    {k : ℕ} (hk : k ≤ Fintype.card m) :
    ((topEigenframe hA hk)ᵀ*A*topEigenframe hA hk).trace=eigenvaluePrefix hA hk := by
  rw [compression_topEigenframe_eq_diagonal, Matrix.trace_diagonal]
  rfl

/-- Every competing width-`k` frame has no larger compression trace than
the named top frame. Yu–Wang–Samworth, Theorem 2, Ky Fan optimality. -/
theorem trace_compression_le_trace_topEigenframe (hA : A.IsHermitian)
    {k : ℕ} (hk : k ≤ Fintype.card m) {Q : Matrix m (Fin k) ℝ}
    (hQ : HasOrthonormalCols Q) :
    (Qᵀ*A*Q).trace ≤ ((topEigenframe hA hk)ᵀ*A*topEigenframe hA hk).trace := by
  have hh := trace_compression_le_eigenvaluePrefix hA hQ
  rw [trace_topEigenframe_compression_eq_prefix hA hk]
  have hpref : eigenvaluePrefix hA (card_le_card_of_hasOrthonormalCols hQ)=eigenvaluePrefix hA hk := by
    unfold eigenvaluePrefix
    let e : Fin (Fintype.card (Fin k)) ≃ Fin k := finCongr (Fintype.card_fin k)
    calc
      _ = ∑ i : Fin (Fintype.card (Fin k)), hA.eigenvalues₀ (Fin.castLE hk (e i)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply congrArg hA.eigenvalues₀
        exact Fin.ext rfl
      _ = _ := e.sum_comp (fun j : Fin k => hA.eigenvalues₀ (Fin.castLE hk j))
  exact hh.trans hpref.le

end NLAlib
