import NLAlib.Matrix.SVD
import NLAlib.Matrix.Pseudoinverse

/-!
# Moore–Penrose inverses of real rectangular matrices

The inverse constructed here is distinct from the full-rank formulas `pinvL` and
`pinvR`. It exists for arbitrary finite row and column types, including empty
types, and for rank-deficient matrices. The construction uses NLAlib's real SVD
and scalar reciprocals, with zero singular values sent to zero. The four Penrose
identities characterize it uniquely and identify it with the existing full-rank
formulas when their Gram matrices are invertible.

Source: Horn–Johnson, Matrix Analysis, §7.3. Atlas: `pseudoinverse`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

/-- The four Penrose identities for a real matrix and a candidate pseudoinverse.
No rank assumption is imposed. Horn–Johnson §7.3; atlas `pseudoinverse`.
atlas: pseudoinverse -/
structure IsMoorePenroseInverse {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (B : Matrix n m ℝ) : Prop where
  /-- The first Penrose identity, `A B A = A`. -/
  mul_mul_eq : A * B * A = A
  /-- The second Penrose identity, `B A B = B`. -/
  inv_mul_inv_eq : B * A * B = B
  /-- The image-space projector is symmetric. -/
  transpose_mul_eq : (A * B)ᵀ = A * B
  /-- The row-space projector is symmetric. -/
  transpose_inv_mul_eq : (B * A)ᵀ = B * A

namespace IsMoorePenroseInverse

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  {A : Matrix m n ℝ} {B C : Matrix n m ℝ}

/-- The Moore–Penrose inverse is unique, also for zero-rank and empty matrices.
Horn–Johnson §7.3; atlas `pseudoinverse`.
atlas: pseudoinverse -/
theorem unique (hB : IsMoorePenroseInverse A B) (hC : IsMoorePenroseInverse A C) :
    B = C := by
  have hBA : (B * A) * (C * A) = B * A := by
    calc
      (B * A) * (C * A) = B * (A * C * A) := by simp only [Matrix.mul_assoc]
      _ = B * A := by rw [hC.mul_mul_eq]
  have hCA : (C * A) * (B * A) = C * A := by
    calc
      (C * A) * (B * A) = C * (A * B * A) := by simp only [Matrix.mul_assoc]
      _ = C * A := by rw [hB.mul_mul_eq]
  have hBAeq : B * A = C * A := by
    have ht := congrArg Matrix.transpose hBA
    simp only [Matrix.transpose_mul, hC.transpose_inv_mul_eq,
      hB.transpose_inv_mul_eq] at ht
    rw [hCA] at ht
    exact ht.symm
  have hAB : (A * B) * (A * C) = A * C := by
    calc
      (A * B) * (A * C) = (A * B * A) * C := by simp only [Matrix.mul_assoc]
      _ = A * C := by rw [hB.mul_mul_eq]
  have hAC : (A * C) * (A * B) = A * B := by
    calc
      (A * C) * (A * B) = (A * C * A) * B := by simp only [Matrix.mul_assoc]
      _ = A * B := by rw [hC.mul_mul_eq]
  have hABeq : A * B = A * C := by
    have ht := congrArg Matrix.transpose hAB
    simp only [Matrix.transpose_mul, hC.transpose_mul_eq, hB.transpose_mul_eq] at ht
    rw [hAC] at ht
    exact ht
  calc
    B = B * A * B := hB.inv_mul_inv_eq.symm
    _ = C * A * B := by rw [hBAeq]
    _ = C * (A * B) := Matrix.mul_assoc _ _ _
    _ = C * (A * C) := by rw [hABeq]
    _ = C * A * C := (Matrix.mul_assoc _ _ _).symm
    _ = C := hC.inv_mul_inv_eq

/-- Exchanging a matrix and its Moore–Penrose inverse preserves the four
identities. Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem swap (h : IsMoorePenroseInverse A B) : IsMoorePenroseInverse B A :=
  ⟨h.inv_mul_inv_eq, h.mul_mul_eq, h.transpose_inv_mul_eq, h.transpose_mul_eq⟩

/-- Transposing both matrices preserves the Penrose identities.
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem transpose (h : IsMoorePenroseInverse A B) :
    IsMoorePenroseInverse Aᵀ Bᵀ := by
  constructor
  · simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using
      congrArg Matrix.transpose h.mul_mul_eq
  · simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using
      congrArg Matrix.transpose h.inv_mul_inv_eq
  · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
      h.transpose_inv_mul_eq.symm
  · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
      h.transpose_mul_eq.symm

/-- Equivalent row and column indexing preserves the Penrose identities.
This transports the SVD construction to arbitrary finite index types. -/
theorem submatrix (h : IsMoorePenroseInverse A B) (em : p ≃ m) (en : q ≃ n) :
    IsMoorePenroseInverse (A.submatrix em en) (B.submatrix en em) := by
  constructor
  · simpa only [Matrix.submatrix_mul_equiv] using
      congrArg (fun M : Matrix m n ℝ => M.submatrix em en) h.mul_mul_eq
  · simpa only [Matrix.submatrix_mul_equiv] using
      congrArg (fun M : Matrix n m ℝ => M.submatrix en em) h.inv_mul_inv_eq
  · simpa only [Matrix.submatrix_mul_equiv, Matrix.transpose_submatrix] using
      congrArg (fun M : Matrix m m ℝ => M.submatrix em em) h.transpose_mul_eq
  · simpa only [Matrix.submatrix_mul_equiv, Matrix.transpose_submatrix] using
      congrArg (fun M : Matrix n n ℝ => M.submatrix en en) h.transpose_inv_mul_eq

/-- Orthogonal changes of row and column coordinates transport a Moore–Penrose
inverse by the reversed changes. Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem orthogonal_transform [DecidableEq m] [DecidableEq n]
    (h : IsMoorePenroseInverse A B) (U : Matrix m m ℝ) (V : Matrix n n ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    IsMoorePenroseInverse (U * A * Vᵀ) (V * B * Uᵀ) := by
  constructor
  · calc
      (U * A * Vᵀ) * (V * B * Uᵀ) * (U * A * Vᵀ) =
          U * (A * (Vᵀ * V) * B * (Uᵀ * U) * A) * Vᵀ := by
            simp only [Matrix.mul_assoc]
      _ = U * A * Vᵀ := by
        rw [hU, hV, Matrix.mul_one, Matrix.mul_one, h.mul_mul_eq]
  · calc
      (V * B * Uᵀ) * (U * A * Vᵀ) * (V * B * Uᵀ) =
          V * (B * (Uᵀ * U) * A * (Vᵀ * V) * B) * Uᵀ := by
            simp only [Matrix.mul_assoc]
      _ = V * B * Uᵀ := by
        rw [hU, hV, Matrix.mul_one, Matrix.mul_one, h.inv_mul_inv_eq]
  · have he : (U * A * Vᵀ) * (V * B * Uᵀ) = U * (A * B) * Uᵀ := by
      calc
        _ = U * (A * (Vᵀ * V) * B) * Uᵀ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hV, Matrix.mul_one]
    rw [he]
    calc
      (U * (A * B) * Uᵀ)ᵀ = U * (A * B)ᵀ * Uᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = U * (A * B) * Uᵀ := by rw [h.transpose_mul_eq]
  · have he : (V * B * Uᵀ) * (U * A * Vᵀ) = V * (B * A) * Vᵀ := by
      calc
        _ = V * (B * (Uᵀ * U) * A) * Vᵀ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU, Matrix.mul_one]
    rw [he]
    calc
      (V * (B * A) * Vᵀ)ᵀ = V * (B * A)ᵀ * Vᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = V * (B * A) * Vᵀ := by rw [h.transpose_inv_mul_eq]

/-- `A B` is an idempotent image-space projector. Together with the third
Penrose identity this is an orthogonal projector. -/
theorem mul_isIdempotentElem (h : IsMoorePenroseInverse A B) :
    IsIdempotentElem (A * B) := by
  change (A * B) * (A * B) = A * B
  calc
    _ = (A * B * A) * B := by simp only [Matrix.mul_assoc]
    _ = A * B := by rw [h.mul_mul_eq]

/-- `B A` is an idempotent row-space projector. -/
theorem inv_mul_isIdempotentElem (h : IsMoorePenroseInverse A B) :
    IsIdempotentElem (B * A) := h.swap.mul_isIdempotentElem

/-- The fixed vectors of the image-space projector are exactly the image of
the original matrix, including rank-deficient and empty matrices. -/
theorem mulVec_eq_self_iff (h : IsMoorePenroseInverse A B) (x : m → ℝ) :
    (A * B) *ᵥ x = x ↔ ∃ y : n → ℝ, A *ᵥ y = x := by
  constructor
  · intro hx
    exact ⟨B *ᵥ x, by rw [Matrix.mulVec_mulVec]; exact hx⟩
  · rintro ⟨y, rfl⟩
    rw [Matrix.mulVec_mulVec, h.mul_mul_eq]

/-- The image of `A B` equals the image of `A`: the symmetric idempotent
`A B` is the orthogonal projector onto the original column space. -/
theorem range_mul_eq (h : IsMoorePenroseInverse A B) :
    LinearMap.range (A * B).mulVecLin = LinearMap.range A.mulVecLin := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨B *ᵥ y, by simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using hy⟩
  · rintro ⟨y, rfl⟩
    exact ⟨A *ᵥ y, by simp only [Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, h.mul_mul_eq]⟩

/-- The Moore–Penrose inverse of a column Gram matrix is the corresponding
Gram matrix of the inverse. This identity holds at every rank.
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem transpose_mul_self (h : IsMoorePenroseInverse A B) :
    IsMoorePenroseInverse (Aᵀ * A) (B * Bᵀ) := by
  have hCG : (B * Bᵀ) * (Aᵀ * A) = B * A := by
    calc
      _ = B * (A * B)ᵀ * A := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = B * (A * B) * A := by rw [h.transpose_mul_eq]
      _ = (B * A * B) * A := by simp only [Matrix.mul_assoc]
      _ = B * A := by rw [h.inv_mul_inv_eq]
  have hGC : (Aᵀ * A) * (B * Bᵀ) = B * A := by
    calc
      _ = ((B * Bᵀ) * (Aᵀ * A))ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
      _ = (B * A)ᵀ := by rw [hCG]
      _ = B * A := h.transpose_inv_mul_eq
  constructor
  · calc
      _ = (Aᵀ * A) * ((B * Bᵀ) * (Aᵀ * A)) := Matrix.mul_assoc _ _ _
      _ = (Aᵀ * A) * (B * A) := by rw [hCG]
      _ = Aᵀ * (A * B * A) := by simp only [Matrix.mul_assoc]
      _ = Aᵀ * A := by rw [h.mul_mul_eq]
  · calc
      _ = (B * A) * (B * Bᵀ) := by rw [hCG]
      _ = (B * A * B) * Bᵀ := by simp only [Matrix.mul_assoc]
      _ = B * Bᵀ := by rw [h.inv_mul_inv_eq]
  · rw [hGC]
    exact h.transpose_inv_mul_eq
  · rw [hCG]
    exact h.transpose_inv_mul_eq

end IsMoorePenroseInverse

private theorem rectDiag_mul_reversed (m n : ℕ) (σ τ : ℕ → ℝ) :
    (rectDiag σ : Matrix (Fin m) (Fin n) ℝ) *
        (rectDiag τ : Matrix (Fin n) (Fin m) ℝ) =
      Matrix.diagonal (fun i : Fin m => if (i : ℕ) < n then σ i * τ i else 0) := by
  ext i j
  simp only [Matrix.mul_apply, rectDiag_apply, Matrix.diagonal_apply]
  by_cases hin : (i : ℕ) < n
  · rw [Finset.sum_eq_single ⟨i, hin⟩]
    · by_cases hij : i = j
      · subst j
        simp [hin]
      · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
        simp [hij, hij']
    · intro k _ hki
      rw [if_neg (fun h => hki (Fin.ext h.symm)), zero_mul]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hin]
    · intro k _
      rw [if_neg (fun (h : (i : ℕ) = k) => hin (h.symm ▸ k.isLt)), zero_mul]

private theorem rectDiag_mul_inverse_mul (m n : ℕ) (σ : ℕ → ℝ) :
    (rectDiag σ : Matrix (Fin m) (Fin n) ℝ) *
        (rectDiag (fun k => (σ k)⁻¹) : Matrix (Fin n) (Fin m) ℝ) *
        (rectDiag σ : Matrix (Fin m) (Fin n) ℝ) =
      (rectDiag σ : Matrix (Fin m) (Fin n) ℝ) := by
  rw [rectDiag_mul_reversed]
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [rectDiag_apply]
  by_cases hij : (i : ℕ) = j
  · have hin : (i : ℕ) < n := by simpa only [hij] using j.isLt
    simp only [if_pos hin, if_pos hij]
    by_cases hσ : σ i = 0
    · simp [hσ]
    · rw [mul_inv_cancel₀ hσ, one_mul]
  · simp [hij]

private theorem isMoorePenroseInverse_rectDiag (m n : ℕ) (σ : ℕ → ℝ) :
    IsMoorePenroseInverse (rectDiag σ : Matrix (Fin m) (Fin n) ℝ)
      (rectDiag (fun k => (σ k)⁻¹) : Matrix (Fin n) (Fin m) ℝ) := by
  constructor
  · exact rectDiag_mul_inverse_mul m n σ
  · simpa only [inv_inv] using rectDiag_mul_inverse_mul n m (fun k => (σ k)⁻¹)
  · rw [rectDiag_mul_reversed]
    exact (Matrix.isSymm_diagonal _).eq
  · rw [rectDiag_mul_reversed]
    exact (Matrix.isSymm_diagonal _).eq

/-- An SVD produces the Moore–Penrose inverse by reciprocating its nonzero
singular values; scalar `0⁻¹ = 0` handles zero singular values.
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem IsSVD.isMoorePenroseInverse {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ}
    (h : IsSVD A U V) :
    IsMoorePenroseInverse A
      (V * (rectDiag (fun k => (singularValues A k)⁻¹) : Matrix (Fin n) (Fin m) ℝ) * Uᵀ) := by
  have hP := (isMoorePenroseInverse_rectDiag m n (singularValues A)).orthogonal_transform
    U V h.transpose_mul_left h.transpose_mul_right
  rw [← h.eq] at hP
  exact hP

/-- Every real rectangular matrix has a Moore–Penrose inverse, with arbitrary
finite row and column types and without a rank or nonempty assumption.
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem exists_isMoorePenroseInverse {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ∃ B : Matrix n m ℝ, IsMoorePenroseInverse A B := by
  classical
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  let A' : Matrix (Fin (Fintype.card m)) (Fin (Fintype.card n)) ℝ :=
    A.submatrix em.symm en.symm
  obtain ⟨U, V, h⟩ := exists_isSVD A'
  let B' : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card m)) ℝ :=
    V * (rectDiag (fun k => (singularValues A' k)⁻¹) :
      Matrix (Fin (Fintype.card n)) (Fin (Fintype.card m)) ℝ) * Uᵀ
  have hB' : IsMoorePenroseInverse A' B' := h.isMoorePenroseInverse
  refine ⟨B'.submatrix en em, ?_⟩
  have hAA : A'.submatrix em en = A := by
    ext i j
    change A (em.symm (em i)) (en.symm (en j)) = A i j
    simp only [Equiv.symm_apply_apply]
  have hTransport := hB'.submatrix em en
  rw [hAA] at hTransport
  exact hTransport

/-- The unique Moore–Penrose inverse of a real rectangular matrix. This is
defined for rank-deficient and empty matrices and preserves the existing
full-rank formulas `pinvL` and `pinvR` as separate definitions.
Horn–Johnson §7.3; atlas `pseudoinverse`.
atlas: pseudoinverse -/
def moorePenroseInverse {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : Matrix n m ℝ := (exists_isMoorePenroseInverse A).choose

/-- The constructed Moore–Penrose inverse satisfies all four Penrose identities.
Horn–Johnson §7.3; atlas `pseudoinverse`.
atlas: pseudoinverse -/
theorem isMoorePenroseInverse {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : IsMoorePenroseInverse A (moorePenroseInverse A) :=
  (exists_isMoorePenroseInverse A).choose_spec

/-- The first Penrose identity for every real rectangular matrix. -/
theorem mul_moorePenroseInverse_mul {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : A * moorePenroseInverse A * A = A :=
  (isMoorePenroseInverse A).mul_mul_eq

/-- The second Penrose identity for every real rectangular matrix. -/
theorem moorePenroseInverse_mul_moorePenroseInverse {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : moorePenroseInverse A * A * moorePenroseInverse A =
      moorePenroseInverse A := (isMoorePenroseInverse A).inv_mul_inv_eq

/-- The column-space projector obtained from the Moore–Penrose inverse is symmetric. -/
theorem mul_moorePenroseInverse_isSymm {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : (A * moorePenroseInverse A).IsSymm :=
  (isMoorePenroseInverse A).transpose_mul_eq

/-- The row-space projector obtained from the Moore–Penrose inverse is symmetric. -/
theorem moorePenroseInverse_mul_isSymm {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : (moorePenroseInverse A * A).IsSymm :=
  (isMoorePenroseInverse A).transpose_inv_mul_eq

/-- The Moore–Penrose column-space projector is idempotent at every rank. -/
theorem mul_moorePenroseInverse_isIdempotentElem {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : IsIdempotentElem (A * moorePenroseInverse A) :=
  (isMoorePenroseInverse A).mul_isIdempotentElem

/-- The Moore–Penrose row-space projector is idempotent at every rank. -/
theorem moorePenroseInverse_mul_isIdempotentElem {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : IsIdempotentElem (moorePenroseInverse A * A) :=
  (isMoorePenroseInverse A).inv_mul_isIdempotentElem

/-- The image of the Moore–Penrose column-space projector is exactly the
original column space. This includes rank-deficient and empty matrices.
atlas: pseudoinverse -/
theorem range_mul_moorePenroseInverse_eq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : LinearMap.range (A * moorePenroseInverse A).mulVecLin =
      LinearMap.range A.mulVecLin := (isMoorePenroseInverse A).range_mul_eq

/-- Any real SVD computes the same Moore–Penrose inverse, independently of the
choice of singular vectors. Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem IsSVD.moorePenroseInverse_eq {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U V) :
    moorePenroseInverse A =
      V * (rectDiag (fun k => (singularValues A k)⁻¹) : Matrix (Fin n) (Fin m) ℝ) * Uᵀ :=
  (NLAlib.isMoorePenroseInverse A).unique h.isMoorePenroseInverse

/-- The existing left full-rank formula satisfies the four Penrose identities
when its column Gram matrix is invertible. -/
theorem isMoorePenroseInverse_pinvL {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (h : IsUnit (Aᵀ * A)) : IsMoorePenroseInverse A (pinvL A) :=
  ⟨mul_pinvL_mul h, pinvL_mul_pinvL h, (mul_pinvL_isSymm A).eq,
    (pinvL_mul_isSymm h).eq⟩

/-- The existing right full-rank formula satisfies the four Penrose identities
when its row Gram matrix is invertible. -/
theorem isMoorePenroseInverse_pinvR {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n ℝ) (h : IsUnit (A * Aᵀ)) : IsMoorePenroseInverse A (pinvR A) :=
  ⟨mul_pinvR_mul h, pinvR_mul_pinvR h, (mul_pinvR_isSymm h).eq,
    (pinvR_mul_isSymm A).eq⟩

/-- The general Moore–Penrose inverse agrees with `pinvL` for full column rank.
atlas: pseudoinverse -/
theorem moorePenroseInverse_eq_pinvL {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (h : IsUnit (Aᵀ * A)) : moorePenroseInverse A = pinvL A :=
  (isMoorePenroseInverse A).unique (isMoorePenroseInverse_pinvL A h)

/-- The general Moore–Penrose inverse agrees with `pinvR` for full row rank.
atlas: pseudoinverse -/
theorem moorePenroseInverse_eq_pinvR {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n ℝ) (h : IsUnit (A * Aᵀ)) : moorePenroseInverse A = pinvR A :=
  (isMoorePenroseInverse A).unique (isMoorePenroseInverse_pinvR A h)

/-- Transpose commutes with the general Moore–Penrose inverse. -/
theorem moorePenroseInverse_transpose {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : moorePenroseInverse Aᵀ = (moorePenroseInverse A)ᵀ :=
  (isMoorePenroseInverse Aᵀ).unique (isMoorePenroseInverse A).transpose

/-- Taking the Moore–Penrose inverse twice recovers the original matrix.
atlas: pseudoinverse -/
theorem moorePenroseInverse_moorePenroseInverse {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : moorePenroseInverse (moorePenroseInverse A) = A :=
  (isMoorePenroseInverse (moorePenroseInverse A)).unique (isMoorePenroseInverse A).swap

/-- The Moore–Penrose inverse of a zero matrix is zero, for any finite shape. -/
@[simp] theorem moorePenroseInverse_zero {m n : Type*} [Fintype m] [Fintype n] :
    moorePenroseInverse (0 : Matrix m n ℝ) = 0 := by
  apply (isMoorePenroseInverse (0 : Matrix m n ℝ)).unique
  constructor <;> simp

/-- A matrix has zero Moore–Penrose inverse exactly when the matrix is zero.
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
@[simp] theorem moorePenroseInverse_eq_zero_iff {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : moorePenroseInverse A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hA := mul_moorePenroseInverse_mul A
    rw [h, Matrix.mul_zero, Matrix.zero_mul] at hA
    exact hA.symm
  · rintro rfl
    exact moorePenroseInverse_zero

/-- The general inverse of `Aᵀ A` is `A† (A†)ᵀ`, including singular Gram
matrices. Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem moorePenroseInverse_transpose_mul_self {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : moorePenroseInverse (Aᵀ * A) =
      moorePenroseInverse A * (moorePenroseInverse A)ᵀ :=
  (isMoorePenroseInverse (Aᵀ * A)).unique (isMoorePenroseInverse A).transpose_mul_self

/-- The general inverse of `A Aᵀ` is `(A†)ᵀ A†`, including singular Gram
matrices. Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem moorePenroseInverse_self_mul_transpose {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : moorePenroseInverse (A * Aᵀ) =
      (moorePenroseInverse A)ᵀ * moorePenroseInverse A := by
  simpa only [Matrix.transpose_transpose, moorePenroseInverse_transpose] using
    moorePenroseInverse_transpose_mul_self Aᵀ

/-- The squared Frobenius norm of the general inverse equals the trace of
the general inverse of the row Gram matrix. Unlike an ordinary inverse of a
singular Gram matrix, this preserves all positive singular-value contributions.
Horn–Johnson §7.3; atlas `pseudoinverse`.
atlas: pseudoinverse -/
theorem frobSq_moorePenroseInverse_eq_trace_moorePenroseInverse
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) :
    frobSq (moorePenroseInverse A) = (moorePenroseInverse (A * Aᵀ)).trace := by
  rw [frobSq, frobInner_eq_trace, moorePenroseInverse_self_mul_transpose]

/-- The squared spectral norm of the general inverse equals the spectral
norm of the general inverse of the row Gram matrix, at every rank.
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem specNorm_moorePenroseInverse_sq {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    specNorm (moorePenroseInverse A) ^ 2 = specNorm (moorePenroseInverse (A * Aᵀ)) := by
  rw [moorePenroseInverse_self_mul_transpose]
  unfold specNorm
  rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self,
    Matrix.conjTranspose_eq_transpose_of_trivial]

end NLAlib
