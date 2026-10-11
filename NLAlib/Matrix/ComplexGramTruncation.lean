import NLAlib.Matrix.ComplexEckartYoung

/-!
# Actual complex Gram-eigenvector truncation

Truncating the right singular-vector eigensystem of `AᴴA` gives a literal
rank-bounded matrix with squared Frobenius error equal to the sorted Gram
tail. Source: Horn–Johnson Theorem 7.4.9; `sa:volume-theorem`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped Classical Matrix Matrix.Norms.Frobenius ComplexOrder
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The actual zero-one mask for the first `k` sorted Gram eigenvectors.
Source: the right singular-vector cutoff, `sa:volume-theorem`. -/
def complexGramTopMask (_A : Matrix m n ℂ) (k : ℕ) : n → ℂ := fun j =>
  if ((Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card n) ≃ n).symm j : ℕ) < k
    then 1 else 0

/-- The actual orthogonal projector onto the first `k` Gram eigenvectors.
Source: complex SVD truncation, `sa:volume-theorem`. -/
def complexGramTopProjector (A : Matrix m n ℂ) (k : ℕ) : Matrix n n ℂ :=
  let V : Matrix n n ℂ := (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary
  V * Matrix.diagonal (complexGramTopMask A k) * Vᴴ

/-- The genuine complex SVD truncation, formed by cutting off the sorted
right Gram eigenvectors. Source: `sa:volume-theorem`, its matrix `A_k`. -/
def complexTruncatedSVD (A : Matrix m n ℂ) (k : ℕ) : Matrix m n ℂ :=
  A * complexGramTopProjector A k

/-- The actual Gram cutoff projector is Hermitian.
Source: `sa:volume-theorem`, complex singular-vector cutoff. -/
theorem complexGramTopProjector_isHermitian (A : Matrix m n ℂ) (k : ℕ) :
    (complexGramTopProjector A k).IsHermitian := by
  let V : Matrix n n ℂ := (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary
  have hD : (Matrix.diagonal (complexGramTopMask A k)).IsHermitian := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq, complexGramTopMask]
      split_ifs <;> simp
    · simp [Matrix.conjTranspose_apply, hij, Ne.symm hij]
  simpa only [complexGramTopProjector, V, Matrix.conjTranspose_conjTranspose] using
    Matrix.isHermitian_conjTranspose_mul_mul Vᴴ hD

/-- The actual Gram cutoff projector is idempotent.
Source: `sa:volume-theorem`, complex singular-vector cutoff. -/
theorem complexGramTopProjector_mul_self (A : Matrix m n ℂ) (k : ℕ) :
    complexGramTopProjector A k * complexGramTopProjector A k = complexGramTopProjector A k := by
  let V : Matrix n n ℂ := (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary
  let D := Matrix.diagonal (complexGramTopMask A k)
  have hV : Vᴴ * V = 1 := Unitary.coe_star_mul_self
    (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary
  have hD : D * D = D := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    simp [complexGramTopMask]
  change (V * D * Vᴴ) * (V * D * Vᴴ) = V * D * Vᴴ
  calc
    _ = V * (D * (Vᴴ * V) * D) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.mul_one, hD]

/-- The true complex singular-vector cutoff has rank at most `k`, for every
cutoff including zero and cutoffs beyond the matrix dimensions.
Source: `sa:volume-theorem`, actual rank of the attaining witness. -/
theorem rank_complexGramTopProjector_le (A : Matrix m n ℂ) (k : ℕ) :
    (complexGramTopProjector A k).rank ≤ k := by
  let V : Matrix n n ℂ := (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorUnitary
  let D := Matrix.diagonal (complexGramTopMask A k)
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hD : D.rank ≤ k := by
    rw [Matrix.rank_diagonal]
    let f : {j : n // complexGramTopMask A k j ≠ 0} → Fin k := fun j =>
      ⟨(e.symm j.val : ℕ), by
        by_contra hnot
        exact j.prop (by simp only [complexGramTopMask, e, if_neg hnot])⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply e.symm.injective
      apply Fin.ext
      exact congrArg (fun z : Fin k => z.val) hxy
    exact (Fintype.card_le_of_injective f hf).trans_eq (Fintype.card_fin k)
  exact ((Matrix.rank_mul_le_left (V * D) Vᴴ).trans (Matrix.rank_mul_le_right V D)).trans hD

/-- The literal complex SVD truncation is a valid rank-at-most-`k` competitor.
Source: Horn–Johnson Theorem 7.4.9; `sa:volume-theorem`. -/
theorem rank_complexTruncatedSVD_le (A : Matrix m n ℂ) (k : ℕ) :
    (complexTruncatedSVD A k).rank ≤ k :=
  (Matrix.rank_mul_le_right A _).trans (rank_complexGramTopProjector_le A k)

/-- The literal complex singular-vector truncation attains the exact sorted
Gram Frobenius tail. Source: Horn–Johnson Theorem 7.4.9; `sa:volume-theorem`.
atlas: volume-sampling (partial) -/
theorem frobenius_norm_sq_sub_complexTruncatedSVD_eq_tail
    (A : Matrix m n ℂ) (k : ℕ) :
    ‖A - complexTruncatedSVD A k‖ ^ 2 = complexGramTail A k := by
  let hG := Matrix.isHermitian_conjTranspose_mul_self A
  let V : Matrix n n ℂ := hG.eigenvectorUnitary
  let D := Matrix.diagonal (complexGramTopMask A k)
  let P := complexGramTopProjector A k
  let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hV : Vᴴ * V = 1 := Unitary.coe_star_mul_self hG.eigenvectorUnitary
  have hrot : Vᴴ * P * V = D := by
    change Vᴴ * (V * D * Vᴴ) * V = D
    calc
      _ = (Vᴴ * V) * D * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.one_mul, Matrix.mul_one]
  have hcaptured : ‖A * P‖ ^ 2 =
      ∑ i : Fin (Fintype.card n), if (i : ℕ) < k then complexGramEigenvalues A i else 0 := by
    rw [frobenius_norm_sq_mul_projector_eq_sum_gram_eigenvalues A P
      (complexGramTopProjector_isHermitian A k) (complexGramTopProjector_mul_self A k)]
    change (∑ i : Fin (Fintype.card n), complexGramEigenvalues A i * ((Vᴴ * P * V) (e i) (e i)).re) = _
    rw [hrot]
    apply Finset.sum_congr rfl
    intro i _
    simp only [D, Matrix.diagonal_apply_eq, complexGramTopMask, e,
      Equiv.symm_apply_apply]
    by_cases hi : (i : ℕ) < k <;> simp only [hi, if_pos, if_false,
      Complex.one_re, Complex.zero_re, mul_one, mul_zero]
  have htotal : ‖A‖ ^ 2 = ∑ i : Fin (Fintype.card n), complexGramEigenvalues A i := by
    rw [frobenius_norm_sq_eq_re_trace_conjTranspose_mul, hG.trace_eq_sum_eigenvalues,
      Complex.re_sum]
    change (∑ j : n, hG.eigenvalues j) = _
    rw [← e.sum_comp hG.eigenvalues]
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply, complexGramEigenvalues]
  have hsplit : ‖A‖ ^ 2 =
      (∑ i : Fin (Fintype.card n), if (i : ℕ) < k then complexGramEigenvalues A i else 0) +
        complexGramTail A k := by
    rw [htotal, complexGramTail, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : ℕ) < k
    · simp only [if_pos hi, if_neg (not_le.mpr hi), add_zero]
    · simp only [if_neg hi, if_pos (not_lt.mp hi), zero_add]
  have hpyth := frobenius_norm_sq_eq_right_projection_add_residual P
    (complexGramTopProjector_isHermitian A k) (complexGramTopProjector_mul_self A k) A
  have hres : A - complexTruncatedSVD A k = A * (1 - P) := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    rfl
  rw [hres]
  linarith

end NLAlib
