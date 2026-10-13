import NLAlib.Matrix.Basic.PenroseIdentities
import NLAlib.Matrix.Spectral.SVD
import NLAlib.Matrix.Basic.Pseudoinverse
/-!
# Moore–Penrose inverses of rectangular matrices over `ℝ` or `ℂ`

The inverse constructed here (`moorePenroseInverse`, characterised by the Penrose identities
`IsMoorePenroseInverse` of `Matrix/Basic/PenroseIdentities.lean`) is stated over `[RCLike 𝕜]` and is
distinct from the full-rank formulas `pinvL` and `pinvR`. It exists for arbitrary finite row and
column types, including empty types, and for rank-deficient matrices. The construction uses the
SVD `A = U Σ Vᴴ` (`exists_isSVD`) and scalar reciprocals of the singular values, with zero singular
values sent to zero, transported by `IsMoorePenroseInverse.unitary_transform`. The four Penrose
identities characterize it uniquely and identify it with the full-rank formulas when their Gram
matrices are invertible.

Every statement is written with `ᴴ` (F1: no real twins; over `ℝ` the `@[simp]` lemma
`Matrix.conjTranspose_eq_transpose_of_trivial` gives the `ᵀ` forms). The real row projector
`A⁺A` is a quadratic-form contraction (`dotProduct_self_sub_moorePenroseInverse_mul_mulVec`), and
`‖A⁺‖⁻¹` bounds `A` below on `range Aᵀ` (`inv_specNorm_moorePenroseInverse_sq_mul_dotProduct_le`).

Source: Horn–Johnson, Matrix Analysis, §7.3. Atlas: `pseudoinverse`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

private theorem rectDiag_mul_reversed (m n : ℕ) (σ τ : ℕ → ℝ) :
    (rectDiag σ : Matrix (Fin m) (Fin n) 𝕜) *
        (rectDiag τ : Matrix (Fin n) (Fin m) 𝕜) =
      Matrix.diagonal (fun i : Fin m => (((if (i : ℕ) < n then σ i * τ i else 0 : ℝ)) : 𝕜)) := by
  ext i j
  simp only [Matrix.mul_apply, rectDiag_apply_ofReal, Matrix.diagonal_apply]
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
    (rectDiag σ : Matrix (Fin m) (Fin n) 𝕜) *
        (rectDiag (fun k => (σ k)⁻¹) : Matrix (Fin n) (Fin m) 𝕜) *
        (rectDiag σ : Matrix (Fin m) (Fin n) 𝕜) =
      (rectDiag σ : Matrix (Fin m) (Fin n) 𝕜) := by
  rw [rectDiag_mul_reversed]
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [rectDiag_apply_ofReal]
  by_cases hij : (i : ℕ) = j
  · have hin : (i : ℕ) < n := by simpa only [hij] using j.isLt
    simp only [if_pos hin, if_pos hij]
    by_cases hσ : σ i = 0
    · simp [hσ]
    · rw [mul_inv_cancel₀ hσ, RCLike.ofReal_one, one_mul]
  · simp [hij]

private theorem isHermitian_diagonal_ofReal {k : Type*} [DecidableEq k] (d : k → ℝ) :
    (Matrix.diagonal fun i => (d i : 𝕜)).IsHermitian :=
  Matrix.isHermitian_diagonal_of_self_adjoint _ (by
    funext i
    simp [RCLike.star_def])

private theorem isMoorePenroseInverse_rectDiag (m n : ℕ) (σ : ℕ → ℝ) :
    IsMoorePenroseInverse (rectDiag σ : Matrix (Fin m) (Fin n) 𝕜)
      (rectDiag (fun k => (σ k)⁻¹) : Matrix (Fin n) (Fin m) 𝕜) := by
  refine ⟨rectDiag_mul_inverse_mul m n σ, ?_, ?_, ?_⟩
  · simpa only [inv_inv] using rectDiag_mul_inverse_mul (𝕜 := 𝕜) n m (fun k => (σ k)⁻¹)
  · rw [rectDiag_mul_reversed]
    exact isHermitian_diagonal_ofReal _
  · rw [rectDiag_mul_reversed]
    exact isHermitian_diagonal_ofReal _

/-- An SVD `A = U Σ Vᴴ` produces the Moore–Penrose inverse `V Σ⁺ Uᴴ` by reciprocating the
singular values; scalar `0⁻¹ = 0` handles zero singular values.
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem IsSVD.isMoorePenroseInverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {p q : ℕ} {A : Matrix m n 𝕜} {U : Matrix m (Fin p) 𝕜}
    {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) :
    IsMoorePenroseInverse A
      (V * (rectDiag (fun k => (singularValues A k)⁻¹) : Matrix (Fin q) (Fin p) 𝕜) * Uᴴ) := by
  have hP := (isMoorePenroseInverse_rectDiag (𝕜 := 𝕜) p q (singularValues A)).unitary_transform
    U V h.conjTranspose_mul_left h.conjTranspose_mul_right
  rwa [← h.eq] at hP

/-- Every rectangular matrix over `ℝ` or `ℂ` has a Moore–Penrose inverse, with arbitrary
finite row and column types and without a rank or nonempty assumption.
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem exists_isMoorePenroseInverse {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n 𝕜) : ∃ B : Matrix n m 𝕜, IsMoorePenroseInverse A B := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD A
  exact ⟨_, h.isMoorePenroseInverse⟩

/-- The unique Moore–Penrose inverse of a rectangular matrix over `ℝ` or `ℂ`. This is
defined for rank-deficient and empty matrices and preserves the existing
full-rank formulas `pinvL` and `pinvR` as separate definitions.
Horn–Johnson §7.3; atlas `pseudoinverse`.
atlas: pseudoinverse -/
def moorePenroseInverse {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n 𝕜) : Matrix n m 𝕜 := (exists_isMoorePenroseInverse A).choose

section General

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The constructed Moore–Penrose inverse satisfies all four Penrose identities.
Horn–Johnson §7.3; atlas `pseudoinverse`.
atlas: pseudoinverse -/
theorem isMoorePenroseInverse (A : Matrix m n 𝕜) :
    IsMoorePenroseInverse A (moorePenroseInverse A) :=
  (exists_isMoorePenroseInverse A).choose_spec

/-- The first Penrose identity `A A⁺ A = A`, at every rank. -/
theorem mul_moorePenroseInverse_mul (A : Matrix m n 𝕜) :
    A * moorePenroseInverse A * A = A :=
  (isMoorePenroseInverse A).mul_mul_eq

/-- The second Penrose identity `A⁺ A A⁺ = A⁺`, at every rank. -/
theorem moorePenroseInverse_mul_moorePenroseInverse (A : Matrix m n 𝕜) :
    moorePenroseInverse A * A * moorePenroseInverse A = moorePenroseInverse A :=
  (isMoorePenroseInverse A).inv_mul_inv_eq

/-- The column-space projector `A A⁺` is Hermitian. -/
theorem mul_moorePenroseInverse_isHermitian (A : Matrix m n 𝕜) :
    (A * moorePenroseInverse A).IsHermitian :=
  (isMoorePenroseInverse A).conjTranspose_mul_eq

/-- Deprecated alias (F1, transpose twins removed): use `mul_moorePenroseInverse_isHermitian`. -/
@[deprecated (since := "2026-10-13")]
alias mul_moorePenroseInverse_isSymm := mul_moorePenroseInverse_isHermitian

/-- The row-space projector `A⁺ A` is Hermitian. -/
theorem moorePenroseInverse_mul_isHermitian (A : Matrix m n 𝕜) :
    (moorePenroseInverse A * A).IsHermitian :=
  (isMoorePenroseInverse A).conjTranspose_inv_mul_eq

/-- Deprecated alias (F1, transpose twins removed): use `moorePenroseInverse_mul_isHermitian`. -/
@[deprecated (since := "2026-10-13")]
alias moorePenroseInverse_mul_isSymm := moorePenroseInverse_mul_isHermitian

/-- The Moore–Penrose column-space projector is idempotent at every rank. -/
theorem mul_moorePenroseInverse_isIdempotentElem (A : Matrix m n 𝕜) :
    IsIdempotentElem (A * moorePenroseInverse A) :=
  (isMoorePenroseInverse A).mul_isIdempotentElem

/-- The Moore–Penrose row-space projector is idempotent at every rank. -/
theorem moorePenroseInverse_mul_isIdempotentElem (A : Matrix m n 𝕜) :
    IsIdempotentElem (moorePenroseInverse A * A) :=
  (isMoorePenroseInverse A).inv_mul_isIdempotentElem

/-- The image of the Moore–Penrose column-space projector is exactly the
original column space. This includes rank-deficient and empty matrices.
atlas: pseudoinverse -/
theorem range_mul_moorePenroseInverse_eq (A : Matrix m n 𝕜) :
    LinearMap.range (A * moorePenroseInverse A).mulVecLin = LinearMap.range A.mulVecLin :=
  (isMoorePenroseInverse A).range_mul_eq

/-- The left full-rank formula `pinvL A = (AᴴA)⁻¹Aᴴ` satisfies the four Penrose identities
when the column Gram matrix is invertible. -/
theorem isMoorePenroseInverse_pinvL [DecidableEq n]
    (A : Matrix m n 𝕜) (h : IsUnit (Aᴴ * A)) : IsMoorePenroseInverse A (pinvL A) :=
  ⟨mul_pinvL_mul h,
    pinvL_mul_pinvL h, mul_pinvL_isHermitian A,
    pinvL_mul_isHermitian h⟩

/-- The right full-rank formula `pinvR A = Aᴴ(AAᴴ)⁻¹` satisfies the four Penrose identities
when the row Gram matrix is invertible. -/
theorem isMoorePenroseInverse_pinvR [DecidableEq m]
    (A : Matrix m n 𝕜) (h : IsUnit (A * Aᴴ)) : IsMoorePenroseInverse A (pinvR A) :=
  ⟨mul_pinvR_mul h,
    pinvR_mul_pinvR h, mul_pinvR_isHermitian h,
    pinvR_mul_isHermitian A⟩

/-- The general Moore–Penrose inverse agrees with `pinvL` for full column rank.
atlas: pseudoinverse -/
theorem moorePenroseInverse_eq_pinvL [DecidableEq n]
    (A : Matrix m n 𝕜) (h : IsUnit (Aᴴ * A)) : moorePenroseInverse A = pinvL A :=
  (isMoorePenroseInverse A).unique
    (isMoorePenroseInverse_pinvL A h)

/-- The general Moore–Penrose inverse agrees with `pinvR` for full row rank.
atlas: pseudoinverse -/
theorem moorePenroseInverse_eq_pinvR [DecidableEq m]
    (A : Matrix m n 𝕜) (h : IsUnit (A * Aᴴ)) : moorePenroseInverse A = pinvR A :=
  (isMoorePenroseInverse A).unique
    (isMoorePenroseInverse_pinvR A h)

/-- Transpose commutes with the general Moore–Penrose inverse. -/
theorem moorePenroseInverse_transpose (A : Matrix m n 𝕜) :
    moorePenroseInverse Aᵀ = (moorePenroseInverse A)ᵀ :=
  (isMoorePenroseInverse Aᵀ).unique (isMoorePenroseInverse A).transpose

/-- Conjugate transpose commutes with the general Moore–Penrose inverse: `(Aᴴ)⁺ = (A⁺)ᴴ`. -/
theorem moorePenroseInverse_conjTranspose (A : Matrix m n 𝕜) :
    moorePenroseInverse Aᴴ = (moorePenroseInverse A)ᴴ :=
  (isMoorePenroseInverse Aᴴ).unique (isMoorePenroseInverse A).conjTranspose

/-- Taking the Moore–Penrose inverse twice recovers the original matrix.
atlas: pseudoinverse -/
theorem moorePenroseInverse_moorePenroseInverse (A : Matrix m n 𝕜) :
    moorePenroseInverse (moorePenroseInverse A) = A :=
  (isMoorePenroseInverse (moorePenroseInverse A)).unique (isMoorePenroseInverse A).swap

/-- The Moore–Penrose inverse of a zero matrix is zero, for any finite shape. -/
@[simp] theorem moorePenroseInverse_zero :
    moorePenroseInverse (0 : Matrix m n 𝕜) = 0 := by
  apply (isMoorePenroseInverse (0 : Matrix m n 𝕜)).unique
  constructor <;> simp

/-- A matrix has zero Moore–Penrose inverse exactly when the matrix is zero.
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
@[simp] theorem moorePenroseInverse_eq_zero_iff (A : Matrix m n 𝕜) :
    moorePenroseInverse A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hA := mul_moorePenroseInverse_mul A
    rw [h, Matrix.mul_zero, Matrix.zero_mul] at hA
    exact hA.symm
  · rintro rfl
    exact moorePenroseInverse_zero

/-- The general inverse of the column Gram matrix `Aᴴ A` is `A⁺ (A⁺)ᴴ`, including singular Gram
matrices. Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem moorePenroseInverse_conjTranspose_mul_self (A : Matrix m n 𝕜) :
    moorePenroseInverse (Aᴴ * A) = moorePenroseInverse A * (moorePenroseInverse A)ᴴ :=
  (isMoorePenroseInverse (Aᴴ * A)).unique (isMoorePenroseInverse A).conjTranspose_mul_self

/-- The general inverse of the row Gram matrix `A Aᴴ` is `(A⁺)ᴴ A⁺`, including singular Gram
matrices. Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem moorePenroseInverse_self_mul_conjTranspose (A : Matrix m n 𝕜) :
    moorePenroseInverse (A * Aᴴ) = (moorePenroseInverse A)ᴴ * moorePenroseInverse A := by
  simpa only [Matrix.conjTranspose_conjTranspose, moorePenroseInverse_conjTranspose] using
    moorePenroseInverse_conjTranspose_mul_self Aᴴ

/-- The squared Frobenius norm of the general inverse is the real part of the trace of the
general inverse of the row Gram matrix: `‖A⁺‖_F² = re tr (A Aᴴ)⁺`.
Horn–Johnson §7.3; atlas `pseudoinverse`.
atlas: pseudoinverse -/
theorem frobSq_moorePenroseInverse_eq_trace_moorePenroseInverse (A : Matrix m n 𝕜) :
    frobSq (moorePenroseInverse A) = RCLike.re (moorePenroseInverse (A * Aᴴ)).trace := by
  rw [frobSq, frobInner_eq_trace, moorePenroseInverse_self_mul_conjTranspose]

/-- The squared spectral norm of the general inverse equals the spectral
norm of the general inverse of the row Gram matrix `A Aᴴ`, at every rank.
Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem specNorm_moorePenroseInverse_sq [DecidableEq m] (A : Matrix m n 𝕜) :
    specNorm (moorePenroseInverse A) ^ 2 = specNorm (moorePenroseInverse (A * Aᴴ)) := by
  rw [moorePenroseInverse_self_mul_conjTranspose]
  unfold specNorm
  rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self]

/-- Reindexing commutes with the general Moore–Penrose inverse (over `ℝ` or `ℂ`), reversing
row and column labels. Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem moorePenroseInverse_reindex {p q : Type*} [Fintype p] [Fintype q] (A : Matrix m n 𝕜)
    (em : m ≃ p) (en : n ≃ q) :
    moorePenroseInverse (A.reindex em en) = (moorePenroseInverse A).reindex en em :=
  (isMoorePenroseInverse (A.reindex em en)).unique
    ((isMoorePenroseInverse A).submatrix em.symm en.symm)

end General

/-- Any SVD `A = U Σ Vᴴ` computes the same Moore–Penrose inverse `V Σ⁺ Uᴴ`, independently of
the choice of singular vectors. Horn–Johnson §7.3; atlas `pseudoinverse`. -/
theorem IsSVD.moorePenroseInverse_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {p q : ℕ} {A : Matrix m n 𝕜} {U : Matrix m (Fin p) 𝕜}
    {V : Matrix n (Fin q) 𝕜} (h : IsSVD A U V) :
    moorePenroseInverse A =
      V * (rectDiag (fun k => (singularValues A k)⁻¹) : Matrix (Fin q) (Fin p) 𝕜) * Uᴴ :=
  (NLAlib.isMoorePenroseInverse A).unique h.isMoorePenroseInverse

/-- Deprecated alias (F1, transpose twins removed): use `IsSVD.moorePenroseInverse_eq`. -/
@[deprecated (since := "2026-10-13")]
alias IsSVD.moorePenroseInverse_eq_mul_conjTranspose := IsSVD.moorePenroseInverse_eq

/-! ### The row projector `A⁺A` and the smallest positive singular value -/

section RowProjector

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The Moore–Penrose row projector `Z = M⁺M` satisfies `(d − Zd)ᵀ(d − Zd) = dᵀd − dᵀZd`
(Pythagoras for the orthogonal projector onto `range Mᵀ`). Horn–Johnson §7.3; helper for
`sketch-and-project` (Gower–Richtárik 2015). -/
theorem dotProduct_self_sub_moorePenroseInverse_mul_mulVec (M : Matrix m n ℝ) (d : n → ℝ) :
    (d - (moorePenroseInverse M * M) *ᵥ d) ⬝ᵥ (d - (moorePenroseInverse M * M) *ᵥ d) =
      d ⬝ᵥ d - d ⬝ᵥ ((moorePenroseInverse M * M) *ᵥ d) := by
  set Z := moorePenroseInverse M * M
  have hsym : Zᵀ = Z := (moorePenroseInverse_mul_isHermitian M).eq
  have hidem : Z * Z = Z := (moorePenroseInverse_mul_isIdempotentElem M).eq
  have hZZ : (Z *ᵥ d) ⬝ᵥ (Z *ᵥ d) = d ⬝ᵥ (Z *ᵥ d) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, Matrix.mulVec_mulVec,
      hidem, dotProduct_comm]
  have hdZ : (Z *ᵥ d) ⬝ᵥ d = d ⬝ᵥ (Z *ᵥ d) := dotProduct_comm _ _
  simp only [sub_dotProduct, dotProduct_sub, hZZ, hdZ]
  ring

/-- The Moore–Penrose row projector is a contraction in the quadratic-form sense:
`dᵀ (M⁺M) d ≤ dᵀd`. Horn–Johnson §7.3; helper for `sketch-and-project`. -/
theorem dotProduct_moorePenroseInverse_mul_mulVec_le_dotProduct_self (M : Matrix m n ℝ)
    (d : n → ℝ) :
    d ⬝ᵥ ((moorePenroseInverse M * M) *ᵥ d) ≤ d ⬝ᵥ d := by
  have h := dotProduct_self_sub_moorePenroseInverse_mul_mulVec M d
  have h0 := dotProduct_self_nonneg (d - (moorePenroseInverse M * M) *ᵥ d)
  linarith

/-- The Moore–Penrose lower bound on the row space: for `v ∈ range Aᵀ`,
`‖A⁺‖⁻² ‖v‖² ≤ ‖Av‖²`. Source: Zouzias–Freris (2013) [`zf13`], §2 (`σ_min⁺ = ‖A⁺‖⁻¹`).
Helper for atlas `kaczmarz-rank-deficient`. -/
theorem inv_specNorm_moorePenroseInverse_sq_mul_dotProduct_le [DecidableEq m]
    (A : Matrix m n ℝ) {v : n → ℝ} (hv : v ∈ LinearMap.range Aᵀ.mulVecLin) :
    (specNorm (moorePenroseInverse A))⁻¹ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v) := by
  set B := moorePenroseInverse A
  by_cases hB : specNorm B = 0
  · simp only [hB, _root_.inv_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul]
    exact dotProduct_self_nonneg _
  obtain ⟨w, rfl⟩ := hv
  simp only [Matrix.mulVecLin_apply]
  have hfix : B *ᵥ (A *ᵥ (Aᵀ *ᵥ w)) = Aᵀ *ᵥ w := by
    have hsym : (B * A)ᵀ = B * A := (moorePenroseInverse_mul_isHermitian A).eq
    have h : B * A * Aᵀ = Aᵀ := by
      calc B * A * Aᵀ = (B * A)ᵀ * Aᵀ := by rw [hsym]
        _ = (A * (B * A))ᵀ := (Matrix.transpose_mul _ _).symm
        _ = Aᵀ := by rw [← Matrix.mul_assoc, mul_moorePenroseInverse_mul]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
  have hBound := sum_sq_mulVec_le_specNorm_sq B (A *ᵥ (Aᵀ *ᵥ w))
  rw [hfix] at hBound
  have hScale := mul_le_mul_of_nonneg_left hBound (sq_nonneg (specNorm B)⁻¹)
  have hCancel : (specNorm B)⁻¹ ^ 2 * specNorm B ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hB, one_pow]
  rw [← mul_assoc, hCancel, one_mul] at hScale
  simpa only [dotProduct, pow_two] using hScale

/-- Full-column-rank case of `inv_specNorm_moorePenroseInverse_sq_mul_dotProduct_le`: an
invertible column Gram matrix gives `‖A⁺_L‖⁻² ‖v‖² ≤ ‖Av‖²` for every `v`, with the
full-rank left inverse `pinvL A`. This is the lower singular bound required by the Kaczmarz
recurrence. Source: Strohmer–Vershynin 2009, Theorem 2; helper for atlas
`randomized-kaczmarz`. -/
theorem inv_specNorm_pinvL_sq_mul_dotProduct_le [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (hA : IsUnit (Aᵀ * A)) (v : n → ℝ) :
    (specNorm (pinvL A))⁻¹ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v) := by
  classical
  by_cases hB : specNorm (pinvL A) = 0
  · simp only [hB, inv_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]
    exact dotProduct_self_nonneg _
  have hBound := sum_sq_mulVec_le_specNorm_sq (pinvL A) (A *ᵥ v)
  have hId : pinvL A *ᵥ (A *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, pinvL_mul hA, Matrix.one_mulVec]
  rw [hId] at hBound
  have hScale := mul_le_mul_of_nonneg_left hBound (sq_nonneg (specNorm (pinvL A))⁻¹)
  have hCancel : (specNorm (pinvL A))⁻¹ ^ 2 * specNorm (pinvL A) ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hB, one_pow]
  rw [← mul_assoc, hCancel, one_mul] at hScale
  simpa only [dotProduct, pow_two] using hScale

end RowProjector

end NLAlib
