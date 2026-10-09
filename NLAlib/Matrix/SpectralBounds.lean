import NLAlib.Matrix.Spectral
import NLAlib.Matrix.SVD
import Mathlib.Tactic

/-!
# Spectral-norm perturbation of the smallest singular value

Atlas: `norm-lipschitz`. This strengthens the Frobenius-norm bound in
`NLAlib.Matrix.Spectral` using the same infimum argument and Mathlib's actual
Euclidean operator norm. Empty source dimensions are handled explicitly.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Spectral-norm control of the Euclidean length of a matrix-vector product.
Atlas: `norms-frob-spec`, `norm-lipschitz`. -/
theorem sqrt_mulVec_dotProduct_le_specNorm_mul (A : Matrix m n ℝ) (x : n → ℝ) :
    Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) ≤ specNorm A * Real.sqrt (x ⬝ᵥ x) := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  have hnAx : ‖(EuclideanSpace.equiv m ℝ).symm (A *ᵥ x)‖ =
      Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp [dotProduct, sq]
  simpa only [hnAx, ← sqrt_dotProduct_self_eq_norm, specNorm] using h

/-- One-sided Weyl perturbation bound in the spectral norm, including empty
dimensions. Atlas: `norm-lipschitz`. -/
theorem sigmaMin_le_sigmaMin_add_specNorm (A B : Matrix m n ℝ) :
    sigmaMin A ≤ sigmaMin B + specNorm (A - B) := by
  have hN : 0 ≤ specNorm (A - B) := specNorm_nonneg _
  rcases isEmpty_or_nonempty {x : n → ℝ // x ⬝ᵥ x = 1} with hE | hE
  · unfold sigmaMin
    rw [Real.iInf_of_isEmpty, Real.iInf_of_isEmpty]
    linarith
  · rw [← sub_le_iff_le_add]
    unfold sigmaMin
    refine le_ciInf fun x => ?_
    have h1 := ciInf_le (bddBelow_range_sqrt_mulVec A) x
    have h2 : Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1)) ≤
        Real.sqrt ((B *ᵥ x.1) ⬝ᵥ (B *ᵥ x.1)) +
          Real.sqrt (((A - B) *ᵥ x.1) ⬝ᵥ ((A - B) *ᵥ x.1)) := by
      have hsplit : A *ᵥ x.1 = B *ᵥ x.1 + (A - B) *ᵥ x.1 := by
        rw [Matrix.sub_mulVec]
        abel
      rw [hsplit]
      exact sqrt_dotProduct_add_le _ _
    have h3 := sqrt_mulVec_dotProduct_le_specNorm_mul (A - B) x.1
    rw [x.2, Real.sqrt_one, mul_one] at h3
    linarith

/-- The smallest singular value is `1`-Lipschitz for the spectral norm:
`|σ_min(A) − σ_min(B)| ≤ ‖A − B‖₂`. Atlas: `norm-lipschitz`. -/
theorem abs_sigmaMin_sub_sigmaMin_le_specNorm (A B : Matrix m n ℝ) :
    |sigmaMin A - sigmaMin B| ≤ specNorm (A - B) := by
  rw [abs_le]
  have h1 := sigmaMin_le_sigmaMin_add_specNorm A B
  have h2 := sigmaMin_le_sigmaMin_add_specNorm B A
  have h3 : specNorm (B - A) = specNorm (A - B) := by
    unfold specNorm
    rw [norm_sub_rev]
  constructor <;> linarith

/-- Multiplication by an orthonormal frame preserves the spectral norm.
Atlas: `norms-frob-spec`, `svd`. -/
theorem specNorm_mul_left_of_hasOrthonormalCols {p : Type*} [Fintype p]
    [DecidableEq p] {P : Matrix m n ℝ} (hP : Pᵀ * P = 1) (A : Matrix n p ℝ) :
    specNorm (P * A) = specNorm A := by
  have hPA : P * A = P * (Pᵀ * (P * A)) := by
    rw [← Matrix.mul_assoc Pᵀ P, hP, Matrix.one_mul]
  have h := specNorm_transpose_mul_of_eq_mul hP hPA
  simpa only [← Matrix.mul_assoc, hP, Matrix.one_mul] using h.symm

/-- Right multiplication by the transpose of an orthonormal frame preserves
the spectral norm. Atlas: `norms-frob-spec`, `svd`. -/
theorem specNorm_mul_transpose_right_of_hasOrthonormalCols {p : Type*}
    [Fintype p] [DecidableEq p] {P : Matrix m n ℝ} (hP : Pᵀ * P = 1)
    (A : Matrix p n ℝ) : specNorm (A * Pᵀ) = specNorm A := by
  rw [← specNorm_transpose (A * Pᵀ), Matrix.transpose_mul, Matrix.transpose_transpose,
    specNorm_mul_left_of_hasOrthonormalCols hP, specNorm_transpose]

/-- The spectral norm squared is the norm of the Gram matrix, including
empty dimensions. Atlas: `norms-frob-spec`, `svd`. -/
theorem specNorm_sq_eq_specNorm_transpose_mul_self (A : Matrix m n ℝ) :
    specNorm A ^ 2 = specNorm (Aᵀ * A) := by
  unfold specNorm
  rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self,
    Matrix.conjTranspose_eq_transpose_of_trivial]

end NLAlib

namespace NLAlib

/-- The largest sorted singular value equals the spectral norm. The padded
singular-value convention also covers matrices with zero rows or columns.
Atlas: `svd`, `norms-frob-spec`. -/
theorem singularValues_zero_eq_specNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    singularValues A 0 = specNorm A := by
  by_cases hn : n = 0
  · subst n
    have hA : A = 0 := by ext i j; exact Fin.elim0 j
    rw [singularValues_eq_zero_of_width_le A (by omega), hA, specNorm_zero]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨U, V, hSVD⟩ := exists_isSVD A
    have hGram : specNorm (Aᵀ * A) =
        ‖(fun j : Fin n => singularValues A j ^ 2)‖ := by
      rw [hSVD.transpose_mul_self,
        specNorm_mul_transpose_right_of_hasOrthonormalCols hSVD.transpose_mul_right,
        specNorm_mul_left_of_hasOrthonormalCols hSVD.transpose_mul_right,
        specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
    have hMax : ‖(fun j : Fin n => singularValues A j ^ 2)‖ = singularValues A 0 ^ 2 := by
      apply le_antisymm
      · apply (pi_norm_le_iff_of_nonneg (sq_nonneg _)).2
        intro j
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (singularValues_nonneg A j)
          (singularValues_antitone A (Nat.zero_le _)) 2
      · have h0 := norm_le_pi_norm (fun j : Fin n => singularValues A j ^ 2) ⟨0, hnpos⟩
        change ‖(singularValues A 0 ^ 2 : ℝ)‖ ≤ _ at h0
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (singularValues A 0))] at h0
        exact h0
    have hSq := specNorm_sq_eq_specNorm_transpose_mul_self A
    rw [hGram, hMax] at hSq
    nlinarith [singularValues_nonneg A 0, specNorm_nonneg A]

/-- A Gram error has the norm of the list `σᵢ² − 1`, for every domain
singular value (including zero singular values and empty dimensions).
Atlas: `ose-def`, `svd`. -/
theorem specNorm_gram_sub_one_eq_norm_singularValues_sq_sub_one {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    specNorm (Aᵀ * A - 1) = ‖(fun j : Fin n => singularValues A j ^ 2 - 1)‖ := by
  obtain ⟨U, V, hSVD⟩ := exists_isSVD A
  have hdiag : (Matrix.diagonal (fun j : Fin n => singularValues A j ^ 2 - 1)) =
      Matrix.diagonal (fun j : Fin n => singularValues A j ^ 2) - 1 := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_sub]
  have hGram : Aᵀ * A - 1 =
      V * Matrix.diagonal (fun j : Fin n => singularValues A j ^ 2 - 1) * Vᵀ := by
    rw [hSVD.transpose_mul_self, hdiag, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, hSVD.mul_transpose_right]
  rw [hGram,
    specNorm_mul_transpose_right_of_hasOrthonormalCols hSVD.transpose_mul_right,
    specNorm_mul_left_of_hasOrthonormalCols hSVD.transpose_mul_right,
    specNorm_eq_norm, Matrix.l2_opNorm_diagonal]

/-- The SVD gives the squared length as a weighted sum in right-singular
coordinates. Atlas: `svd`, `norm-lipschitz`. -/
theorem IsSVD.mulVec_dotProduct_mulVec_eq_sum {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (hSVD : IsSVD A U V) (x : Fin n → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) =
      ∑ j : Fin n, singularValues A j ^ 2 * ((Vᵀ *ᵥ x) j) ^ 2 := by
  rw [mulVec_dotProduct_mulVec_self, hSVD.transpose_mul_self,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The variational smallest singular value equals the last singular value
in the list indexed by the domain dimension. For wide matrices this list
includes kernel zeros; for tall matrices it is the usual smallest singular
value. Atlas: `svd`, `norm-lipschitz`. The empty-domain value is handled by
the existing theorem `sigmaMin_of_isEmpty`. -/
theorem sigmaMin_eq_singularValues_last {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n) :
    sigmaMin A = singularValues A (n - 1) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨U, V, hSVD⟩ := exists_isSVD A
  have hs : 0 ≤ singularValues A (n - 1) := singularValues_nonneg A _
  apply le_antisymm
  · let j : Fin n := ⟨n - 1, by omega⟩
    let e : Fin n → ℝ := Pi.single j 1
    let x := V *ᵥ e
    have hx : x ⬝ᵥ x = 1 := by
      dsimp [x]
      rw [mulVec_dotProduct_mulVec_self, hSVD.transpose_mul_right, Matrix.one_mulVec]
      simp [e]
    have hy : Vᵀ *ᵥ x = e := by
      dsimp [x]
      rw [Matrix.mulVec_mulVec, hSVD.transpose_mul_right, Matrix.one_mulVec]
    have hAx : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = singularValues A (n - 1) ^ 2 := by
      rw [hSVD.mulVec_dotProduct_mulVec_eq_sum, hy]
      simp [e, Pi.single_apply, j]
    have h := sigmaMin_le_sqrt_mulVec A hx
    rw [hAx, Real.sqrt_sq hs] at h
    exact h
  · apply le_sigmaMin A
    intro x hx
    have hy : (Vᵀ *ᵥ x) ⬝ᵥ (Vᵀ *ᵥ x) = 1 := by
      rw [mulVec_dotProduct_mulVec_self, Matrix.transpose_transpose,
        hSVD.mul_transpose_right, Matrix.one_mulVec, hx]
    have hsum : singularValues A (n - 1) ^ 2 ≤
        ∑ j : Fin n, singularValues A j ^ 2 * ((Vᵀ *ᵥ x) j) ^ 2 := by
      calc
        singularValues A (n - 1) ^ 2 =
            ∑ j : Fin n, singularValues A (n - 1) ^ 2 * ((Vᵀ *ᵥ x) j) ^ 2 := by
          rw [← Finset.mul_sum]
          have hy' : (∑ j : Fin n, ((Vᵀ *ᵥ x) j) ^ 2) = 1 := by
            simpa only [dotProduct, sq] using hy
          rw [hy', mul_one]
        _ ≤ _ := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ hs (singularValues_antitone A (by omega)) 2) (sq_nonneg _)
    rw [← hSVD.mulVec_dotProduct_mulVec_eq_sum] at hsum
    have h := Real.sqrt_le_sqrt hsum
    rw [Real.sqrt_sq hs] at h
    exact h

/-- Positivity of the variational smallest singular value is exactly full
column rank when there is at least one column. Atlas: `svd`,
`randomized-kaczmarz`, `norm-lipschitz`. -/
theorem sigmaMin_pos_iff_rank_eq_width {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n) :
    0 < sigmaMin A ↔ A.rank = n := by
  rw [sigmaMin_eq_singularValues_last A hn, singularValues_pos_iff]
  have hr := A.rank_le_width
  omega

end NLAlib
