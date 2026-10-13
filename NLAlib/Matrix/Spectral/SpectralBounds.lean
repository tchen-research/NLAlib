import NLAlib.Matrix.Spectral.Core
import NLAlib.Matrix.Spectral.SingularValueSpectrum
import NLAlib.Matrix.Norms.Reindex
import Mathlib.Tactic

/-!
# Spectral-norm perturbation of the smallest singular value

Atlas: `norm-lipschitz`. This strengthens the Frobenius-norm bound in
`NLAlib.Matrix.Spectral.Core` using the same infimum argument and Mathlib's actual
Euclidean operator norm. Empty source dimensions are handled explicitly.

It also identifies the extreme singular values on arbitrary finite index types:
`singularValues_zero_eq_specNorm` (`σ₀ = ‖A‖₂`), `singularValues_le_specNorm`, and
`sigmaMin_eq_singularValues_last` (the variational `σ_min` is `σ_{card n - 1}`), together with
the relabeling invariance `sigmaMin_reindex`. The `Fin` cases are proved from the SVD and
transported with `singularValues_reindex`, `specNorm_reindex` and `sigmaMin_reindex`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

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
`|σ_min(A) − σ_min(B)| ≤ ‖A − B‖₂`. Atlas: `norm-lipschitz`.
atlas: norm-lipschitz -/
theorem abs_sigmaMin_sub_sigmaMin_le_specNorm (A B : Matrix m n ℝ) :
    |sigmaMin A - sigmaMin B| ≤ specNorm (A - B) := by
  rw [abs_le]
  have h1 := sigmaMin_le_sigmaMin_add_specNorm A B
  have h2 := sigmaMin_le_sigmaMin_add_specNorm B A
  have h3 : specNorm (B - A) = specNorm (A - B) := by
    unfold specNorm
    rw [norm_sub_rev]
  constructor <;> linarith

/-- The spectral norm squared is the norm of the Gram matrix `AᴴA`, over `ℝ` or `ℂ`, including
empty dimensions. Atlas: `norms-frob-spec`, `svd`.
atlas: norms-frob-spec -/
theorem specNorm_sq_eq_specNorm_conjTranspose_mul_self {𝕜 : Type*} [RCLike 𝕜]
    (A : Matrix m n 𝕜) : specNorm A ^ 2 = specNorm (Aᴴ * A) := by
  unfold specNorm
  rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self]

/-- The spectral norm squared is the norm of the Gram matrix, including
empty dimensions (real form of `specNorm_sq_eq_specNorm_conjTranspose_mul_self`).
Atlas: `norms-frob-spec`, `svd`.
atlas: norms-frob-spec -/
theorem specNorm_sq_eq_specNorm_transpose_mul_self (A : Matrix m n ℝ) :
    specNorm A ^ 2 = specNorm (Aᵀ * A) :=
  specNorm_sq_eq_specNorm_conjTranspose_mul_self A

end NLAlib

namespace NLAlib

/-- Relabeling finite real matrix indices preserves the variational smallest
singular value, including empty domains. The unit spheres are explicitly
equivalent. Horn--Johnson, Section 2.6; supports `principal-angles-def`. -/
theorem sigmaMin_reindex {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m n ℝ) (em : m ≃ p) (en : n ≃ q) :
    sigmaMin (A.reindex em en) = sigmaMin A := by
  let E : {x : n → ℝ // x ⬝ᵥ x = 1} ≃ {x : q → ℝ // x ⬝ᵥ x = 1} :=
    { toFun x := ⟨fun j => x.val (en.symm j),
        (en.symm.sum_comp (fun j => x.val j * x.val j)).trans x.property⟩
      invFun y := ⟨fun i => y.val (en i),
        (en.sum_comp (fun i => y.val i * y.val i)).trans y.property⟩
      left_inv x := by apply Subtype.ext; funext i; simp
      right_inv y := by apply Subtype.ext; funext j; simp }
  unfold sigmaMin
  rw [← E.surjective.iInf_comp]
  apply iInf_congr
  intro x
  have hMv : (A.reindex em en) *ᵥ (E x).val = (A *ᵥ x.val) ∘ em.symm := by
    funext i
    change (∑ j : q, A (em.symm i) (en.symm j) * x.val (en.symm j)) =
      ∑ j : n, A (em.symm i) j * x.val j
    exact en.symm.sum_comp (fun j : n => A (em.symm i) j * x.val j)
  rw [hMv]
  exact congrArg Real.sqrt (em.symm.sum_comp
    (fun i => (A *ᵥ x.val) i * (A *ᵥ x.val) i))

private theorem singularValues_zero_eq_specNorm_fin {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) 𝕜) : singularValues A 0 = specNorm A := by
  by_cases hn : n = 0
  · subst n
    have hA : A = 0 := by ext i j; exact Fin.elim0 j
    rw [singularValues_eq_zero_of_width_le A (by simp), hA, specNorm_zero]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨U, V, hSVD⟩ := exists_isSVD A
    have hGram : specNorm (Aᴴ * A) =
        ‖(fun j : Fin n => ((singularValues A j ^ 2 : ℝ) : 𝕜))‖ := by
      rw [hSVD.conjTranspose_mul_self,
        specNorm_mul_conjTranspose_right_of_conjTranspose_mul_self hSVD.conjTranspose_mul_right,
        specNorm_mul_left_of_conjTranspose_mul_self hSVD.conjTranspose_mul_right,
        specNorm_eq_norm, Matrix.l2_opNorm_diagonal]
    have hMax : ‖(fun j : Fin n => ((singularValues A j ^ 2 : ℝ) : 𝕜))‖ =
        singularValues A 0 ^ 2 := by
      apply le_antisymm
      · apply (pi_norm_le_iff_of_nonneg (sq_nonneg _)).2
        intro j
        rw [RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (singularValues_nonneg A j)
          (singularValues_antitone A (Nat.zero_le _)) 2
      · have h0 := norm_le_pi_norm
          (fun j : Fin n => ((singularValues A j ^ 2 : ℝ) : 𝕜)) ⟨0, hnpos⟩
        change ‖((singularValues A 0 ^ 2 : ℝ) : 𝕜)‖ ≤ _ at h0
        rw [RCLike.norm_ofReal, abs_of_nonneg (sq_nonneg (singularValues A 0))] at h0
        exact h0
    have hSq := specNorm_sq_eq_specNorm_conjTranspose_mul_self A
    rw [hGram, hMax] at hSq
    nlinarith [singularValues_nonneg A 0, specNorm_nonneg A]

/-- The largest sorted singular value equals the spectral norm, on arbitrary finite index
types and over `ℝ` or `ℂ`. The padded singular-value convention also covers matrices with zero
rows or columns. Horn–Johnson 2013, §5.6. Atlas: `svd`, `norms-frob-spec`.
atlas: norm-lipschitz -/
theorem singularValues_zero_eq_specNorm {m n 𝕜 : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜) : singularValues A 0 = specNorm A := by
  rw [← singularValues_reindex A (Fintype.equivFin m) (Fintype.equivFin n),
    ← specNorm_reindex A (Fintype.equivFin m) (Fintype.equivFin n)]
  exact singularValues_zero_eq_specNorm_fin _

/-- Every padded singular value is bounded by the spectral norm, on arbitrary finite index
types and over `ℝ` or `ℂ`. Horn–Johnson §5.6; atlas `norms-frob-spec`, `svd`. -/
theorem singularValues_le_specNorm {m n 𝕜 : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k ≤ specNorm A :=
  (singularValues_antitone A (Nat.zero_le k)).trans_eq (singularValues_zero_eq_specNorm A)

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

private theorem sigmaMin_eq_singularValues_last_fin {m n : ℕ}
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

/-- The variational smallest singular value equals the last singular value
in the list indexed by the domain dimension, on arbitrary finite index types. For wide
matrices this list includes kernel zeros; for tall matrices it is the usual smallest singular
value. Horn–Johnson 2013, Section 2.6. Atlas: `svd`, `norm-lipschitz`. The empty-domain value
is handled by the existing theorem `sigmaMin_of_isEmpty`.
atlas: norm-lipschitz -/
theorem sigmaMin_eq_singularValues_last {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (hn : 0 < Fintype.card n) :
    sigmaMin A = singularValues A (Fintype.card n - 1) := by
  rw [← sigmaMin_reindex A (Fintype.equivFin m) (Fintype.equivFin n),
    sigmaMin_eq_singularValues_last_fin _ hn, singularValues_reindex]

/-- Positivity of the variational smallest singular value is exactly full
column rank when there is at least one column. Atlas: `svd`,
`randomized-kaczmarz`, `norm-lipschitz`.
atlas: norm-lipschitz -/
theorem sigmaMin_pos_iff_rank_eq_width {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) (hn : 0 < Fintype.card n) :
    0 < sigmaMin A ↔ A.rank = Fintype.card n := by
  rw [sigmaMin_eq_singularValues_last A hn, singularValues_pos_iff]
  have hr := A.rank_le_card_width
  omega

end NLAlib
