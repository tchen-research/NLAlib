import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.DotProduct
import NLAlib.Matrix.Basic.Pseudoinverse
import NLAlib.Matrix.Norms.SpectralNormBounds
import NLAlib.Matrix.Spectral.SVD
/-!
# Extreme eigenvalues and singular values

The extreme spectral quantities of a matrix over `𝕜` (`ℝ` or `ℂ`), their variational
characterisations, and the bounds on the inverse Gram matrix that the probabilistic arguments
about the smallest singular value start from.

* `NLAlib.lambdaMax A`, `NLAlib.lambdaMin A`: `sSup` / `sInf` of the real spectrum of a square
 matrix. For a Hermitian `A` they are Mathlib's sorted eigenvalues at the first and last index
 (`lambdaMax_eq_eigenvalues₀_zero`, `lambdaMin_eq_eigenvalues₀_last`); for a non-Hermitian `A`
 the real spectrum may be empty and the values are junk (`sSup ∅ = 0`).
* The smallest eigenvalue of a Hermitian `M` is `hM.eigenvalues₀ ⟨card n - 1, _⟩`, with the
 Rayleigh characterisation `Matrix.IsHermitian.eigenvalues₀_last_eq_iInf`
 (`λ_min(M) = inf { Re(x* M x) : ‖x‖₂ = 1 }`).
* The smallest singular value of `A : Matrix m n 𝕜` is `singularValues A (card n - 1)` (for a
 wide matrix this is `0`; for the smallest singular value of a wide matrix use `Aᴴ`), with the
 variational form `singularValues_last_eq_iInf` (`σ_min(A) = inf { ‖Ax‖₂ : ‖x‖₂ = 1 }`) and
 the consequences `singularValues_last_le_norm_mulVec`, `le_singularValues_last`,
 `singularValues_last_mul_norm_le`.

## Contents

* Coordinates and nets: `⟨v, A u⟩ = ∑ᵢⱼ vᵢ Aᵢⱼ uⱼ`, and the net bound
 `(1 - 2ε)‖A‖₂ ≤ max_{(u,v) ∈ I} ⟨v, A u⟩` for an `ε`-net `I` of pairs of unit vectors
 (`one_sub_two_mul_mul_specNorm_le_iSup`), used by the Gaussian comparison proofs of
 `NLAlib.RandomMatrix.Gaussian.Spectral`.
* Small `σ_min` and column distances (atlas `smin-small-ball`): if `σ_min(A) ≤ s` then some column
 of `A` is within `√n · s` of the span of the others
 (`exists_iInf_norm_mulVec_le_of_singularValues_last_le`).
* The inverse Gram matrix (atlas `pseudoinverse`): for `A Aᵀ` invertible,
 `‖(A Aᵀ)⁻¹‖₂ = 1/σ_min(Aᵀ)²` and `‖A†‖₂² = ‖(A Aᵀ)⁻¹‖₂` with `A† = pinvR A`.

The Frobenius Lipschitz bound `|σ_k(A) − σ_k(B)| ≤ ‖A − B‖_F` (atlas `norm-lipschitz`) is
`abs_singularValues_sub_le_frobNorm` in `NLAlib.Matrix.Spectral.Weyl`. The entrywise extension
`realMatrixComplexification` is in `NLAlib.Matrix.Spectral.Complexification`.
-/

noncomputable section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-! ### Extreme eigenvalues -/

/-- The largest real spectral value `sSup (spectrum ℝ A)`; the largest eigenvalue of a Hermitian
matrix (`lambdaMax_eq_eigenvalues₀_zero`). For a non-Hermitian `A` the real spectrum may be
empty and the value is Mathlib's `sSup ∅ = 0`. Tropp 2015, §2.1.
atlas: matrix-calculus-def -/
def lambdaMax [DecidableEq n] (A : Matrix n n 𝕜) : ℝ := sSup (spectrum ℝ A)

/-- The smallest real spectral value `sInf (spectrum ℝ A)`; the smallest eigenvalue of a
Hermitian matrix (`lambdaMin_eq_eigenvalues₀_last`). For a non-Hermitian `A` the real spectrum
may be empty and the value is Mathlib's `sInf ∅ = 0`. Tropp 2015, §2.1.
atlas: matrix-calculus-def -/
def lambdaMin [DecidableEq n] (A : Matrix n n 𝕜) : ℝ := sInf (spectrum ℝ A)

/-- The sorted eigenvalues `eigenvalues₀` and the `n`-indexed `eigenvalues` have the same
range. -/
theorem _root_.Matrix.IsHermitian.range_eigenvalues₀ [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : Set.range hA.eigenvalues₀ = Set.range hA.eigenvalues := by
  have h : hA.eigenvalues = hA.eigenvalues₀ ∘ (Fintype.equivOfCardEq (Fintype.card_fin _)).symm :=
    rfl
  rw [h, (Equiv.surjective _).range_comp]

/-- For a Hermitian `A` on a nonempty index type, `lambdaMax A` is the first (largest) of
Mathlib's decreasingly sorted eigenvalues. Horn–Johnson 2013, Thm 4.2.2. -/
theorem lambdaMax_eq_eigenvalues₀_zero [DecidableEq n] [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : lambdaMax A = hA.eigenvalues₀ ⟨0, Fintype.card_pos⟩ := by
  rw [lambdaMax, hA.spectrum_real_eq_range_eigenvalues, ← hA.range_eigenvalues₀]
  refine IsGreatest.csSup_eq ⟨⟨_, rfl⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact hA.eigenvalues₀_antitone (Nat.zero_le (i : ℕ))

/-- For a Hermitian `A` on a nonempty index type, `lambdaMin A` is the last (smallest) of
Mathlib's decreasingly sorted eigenvalues. Horn–Johnson 2013, Thm 4.2.2. -/
theorem lambdaMin_eq_eigenvalues₀_last [DecidableEq n] [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    lambdaMin A = hA.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_one_lt_of_lt Fintype.card_pos⟩ := by
  rw [lambdaMin, hA.spectrum_real_eq_range_eigenvalues, ← hA.range_eigenvalues₀]
  refine IsLeast.csInf_eq ⟨⟨_, rfl⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact hA.eigenvalues₀_antitone (Nat.le_sub_one_of_lt i.isLt)

/-- Sorted eigenvalues depend only on the matrix: equal matrices have equal `eigenvalues₀`
(whatever Hermitian proofs are supplied). -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_congr [DecidableEq n] {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) (i : Fin (Fintype.card n)) :
    hA.eigenvalues₀ i = hB.eigenvalues₀ i := by
  subst h; rfl

/-! ### The unit sphere -/

/-- The Euclidean unit sphere of `n → 𝕜` is nonempty as soon as the index type is. -/
theorem nonempty_unitSphere [Nonempty n] :
    Nonempty {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} := by
  classical
  obtain ⟨i⟩ := ‹Nonempty n›
  refine ⟨⟨Pi.single i 1, ?_⟩⟩
  rw [show (WithLp.toLp 2 (Pi.single i (1 : 𝕜)) : EuclideanSpace 𝕜 n) = EuclideanSpace.single i 1
    from rfl, EuclideanSpace.norm_single, norm_one]

/-- The Euclidean unit sphere of `n → 𝕜` is empty when the index type is. -/
theorem isEmpty_unitSphere [IsEmpty n] :
    IsEmpty {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} := ⟨fun x => by
  have h := x.2
  rw [Subsingleton.elim x.1 0, WithLp.toLp_zero, norm_zero] at h
  exact zero_ne_one h⟩

/-! ### Rayleigh characterisation of the smallest eigenvalue -/

/-- **Rayleigh characterisation of the smallest eigenvalue.** For a Hermitian `M` on a nonempty
index type, the last (smallest) of Mathlib's decreasingly sorted eigenvalues is
`λ_min(M) = inf { Re(x* M x) : ‖x‖₂ = 1 }`. Horn–Johnson 2013, Theorem 4.2.2. -/
theorem _root_.Matrix.IsHermitian.eigenvalues₀_last_eq_iInf [DecidableEq n] {M : Matrix n n 𝕜}
    (hM : M.IsHermitian) (hn : 0 < Fintype.card n) :
    hM.eigenvalues₀ ⟨Fintype.card n - 1, Nat.sub_one_lt_of_lt hn⟩ =
      ⨅ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (star x.1 ⬝ᵥ (M *ᵥ x.1)) := by
  set e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
  set k : Fin (Fintype.card n) := ⟨Fintype.card n - 1, Nat.sub_one_lt_of_lt hn⟩
  have hmin : ∀ i, hM.eigenvalues₀ k ≤ hM.eigenvalues i := fun i =>
    hM.eigenvalues₀_antitone (Nat.le_sub_one_of_lt (e.symm i).isLt)
  -- eigen-coordinates `y = Uᴴ x`: `Re(x* M x) = ∑ᵢ λᵢ ‖yᵢ‖²` and `∑ᵢ ‖yᵢ‖² = ‖x‖²`
  set U : Matrix n n 𝕜 := (hM.eigenvectorUnitary : Matrix n n 𝕜)
  have hUU : U * Uᴴ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hD : Uᴴ * M * U = Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues) := by
    have h := hM.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, U, Matrix.star_eq_conjTranspose] using h
  have hUy : ∀ x : n → 𝕜, U *ᵥ (Uᴴ *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  have hquad : ∀ x : n → 𝕜, RCLike.re (star x ⬝ᵥ (M *ᵥ x)) =
      ∑ i, hM.eigenvalues i * ‖(Uᴴ *ᵥ x) i‖ ^ 2 := by
    intro x
    have h1 : star x ⬝ᵥ (M *ᵥ x) =
        ∑ i, (hM.eigenvalues i : 𝕜) * (star ((Uᴴ *ᵥ x) i) * (Uᴴ *ᵥ x) i) := by
      calc star x ⬝ᵥ (M *ᵥ x) = star (U *ᵥ (Uᴴ *ᵥ x)) ⬝ᵥ (M *ᵥ (U *ᵥ (Uᴴ *ᵥ x))) := by
            rw [hUy]
        _ = star (Uᴴ *ᵥ x) ⬝ᵥ ((Uᴴ * M * U) *ᵥ (Uᴴ *ᵥ x)) := by
            rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
              Matrix.mulVec_mulVec]
        _ = _ := by
            rw [hD]
            simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply, Pi.star_apply]
            exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
      RCLike.ofReal_re]
  have hnorm : ∀ x : n → 𝕜, ∑ i, ‖(Uᴴ *ᵥ x) i‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 := by
    intro x
    rw [← EuclideanSpace.norm_sq_eq (WithLp.toLp 2 (Uᴴ *ᵥ x)), norm_toLp_sq_eq_re_star_dotProduct,
      norm_toLp_sq_eq_re_star_dotProduct, star_mulVec_dotProduct_mulVec_self,
      Matrix.conjTranspose_conjTranspose, hUU, Matrix.one_mulVec]
  have hlow : ∀ x : n → 𝕜, hM.eigenvalues₀ k * ‖WithLp.toLp 2 x‖ ^ 2 ≤
      RCLike.re (star x ⬝ᵥ (M *ᵥ x)) := by
    intro x
    rw [hquad, ← hnorm, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hmin i) (sq_nonneg _)
  -- the eigenvector of `λ_min` attains the bound
  set v : n → 𝕜 := ⇑(hM.eigenvectorBasis (e k))
  have hv : ‖WithLp.toLp 2 v‖ = 1 := by
    rw [show (WithLp.toLp 2 v : EuclideanSpace 𝕜 n) = hM.eigenvectorBasis (e k) from rfl]
    exact hM.eigenvectorBasis.orthonormal.1 (e k)
  have hbdd : BddBelow (Set.range fun x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} =>
      RCLike.re (star x.1 ⬝ᵥ (M *ᵥ x.1))) :=
    ⟨hM.eigenvalues₀ k, by rintro _ ⟨x, rfl⟩; simpa [x.2] using hlow x.1⟩
  apply le_antisymm
  · have : Nonempty {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} := ⟨⟨v, hv⟩⟩
    exact le_ciInf fun x => by simpa [x.2] using hlow x.1
  · refine (ciInf_le hbdd ⟨v, hv⟩).trans_eq ?_
    show RCLike.re (star v ⬝ᵥ (M *ᵥ v)) = _
    rw [hM.mulVec_eigenvectorBasis, dotProduct_smul, RCLike.smul_re, ← norm_toLp_sq_eq_re_star_dotProduct,
      hv, one_pow, mul_one]
    simp [Matrix.IsHermitian.eigenvalues, e, k]

/-! ### Variational characterisation of the smallest singular value -/

/-- **Variational form of the smallest singular value.** For `A : Matrix m n 𝕜`,
`σ_{card n - 1}(A) = inf { ‖Ax‖₂ : ‖x‖₂ = 1 }` (the last singular value in the list indexed by
the number of columns; for a wide matrix both sides are `0`, and for an empty `n` both sides are
`0` by the real convention `inf ∅ = 0`). Horn–Johnson 2013, Thm 7.3.8; proved from the Rayleigh
characterisation of the smallest eigenvalue of `AᴴA`.
atlas: svd -/
theorem singularValues_last_eq_iInf [DecidableEq n] (A : Matrix m n 𝕜) :
    singularValues A (Fintype.card n - 1) =
      ⨅ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1}, ‖WithLp.toLp 2 (A *ᵥ x.1)‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hE := isEmpty_unitSphere (𝕜 := 𝕜) (n := n)
    rw [Real.iInf_of_isEmpty, singularValues_eq_zero_of_width_le A
      (by simp)]
  · have hn' : 0 < Fintype.card n := Fintype.card_pos
    have hq : ∀ x : n → 𝕜, RCLike.re (star x ⬝ᵥ ((Aᴴ * A) *ᵥ x)) =
        ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 := fun x => by
      rw [← star_mulVec_dotProduct_mulVec_self, norm_toLp_sq_eq_re_star_dotProduct]
    have hsq : singularValues A (Fintype.card n - 1) ^ 2 =
        ⨅ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1}, ‖WithLp.toLp 2 (A *ᵥ x.1)‖ ^ 2 := by
      have h := sq_singularValues_eq_eigenvalues₀ A ⟨Fintype.card n - 1, Nat.sub_one_lt_of_lt hn'⟩
      rw [(Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues₀_last_eq_iInf hn'] at h
      simp_rw [hq] at h
      exact h
    have hne : Nonempty {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} := nonempty_unitSphere
    have hbdd : BddBelow (Set.range fun x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} =>
        ‖WithLp.toLp 2 (A *ᵥ x.1)‖ ^ 2) := ⟨0, by rintro _ ⟨y, rfl⟩; positivity⟩
    calc singularValues A (Fintype.card n - 1)
        = Real.sqrt (singularValues A (Fintype.card n - 1) ^ 2) :=
          (Real.sqrt_sq (singularValues_nonneg A _)).symm
      _ = Real.sqrt (⨅ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1},
            ‖WithLp.toLp 2 (A *ᵥ x.1)‖ ^ 2) := by rw [hsq]
      _ = ⨅ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1},
            Real.sqrt (‖WithLp.toLp 2 (A *ᵥ x.1)‖ ^ 2) :=
          Monotone.map_ciInf_of_continuousAt Real.continuous_sqrt.continuousAt
            (fun _ _ h => Real.sqrt_le_sqrt h) hbdd
      _ = _ := iInf_congr fun x => Real.sqrt_sq (norm_nonneg _)

/-- `σ_min(A) ≤ ‖Ax‖₂` for every unit vector `x` (with `σ_min = singularValues A (card n - 1)`).
Horn–Johnson 2013, Thm 7.3.8. -/
theorem singularValues_last_le_norm_mulVec [DecidableEq n] (A : Matrix m n 𝕜) {x : n → 𝕜}
    (hx : ‖WithLp.toLp 2 x‖ = 1) :
    singularValues A (Fintype.card n - 1) ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖ := by
  have hbdd : BddBelow (Set.range fun y : {y : n → 𝕜 // ‖WithLp.toLp 2 y‖ = 1} =>
      ‖WithLp.toLp 2 (A *ᵥ y.1)‖) := ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩
  rw [singularValues_last_eq_iInf]
  exact ciInf_le hbdd (⟨x, hx⟩ : {y : n → 𝕜 // ‖WithLp.toLp 2 y‖ = 1})

/-- `c ≤ σ_min(A)` as soon as `c ≤ ‖Ax‖₂` for every unit vector `x` (index type nonempty).
Horn–Johnson 2013, Thm 7.3.8. -/
theorem le_singularValues_last [DecidableEq n] [Nonempty n] (A : Matrix m n 𝕜) {c : ℝ}
    (h : ∀ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 → c ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖) :
    c ≤ singularValues A (Fintype.card n - 1) := by
  rw [singularValues_last_eq_iInf]
  have := nonempty_unitSphere (𝕜 := 𝕜) (n := n)
  exact le_ciInf fun x => h x.1 x.2

/-- `σ_min(A) ‖x‖₂ ≤ ‖Ax‖₂` for every vector `x`. Horn–Johnson 2013, Thm 7.3.8. -/
theorem singularValues_last_mul_norm_le [DecidableEq n] (A : Matrix m n 𝕜) (x : n → 𝕜) :
    singularValues A (Fintype.card n - 1) * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (A *ᵥ x)‖ := by
  by_cases hx : x = 0
  · rw [hx, WithLp.toLp_zero, norm_zero, mul_zero]; exact norm_nonneg _
  · have hx' : (WithLp.toLp 2 x : EuclideanSpace 𝕜 n) ≠ 0 := fun h => hx ((WithLp.toLp_eq_zero 2).1 h)
    have hpos : 0 < ‖WithLp.toLp 2 x‖ := norm_pos_iff.2 hx'
    set r := ‖WithLp.toLp 2 x‖ with hr
    have hu : ‖WithLp.toLp 2 (r⁻¹ • x)‖ = 1 := by
      rw [WithLp.toLp_smul]; exact norm_smul_inv_norm hx'
    have h := singularValues_last_le_norm_mulVec A hu
    rw [Matrix.mulVec_smul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hpos] at h
    calc singularValues A (Fintype.card n - 1) * r ≤ r⁻¹ * ‖WithLp.toLp 2 (A *ᵥ x)‖ * r :=
          mul_le_mul_of_nonneg_right h hpos.le
      _ = ‖WithLp.toLp 2 (A *ᵥ x)‖ := by field_simp

/-- Squared form of `singularValues_last_mul_norm_le`: `σ_min(A)² ‖x‖₂² ≤ ‖Ax‖₂²`.
Horn–Johnson 2013, Thm 7.3.8. -/
theorem sq_singularValues_last_mul_norm_sq_le [DecidableEq n] (A : Matrix m n 𝕜) (x : n → 𝕜) :
    singularValues A (Fintype.card n - 1) ^ 2 * ‖WithLp.toLp 2 x‖ ^ 2 ≤
      ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg (singularValues_nonneg A _) (norm_nonneg _))
    (singularValues_last_mul_norm_le A x) 2

/-! ### Coordinates and nets -/

open scoped RealInnerProductSpace in
/-- The bilinear form of a matrix in coordinates: `⟨v, A u⟩ = ∑ᵢⱼ vᵢ Aᵢⱼ uⱼ`. -/
theorem inner_toEuclideanLin_eq_sum [DecidableEq n] (A : Matrix m n ℝ)
    (u : EuclideanSpace ℝ n) (v : EuclideanSpace ℝ m) :
    ⟪v, (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A u⟫
      = ∑ i, ∑ j, v i * A i j * u j := by
  simp [PiLp.inner_apply, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

open scoped Matrix.Norms.L2Operator RealInnerProductSpace in
/-- Net argument for the spectral norm: if every pair of unit vectors `(u, v)` is `ε`-close to a
pair in the finite set `I` (whose second components are unit vectors), then
`(1 - 2ε)‖A‖₂ ≤ max_{(u,v) ∈ I} ⟨v, A u⟩`. Vershynin 2012, Lemma 5.4 (in this form). Helper for
atlas `gordon`, `spectral-second-moment`. -/
theorem one_sub_two_mul_mul_specNorm_le_iSup [DecidableEq n] (A : Matrix m n ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (I : Finset (EuclideanSpace ℝ n × EuclideanSpace ℝ m))
    (hI : ∀ t ∈ I, ‖t.2‖ = 1)
    (hcov : ∀ (u : EuclideanSpace ℝ n) (v : EuclideanSpace ℝ m), ‖u‖ = 1 → ‖v‖ = 1 →
      ∃ t ∈ I, ‖u - t.1‖ ≤ ε ∧ ‖v - t.2‖ ≤ ε) :
    (1 - 2 * ε) * specNorm A ≤ ⨆ t : I, ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j := by
  set Φ := (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A with hΦ
  have hM : specNorm A = ‖Φ‖ := rfl
  set S := ⨆ t : I, ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j with hS
  have hbdd : BddAbove (Set.range fun t : I => ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j) :=
    (Set.finite_range _).bddAbove
  set M := ‖Φ‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  rw [hM]
  rcases hM0.lt_or_eq with hMpos | hMzero
  · -- main case
    have claim : ∀ r : ℝ, 0 ≤ r → r < M → r - 2 * ε * M ≤ S := by
      intro r hr0 hrM
      obtain ⟨x, hx1, hrx⟩ := Φ.exists_lt_apply_of_lt_opNorm hrM
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hrx
        linarith
      have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
      set u : EuclideanSpace ℝ n := (‖x‖⁻¹ : ℝ) • x with hu
      have hu1 : ‖u‖ = 1 := norm_smul_inv_norm hx0
      have hΦu : ‖Φ x‖ ≤ ‖Φ u‖ := by
        rw [hu, map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
        rw [le_inv_mul_iff₀ hxpos]
        exact mul_le_of_le_one_left (norm_nonneg _) hx1.le
      set w := Φ u with hw
      have hrw : r < ‖w‖ := lt_of_lt_of_le hrx hΦu
      have hw0 : w ≠ 0 := by
        intro h; rw [h, norm_zero] at hrw; linarith
      set v : EuclideanSpace ℝ m := (‖w‖⁻¹ : ℝ) • w with hv
      have hv1 : ‖v‖ = 1 := norm_smul_inv_norm hw0
      have hvw : ⟪v, w⟫ = ‖w‖ := by
        rw [hv, real_inner_smul_left, real_inner_self_eq_norm_sq]
        have : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
        field_simp
      obtain ⟨t, ht, htu, htv⟩ := hcov u v hu1 hv1
      have ht2 : ‖t.2‖ = 1 := hI t ht
      have hwM : ‖w‖ ≤ M := by
        have := Φ.le_opNorm u; rw [hu1, mul_one] at this; exact this
      have hdecomp : Φ t.1 = w - Φ (u - t.1) := by
        rw [map_sub]; abel
      have hval : ∑ i, ∑ j, t.2 i * A i j * t.1 j = ⟪t.2, Φ t.1⟫ :=
        (inner_toEuclideanLin_eq_sum A t.1 t.2).symm
      have hval2 : ⟪t.2, Φ t.1⟫ = ⟪v, w⟫ - ⟪v - t.2, w⟫ - ⟪t.2, Φ (u - t.1)⟫ := by
        rw [hdecomp, inner_sub_right, inner_sub_left]; ring
      have hb1 : ⟪v - t.2, w⟫ ≤ ε * M := by
        refine (real_inner_le_norm _ _).trans ?_
        exact mul_le_mul htv hwM (norm_nonneg _) hε
      have hb2 : ⟪t.2, Φ (u - t.1)⟫ ≤ ε * M := by
        refine (real_inner_le_norm _ _).trans ?_
        rw [ht2, one_mul]
        refine (Φ.le_opNorm _).trans ?_
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right htu hM0
      have hle : ∑ i, ∑ j, t.2 i * A i j * t.1 j ≤ S :=
        le_ciSup hbdd (⟨t, ht⟩ : I)
      rw [hval, hval2, hvw] at hle
      linarith
    by_contra hcon
    push Not at hcon
    set r := (S + 2 * ε * M + M) / 2
    have h1 := claim (max r 0) (le_max_right _ _) (max_lt (by
      simp only [r]; nlinarith) hMpos)
    have : r ≤ max r 0 := le_max_left _ _
    simp only [r] at this
    nlinarith
  · -- `A = 0`
    have hA : Φ = 0 := norm_eq_zero.1 hMzero.symm
    have hA' : ∀ t : I, ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j = 0 := by
      intro t
      rw [← inner_toEuclideanLin_eq_sum, ← hΦ, hA]
      simp
    rw [← hMzero]
    simp only [mul_zero]
    rw [hS]
    simp only [hA', Real.iSup_const_zero, le_refl]

/-! ### Small `σ_min` and column distances -/

/-- For a unit vector `x`, some column `j` satisfies `inf { ‖A y‖₂ : y_j = 1 } ≤ √n ‖A x‖₂`
(take `j` maximising `|x_j|`, so `|x_j| ≥ 1/√n`, and `y = x / x_j`). -/
private lemma exists_iInf_norm_mulVec_le_of_norm_eq_one [Nonempty n]
    (A : Matrix m n ℝ) (x : n → ℝ) (hx : ‖WithLp.toLp 2 x‖ = 1) :
    ∃ j : n, (⨅ y : {y : n → ℝ // y j = 1}, ‖WithLp.toLp 2 (A *ᵥ y.1)‖)
      ≤ Real.sqrt (Fintype.card n) * ‖WithLp.toLp 2 (A *ᵥ x)‖ := by
  simp only [← sqrt_dotProduct_self_eq_norm] at hx ⊢
  rw [Real.sqrt_eq_one] at hx
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|) Finset.univ_nonempty
  refine ⟨j, ?_⟩
  -- `1 ≤ n * x_j²`
  have hsum : (1 : ℝ) ≤ Fintype.card n * x j ^ 2 := by
    have h1 : x ⬝ᵥ x = ∑ i, x i ^ 2 := by simp [dotProduct, sq]
    have h2 : ∑ i, x i ^ 2 ≤ ∑ _i : n, x j ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := hj i (Finset.mem_univ _)
      rw [← sq_abs (x i), ← sq_abs (x j)]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    linarith
  have hxj : x j ≠ 0 := by
    intro h; rw [h] at hsum; norm_num at hsum
  have hxa : 0 < |x j| := abs_pos.2 hxj
  -- `1 ≤ √n |x_j|`
  have hsq : 1 ≤ Real.sqrt (Fintype.card n) * |x j| := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.one_le_sqrt.2 hsum
  set y : n → ℝ := (x j)⁻¹ • x with hy
  have hyj : y j = 1 := by simp [hy, hxj]
  have hbdd : BddBelow (Set.range fun y : {y : n → ℝ // y j = 1} =>
      Real.sqrt ((A *ᵥ y.1) ⬝ᵥ (A *ᵥ y.1))) :=
    ⟨0, by rintro _ ⟨y, rfl⟩; exact Real.sqrt_nonneg _⟩
  refine (ciInf_le hbdd ⟨y, hyj⟩).trans ?_
  show Real.sqrt ((A *ᵥ y) ⬝ᵥ (A *ᵥ y)) ≤ _
  have hsmul : Real.sqrt ((A *ᵥ ((x j)⁻¹ • x)) ⬝ᵥ (A *ᵥ ((x j)⁻¹ • x))) =
      |(x j)⁻¹| * Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self_eq_abs]
  rw [hy, hsmul, abs_inv]
  set F := Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x))
  have hF : 0 ≤ F := Real.sqrt_nonneg _
  rw [inv_mul_le_iff₀ hxa]
  nlinarith

/-- **Small `σ_min` forces a column close to the span of the others.** For `A : Matrix m n ℝ`
with `n` nonempty, if `σ_min(A) ≤ s` then for some column `j`,
`inf { ‖A x‖₂ : x_j = 1 } ≤ √|n| · s`; the left side is the distance from column `j` to the
span of the other columns. Davidson–Szarek 2001, proof of Thm II.13; Rudelson–Vershynin 2008,
Lemma 3.5 (the "invertibility via distance" step).
atlas: smin-small-ball -/
theorem exists_iInf_norm_mulVec_le_of_singularValues_last_le [DecidableEq n] [Nonempty n]
    (A : Matrix m n ℝ) (s : ℝ) (hs : singularValues A (Fintype.card n - 1) ≤ s) :
    ∃ j : n, (⨅ x : {x : n → ℝ // x j = 1}, ‖WithLp.toLp 2 (A *ᵥ x.1)‖)
      ≤ Real.sqrt (Fintype.card n) * s := by
  set D : n → ℝ := fun j =>
    ⨅ x : {x : n → ℝ // x j = 1}, ‖WithLp.toLp 2 (A *ᵥ x.1)‖ with hD
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ D Finset.univ_nonempty
  refine ⟨j₀, ?_⟩
  have hn0 : 0 < Real.sqrt (Fintype.card n) :=
    Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos)
  -- `D j₀ / √n ≤ σ_min(A)`
  have hlow : D j₀ / Real.sqrt (Fintype.card n) ≤ singularValues A (Fintype.card n - 1) := by
    refine le_singularValues_last A fun x hx => ?_
    obtain ⟨j, hj⟩ := exists_iInf_norm_mulVec_le_of_norm_eq_one A x hx
    rw [div_le_iff₀ hn0]
    calc D j₀ ≤ D j := hj₀ j (Finset.mem_univ _)
      _ ≤ _ := by rw [mul_comm]; exact hj
  have := (div_le_iff₀ hn0).1 (hlow.trans hs)
  linarith

/-! ### The inverse Gram matrix and the pseudoinverse -/

section InverseGram

/-- Cauchy–Schwarz for the dot product. -/
private lemma dotProduct_le_norm_mul_norm (v w : m → ℝ) :
    v ⬝ᵥ w ≤ ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 w‖ := by
  simp only [← sqrt_dotProduct_self_eq_norm]
  rw [← Real.sqrt_mul (dotProduct_self_nonneg v)]
  refine le_trans (le_abs_self _) ?_
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
  simpa [dotProduct, sq] using h

/-- `xᵀ (A Aᵀ) x = ‖Aᵀ x‖²`. -/
private lemma dotProduct_mul_transpose_mulVec (A : Matrix m n ℝ) (x : m → ℝ) :
    x ⬝ᵥ ((A * Aᵀ) *ᵥ x) = (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]

/-- Homogeneous form of the variational characterisation: `σ_min(B)² ‖y‖² ≤ ‖B y‖²`, with dot
products. -/
private lemma sq_singularValues_last_mul_le [DecidableEq n] (B : Matrix m n ℝ) (y : n → ℝ) :
    singularValues B (Fintype.card n - 1) ^ 2 * (y ⬝ᵥ y) ≤ (B *ᵥ y) ⬝ᵥ (B *ᵥ y) := by
  have h := sq_singularValues_last_mul_norm_sq_le B y
  rwa [norm_toLp_sq_eq_dotProduct_self, norm_toLp_sq_eq_dotProduct_self] at h

variable [DecidableEq m]

open scoped Matrix.Norms.L2Operator in
/-- For an invertible Gram matrix and a unit vector `x`, `‖(AAᵀ)⁻¹‖₂ ≥ 1 / ‖Aᵀ x‖²`. -/
private lemma one_div_le_specNorm_inv_self_mul_transpose (A : Matrix m n ℝ)
    (hM : IsUnit (A * Aᵀ).det) (x : m → ℝ) (hx : ‖WithLp.toLp 2 x‖ = 1) :
    0 < (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) ∧
      1 / ((Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x)) ≤ specNorm (A * Aᵀ)⁻¹ := by
  rw [specNorm_eq_norm]
  have hx' : x ⬝ᵥ x = 1 := by rw [← norm_toLp_sq_eq_dotProduct_self, hx, one_pow]
  clear hx
  set M := A * Aᵀ with hM_def
  set q := (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) with hq_def
  have hMinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hq : 0 < q := by
    rcases (dotProduct_self_nonneg (Aᵀ *ᵥ x)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : Aᵀ *ᵥ x = 0 := dotProduct_self_eq_zero.1 h.symm
      have h1 : M *ᵥ x = 0 := by rw [hM_def, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
      have h2 : x = 0 := by
        have : M⁻¹ *ᵥ (M *ᵥ x) = x := by
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec]
        rw [← this, h1, Matrix.mulVec_zero]
      rw [h2, dotProduct_zero] at hx'
      exact zero_ne_one hx'
  refine ⟨hq, ?_⟩
  set w := M⁻¹ *ᵥ x with hw_def
  have hMw : M *ᵥ w = x := by rw [hw_def, Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
  have hsym : Mᵀ = M := by rw [hM_def, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hwMx : w ⬝ᵥ (M *ᵥ x) = 1 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, hMw, hx']
  have hxMx : x ⬝ᵥ (M *ᵥ x) = q := dotProduct_mul_transpose_mulVec A x
  set c := 1 / q with hc_def
  have hpsd : 0 ≤ (w - c • x) ⬝ᵥ (M *ᵥ (w - c • x)) := by
    rw [hM_def, dotProduct_mul_transpose_mulVec]; exact dotProduct_self_nonneg _
  have hexp : (w - c • x) ⬝ᵥ (M *ᵥ (w - c • x)) = w ⬝ᵥ x - 1 / q := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hMw, sub_dotProduct, dotProduct_sub,
      dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_dotProduct]
    simp only [smul_eq_mul, hwMx, hxMx, hx', dotProduct_smul]
    rw [hc_def]
    field_simp
    ring
  have hwx : 1 / q ≤ w ⬝ᵥ x := by linarith
  have hCS : w ⬝ᵥ x ≤ ‖WithLp.toLp 2 w‖ := by
    have := dotProduct_le_norm_mul_norm w x
    rwa [← sqrt_dotProduct_self_eq_norm x, hx', Real.sqrt_one, mul_one] at this
  have hop : ‖WithLp.toLp 2 w‖ ≤ ‖M⁻¹‖ := by
    have h := Matrix.l2_opNorm_mulVec M⁻¹ (WithLp.toLp 2 x)
    rw [← sqrt_dotProduct_self_eq_norm x, hx', Real.sqrt_one, mul_one] at h
    exact h
  linarith

open scoped Matrix.Norms.L2Operator in
/-- If `σ_min(Aᵀ) > 0` then `AAᵀ` is invertible and `‖(AAᵀ)⁻¹‖₂ ≤ 1/σ_min(Aᵀ)²`. -/
private lemma isUnit_and_specNorm_inv_self_mul_transpose_le (A : Matrix m n ℝ)
    (hs : 0 < singularValues Aᵀ (Fintype.card m - 1)) :
    IsUnit (A * Aᵀ).det ∧
      specNorm (A * Aᵀ)⁻¹ ≤ 1 / singularValues Aᵀ (Fintype.card m - 1) ^ 2 := by
  rw [specNorm_eq_norm]
  set M := A * Aᵀ with hM_def
  set s := singularValues Aᵀ (Fintype.card m - 1) with hs_def
  have hs2 : 0 < s ^ 2 := by positivity
  have hlow : ∀ y : m → ℝ, s ^ 2 * (y ⬝ᵥ y) ≤ y ⬝ᵥ (M *ᵥ y) := fun y => by
    rw [hM_def, dotProduct_mul_transpose_mulVec]; exact sq_singularValues_last_mul_le Aᵀ y
  have hunit : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have h1 := hlow v
    rw [hv, dotProduct_zero] at h1
    have h2 : v ⬝ᵥ v = 0 := le_antisymm (by nlinarith [dotProduct_self_nonneg v])
      (dotProduct_self_nonneg v)
    exact hv0 (dotProduct_self_eq_zero.1 h2)
  refine ⟨hunit, ?_⟩
  have hMinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hunit
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  show ‖(Matrix.toEuclideanLin M⁻¹ y)‖ ≤ 1 / s ^ 2 * ‖y‖
  rw [norm_eq_sqrt_dotProduct, norm_eq_sqrt_dotProduct]
  have hT : (Matrix.toEuclideanLin M⁻¹ y).ofLp = M⁻¹ *ᵥ y.ofLp := rfl
  rw [hT]
  set w := M⁻¹ *ᵥ y.ofLp with hw_def
  set yy := y.ofLp with hyy
  have hMw : M *ᵥ w = yy := by rw [hw_def, Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
  have h1 := hlow w
  rw [hMw] at h1
  have h2 := dotProduct_le_norm_mul_norm w yy
  rw [← sqrt_dotProduct_self_eq_norm, ← sqrt_dotProduct_self_eq_norm] at h2
  set a := Real.sqrt (w ⬝ᵥ w)
  set b := Real.sqrt (yy ⬝ᵥ yy)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have haa : a ^ 2 = w ⬝ᵥ w := Real.sq_sqrt (dotProduct_self_nonneg _)
  have h3 : s ^ 2 * a ^ 2 ≤ a * b := by rw [haa]; linarith
  have h4 : s ^ 2 * a ≤ b := by
    rcases ha.lt_or_eq with hapos | ha0
    · nlinarith
    · rw [← ha0, mul_zero]; exact hb
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hs2]
  linarith

/-- **Spectral norm of the inverse Gram matrix.** For a real matrix `A` with `A Aᵀ` invertible,
`‖(A Aᵀ)⁻¹‖₂ = 1 / σ_min(Aᵀ)²`, i.e. `λ_max((A Aᵀ)⁻¹) = 1 / λ_min(A Aᵀ)`, with
`σ_min(Aᵀ) = singularValues Aᵀ (card m - 1)`. (Without the hypothesis both sides are `0`:
Mathlib's `M⁻¹ = 0` and `1 / 0 = 0`.) HMT 2011, proof of Prop A.3; Tropp–Webber 2023, proof of
Lemma B.4. Helper for `pinv-spectral-tail`, `inverse-wishart-spectral-moment`.
atlas: pseudoinverse -/
theorem specNorm_inv_self_mul_transpose_eq (A : Matrix m n ℝ) (hA : IsUnit (A * Aᵀ)) :
    specNorm (A * Aᵀ)⁻¹ = 1 / singularValues Aᵀ (Fintype.card m - 1) ^ 2 := by
  have hM : IsUnit (A * Aᵀ).det := (Matrix.isUnit_iff_isUnit_det _).1 hA
  rcases isEmpty_or_nonempty m with hr | hr
  · have h1 : (A * Aᵀ)⁻¹ = 0 := Subsingleton.elim _ _
    rw [h1, specNorm_zero, singularValues_eq_zero_of_width_le Aᵀ
      (by simp)]
    simp
  · have hne := nonempty_unitSphere (𝕜 := ℝ) (n := m)
    set N := specNorm (A * Aᵀ)⁻¹ with hN_def
    have x0 := hne.some
    have hNpos : 0 < N := by
      obtain ⟨hq, hle⟩ := one_div_le_specNorm_inv_self_mul_transpose A hM x0.1 x0.2
      exact lt_of_lt_of_le (by positivity) hle
    have hlow : 1 / Real.sqrt N ≤ singularValues Aᵀ (Fintype.card m - 1) := by
      refine le_singularValues_last _ fun x hx => ?_
      obtain ⟨hq, hle⟩ := one_div_le_specNorm_inv_self_mul_transpose A hM x hx
      have h1 : 1 / N ≤ (Aᵀ *ᵥ x) ⬝ᵥ (Aᵀ *ᵥ x) := by
        rw [div_le_iff₀ hNpos]; rw [div_le_iff₀ hq] at hle; linarith
      have h2 := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_div' _ hNpos.le, Real.sqrt_one, sqrt_dotProduct_self_eq_norm] at h2
    have hs : 0 < singularValues Aᵀ (Fintype.card m - 1) := lt_of_lt_of_le (by positivity) hlow
    have hup := (isUnit_and_specNorm_inv_self_mul_transpose_le A hs).2
    apply le_antisymm hup
    have h1 : 1 / N ≤ singularValues Aᵀ (Fintype.card m - 1) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hlow 2
      rwa [div_pow, one_pow, Real.sq_sqrt hNpos.le] at this
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hNpos] at h1
    linarith

open scoped Matrix.Norms.L2Operator in
/-- **Spectral norm of the pseudoinverse.** For a real matrix `A` with `A Aᵀ` invertible,
`‖A†‖₂² = ‖(A Aᵀ)⁻¹‖₂` with `A† = pinvR A = Aᵀ (A Aᵀ)⁻¹` (`C*`-identity `‖A†‖² = ‖(A†)ᵀ A†‖`
and `(A†)ᵀ A† = (A Aᵀ)⁻¹`). (Without the hypothesis both sides are `0`.) HMT 2011, proof of
Prop A.3 / Prop 10.4; helper for `pinv-spectral-tail`.
atlas: pseudoinverse -/
theorem specNorm_pinvR_sq [DecidableEq n] (A : Matrix m n ℝ) (hA : IsUnit (A * Aᵀ)) :
    specNorm (pinvR A) ^ 2 = specNorm (A * Aᵀ)⁻¹ := by
  unfold specNorm pinvR
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial]
  have hsym : (A * Aᵀ)ᵀ = A * Aᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have key : (Aᵀ * (A * Aᵀ)⁻¹)ᴴ * (Aᵀ * (A * Aᵀ)⁻¹) = (A * Aᵀ)⁻¹ := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, hsym, Matrix.mul_assoc,
      ← Matrix.mul_assoc A, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hA),
      Matrix.mul_one]
  rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self, key]

end InverseGram

end NLAlib
