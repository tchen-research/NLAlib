import NLAlib.LowRank.ComplexPolynomialFilter
import NLAlib.Matrix.ComplexDiagonalFilter
import NLAlib.Matrix.ComplexFullRowInverse
import NLAlib.Matrix.ComplexProjectionComposition

/-!
# Canonical complex polynomial-filter bounds

Native full row rank supplies the canonical complex pseudoinverse expression.
The actual scalar filter envelopes and actual complex column projector give the
source's squared spectral and Frobenius bounds, including containing Krylov spaces.
Source: manuscript `sa:filter-theorem`; HMT (2011), §9 and §A.2.
-/

noncomputable section
open Polynomial
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {m n t q : Type*} [Fintype m] [Fintype n] [Fintype t] [Fintype q]
  [DecidableEq m] [DecidableEq n] [DecidableEq t] [DecidableEq q]

/-- The actual complex canonical right inverse gives the source's scalar spectral
filter envelope, for every column space containing the filtered sketch.
Source: manuscript `sa:filter-theorem`; HMT (2011), full-row-rank pseudoinverse.
The inverse certificate follows from native full row rank.
atlas: polynomial-filter-range-finder (partial) -/
theorem norm_complex_polynomial_filter_residual_sq_le_of_rank_eq_card
    {κ a b : ℕ} {A : Matrix m n ℂ} {U₁ : Matrix m (Fin κ) ℂ}
    {U₂ : Matrix m (Fin a) ℂ} {V₁ : Matrix n (Fin κ) ℂ} {V₂ : Matrix n (Fin b) ℂ}
    (s₁ : Fin κ → ℝ) (s₂ : ℕ → ℝ)
    (hA : A = U₁ * Matrix.diagonal (fun i => (s₁ i : ℂ)) * V₁ᴴ +
      U₂ * (rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ).map Complex.ofReal * V₂ᴴ)
    (hU₁ : U₁ᴴ * U₁ = 1) (hU₂ : U₂ᴴ * U₂ = 1) (hU : U₁ᴴ * U₂ = 0)
    (hV₁ : V₁ᴴ * V₁ = 1) (hV₂ : V₂ᴴ * V₂ = 1) (hV : V₁ᴴ * V₂ = 0)
    (p : ℝ[X]) (Ω : Matrix n t ℂ) (hB : (V₁ᴴ * Ω).rank = κ)
    {c τ : ℝ} (hc : 0 < c) (hmin : ∀ i, c ≤ |p.eval (s₁ i ^ 2)|)
    (hτ : 0 ≤ τ) (hmax : ∀ i, i < min a b → |s₂ i * p.eval (s₂ i ^ 2)| ≤ τ)
    (Q : Matrix m q ℂ)
    (hQ : complexColumnProjector Q * (aeval (A * Aᴴ) p * A * Ω) = aeval (A * Aᴴ) p * A * Ω) :
    let S₂ := (rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ).map Complex.ofReal
    let B := V₁ᴴ * Ω
    let R := Bᴴ * (B * Bᴴ)⁻¹
    ‖A - complexColumnProjector Q * A‖ ^ 2 ≤ ‖S₂‖ ^ 2 +
      (τ / c) ^ 2 * ‖V₂ᴴ * Ω‖ ^ 2 * ‖R‖ ^ 2 := by
  dsimp only
  let S₂ := (rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ).map Complex.ofReal
  let D := aeval (S₂ᴴ * S₂) p
  let R := (V₁ᴴ * Ω)ᴴ * ((V₁ᴴ * Ω) * (V₁ᴴ * Ω)ᴴ)⁻¹
  let Cinv := Matrix.diagonal fun i => Complex.ofReal ((p.eval (s₁ i ^ 2))⁻¹)
  obtain ⟨hC, hCi⟩ := diagonal_complex_filter_right_inverse_and_norm_le s₁ p hc hmin
  have hR : (V₁ᴴ * Ω) * R = 1 :=
    mul_conjTranspose_mul_inv_gram_eq_one_of_rank_eq_card _ (by simpa using hB)
  have htail : ‖S₂ * D‖ ≤ τ := norm_rectDiag_map_ofReal_mul_aeval_conjGram_le s₂ p hτ hmax
  have hcore := norm_complex_polynomial_filter_residual_sq_le hA hU₁ hU₂ hU hV₁ hV₂ hV
    p Ω R Cinv hR hC
  have hmono := norm_sub_complexColumnProjector_mul_le_of_mul_eq Q
    (aeval (A * Aᴴ) p * A * Ω) hQ A
  have hTR : ‖S₂ * D * (V₂ᴴ * Ω) * R‖ ≤ (‖S₂ * D‖ * ‖V₂ᴴ * Ω‖) * ‖R‖ :=
    (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
  have hchain : ‖S₂ * D * (V₂ᴴ * Ω) * R * Cinv‖ ≤ (τ / c) * ‖V₂ᴴ * Ω‖ * ‖R‖ := by
    calc ‖S₂ * D * (V₂ᴴ * Ω) * R * Cinv‖ ≤
        ((‖S₂ * D‖ * ‖V₂ᴴ * Ω‖) * ‖R‖) * ‖Cinv‖ :=
          (Matrix.l2_opNorm_mul _ _).trans
            (mul_le_mul_of_nonneg_right hTR (norm_nonneg _))
      _ = ‖S₂ * D‖ * (‖V₂ᴴ * Ω‖ * ‖R‖ * ‖Cinv‖) := by ring
      _ ≤ τ * (‖V₂ᴴ * Ω‖ * ‖R‖ * ‖Cinv‖) :=
        mul_le_mul_of_nonneg_right htail
          (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
      _ = (τ * ‖V₂ᴴ * Ω‖ * ‖R‖) * ‖Cinv‖ := by ring
      _ ≤ (τ * ‖V₂ᴴ * Ω‖ * ‖R‖) * (1 / c) :=
        mul_le_mul_of_nonneg_left hCi
          (mul_nonneg (mul_nonneg hτ (norm_nonneg _)) (norm_nonneg _))
      _ = _ := by ring
  calc ‖A - complexColumnProjector Q * A‖ ^ 2 ≤
      ‖A - complexColumnProjector (aeval (A * Aᴴ) p * A * Ω) * A‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hmono 2
    _ ≤ ‖S₂‖ ^ 2 + ‖S₂ * D * (V₂ᴴ * Ω) * R * Cinv‖ ^ 2 := hcore
    _ ≤ ‖S₂‖ ^ 2 + ((τ / c) * ‖V₂ᴴ * Ω‖ * ‖R‖) ^ 2 :=
      add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hchain 2)
    _ = _ := by rw [mul_pow, mul_pow]

/-- The actual native complex canonical inverse gives the exact spectral tail
correction from the source theorem, before replacing it by a scalar envelope.
Source: manuscript `sa:filter-theorem`; HMT (2011), deterministic competitor.
atlas: polynomial-filter-range-finder (partial) -/
theorem norm_complex_polynomial_filter_residual_sq_le_exact_of_rank_eq_card
    {κ a b : ℕ} {A : Matrix m n ℂ} {U₁ : Matrix m (Fin κ) ℂ}
    {U₂ : Matrix m (Fin a) ℂ} {V₁ : Matrix n (Fin κ) ℂ} {V₂ : Matrix n (Fin b) ℂ}
    (s₁ : Fin κ → ℝ) (s₂ : ℕ → ℝ)
    (hA : A = U₁ * Matrix.diagonal (fun i => (s₁ i : ℂ)) * V₁ᴴ +
      U₂ * (rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ).map Complex.ofReal * V₂ᴴ)
    (hU₁ : U₁ᴴ * U₁ = 1) (hU₂ : U₂ᴴ * U₂ = 1) (hU : U₁ᴴ * U₂ = 0)
    (hV₁ : V₁ᴴ * V₁ = 1) (hV₂ : V₂ᴴ * V₂ = 1) (hV : V₁ᴴ * V₂ = 0)
    (p : ℝ[X]) (Ω : Matrix n t ℂ) (hB : (V₁ᴴ * Ω).rank = κ)
    {c : ℝ} (hc : 0 < c) (hmin : ∀ i, c ≤ |p.eval (s₁ i ^ 2)|)
    (Q : Matrix m q ℂ)
    (hQ : complexColumnProjector Q * (aeval (A * Aᴴ) p * A * Ω) = aeval (A * Aᴴ) p * A * Ω) :
    let S₂ := (rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ).map Complex.ofReal
    let B := V₁ᴴ * Ω
    let R := Bᴴ * (B * Bᴴ)⁻¹
    let Cinv := Matrix.diagonal fun i => Complex.ofReal ((p.eval (s₁ i ^ 2))⁻¹)
    ‖A - complexColumnProjector Q * A‖ ^ 2 ≤ ‖S₂‖ ^ 2 +
      ‖S₂ * aeval (S₂ᴴ * S₂) p * (V₂ᴴ * Ω) * R * Cinv‖ ^ 2 := by
  dsimp only
  let R := (V₁ᴴ * Ω)ᴴ * ((V₁ᴴ * Ω) * (V₁ᴴ * Ω)ᴴ)⁻¹
  let Cinv := Matrix.diagonal fun i => Complex.ofReal ((p.eval (s₁ i ^ 2))⁻¹)
  obtain ⟨hC, _⟩ := diagonal_complex_filter_right_inverse_and_norm_le s₁ p hc hmin
  have hR : (V₁ᴴ * Ω) * R = 1 :=
    mul_conjTranspose_mul_inv_gram_eq_one_of_rank_eq_card _ (by simpa using hB)
  have hcore := norm_complex_polynomial_filter_residual_sq_le
    hA hU₁ hU₂ hU hV₁ hV₂ hV p Ω R Cinv hR hC
  have hmono := norm_sub_complexColumnProjector_mul_le_of_mul_eq Q
    (aeval (A * Aᴴ) p * A * Ω) hQ A
  exact (pow_le_pow_left₀ (norm_nonneg _) hmono 2).trans hcore

section Frobenius
open scoped Matrix.Norms.Frobenius

omit [DecidableEq n] in
/-- The source's exact Frobenius correction uses the native complex canonical
right inverse, derived from full row rank, and the actual containing column space.
Source: manuscript `sa:filter-theorem`; HMT (2011), deterministic competitor.
atlas: polynomial-filter-range-finder (partial) -/
theorem frobenius_norm_complex_polynomial_filter_residual_sq_le_of_rank_eq_card
    {κ a b : ℕ} {A : Matrix m n ℂ} {U₁ : Matrix m (Fin κ) ℂ}
    {U₂ : Matrix m (Fin a) ℂ} {V₁ : Matrix n (Fin κ) ℂ} {V₂ : Matrix n (Fin b) ℂ}
    (s₁ : Fin κ → ℝ) (s₂ : ℕ → ℝ)
    (hA : A = U₁ * Matrix.diagonal (fun i => (s₁ i : ℂ)) * V₁ᴴ +
      U₂ * (rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ).map Complex.ofReal * V₂ᴴ)
    (hU₁ : U₁ᴴ * U₁ = 1) (hU₂ : U₂ᴴ * U₂ = 1) (hU : U₁ᴴ * U₂ = 0)
    (hV₁ : V₁ᴴ * V₁ = 1) (hV₂ : V₂ᴴ * V₂ = 1) (hV : V₁ᴴ * V₂ = 0)
    (p : ℝ[X]) (Ω : Matrix n t ℂ) (hB : (V₁ᴴ * Ω).rank = κ)
    {c : ℝ} (hc : 0 < c) (hmin : ∀ i, c ≤ |p.eval (s₁ i ^ 2)|)
    (Q : Matrix m q ℂ)
    (hQ : complexColumnProjector Q * (aeval (A * Aᴴ) p * A * Ω) = aeval (A * Aᴴ) p * A * Ω) :
    let S₂ := (rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ).map Complex.ofReal
    let B := V₁ᴴ * Ω
    let R := Bᴴ * (B * Bᴴ)⁻¹
    let Cinv := Matrix.diagonal fun i => Complex.ofReal ((p.eval (s₁ i ^ 2))⁻¹)
    ‖A - complexColumnProjector Q * A‖ ^ 2 ≤ ‖S₂‖ ^ 2 +
      ‖S₂ * aeval (S₂ᴴ * S₂) p * (V₂ᴴ * Ω) * R * Cinv‖ ^ 2 := by
  dsimp only
  let R := (V₁ᴴ * Ω)ᴴ * ((V₁ᴴ * Ω) * (V₁ᴴ * Ω)ᴴ)⁻¹
  let Cinv := Matrix.diagonal fun i => Complex.ofReal ((p.eval (s₁ i ^ 2))⁻¹)
  obtain ⟨hC, _⟩ := diagonal_complex_filter_right_inverse_and_norm_le s₁ p hc hmin
  have hR : (V₁ᴴ * Ω) * R = 1 :=
    mul_conjTranspose_mul_inv_gram_eq_one_of_rank_eq_card _ (by simpa using hB)
  have hcore := frobenius_norm_complex_polynomial_filter_residual_sq_le
    hA hU₁ hU₂ hU hV₁ hV₂ hV p Ω R Cinv hR hC
  exact (frobenius_norm_sub_complexColumnProjector_mul_sq_le_of_mul_eq Q
    (aeval (A * Aᴴ) p * A * Ω) hQ A).trans hcore

end Frobenius

/-- Native complex polynomial-filter range finding has both intended squared
spectral and exact Frobenius competitor bounds, using the actual finite filter
maximum/minimum and the canonical full-row-rank pseudoinverse expression.
Source: manuscript `sa:filter-theorem`; HMT (2011), §9 and §A.2. The Frobenius
norm instances are explicit to distinguish them from the spectral norm in the
same statement. Any actual column space containing the filtered sketch is allowed.
atlas: polynomial-filter-range-finder -/
theorem complex_polynomial_filter_residual_bounds
    {κ a b : ℕ} [Nonempty (Fin κ)] {A : Matrix m n ℂ} {U₁ : Matrix m (Fin κ) ℂ}
    {U₂ : Matrix m (Fin a) ℂ} {V₁ : Matrix n (Fin κ) ℂ} {V₂ : Matrix n (Fin b) ℂ}
    (s₁ : Fin κ → ℝ) (s₂ : ℕ → ℝ)
    (hA : A = U₁ * Matrix.diagonal (fun i => (s₁ i : ℂ)) * V₁ᴴ +
      U₂ * (rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ).map Complex.ofReal * V₂ᴴ)
    (hU₁ : U₁ᴴ * U₁ = 1) (hU₂ : U₂ᴴ * U₂ = 1) (hU : U₁ᴴ * U₂ = 0)
    (hV₁ : V₁ᴴ * V₁ = 1) (hV₂ : V₂ᴴ * V₂ = 1) (hV : V₁ᴴ * V₂ = 0)
    (p : ℝ[X]) (Ω : Matrix n t ℂ) (hB : (V₁ᴴ * Ω).rank = κ)
    (hc : 0 < filterHeadMinAbs s₁ p) (Q : Matrix m q ℂ)
    (hQ : complexColumnProjector Q * (aeval (A * Aᴴ) p * A * Ω) = aeval (A * Aᴴ) p * A * Ω) :
    let S₂ := (rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ).map Complex.ofReal
    let B := V₁ᴴ * Ω
    let R := Bᴴ * (B * Bᴴ)⁻¹
    let Cinv := Matrix.diagonal fun i => Complex.ofReal ((p.eval (s₁ i ^ 2))⁻¹)
    ‖A - complexColumnProjector Q * A‖ ^ 2 ≤ ‖S₂‖ ^ 2 +
        ‖S₂ * aeval (S₂ᴴ * S₂) p * (V₂ᴴ * Ω) * R * Cinv‖ ^ 2 ∧
      ‖A - complexColumnProjector Q * A‖ ^ 2 ≤ ‖S₂‖ ^ 2 +
        (filterTailMaxAbs s₂ p a b / filterHeadMinAbs s₁ p) ^ 2 * ‖V₂ᴴ * Ω‖ ^ 2 * ‖R‖ ^ 2 ∧
      (@norm _ (Matrix.frobeniusNormedAddCommGroup (m := m) (n := n) (α := ℂ)).toNorm
        (A - complexColumnProjector Q * A)) ^ 2 ≤
      (@norm _ (Matrix.frobeniusNormedAddCommGroup (m := Fin a) (n := Fin b) (α := ℂ)).toNorm S₂) ^ 2 +
      (@norm _ (Matrix.frobeniusNormedAddCommGroup (m := Fin a) (n := Fin κ) (α := ℂ)).toNorm
        (S₂ * aeval (S₂ᴴ * S₂) p * (V₂ᴴ * Ω) * R * Cinv)) ^ 2 := by
  dsimp only
  refine ⟨norm_complex_polynomial_filter_residual_sq_le_exact_of_rank_eq_card s₁ s₂
    hA hU₁ hU₂ hU hV₁ hV₂ hV p Ω hB hc (filterHeadMinAbs_le s₁ p) Q hQ,
    norm_complex_polynomial_filter_residual_sq_le_of_rank_eq_card s₁ s₂
    hA hU₁ hU₂ hU hV₁ hV₂ hV p Ω hB hc (filterHeadMinAbs_le s₁ p)
    (NNReal.coe_nonneg _) (fun _ hi => abs_mul_eval_le_filterTailMaxAbs s₂ p hi) Q hQ, ?_⟩
  exact frobenius_norm_complex_polynomial_filter_residual_sq_le_of_rank_eq_card s₁ s₂
    hA hU₁ hU₂ hU hV₁ hV₂ hV p Ω hB hc (filterHeadMinAbs_le s₁ p) Q hQ

/-- Every actual complex block Krylov range has both canonical polynomial-filter
bounds simultaneously for every filter below its order. Source: manuscript
`sa:filter`, block Krylov specialization; Musco--Musco (2015).
atlas: polynomial-filter-range-finder (partial) -/
theorem complex_polynomial_filter_residual_bounds_of_complexBlockKrylovSpace_le
    {κ a b order : ℕ} [Nonempty (Fin κ)] {A : Matrix m n ℂ}
    {U₁ : Matrix m (Fin κ) ℂ} {U₂ : Matrix m (Fin a) ℂ}
    {V₁ : Matrix n (Fin κ) ℂ} {V₂ : Matrix n (Fin b) ℂ}
    (s₁ : Fin κ → ℝ) (s₂ : ℕ → ℝ)
    (hA : A = U₁ * Matrix.diagonal (fun i => (s₁ i : ℂ)) * V₁ᴴ +
      U₂ * (rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ).map Complex.ofReal * V₂ᴴ)
    (hU₁ : U₁ᴴ * U₁ = 1) (hU₂ : U₂ᴴ * U₂ = 1) (hU : U₁ᴴ * U₂ = 0)
    (hV₁ : V₁ᴴ * V₁ = 1) (hV₂ : V₂ᴴ * V₂ = 1) (hV : V₁ᴴ * V₂ = 0)
    (p : ℝ[X]) (hp : p.degree < order) (Ω : Matrix n t ℂ)
    (hB : (V₁ᴴ * Ω).rank = κ) (hc : 0 < filterHeadMinAbs s₁ p) (Q : Matrix m q ℂ)
    (hK : complexBlockKrylovSpace (A * Aᴴ) (A * Ω) order ≤ LinearMap.range Q.mulVecLin) :
    let S₂ := (rectDiag s₂ : Matrix (Fin a) (Fin b) ℝ).map Complex.ofReal
    let B := V₁ᴴ * Ω
    let R := Bᴴ * (B * Bᴴ)⁻¹
    let Cinv := Matrix.diagonal fun i => Complex.ofReal ((p.eval (s₁ i ^ 2))⁻¹)
    ‖A - complexColumnProjector Q * A‖ ^ 2 ≤ ‖S₂‖ ^ 2 +
        ‖S₂ * aeval (S₂ᴴ * S₂) p * (V₂ᴴ * Ω) * R * Cinv‖ ^ 2 ∧
      ‖A - complexColumnProjector Q * A‖ ^ 2 ≤ ‖S₂‖ ^ 2 +
        (filterTailMaxAbs s₂ p a b / filterHeadMinAbs s₁ p) ^ 2 * ‖V₂ᴴ * Ω‖ ^ 2 * ‖R‖ ^ 2 ∧
      (@norm _ (Matrix.frobeniusNormedAddCommGroup (m := m) (n := n) (α := ℂ)).toNorm
        (A - complexColumnProjector Q * A)) ^ 2 ≤
      (@norm _ (Matrix.frobeniusNormedAddCommGroup (m := Fin a) (n := Fin b) (α := ℂ)).toNorm S₂) ^ 2 +
      (@norm _ (Matrix.frobeniusNormedAddCommGroup (m := Fin a) (n := Fin κ) (α := ℂ)).toNorm
        (S₂ * aeval (S₂ᴴ * S₂) p * (V₂ᴴ * Ω) * R * Cinv)) ^ 2 :=
  complex_polynomial_filter_residual_bounds s₁ s₂ hA hU₁ hU₂ hU hV₁ hV₂ hV p Ω hB hc Q
    (complexColumnProjector_aeval_conjGram_mul_mul_eq_of_complexBlockKrylovSpace_le A Ω Q hK hp)

end NLAlib
