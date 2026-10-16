import NLAlib.Matrix.Spectral.ThinSVD
import NLAlib.Matrix.Spectral.SingularValueSpectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
/-!
# Gramian balancing from positive singular triplets

The SVD square-root construction gives biorthogonal trial and test bases
and balances both compressed Gramian forms. No choice of eigenbasis for
`PQ` is made, so repeated singular values cause no ambiguity.

Source: Brunton–Kutz (2022), §9.2; matrix-toolkit re-derivation, §64.
Atlas: `gramian-svd-balancing`.
-/
noncomputable section
open Matrix
open scoped Matrix
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n a b r : Type*} [Fintype n] [Fintype a] [Fintype b] [Fintype r]
variable [DecidableEq n] [DecidableEq a] [DecidableEq b] [DecidableEq r]

/-- Inverse square roots of a positive singular-value diagonal. -/
def invSqrtDiagonal (σ : r → ℝ) : Matrix r r 𝕜 :=
  diagonal (fun i => ((Real.sqrt (σ i))⁻¹ : 𝕜))

/-- Positive square roots of a singular-value diagonal. -/
def sqrtDiagonal (σ : r → ℝ) : Matrix r r 𝕜 :=
  diagonal (fun i => (Real.sqrt (σ i) : 𝕜))

/-- Inverse square-root scaling of a positive singular diagonal. -/
theorem invSqrtDiagonal_mul_diagonal (σ : r → ℝ) (hσ : ∀ i, 0 < σ i) :
    invSqrtDiagonal (𝕜 := 𝕜) σ * diagonal (fun i => (σ i : 𝕜)) = sqrtDiagonal σ := by
  rw [invSqrtDiagonal, sqrtDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  norm_cast
  have hs := Real.sq_sqrt (hσ i).le
  have hn := (Real.sqrt_pos.mpr (hσ i)).ne'
  field_simp
  nlinarith

/-- Right inverse square-root scaling of a positive singular diagonal. -/
theorem diagonal_mul_invSqrtDiagonal (σ : r → ℝ) (hσ : ∀ i, 0 < σ i) :
    diagonal (fun i => (σ i : 𝕜)) * invSqrtDiagonal (𝕜 := 𝕜) σ = sqrtDiagonal σ := by
  rw [invSqrtDiagonal, sqrtDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  norm_cast
  have hs := Real.sq_sqrt (hσ i).le
  have hn := (Real.sqrt_pos.mpr (hσ i)).ne'
  field_simp
  nlinarith

/-- The inverse-square-root diagonal is Hermitian. -/
theorem invSqrtDiagonal_isHermitian (σ : r → ℝ) :
    (invSqrtDiagonal (𝕜 := 𝕜) σ).IsHermitian := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [invSqrtDiagonal, Matrix.conjTranspose_apply]
  · simp [invSqrtDiagonal, Matrix.conjTranspose_apply, hij, Ne.symm hij]

private theorem diagonal_ofReal_isHermitian (σ : r → ℝ) :
    (diagonal fun i => (σ i : 𝕜)).IsHermitian := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [Matrix.conjTranspose_apply]
  · simp [Matrix.conjTranspose_apply, hij, Ne.symm hij]

private theorem invSqrtDiagonal_mul_diagonal_mul (σ : r → ℝ) (hσ : ∀ i, 0 < σ i) :
    invSqrtDiagonal (𝕜 := 𝕜) σ * diagonal (fun i => (σ i : 𝕜)) *
      invSqrtDiagonal σ = 1 := by
  rw [invSqrtDiagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    norm_cast
    have hs := Real.sq_sqrt (hσ i).le
    have hn := (Real.sqrt_pos.mpr (hσ i)).ne'
    field_simp
    nlinarith
  · simp [hij]

private theorem invSqrtDiagonal_mul_diagonal_sq_mul (σ : r → ℝ) (hσ : ∀ i, 0 < σ i) :
    invSqrtDiagonal (𝕜 := 𝕜) σ * diagonal (fun i => (σ i : 𝕜)) *
      diagonal (fun i => (σ i : 𝕜)) * invSqrtDiagonal σ = diagonal (fun i => (σ i : 𝕜)) := by
  rw [invSqrtDiagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  norm_cast
  have hs := Real.sq_sqrt (hσ i).le
  have hn := (Real.sqrt_pos.mpr (hσ i)).ne'
  field_simp
  nlinarith

/-- Trial coordinates `R V Σ⁻¹ᐟ²` in square-root balancing. -/
def balancingTrialMap (R : Matrix n a 𝕜) (V : Matrix a r 𝕜) (σ : r → ℝ) :
    Matrix n r 𝕜 := R * V * invSqrtDiagonal σ

/-- Test coordinates `Oᴴ U Σ⁻¹ᐟ²` in square-root balancing. -/
def balancingTestMap (O : Matrix b n 𝕜) (U : Matrix b r 𝕜) (σ : r → ℝ) :
    Matrix n r 𝕜 := Oᴴ * U * invSqrtDiagonal σ

/-- Positive retained singular triplets construct biorthogonal coordinates
and balance both compressed Gramian forms, even when directions are discarded.
Brunton–Kutz (2022), equations (9.29)–(9.35).
atlas: gramian-svd-balancing (partial) -/
theorem IsSingularTripletFamily.gramian_balancing {R : Matrix n a 𝕜} {O : Matrix b n 𝕜}
    {U : Matrix b r 𝕜} {V : Matrix a r 𝕜} {σ : r → ℝ}
    (h : IsSingularTripletFamily (O * R) U V σ) :
    let Ψ := balancingTrialMap R V σ
    let Φ := balancingTestMap O U σ
    Φᴴ * Ψ = 1 ∧
      Φᴴ * (R * Rᴴ) * Φ = diagonal (fun i => (σ i : 𝕜)) ∧
      Ψᴴ * (Oᴴ * O) * Ψ = diagonal (fun i => (σ i : 𝕜)) := by
  let D := invSqrtDiagonal (𝕜 := 𝕜) σ
  let S := diagonal (fun i => (σ i : 𝕜))
  have hD : Dᴴ = D := invSqrtDiagonal_isHermitian σ
  have hS : (diagonal fun i => (σ i : 𝕜))ᴴ = diagonal (fun i => (σ i : 𝕜)) :=
    diagonal_ofReal_isHermitian σ
  have hSS : Sᴴ = S := hS
  have hUV : Uᴴ * (O * R) * V = S := by
    rw [Matrix.mul_assoc, h.mul_right, ← Matrix.mul_assoc,
      h.left_orth.conjTranspose_mul_self, Matrix.one_mul]
  have hleft : Uᴴ * (O * R) = S * Vᴴ := by
    have he := congrArg Matrix.conjTranspose h.adjoint_mul_left
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hS] using he
  dsimp only
  constructor
  · change (Oᴴ * U * D)ᴴ * (R * V * D) = 1
    calc
      _ = D * (Uᴴ * (O * R) * V) * D := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD,
          Matrix.mul_assoc]
      _ = 1 := by rw [hUV]; exact invSqrtDiagonal_mul_diagonal_mul σ h.pos
  constructor
  · change (Oᴴ * U * D)ᴴ * (R * Rᴴ) * (Oᴴ * U * D) = S
    calc
      _ = D * (Uᴴ * (O * R)) * (Uᴴ * (O * R))ᴴ * D := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD,
          Matrix.mul_assoc]
      _ = D * S * (Vᴴ * V) * S * D := by
        rw [hleft]
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hSS,
          Matrix.mul_assoc]
      _ = S := by
        rw [h.right_orth.conjTranspose_mul_self, Matrix.mul_one]
        exact invSqrtDiagonal_mul_diagonal_sq_mul σ h.pos
  · change (R * V * D)ᴴ * (Oᴴ * O) * (R * V * D) = S
    calc
      _ = D * ((O * R) * V)ᴴ * ((O * R) * V) * D := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD,
          Matrix.mul_assoc]
      _ = D * S * (Uᴴ * U) * S * D := by
        rw [h.mul_right]
        simp only [Matrix.conjTranspose_mul, hS, S, Matrix.mul_assoc]
      _ = S := by
        rw [h.left_orth.conjTranspose_mul_self, Matrix.mul_one]
        exact invSqrtDiagonal_mul_diagonal_sq_mul σ h.pos

/-- With all state directions retained, the trial map is invertible and its
inverse is the test map's adjoint. Both Gramian forms and their product are
balanced in these coordinates. The positive-definite full-state case in the
source is included; the biorthogonality already proves invertibility.
atlas: gramian-svd-balancing (partial) -/
theorem IsSingularTripletFamily.full_gramian_balancing {R : Matrix n a 𝕜} {O : Matrix b n 𝕜}
    {U : Matrix b n 𝕜} {V : Matrix a n 𝕜} {σ : n → ℝ}
    (h : IsSingularTripletFamily (O * R) U V σ) :
    let T := balancingTrialMap R V σ
    let Φ := balancingTestMap O U σ
    IsUnit T ∧ T⁻¹ = Φᴴ ∧
      T⁻¹ * (R * Rᴴ) * T⁻¹ᴴ = diagonal (fun i => (σ i : 𝕜)) ∧
      Tᴴ * (Oᴴ * O) * T = diagonal (fun i => (σ i : 𝕜)) ∧
      T⁻¹ * ((R * Rᴴ) * (Oᴴ * O)) * T = diagonal (fun i => (σ i : 𝕜) ^ 2) := by
  let T := balancingTrialMap R V σ
  let Φ := balancingTestMap O U σ
  obtain ⟨hcross, hP, hQ⟩ := h.gramian_balancing
  have hother : T * Φᴴ = 1 := mul_eq_one_comm.mp hcross
  have hunit : IsUnit T := ⟨⟨T, Φᴴ, hother, hcross⟩, rfl⟩
  have hinv : T⁻¹ = Φᴴ := Matrix.inv_eq_left_inv hcross
  have hmid : Φ * Tᴴ = 1 := by
    have hc := congrArg Matrix.conjTranspose hother
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one] using hc
  refine ⟨hunit, hinv, ?_, hQ, ?_⟩
  · rw [hinv, Matrix.conjTranspose_conjTranspose]
    exact hP
  · rw [hinv]
    calc
      _ = (Φᴴ * (R * Rᴴ) * Φ) * (Tᴴ * (Oᴴ * O) * T) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Φ Tᴴ, hmid, Matrix.one_mul]
      _ = _ := by rw [hP, hQ, Matrix.diagonal_mul_diagonal]; simp only [pow_two]

/-- The Gramian product and `HᴴH`, `H=OR`, have identical nonzero
characteristic roots, with multiplicities certified before cancellation.
Thus its positive eigenvalues are precisely positive squared singular values
of `OR`, including the rectangular and singular cases.
atlas: gramian-svd-balancing (partial) -/
theorem charpoly_gramian_product_mul_X (R : Matrix n a 𝕜) (O : Matrix b n 𝕜) :
    Polynomial.X ^ Fintype.card a * ((R * Rᴴ) * (Oᴴ * O)).charpoly =
      Polynomial.X ^ Fintype.card n * ((O * R)ᴴ * (O * R)).charpoly := by
  have he := Matrix.charpoly_mul_comm' R (Rᴴ * Oᴴ * O)
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using he

/-- Away from zero, Gramian-product eigenvalues are exactly Gram eigenvalues
of the factor product. The preceding identity also retains multiplicities. -/
theorem isRoot_charpoly_gramian_product_iff (R : Matrix n a 𝕜) (O : Matrix b n 𝕜)
    {z : 𝕜} (hz : z ≠ 0) :
    ((R * Rᴴ) * (Oᴴ * O)).charpoly.IsRoot z ↔
      ((O * R)ᴴ * (O * R)).charpoly.IsRoot z := by
  have he := congrArg (Polynomial.eval z) (charpoly_gramian_product_mul_X R O)
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at he
  change _ = 0 ↔ _ = 0
  constructor
  · intro hzero
    have hprod : z ^ Fintype.card n * (((O * R)ᴴ * (O * R)).charpoly.eval z) = 0 := by
      rw [← he, hzero, mul_zero]
    exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ hz)
  · intro hzero
    have hprod : z ^ Fintype.card a * (((R * Rᴴ) * (Oᴴ * O)).charpoly.eval z) = 0 := by
      rw [he, hzero, mul_zero]
    exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ hz)

/-- The positive eigenvalues of the Gramian product are precisely the
positive squares of singular values of the Hankel factor product, without
positive-definiteness or square-factor assumptions.
atlas: gramian-svd-balancing (partial) -/
theorem isRoot_charpoly_gramian_product_iff_sq_singularValues
    (R : Matrix n a 𝕜) (O : Matrix b n 𝕜) {μ : ℝ} (hμ : 0 < μ) :
    ((R * Rᴴ) * (Oᴴ * O)).charpoly.IsRoot (μ : 𝕜) ↔
      ∃ j : Fin (Fintype.card a), μ = singularValues (O * R) j ^ 2 := by
  rw [isRoot_charpoly_gramian_product_iff R O (by exact_mod_cast hμ.ne')]
  obtain ⟨U, V, hSVD⟩ := exists_isSVD (O * R)
  have hchar : ((O * R)ᴴ * (O * R)).charpoly =
      (diagonal fun j : Fin (Fintype.card a) =>
        ((singularValues (O * R) j ^ 2 : ℝ) : 𝕜)).charpoly := by
    rw [hSVD.conjTranspose_mul_self,
      Matrix.charpoly_mul_comm_of_le _ Vᴴ (by simp), Fintype.card_fin,
      Nat.sub_self, pow_zero, one_mul, ← Matrix.mul_assoc,
      hSVD.conjTranspose_mul_right, Matrix.one_mul]
  rw [hchar, Matrix.charpoly_diagonal, Polynomial.IsRoot, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, by exact_mod_cast hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, by exact_mod_cast hj⟩

end NLAlib
