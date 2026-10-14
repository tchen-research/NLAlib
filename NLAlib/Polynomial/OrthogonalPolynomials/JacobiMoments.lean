import NLAlib.Polynomial.OrthogonalPolynomials.JacobiMatrix

/-! # First-coordinate moments of finite moment Jacobi matrices

Compressed multiplication preserves polynomial coordinates until the first
omitted degree. Splitting a power into two bounded halves gives the full
degree-`2n-1` moment range, including finite-support termination.
Source: Golub–Meurant (2010), Chapter 2; operator derivations BL3.
-/

noncomputable section

open Polynomial Matrix Finset MeasureTheory
open scoped Matrix

namespace NLAlib

/-- Coordinates of a polynomial obtained by pairing against the first
normalized moment polynomials. -/
def orthonormalMomentCoordinates (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) (p : ℝ[X]) : Fin n → ℝ :=
  fun i => L (p * orthonormalMomentPolynomial L i.val)

/-- Every lower-degree polynomial is recovered by its orthonormal moment
coordinates. -/
theorem sum_C_mul_orthonormalMomentCoordinates_eq (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ}
    (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0)
    (hH : ∀ k < n, 0 < orthogonalPolynomialNorm L k)
    {p : ℝ[X]} (hp : p.degree < n) :
    (∑ i : Fin n, C (orthonormalMomentCoordinates L n p i) *
      orthonormalMomentPolynomial L i.val) = p := by
  obtain ⟨c, hc⟩ := exists_sum_smul_monicOrthogonalPolynomial_eq_of_degree_lt L hp
  let v : Fin n → ℝ := fun i => c i.val * Real.sqrt (orthogonalPolynomialNorm L i.val)
  have hv : (∑ i : Fin n, C (v i) * orthonormalMomentPolynomial L i.val) = p := by
    calc
      _ = ∑ i : Fin n, c i.val • monicOrthogonalPolynomial L i.val := by
        apply sum_congr rfl
        intro i _
        dsimp only [v]
        rw [C_mul, mul_assoc, sqrt_norm_mul_orthonormalMomentPolynomial (hH i.val i.isLt), C_mul']
      _ = p := by
        exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => c j • monicOrthogonalPolynomial L j) n).trans hc
  have hcoord (i : Fin n) : orthonormalMomentCoordinates L n p i = v i := by
    rw [orthonormalMomentCoordinates, ← hv]
    exact functional_sum_C_mul_orthonormalMomentPolynomial_mul L hL hH v i
  simp only [hcoord]
  exact hv

/-- The coordinate vector of `X*p` is the Jacobi matrix applied to the
coordinate vector of `p` whenever `p` lies in the compressed space. -/
theorem jacobi_mulVec_orthonormalMomentCoordinates (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ}
    (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0)
    (hH : ∀ k < n, 0 < orthogonalPolynomialNorm L k)
    {p : ℝ[X]} (hp : p.degree < n) :
    orthogonalPolynomialJacobiMatrix L n *ᵥ orthonormalMomentCoordinates L n p =
      orthonormalMomentCoordinates L n (X * p) := by
  have hrec := sum_C_mul_orthonormalMomentCoordinates_eq L hL hH hp
  ext i
  change (orthogonalPolynomialJacobiMatrix L n *ᵥ orthonormalMomentCoordinates L n p) i =
    L ((X * p) * orthonormalMomentPolynomial L i.val)
  conv_rhs => rw [← hrec]
  simp only [orthogonalPolynomialJacobiMatrix, Matrix.mulVec, dotProduct,
    mul_sum, sum_mul, map_sum]
  apply sum_congr rfl
  intro j _
  rw [show X * (C (orthonormalMomentCoordinates L n p j) * orthonormalMomentPolynomial L j.val) *
      orthonormalMomentPolynomial L i.val =
      C (orthonormalMomentCoordinates L n p j) *
        (X * orthonormalMomentPolynomial L j.val * orthonormalMomentPolynomial L i.val) by ring,
    C_mul', map_smul, smul_eq_mul]
  exact mul_comm _ _

/-- Pairing one lower-degree polynomial with any polynomial is the dot
product of their moment coordinates; the second polynomial may have the first
omitted degree. -/
theorem functional_mul_eq_dotProduct_orthonormalMomentCoordinates (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ}
    (hL : ∀ k ≤ n, hankelMomentDet L k ≠ 0)
    (hH : ∀ k < n, 0 < orthogonalPolynomialNorm L k)
    {p : ℝ[X]} (hp : p.degree < n) (r : ℝ[X]) :
    L (p * r) = orthonormalMomentCoordinates L n p ⬝ᵥ orthonormalMomentCoordinates L n r := by
  have hrec := sum_C_mul_orthonormalMomentCoordinates_eq L hL hH hp
  conv_lhs => rw [← hrec]
  simp only [sum_mul, map_sum, dotProduct, orthonormalMomentCoordinates]
  apply sum_congr rfl
  intro i _
  rw [mul_assoc, C_mul', map_smul, smul_eq_mul, mul_comm (orthonormalMomentPolynomial L i.val) r]

/-- Matrix powers through the compressed order recover the coordinates of
`X^k*p₀`, including the first projected omitted degree. -/
theorem pow_jacobi_mulVec_single_eq_orthonormalMomentCoordinates
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ} (hn : 0 < n)
    (hL : ∀ j ≤ n, hankelMomentDet L j ≠ 0)
    (hH : ∀ j < n, 0 < orthogonalPolynomialNorm L j) (k : ℕ) (hk : k ≤ n) :
    (orthogonalPolynomialJacobiMatrix L n ^ k) *ᵥ Pi.single ⟨0, hn⟩ 1 =
      orthonormalMomentCoordinates L n (X ^ k * orthonormalMomentPolynomial L 0) := by
  induction k with
  | zero =>
    simp only [pow_zero, one_mul, Matrix.one_mulVec]
    ext i
    simp only [orthonormalMomentCoordinates,
      functional_orthonormalMomentPolynomial_mul L (hL 0 (by omega)) (hL i.val i.isLt.le)
        (hH 0 hn) (hH i.val i.isLt), Pi.single_apply]
    congr 1
    exact propext ⟨fun h => (congrArg Fin.val h).symm, fun h => Fin.ext h.symm⟩
  | succ k ih =>
    have hd : (X ^ k * orthonormalMomentPolynomial L 0).degree < (n : WithBot ℕ) := by
      rw [degree_mul, degree_X_pow, degree_orthonormalMomentPolynomial (hH 0 hn)]
      simp only [Nat.cast_zero, add_zero]
      exact_mod_cast (show k < n by omega)
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih (by omega),
      jacobi_mulVec_orthonormalMomentCoordinates L hL hH hd]
    congr 1
    rw [pow_succ']
    ring

/-- The mass-scaled first-coordinate powers reproduce all moments below
degree twice the finite Jacobi order. No positive norm at the terminal degree
is required. Source: Golub–Meurant (2010), Chapter 2, BL3.
atlas: gauss-radau-lobatto (partial), jacobi-fraction-second-kind (partial), jacobi-matrix-identities (partial) -/
theorem functional_X_pow_eq_mass_mul_jacobi_pow_apply_zero_zero
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ} (hn : 0 < n)
    (hL : ∀ j ≤ n, hankelMomentDet L j ≠ 0)
    (hH : ∀ j < n, 0 < orthogonalPolynomialNorm L j) {k : ℕ} (hk : k < 2 * n) :
    L (X ^ k) = L 1 * (orthogonalPolynomialJacobiMatrix L n ^ k) ⟨0, hn⟩ ⟨0, hn⟩ := by
  let J := orthogonalPolynomialJacobiMatrix L n
  let e : Fin n → ℝ := Pi.single ⟨0, hn⟩ 1
  let i := k / 2
  let j := k - i
  have hi : i < n := by dsimp [i]; omega
  have hj : j ≤ n := by dsimp [j, i]; omega
  have hij : i + j = k := by dsimp [i, j]; omega
  have hsym : Jᵀ = J := (Matrix.isHermitian_iff_isSymm.mp
    (isHermitian_orthogonalPolynomialJacobiMatrix L n)).eq
  have hpow : e ⬝ᵥ ((J ^ k) *ᵥ e) = ((J ^ i) *ᵥ e) ⬝ᵥ ((J ^ j) *ᵥ e) := by
    rw [← hij, pow_add, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
      ← show (J ^ i)ᵀ = J ^ i by rw [transpose_pow, hsym], vecMul_transpose]
    rw [transpose_pow, hsym]
  have hPi : (X ^ i * orthonormalMomentPolynomial L 0).degree < (n : WithBot ℕ) := by
    rw [degree_mul, degree_X_pow, degree_orthonormalMomentPolynomial (hH 0 hn)]
    simp only [Nat.cast_zero, add_zero]
    exact_mod_cast hi
  have hpair := functional_mul_eq_dotProduct_orthonormalMomentCoordinates L hL hH hPi
    (X ^ j * orthonormalMomentPolynomial L 0)
  rw [← pow_jacobi_mulVec_single_eq_orthonormalMomentCoordinates L hn hL hH i hi.le,
    ← pow_jacobi_mulVec_single_eq_orthonormalMomentCoordinates L hn hL hH j hj, ← hpow] at hpair
  have heval : e ⬝ᵥ ((J ^ k) *ᵥ e) = (J ^ k) ⟨0, hn⟩ ⟨0, hn⟩ := by
    rw [dotProduct_comm, dotProduct_single_one, Matrix.mulVec_single_one]
    rfl
  rw [heval] at hpair
  have hH0 : orthogonalPolynomialNorm L 0 = L 1 := by simp [orthogonalPolynomialNorm]
  have hcancel : L 1 * (Real.sqrt (orthogonalPolynomialNorm L 0))⁻¹ ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt (hH 0 hn).le, ← hH0, mul_inv_cancel₀ (hH 0 hn).ne']
  have hp0 : orthonormalMomentPolynomial L 0 = C (Real.sqrt (orthogonalPolynomialNorm L 0))⁻¹ := by
    simp [orthonormalMomentPolynomial]
  have hprod : (X ^ i * orthonormalMomentPolynomial L 0) *
      (X ^ j * orthonormalMomentPolynomial L 0) =
        C ((Real.sqrt (orthogonalPolynomialNorm L 0))⁻¹ ^ 2) * X ^ k := by
    rw [hp0, ← hij, pow_add, C_pow]
    ring
  rw [hprod, C_mul', map_smul, smul_eq_mul] at hpair
  change L (X ^ k) = L 1 * (J ^ k) ⟨0, hn⟩ ⟨0, hn⟩
  rw [← hpair, ← mul_assoc, hcancel, one_mul]

/-- The first-coordinate functional calculus of the finite Jacobi matrix
reproduces every polynomial below twice its order. -/
theorem functional_eq_mass_mul_aeval_jacobi_apply_zero_zero
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n : ℕ} (hn : 0 < n)
    (hL : ∀ j ≤ n, hankelMomentDet L j ≠ 0)
    (hH : ∀ j < n, 0 < orthogonalPolynomialNorm L j) {p : ℝ[X]}
    (hp : p.degree < (2 * n : ℕ)) :
    L p = L 1 * (aeval (orthogonalPolynomialJacobiMatrix L n) p) ⟨0, hn⟩ ⟨0, hn⟩ := by
  have heq := eq_sum_monomial_fin_of_degree_lt hp
  rw [heq, map_sum, map_sum]
  simp only [← C_mul_X_pow_eq_monomial, C_mul', map_smul, smul_eq_mul,
    map_pow, aeval_X]
  rw [Matrix.sum_apply, mul_sum]
  simp only [Matrix.smul_apply, smul_eq_mul]
  apply sum_congr rfl
  intro j _
  rw [functional_X_pow_eq_mass_mul_jacobi_pow_apply_zero_zero L hn hL hH j.isLt]
  ring

/-- The actual measure moment Jacobi matrix reproduces moments through
`2n-1`, including finite-support termination.
atlas: gauss-radau-lobatto (partial), jacobi-matrix-identities (partial) -/
theorem integral_pow_eq_mass_mul_orthogonalPolynomialJacobiMatrix_pow
    {μ : Measure ℝ} (hμ : HasPolynomialMoments μ) {n : ℕ} (hn : 0 < n)
    (hs : (n : ℕ∞) ≤ μ.support.encard) {k : ℕ} (hk : k < 2 * n) :
    (∫ x : ℝ, x ^ k ∂μ) = (∫ _ : ℝ, (1 : ℝ) ∂μ) *
      (orthogonalPolynomialJacobiMatrix (polynomialIntegral μ hμ) n ^ k) ⟨0, hn⟩ ⟨0, hn⟩ := by
  have h := functional_X_pow_eq_mass_mul_jacobi_pow_apply_zero_zero (polynomialIntegral μ hμ) hn
    (fun j hj => hankelMomentDet_ne_zero_of_le_support_encard μ hμ
      ((by exact_mod_cast hj : (j : ℕ∞) ≤ n).trans hs))
    (fun j hj => orthogonalPolynomialNorm_pos_of_lt_support_encard μ hμ
      ((by exact_mod_cast Nat.succ_le_of_lt hj : (j + 1 : ℕ∞) ≤ n).trans hs)) hk
  simpa only [polynomialIntegral_apply, eval_pow, eval_X, eval_one] using h

end NLAlib
