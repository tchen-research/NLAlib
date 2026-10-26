import NLAlib.Matrix.Equations.LyapunovCoercivity
import NLAlib.Matrix.Spectral.NumericalRange
import NLAlib.Matrix.Spectral.HermitianExtremaNorm
import Mathlib.Analysis.Matrix.Order

/-!
# Strictly dissipative Lyapunov equations

Quadratic-form bounds pass to orthonormal compressions. The finite Lyapunov solution
is positive semidefinite for positive semidefinite forcing. For Hermitian errors,
testing at eigenvectors gives the sharp `1/(2a)` spectral-norm bound.
Source: the finite coercivity and eigenvector route in the supplied Krylov derivations.
-/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder InnerProductSpace
namespace NLAlib
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The Loewner dissipativity condition gives its scalar quadratic-form bound. -/
theorem re_quadForm_le_of_add_conjTranspose_le {A : Matrix n n 𝕜} {a : ℝ}
    (hA : A + Aᴴ ≤ (-2 * a) • (1 : Matrix n n 𝕜)) (v : n → 𝕜) :
    RCLike.re (quadForm A v) ≤ -a * ‖WithLp.toLp 2 v‖ ^ 2 := by
  rw [norm_toLp_sq_eq_re_star_dotProduct]
  have h := (Matrix.le_iff.mp hA).re_quadForm_nonneg v
  change 0 ≤ RCLike.re (quadForm ((-2 * a) • (1 : Matrix n n 𝕜) - (A + Aᴴ)) v) at h
  have hs := star_quadForm A v
  simp only [quadForm, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul,
    map_sub, map_add, RCLike.smul_re] at h
  change 0 ≤ (-2 * a) * RCLike.re (star v ⬝ᵥ v) -
    (RCLike.re (quadForm A v) + RCLike.re (quadForm Aᴴ v)) at h
  rw [← hs, RCLike.star_def, RCLike.conj_re] at h
  linarith

omit [DecidableEq n] in
/-- Orthonormal compression preserves the same strict quadratic-form bound. -/
theorem re_quadForm_compression_le {k : Type*} [Fintype k] [DecidableEq k]
    {A : Matrix n n 𝕜} {a : ℝ}
    (hA : ∀ v : n → 𝕜, RCLike.re (quadForm A v) ≤ -a * ‖WithLp.toLp 2 v‖ ^ 2)
    {V : Matrix n k 𝕜} (hV : HasOrthonormalCols V) (v : k → 𝕜) :
    RCLike.re (quadForm (Vᴴ * A * V) v) ≤ -a * ‖WithLp.toLp 2 v‖ ^ 2 := by
  have h := hA (V *ᵥ v)
  rw [← quadForm_conjTranspose_mul_mul, norm_toLp_sq_eq_re_star_dotProduct] at h
  rw [norm_toLp_sq_eq_re_star_dotProduct]
  have hn : star (V *ᵥ v) ⬝ᵥ (V *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      hV.conjTranspose_mul_self, Matrix.one_mulVec]
  rwa [hn] at h

omit [DecidableEq n] in
/-- Testing a Lyapunov operator at a Hermitian eigenvector gives a scalar product. -/
theorem re_quadForm_lyapunov_of_eigenvector (A : Matrix n n 𝕜)
    {E : Matrix n n 𝕜} (hE : E.IsHermitian) {v : n → 𝕜} {lam : ℝ}
    (hv : E *ᵥ v = (lam : 𝕜) • v) :
    RCLike.re (quadForm (A * E + E * Aᴴ) v) = 2 * lam * RCLike.re (quadForm A v) := by
  have hve : star v ᵥ* E = (lam : 𝕜) • star v := by
    rw [← hE.eq, ← Matrix.star_mulVec, hv, star_smul]
    simp
  have hq : quadForm (A * E + E * Aᴴ) v =
      (lam : 𝕜) * (quadForm A v + quadForm Aᴴ v) := by
    simp only [quadForm, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec]
    rw [hv, Matrix.mulVec_smul, dotProduct_smul, Matrix.dotProduct_mulVec (star v) E, hve,
      smul_dotProduct]
    simp only [smul_eq_mul]
    ring
  rw [hq, RCLike.re_ofReal_mul, map_add, ← star_quadForm,
    RCLike.star_def, RCLike.conj_re]
  ring

private theorem eigenvector_star_dotProduct {E : Matrix n n 𝕜}
    (hE : E.IsHermitian) (j : n) :
    star (hE.eigenvectorBasis j).ofLp ⬝ᵥ (hE.eigenvectorBasis j).ofLp = 1 := by
  have h : (inner 𝕜 (hE.eigenvectorBasis j) (hE.eigenvectorBasis j) : 𝕜) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hE.eigenvectorBasis.orthonormal.1 j]
    simp
  rwa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h

/-- Positive semidefinite forcing produces a positive semidefinite Lyapunov solution. -/
theorem posSemidef_lyapunov_solution_of_quadratic_bound {A Q X : Matrix n n 𝕜} {a : ℝ}
    (ha : 0 < a)
    (hA : ∀ v : n → 𝕜, RCLike.re (quadForm A v) ≤ -a * ‖WithLp.toLp 2 v‖ ^ 2)
    (hQ : Q.PosSemidef) (hX : A * X + X * Aᴴ + Q = 0) : X.PosSemidef := by
  have hH := isHermitian_lyapunov_solution ha hA hQ.isHermitian hX
  apply hH.posSemidef_iff_eigenvalues_nonneg.mpr
  intro j
  let v := (hH.eigenvectorBasis j).ofLp
  have hv : X *ᵥ v = (hH.eigenvalues j : 𝕜) • v := by
    rw [← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    exact hH.mulVec_eigenvectorBasis j
  have hq := hA v
  rw [norm_toLp_sq_eq_re_star_dotProduct, eigenvector_star_dotProduct hH j,
    RCLike.one_re, mul_one] at hq
  have he := re_quadForm_lyapunov_of_eigenvector A hH hv
  rw [eq_neg_of_add_eq_zero_left hX] at he
  have hn : RCLike.re (quadForm (-Q) v) ≤ 0 := by
    simpa only [quadForm, Matrix.neg_mulVec, dotProduct_neg, map_neg] using
      neg_nonpos.mpr (hQ.re_quadForm_nonneg v)
  rw [he] at hn
  by_contra hneg
  have hl : hH.eigenvalues j < 0 := lt_of_not_ge hneg
  nlinarith [mul_pos_of_neg_of_neg hl (lt_of_le_of_lt hq (by linarith))]

/-- On Hermitian errors, strict dissipativity gives the spectral inverse bound `1/(2a)`.
No spectral separation or semigroup estimate is assumed. -/
theorem specNorm_le_lyapunov_div {A E : Matrix n n 𝕜} {a : ℝ}
    (ha : 0 < a)
    (hA : ∀ v : n → 𝕜, RCLike.re (quadForm A v) ≤ -a * ‖WithLp.toLp 2 v‖ ^ 2)
    (hE : E.IsHermitian) : specNorm E ≤ specNorm (A * E + E * Aᴴ) / (2 * a) := by
  rw [hE.specNorm_eq_norm_eigenvalues]
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (specNorm_nonneg _) (by positivity))).mpr
  intro j
  let v := (hE.eigenvectorBasis j).ofLp
  have hv : E *ᵥ v = (hE.eigenvalues j : 𝕜) • v := by
    rw [← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    exact hE.mulVec_eigenvectorBasis j
  have hq := hA v
  rw [norm_toLp_sq_eq_re_star_dotProduct, eigenvector_star_dotProduct hE j,
    RCLike.one_re, mul_one] at hq
  have he := re_quadForm_lyapunov_of_eigenvector A hE hv
  have hnorm : ‖WithLp.toLp 2 v‖ = 1 := hE.eigenvectorBasis.orthonormal.1 j
  have hn := (RCLike.abs_re_le_norm (quadForm (A * E + E * Aᴴ) v)).trans
    (norm_quadForm_le_specNorm (A * E + E * Aᴴ) v)
  rw [hnorm, one_pow, mul_one, he] at hn
  rw [Real.norm_eq_abs]
  apply (le_div_iff₀ (by positivity : 0 < 2 * a)).2
  by_cases hl : 0 ≤ hE.eigenvalues j
  · rw [abs_of_nonneg hl]
    have hmul := mul_le_mul_of_nonneg_left hq hl
    nlinarith [neg_le_abs (2 * hE.eigenvalues j * RCLike.re (quadForm A v))]
  · rw [abs_of_neg (lt_of_not_ge hl)]
    have hmul := mul_le_mul_of_nonpos_left hq (le_of_not_ge hl)
    nlinarith [le_abs_self (2 * hE.eigenvalues j * RCLike.re (quadForm A v))]

end NLAlib
