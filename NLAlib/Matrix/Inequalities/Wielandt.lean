import NLAlib.Matrix.Inequalities.Kantorovich
/-!
# Wielandt's inequality for orthogonal vectors

Rescale two orthogonal vectors to equal energy in the positive definite
form. The two endpoint bounds on their sum and difference give the exact
angle constant. Source: Horn--Johnson (2013), Section 7.4.12;
atlas `kantorovich-inequality`.
-/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form of a scalar Loewner sandwich satisfies the same
endpoint bounds on every vector. Horn--Johnson (2013), Section 7.4.12;
helper for Wielandt's inequality. -/
theorem quadForm_bounds_of_sandwich {A : Matrix n n ℝ} {a b : ℝ}
    (hlo : a • (1 : Matrix n n ℝ) ≤ A) (hhi : A ≤ b • (1 : Matrix n n ℝ))
    (x : n → ℝ) : a * (x ⬝ᵥ x) ≤ quadForm A x ∧ quadForm A x ≤ b * (x ⬝ᵥ x) := by
  have hl := (Matrix.le_iff.mp hlo).dotProduct_mulVec_nonneg x
  have hu := (Matrix.le_iff.mp hhi).dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at hl hu
  exact ⟨sub_nonneg.mp hl, sub_nonneg.mp hu⟩

/-- Wielandt's sharp angle bound for orthogonal real vectors and arbitrary
positive spectral endpoints. Zero vectors and empty dimensions are included.
Horn--Johnson (2013), Section 7.4.12.
atlas: kantorovich-inequality (partial) -/
theorem sq_bilinear_le_sq_ratio_mul_quadForm_of_sandwich {A : Matrix n n ℝ}
    (hA : A.PosDef) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlo : a • (1 : Matrix n n ℝ) ≤ A) (hhi : A ≤ b • (1 : Matrix n n ℝ))
    (x y : n → ℝ) (hxy : x ⬝ᵥ y = 0) :
    (x ⬝ᵥ A *ᵥ y) ^ 2 ≤ ((b - a) / (b + a)) ^ 2 * quadForm A x * quadForm A y := by
  by_cases hx : x = 0
  · subst x; simp [quadForm]
  by_cases hy : y = 0
  · subst y; simp [quadForm]
  have hb : 0 < b := ha.trans_le hab
  have hs : 0 < quadForm A x := by simpa only [quadForm, star_trivial] using hA.dotProduct_mulVec_pos hx
  have ht : 0 < quadForm A y := by simpa only [quadForm, star_trivial] using hA.dotProduct_mulVec_pos hy
  let r := Real.sqrt (quadForm A y)
  let s := Real.sqrt (quadForm A x)
  have hr : r ^ 2 = quadForm A y := Real.sq_sqrt ht.le
  have hs' : s ^ 2 = quadForm A x := Real.sq_sqrt hs.le
  let S := quadForm A x * quadForm A y
  let N := quadForm A y * (x ⬝ᵥ x) + quadForm A x * (y ⬝ᵥ y)
  let w := r * s * (x ⬝ᵥ A *ᵥ y)
  have hS : 0 < S := mul_pos hs ht
  have hN (ε : ℝ) (hε : ε ^ 2 = 1) :
      (r • x + (ε * s) • y) ⬝ᵥ (r • x + (ε * s) • y) = N := by
    have hyx : y ⬝ᵥ x = 0 := by rw [dotProduct_comm, hxy]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hxy, hyx, mul_zero, add_zero, zero_add]
    calc
      _ = r ^ 2 * (x ⬝ᵥ x) + ε ^ 2 * s ^ 2 * (y ⬝ᵥ y) := by ring
      _ = N := by rw [hε, hr, hs', one_mul]
  have hE (ε : ℝ) (hε : ε ^ 2 = 1) :
      quadForm A (r • x + (ε * s) • y) = 2 * S + 2 * ε * w := by
    have h := hA.isHermitian.re_quadForm_smul_add_smul x y r (ε * s)
    simp only [RCLike.re_to_real, RCLike.ofReal_real_eq_id, id_eq, star_trivial] at h
    rw [h]
    dsimp [S, w]
    rw [mul_pow, hε, one_mul, hr, hs']
    ring
  have hp := quadForm_bounds_of_sandwich hlo hhi (r • x + (1 * s) • y)
  have hm := quadForm_bounds_of_sandwich hlo hhi (r • x + (-1 * s) • y)
  rw [hN 1 (by norm_num), hE 1 (by norm_num)] at hp
  rw [hN (-1) (by norm_num), hE (-1) (by norm_num)] at hm
  have hupper : (a + b) * w ≤ (b - a) * S := by
    have h1 := mul_le_mul_of_nonneg_left hp.2 ha.le
    have h2 := mul_le_mul_of_nonneg_left hm.1 hb.le
    nlinarith
  have hlower : -((b - a) * S) ≤ (a + b) * w := by
    have h1 := mul_le_mul_of_nonneg_left hm.2 ha.le
    have h2 := mul_le_mul_of_nonneg_left hp.1 hb.le
    nlinarith
  have habs : |(a + b) * w| ≤ (b - a) * S := abs_le.mpr ⟨hlower, hupper⟩
  have hsq := mul_self_le_mul_self (abs_nonneg ((a + b) * w)) habs
  have hw : w ^ 2 = S * (x ⬝ᵥ A *ᵥ y) ^ 2 := by
    dsimp [w, S]
    rw [mul_pow, mul_pow, hr, hs']
    ring
  have hsq' : (a + b) ^ 2 * (x ⬝ᵥ A *ᵥ y) ^ 2 ≤ (b - a) ^ 2 * S := by
    have hsq0 : ((a + b) * w) ^ 2 ≤ ((b - a) * S) ^ 2 := by
      nlinarith [sq_abs ((a + b) * w)]
    rw [mul_pow (a + b) w 2, mul_pow (b - a) S 2, hw] at hsq0
    apply (mul_le_mul_iff_of_pos_left hS).mp
    nlinarith
  rw [div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos (show 0 < b + a by positivity))).mpr
  dsimp [S] at hsq'
  nlinarith

end NLAlib
