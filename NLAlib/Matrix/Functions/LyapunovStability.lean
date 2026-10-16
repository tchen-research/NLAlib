import NLAlib.Matrix.Functions.LyapunovCayley

/-! # Strict Lyapunov certificates characterize Hurwitz stability -/

noncomputable section
open scoped Matrix MatrixOrder ComplexOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A genuine positive definite Lyapunov certificate forces all complex
eigenvalues into the strict left half-plane, without normality. -/
theorem isHurwitz_of_posDef_lyapunov (A X : Matrix n n ℂ) (hX : X.PosDef)
    (hR : (-(A * X + X * Aᴴ)).PosDef) : IsHurwitz A := by
  intro μ hμ
  obtain ⟨y, hy, hyA⟩ := exists_vecMul_eq_smul_of_mem_spectrum hμ
  have hx : star y ≠ 0 := by simpa only [star_ne_zero] using hy
  have hAx : Aᴴ *ᵥ star y = star μ • star y := by rw [← Matrix.star_vecMul, hyA, star_smul]
  have hquad : quadForm (A * X + X * Aᴴ) (star y) =
      (μ + star μ) * quadForm X (star y) := by
    unfold quadForm
    rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (star (star y)) A,
      star_star, hyA, hAx]
    simp only [smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
      ]
    ring
  have hXp : 0 < (quadForm X (star y)).re := (RCLike.pos_iff.mp (hX.quadForm_pos hx)).1
  have hRp := (RCLike.pos_iff.mp (hR.quadForm_pos hx)).1
  change 0 < (quadForm (-(A * X + X * Aᴴ)) (star y)).re at hRp
  have hreal : (quadForm (-(A * X + X * Aᴴ)) (star y)).re =
      -(2 * μ.re * (quadForm X (star y)).re) := by
    have hn : quadForm (-(A * X + X * Aᴴ)) (star y) =
        -quadForm (A * X + X * Aᴴ) (star y) := by
      simp only [quadForm, Matrix.neg_mulVec, dotProduct_neg]
    have hμ : μ + star μ = ((2 * μ.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [RCLike.star_def] <;> ring
    rw [hn, hquad, hμ]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  rw [hreal] at hRp
  by_contra h
  have hμ0 : 0 ≤ μ.re := le_of_not_gt h
  have hprod : 0 ≤ 2 * μ.re * (quadForm X (star y)).re :=
    mul_nonneg (mul_nonneg (by norm_num) hμ0) hXp.le
  linarith

/-- Strict continuous stability is equivalent to a strict positive definite
Lyapunov certificate. Source: user derivations, continuous Lyapunov stability.
atlas: lyapunov-stability-gramian (partial) -/
theorem isHurwitz_iff_exists_posDef_lyapunov (A : Matrix n n ℂ) :
    IsHurwitz A ↔ ∃ X : Matrix n n ℂ, X.PosDef ∧ (-(A * X + X * Aᴴ)).PosDef := by
  constructor
  · intro hA
    let X := lyapunovCayleySolution A 1
    have heq := lyapunovCayleySolution_equation A 1 hA
    refine ⟨X, posDef_lyapunovCayleySolution A 1 hA Matrix.PosDef.one, ?_⟩
    have hsum : A * X + X * Aᴴ = -1 := eq_neg_of_add_eq_zero_left heq
    rw [hsum, neg_neg]
    exact Matrix.PosDef.one
  · rintro ⟨X, hX, hR⟩
    exact isHurwitz_of_posDef_lyapunov A X hX hR

end NLAlib
