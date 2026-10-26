import NLAlib.Matrix.Spectral.SaddlePointPolynomial

/-!
# Paired eigenvalues of a normalized saddle-point matrix

The Gram eigenvalue `mu` gives the two roots `(1 ± sqrt(1+4mu))/2`.
The characteristic-root multiset retains repeated eigenvalues, and full row rank
makes the multiplicity of the unit eigenvalue exactly the rectangular excess.
-/

noncomputable section
open scoped Matrix Polynomial ComplexOrder
open Polynomial
namespace NLAlib

/-- Positive branch of the saddle-point quadratic eigenvalue relation. -/
def saddleEigenvaluePlus (mu : ℝ) : ℝ := (1 + Real.sqrt (1 + 4 * mu)) / 2

/-- Negative branch of the saddle-point quadratic eigenvalue relation. -/
def saddleEigenvalueMinus (mu : ℝ) : ℝ := (1 - Real.sqrt (1 + 4 * mu)) / 2

theorem monotone_saddleEigenvaluePlus : Monotone saddleEigenvaluePlus := by
  intro x y h
  have hs := Real.sqrt_le_sqrt (show 1 + 4 * x ≤ 1 + 4 * y by linarith)
  dsimp [saddleEigenvaluePlus]
  linarith

theorem antitone_saddleEigenvalueMinus : Antitone saddleEigenvalueMinus := by
  intro x y h
  have hs := Real.sqrt_le_sqrt (show 1 + 4 * x ≤ 1 + 4 * y by linarith)
  dsimp [saddleEigenvalueMinus]
  linarith

theorem one_lt_saddleEigenvaluePlus_and_saddleEigenvalueMinus_lt_zero
    {mu : ℝ} (hmu : 0 < mu) :
    1 < saddleEigenvaluePlus mu ∧ saddleEigenvalueMinus mu < 0 := by
  have hs : 1 < Real.sqrt (1 + 4 * mu) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  dsimp [saddleEigenvaluePlus, saddleEigenvalueMinus]
  constructor <;> linarith

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Factorization of each scalar quadratic over either real or complex scalars. -/
theorem saddle_quadratic_factor {mu : ℝ} (hmu : 0 ≤ mu) :
    (X ^ 2 - X - Polynomial.C (mu : 𝕜)) =
      (X - Polynomial.C (saddleEigenvaluePlus mu : 𝕜)) *
        (X - Polynomial.C (saddleEigenvalueMinus mu : 𝕜)) := by
  have hs : saddleEigenvaluePlus mu + saddleEigenvalueMinus mu = 1 := by
    dsimp [saddleEigenvaluePlus, saddleEigenvalueMinus]
    ring
  have hp : saddleEigenvaluePlus mu * saddleEigenvalueMinus mu = -mu := by
    have hsq := Real.sq_sqrt (show 0 ≤ 1 + 4 * mu by positivity)
    dsimp [saddleEigenvaluePlus, saddleEigenvalueMinus]
    nlinarith
  have hsK : (saddleEigenvaluePlus mu : 𝕜) + (saddleEigenvalueMinus mu : 𝕜) = 1 := by
    exact_mod_cast hs
  have hpK : (saddleEigenvaluePlus mu : 𝕜) * (saddleEigenvalueMinus mu : 𝕜) = -(mu : 𝕜) := by
    exact_mod_cast hp
  symm
  calc
    _ = X ^ 2 - Polynomial.C ((saddleEigenvaluePlus mu : 𝕜) +
          (saddleEigenvalueMinus mu : 𝕜)) * X +
        Polynomial.C ((saddleEigenvaluePlus mu : 𝕜) * (saddleEigenvalueMinus mu : 𝕜)) := by
      rw [map_add, map_mul]
      ring
    _ = _ := by rw [hsK, hpK, map_one, map_neg]; ring

/-- The complete spectrum with algebraic multiplicities, including zero Gram
eigenvalues if the coupling is rank deficient. -/
theorem roots_charpoly_kktMatrix_one (C : Matrix m n 𝕜)
    (hmn : Fintype.card m ≤ Fintype.card n) :
    let mu := (Matrix.isHermitian_mul_conjTranspose_self C).eigenvalues
    (kktMatrix 1 C).charpoly.roots =
      (Fintype.card n - Fintype.card m) • ({1} : Multiset 𝕜) +
        Finset.univ.val.bind (fun i : m =>
          {(saddleEigenvaluePlus (mu i) : 𝕜)} + {(saddleEigenvalueMinus (mu i) : 𝕜)}) := by
  dsimp only
  have hp := charpoly_kktMatrix_one_eq_prod C hmn
  simp_rw [saddle_quadratic_factor (Matrix.posSemidef_self_mul_conjTranspose C |>.eigenvalues_nonneg _)] at hp
  rw [hp, Polynomial.roots_mul (by rw [← hp]; exact (Matrix.charpoly_monic _).ne_zero)]
  rw [Polynomial.roots_pow, show (X - 1 : 𝕜[X]) = X - Polynomial.C 1 by simp,
    Polynomial.roots_X_sub_C, Polynomial.roots_prod]
  · congr 1
    congr 1
    funext i
    rw [Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
      Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
  · exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)

/-- Full row rank makes the unit-eigenvalue multiplicity exactly `n-m`. -/
theorem count_one_roots_charpoly_kktMatrix_one {C : Matrix m n 𝕜}
    (hC : (C * Cᴴ).PosDef) (hmn : Fintype.card m ≤ Fintype.card n) :
    (kktMatrix 1 C).charpoly.roots.count 1 = Fintype.card n - Fintype.card m := by
  classical
  rw [roots_charpoly_kktMatrix_one C hmn, Multiset.count_add]
  have hp : ∀ i, (saddleEigenvaluePlus (hC.isHermitian.eigenvalues i) : 𝕜) ≠ 1 := by
    intro i he
    have hr : saddleEigenvaluePlus (hC.isHermitian.eigenvalues i) = 1 := by exact_mod_cast he
    exact (ne_of_gt (one_lt_saddleEigenvaluePlus_and_saddleEigenvalueMinus_lt_zero
      (hC.eigenvalues_pos i)).1) hr
  have hm : ∀ i, (saddleEigenvalueMinus (hC.isHermitian.eigenvalues i) : 𝕜) ≠ 1 := by
    intro i he
    have hr : saddleEigenvalueMinus (hC.isHermitian.eigenvalues i) = 1 := by exact_mod_cast he
    have hn := (one_lt_saddleEigenvaluePlus_and_saddleEigenvalueMinus_lt_zero
      (hC.eigenvalues_pos i)).2
    linarith
  have hz : 1 ∉ Finset.univ.val.bind (fun i : m =>
      {(saddleEigenvaluePlus (hC.isHermitian.eigenvalues i) : 𝕜)} +
        {(saddleEigenvalueMinus (hC.isHermitian.eigenvalues i) : 𝕜)}) := by
    simp [hp, hm]
  rw [Multiset.count_eq_zero.mpr hz]
  simp

end NLAlib
