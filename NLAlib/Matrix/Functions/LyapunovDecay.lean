import NLAlib.Matrix.Functions.LogarithmicNorm
import NLAlib.Matrix.Functions.GeometricMeanIdentities
import NLAlib.Matrix.Functions.LyapunovCayley

/-!
# Exponential decay from a strict Lyapunov certificate

Whitening a positive-definite certificate produces a generator with
strictly negative Hermitian part. The energy estimate then gives decay
for the original, possibly nonnormal, matrix by similarity. Together
with the Cayley construction this proves decay for every Hurwitz matrix.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- A genuine strict Lyapunov equation yields a uniform exponential
semigroup decay bound, without a normality or diagonalizability premise. -/
theorem exists_pos_exponential_decay_of_lyapunov {A X : Matrix n n ℂ}
    (hX : X.PosDef) (hAX : A * X + X * A.conjTranspose + 1 = 0) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧ ∀ t : ℝ, 0 ≤ t →
      specNorm (matrixExp (t • A)) ≤ C * Real.exp (-γ * t) := by
  let S := cfc Real.sqrt X
  let R := cfc (fun x => (Real.sqrt x)⁻¹) X
  let B := R * A * S
  have hS : S.IsHermitian := cfc_predicate _ _
  have hR : R.IsHermitian := cfc_predicate _ _
  have hSR : S * R = 1 := cfc_sqrt_mul_inv_sqrt hX
  have hRS : R * S = 1 := cfc_inv_sqrt_mul_sqrt hX
  have hSS : S * S = X := cfc_sqrt_mul_self hX
  have hRX : R * X = S := by rw [← hSS, ← Matrix.mul_assoc, hRS, Matrix.one_mul]
  have hXR : X * R = S := by rw [← hSS, Matrix.mul_assoc, hSR, Matrix.mul_one]
  have hi : X⁻¹ = R * R := inv_eq_cfc_inv_sqrt_mul_self hX
  have hsum : B + B.conjTranspose = -(R * R) := by
    have hAX' : A * X + X * A.conjTranspose = -1 := eq_neg_of_add_eq_zero_left hAX
    calc
      _ = R * (A * X + X * A.conjTranspose) * R := by
        dsimp [B]
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hR.eq, hS.eq]
        calc
          _ = R * A * (X * R) + (R * X) * A.conjTranspose * R := by
            rw [hXR, hRX]
            noncomm_ring
          _ = _ := by noncomm_ring
      _ = _ := by rw [hAX']; noncomm_ring
  let K : Matrix n n ℂ := -(selfAdjointPart ℝ B : Matrix n n ℂ)
  have hK : K = (2 : ℝ)⁻¹ • X⁻¹ := by
    dsimp [K]
    rw [selfAdjointPart_apply_coe, Matrix.star_eq_conjTranspose, hsum, ← hi]
    simp only [smul_neg, neg_neg, invOf_eq_inv]
  have hKpos : K.PosDef := by rw [hK]; exact hX.inv.smul (by norm_num : (0 : ℝ) < 2⁻¹)
  obtain ⟨γ, hγ, hgap⟩ :=
    (CFC.exists_pos_algebraMap_le_iff hKpos.isHermitian.isSelfAdjoint).mpr
      (fun x hx => hKpos.isStrictlyPositive.spectrum_pos hx)
  have hgap' : γ • (1 : Matrix n n ℂ) ≤ K := by
    simpa only [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] using hgap
  have hB : (selfAdjointPart ℝ B : Matrix n n ℂ) ≤ (-γ) • 1 := by
    apply Matrix.le_iff.mpr
    have hp := Matrix.le_iff.mp hgap'
    convert! hp using 1
    dsimp [K]
    module
  have hinter : S * B = A * S := by
    dsimp [B]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hSR, Matrix.one_mul]
  have hExp (t : ℝ) : matrixExp (t • A) = S * matrixExp (t • B) * R := by
    let : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    have h : SemiconjBy S (t • B) (t • A) := by
      change S * (t • B) = (t • A) * S
      rw [Matrix.mul_smul, Matrix.smul_mul, hinter]
    have he := h.exp_right
    change S * matrixExp (t • B) = matrixExp (t • A) * S at he
    calc
      _ = matrixExp (t • A) * (S * R) := by rw [hSR, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, ← he]
  refine ⟨1 + specNorm S * specNorm R, γ,
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)),
    hγ, ?_⟩
  intro t ht
  have hnorm := specNorm_matrixExp_smul_le_of_selfAdjointPart_le hB ht
  have hs : specNorm (matrixExp (t • A)) ≤
      specNorm S * specNorm (matrixExp (t • B)) * specNorm R := by
    rw [hExp]
    exact (specNorm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
  have heq : t * -γ = -γ * t := mul_comm _ _
  rw [heq] at hnorm
  have hbound := (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hnorm (specNorm_nonneg S)) (specNorm_nonneg R))
  exact (hs.trans hbound).trans (by nlinarith [Real.exp_pos (-γ * t)])

/-- Every Hurwitz complex matrix has a uniform exponential decay bound,
using the actual Cayley/Stein Lyapunov solution as its certificate. -/
theorem IsHurwitz.exists_pos_exponential_decay {A : Matrix n n ℂ} (hA : IsHurwitz A) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧ ∀ t : ℝ, 0 ≤ t →
      specNorm (matrixExp (t • A)) ≤ C * Real.exp (-γ * t) :=
  exists_pos_exponential_decay_of_lyapunov
    (posDef_lyapunovCayleySolution A 1 hA Matrix.PosDef.one)
    (lyapunovCayleySolution_equation A 1 hA)

end NLAlib
