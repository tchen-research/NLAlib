import NLAlib.Matrix.Structured.HermiteCompression
import NLAlib.Matrix.Structured.HermiteOrder
import NLAlib.Matrix.Structured.CoefficientBlockBounds
import NLAlib.Matrix.Norms.LoewnerBounds

/-! # Sharp finite Hermite compression bound

Variance and the largest coefficient-block eigenvalue bound the actual finite
creation matrix. The coefficient block is allowed to be indefinite. The
cutoff projection is used in both the commutator and number-operator estimate.
Source: Bandeira et al. (2026), finite Hermite proof of Theorem 1.5.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix Finset
open scoped Matrix Kronecker MatrixOrder ComplexOrder
namespace NLAlib
variable {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq ι] [DecidableEq d]

private theorem scalar_kronecker_one (r : ℝ) (E F : Type*)
    [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F] :
    (r • (1 : Matrix E E ℂ)) ⊗ₖ (1 : Matrix F F ℂ) =
      r • (1 : Matrix (E × F) (E × F) ℂ) := by
  rw [Matrix.smul_kronecker, Matrix.one_kronecker_one]

/-- The actual finite creation operator satisfies the sharp squared norm
bound governed by variance and the largest, rather than absolute largest,
eigenvalue of the coefficient block.
Source: Bandeira et al. (2026), Theorem 2.1, finite Hermite route.
atlas: gaussian-series-partial-transpose-norm (partial) -/
theorem specNorm_sq_hermiteSeriesCreation_le [Nonempty ι] [Nonempty d]
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (p : ℕ) :
    specNorm (hermiteSeriesCreation A p) ^ 2 ≤
      specNorm (coefficientVariance A) +
        ((p - 1 : ℕ) : ℝ) * lambdaMax (coefficientBlock A) := by
  let L := hermiteSeriesCreation A p
  let P : Matrix (d × HermiteIndex ι p) (d × HermiteIndex ι p) ℂ :=
    (1 : Matrix d d ℂ) ⊗ₖ hermiteInterior p
  let N : Matrix (d × HermiteIndex ι p) (d × HermiteIndex ι p) ℂ :=
    (1 : Matrix d d ℂ) ⊗ₖ hermiteNumber p
  let B := hermiteAnnihilatorStack (ι := ι) d p
  let V := coefficientVariance A ⊗ₖ (1 : Matrix (HermiteIndex ι p) (HermiteIndex ι p) ℂ)
  let T := coefficientBlock A ⊗ₖ (1 : Matrix (HermiteIndex ι p) (HermiteIndex ι p) ℂ)
  let v := specNorm (coefficientVariance A)
  let t := lambdaMax (coefficientBlock A)
  let q : ℝ := (p - 1 : ℕ)
  have hv : 0 ≤ v := specNorm_nonneg _
  have ht : 0 ≤ t := lambdaMax_coefficientBlock_nonneg A hA
  have hq : 0 ≤ q := Nat.cast_nonneg _
  have hP : Pᴴ = P := by
    simp [P, Matrix.conjTranspose_kronecker, isHermitian_hermiteInterior.eq]
  have hPP : P * P = P := by
    simp only [P, ← Matrix.mul_kronecker_mul, Matrix.one_mul, hermiteInterior_mul_self]
  have hP₀ : 0 ≤ P :=
    (Matrix.PosSemidef.one.kronecker posSemidef_hermiteInterior).nonneg
  have hPI : P ≤ 1 := by
    have hh := Matrix.kronecker_le_kronecker_left
      (hermiteInterior_le_one (ι := ι) (p := p)) (Matrix.PosSemidef.one (n := d) (R := ℂ))
    simpa only [P, Matrix.one_kronecker_one] using hh
  have hLP : L * P = L := hermiteSeriesCreation_mul_interior A
  have hPL : P * Lᴴ = Lᴴ := by
    have hh := congrArg (fun M : Matrix (d × HermiteIndex ι p) (d × HermiteIndex ι p) ℂ => Mᴴ) hLP
    simpa only [Matrix.conjTranspose_mul, hP] using hh
  have hGram : Lᴴ * L = P * (V + Bᴴ * T * B) * P := by
    have hh := hermiteSeriesCreation_gram_mul_interior A hA (p := p)
    change Lᴴ * L * P = (V + Bᴴ * T * B) * P at hh
    rw [Matrix.mul_assoc, hLP] at hh
    calc Lᴴ * L = P * (Lᴴ * L) := by rw [← Matrix.mul_assoc, hPL]
         _ = P * ((V + Bᴴ * T * B) * P) := congrArg (P * ·) hh
         _ = _ := (Matrix.mul_assoc _ _ _).symm
  have hVh : (coefficientVariance A).IsHermitian := by
    rw [← coefficientStack_gram A hA]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).isHermitian
  have hV : V ≤ v • 1 := by
    have hh := Matrix.kronecker_le_kronecker_right hVh.le_specNorm_smul_one
      (Matrix.PosSemidef.one (n := HermiteIndex ι p) (R := ℂ))
    simpa only [V, v, scalar_kronecker_one] using hh
  have hT : T ≤ t • 1 := by
    have hh := Matrix.kronecker_le_kronecker_right
      (isHermitian_coefficientBlock A hA).le_lambdaMax_smul_one
      (Matrix.PosSemidef.one (n := HermiteIndex ι p) (R := ℂ))
    simpa only [T, t, scalar_kronecker_one] using hh
  have hB : Bᴴ * B = N := hermiteAnnihilatorStack_gram
  have hBT : Bᴴ * T * B ≤ t • N := by
    have hh := Matrix.conjTranspose_mul_le_conjTranspose_mul hT B
    simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hB] using hh
  have hPN : P * N * P ≤ q • P := by
    have hh := Matrix.kronecker_le_kronecker_left
      (hermiteInterior_number_le (ι := ι) (p := p)) (Matrix.PosSemidef.one (n := d) (R := ℂ))
    simpa only [P, N, q, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.kronecker_smul]
      using hh
  have hD := add_le_add hV hBT
  have hCD := Matrix.conjTranspose_mul_le_conjTranspose_mul hD P
  have hG : Lᴴ * L ≤ (v + q * t) • 1 := by
    rw [hP] at hCD
    rw [hGram]
    calc
      P * (V + Bᴴ * T * B) * P ≤ P * (v • 1 + t • N) * P := hCD
      _ = v • P + t • (P * N * P) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, hPP]
      _ ≤ v • P + t • (q • P) := by
        apply Matrix.le_iff.mpr
        rw [add_sub_add_left_eq_sub, ← smul_sub]
        exact (Matrix.le_iff.mp hPN).smul ht
      _ = (v + q * t) • P := by rw [smul_smul, ← add_smul, mul_comm t q]
      _ ≤ (v + q * t) • 1 := by
        apply Matrix.le_iff.mpr
        rw [← smul_sub]
        exact (Matrix.le_iff.mp hPI).smul (show 0 ≤ v + q * t by positivity)
  exact specNorm_sq_le_of_conjTranspose_mul_self_le L (by positivity) hG

/-- The self-adjoint finite creation-plus-annihilation compression has the
sharp factor two norm bound at every total-degree cutoff.
Source: Bandeira et al. (2026), Theorem 2.1, finite Hermite route.
atlas: gaussian-series-partial-transpose-norm (partial) -/
theorem specNorm_hermiteSeriesCreation_add_conjTranspose_le [Nonempty ι] [Nonempty d]
    (A : ι → Matrix d d ℂ) (hA : ∀ i, (A i).IsHermitian) (p : ℕ) :
    specNorm (hermiteSeriesCreation A p + (hermiteSeriesCreation A p)ᴴ) ≤
      2 * Real.sqrt (specNorm (coefficientVariance A) +
        ((p - 1 : ℕ) : ℝ) * lambdaMax (coefficientBlock A)) := by
  have hh := specNorm_sq_hermiteSeriesCreation_le A hA p
  have hnonneg : 0 ≤ specNorm (coefficientVariance A) +
      ((p - 1 : ℕ) : ℝ) * lambdaMax (coefficientBlock A) :=
    le_trans (sq_nonneg _) hh
  have hroot : specNorm (hermiteSeriesCreation A p) ≤ Real.sqrt _ :=
    (Real.le_sqrt (specNorm_nonneg _) hnonneg).mpr hh
  calc _ ≤ specNorm (hermiteSeriesCreation A p) + specNorm ((hermiteSeriesCreation A p)ᴴ) :=
      specNorm_add_le _ _
    _ = 2 * specNorm (hermiteSeriesCreation A p) := by rw [specNorm_conjTranspose]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hroot (by norm_num)

end NLAlib
