import NLAlib.Matrix.Spectral.SylvesterQualitative
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Algebraic characterization of the matrix sign

Uniqueness follows from Sylvester separation of two positive-stable
products. This proof applies to defective and nonnormal matrices.
Higham, Functions of Matrices, Chapter 5; matrix-toolkit derivations,
Section `eq-sign-projectors`.
-/

noncomputable section
open Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix is positive stable when every complex spectral value has
strictly positive real part. The empty spectrum satisfies this predicate. -/
def IsPositiveStable (A : Matrix n n ℂ) : Prop :=
  ∀ z ∈ spectrum ℂ A, 0 < z.re

/-- The algebraic and spectral characterization of the matrix sign.
Existence under spectral separation is proved separately. -/
def IsMatrixSign (A S : Matrix n n ℂ) : Prop :=
  S ^ 2 = 1 ∧ Commute A S ∧ IsPositiveStable (S * A)

/-- Positive-stable matrices have spectra disjoint from the negative of
every positive-stable matrix. -/
theorem IsPositiveStable.disjoint_neg {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : IsPositiveStable A) (hB : IsPositiveStable B) :
    Disjoint (spectrum ℂ A) (spectrum ℂ (-B)) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  have hn : -z ∈ spectrum ℂ B := by
    rw [← spectrum.neg_eq] at hz'
    exact Set.mem_neg.mp hz'
  have ha := hA z hz
  have hb := hB (-z) hn
  simp only [Complex.neg_re] at hb
  linarith

/-- The matrix sign characterization has at most one solution. It does
not assume that the two proposed solutions commute with one another.
atlas: matrix-sign-spectral-projectors (partial) -/
theorem IsMatrixSign.eq {A S T : Matrix n n ℂ}
    (hS : IsMatrixSign A S) (hT : IsMatrixSign A T) : S = T := by
  have hs : S * S = 1 := by simpa only [pow_two] using hS.1
  have ht : T * T = 1 := by simpa only [pow_two] using hT.1
  have hsep := hS.2.2.disjoint_neg hT.2.2
  have heq : (S * A) * (S - T) = (S - T) * (-(T * A)) := by
    have hSA : A * S = S * A := hS.2.1.eq
    have hTA : A * T = T * A := hT.2.1.eq
    calc
      _ = S * (A * S) - S * (A * T) := by noncomm_ring
      _ = (S * S) * A - S * T * A := by rw [hSA, hTA]; noncomm_ring
      _ = A - S * T * A := by rw [hs, Matrix.one_mul]
      _ = (S - T) * (-(T * A)) := by
        calc
          _ = -(S * T * A) + (T * T) * A := by rw [ht, Matrix.one_mul]; abel
          _ = _ := by noncomm_ring
  exact sub_eq_zero.mp (eq_zero_of_mul_eq_mul_of_disjoint_spectrum hsep heq)

/-- The two half-sign matrices are complementary commuting idempotents. -/
theorem IsMatrixSign.projectors {A S : Matrix n n ℂ} (hS : IsMatrixSign A S) :
    let P := (2 : ℂ)⁻¹ • (1 + S)
    let Q := (2 : ℂ)⁻¹ • (1 - S)
    P * P = P ∧ Q * Q = Q ∧ P * Q = 0 ∧ Q * P = 0 ∧ P + Q = 1 := by
  dsimp
  have hs : S * S = 1 := by simpa only [pow_two] using hS.1
  constructor
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show (1 + S) * (1 + S) = (2 : ℂ) • (1 + S) by
      simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hs]
      module]
    simp [smul_smul]
  constructor
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show (1 - S) * (1 - S) = (2 : ℂ) • (1 - S) by
      simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hs]
      module]
    simp [smul_smul]
  constructor
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show (1 + S) * (1 - S) = 0 by noncomm_ring [hs], smul_zero]
  constructor
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show (1 - S) * (1 + S) = 0 by noncomm_ring [hs], smul_zero]
  · rw [← smul_add]
    have heq : (1 : Matrix n n ℂ) + S + (1 - S) = (2 : ℂ) • 1 := by module
    rw [heq, smul_smul]
    norm_num

end NLAlib
