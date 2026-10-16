import NLAlib.Matrix.Spectral.EigenvectorPairing
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators

/-! # Eigenvector spectral certificates and powers

The converse to extracting an eigenvector from a spectral point, its real
complexification bridge, and the elementary eigenvector equation for powers.
Source: Horn–Johnson, Matrix Analysis, §1.4.
-/
noncomputable section
open Matrix
open scoped Matrix
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonzero eigenvector certifies membership in the matrix spectrum. -/
theorem mem_spectrum_of_mulVec_eq_smul {K : Type*} [Field K]
    {B : Matrix ι ι K} {μ : K} {z : ι → K}
    (hz : z ≠ 0) (hBz : B *ᵥ z = μ • z) : μ ∈ spectrum K B := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
  intro hunit
  have hzero : (μ • (1 : Matrix ι ι K) - B) *ᵥ z = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hBz, sub_self]
  exact hz (Matrix.mulVec_injective_of_isUnit hunit (hzero.trans (Matrix.mulVec_zero _).symm))

/-- A real eigenpair remains an eigenpair, and therefore a spectral point,
after complexification. -/
theorem mem_spectrum_complexification_of_real_eigenpair {A : Matrix ι ι ℝ}
    {p : ι → ℝ} {r : ℝ} (hp : p ≠ 0) (heig : A *ᵥ p = r • p) :
    (r : ℂ) ∈ spectrum ℂ (A.map Complex.ofReal) := by
  have hcp : (fun i => (p i : ℂ)) ≠ 0 := by
    intro hz
    apply hp
    funext i
    apply Complex.ofReal_injective
    simpa only [Pi.zero_apply, Complex.ofReal_zero] using congrFun hz i
  apply mem_spectrum_of_mulVec_eq_smul hcp
  funext i
  have h := congrArg Complex.ofReal (congrFun heig i)
  simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_sum, Complex.ofReal_mul, Matrix.map_apply] using h

/-- Powers preserve the eigenvector equation over any finite commutative semiring. -/
theorem pow_mulVec_eq_pow_smul_of_mulVec_eq_smul {K : Type*} [CommSemiring K]
    {A : Matrix ι ι K} {p : ι → K} {r : K} (hp : A *ᵥ p = r • p) (k : ℕ) :
    A ^ k *ᵥ p = r ^ k • p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hp, Matrix.mulVec_smul, ih,
      smul_smul, ← pow_succ']

end Matrix
