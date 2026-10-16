import NLAlib.Matrix.Functions.LogarithmicNorm
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Sharpness of the logarithmic norm

One-sided slopes at zero recover the generator energy inequality from
any exponential bound. Testing a maximal Hermitian-part eigenvector
shows that the logarithmic norm is the least possible exponent.
Higham, Functions of Matrices; toolkit derivations, Section `eq-lognorm`.
-/

noncomputable section
open Matrix Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An exponential semigroup bound forces the corresponding real
quadratic-form bound on its generator. -/
theorem energy_bound_of_specNorm_matrixExp_smul_le (A : Matrix n n ℂ) (c : ℝ)
    (hA : ∀ t : ℝ, 0 ≤ t → specNorm (matrixExp (t • A)) ≤ Real.exp (t * c))
    (x : EuclideanSpace ℂ n) :
    inner ℝ x (A.toEuclideanLin x) ≤ c * ‖x‖ ^ 2 := by
  let z (s : ℝ) := (matrixExp (s • A)).toEuclideanLin x
  have hz0 : z 0 = x := by simp [z, matrixExp, Matrix.toEuclideanLin]
  have hg : HasDerivAt (fun s : ℝ => ‖z s‖ ^ 2)
      (2 * inner ℝ x (A.toEuclideanLin x)) 0 := by
    convert! (hasDerivAt_matrixExp_orbit A x 0).norm_sq using 1
    change 2 * inner ℝ x (A.toEuclideanLin x) =
      2 * inner ℝ (z 0) (A.toEuclideanLin (z 0))
    rw [hz0]
  have hh : HasDerivAt (fun s : ℝ => Real.exp (s * c) ^ 2 * ‖x‖ ^ 2)
      (2 * c * ‖x‖ ^ 2) 0 := by
    convert! ((((hasDerivAt_id (0 : ℝ)).mul_const c).exp).pow 2).mul_const (‖x‖ ^ 2) using 1
    norm_num
  have hle : 2 * inner ℝ x (A.toEuclideanLin x) ≤ 2 * c * ‖x‖ ^ 2 := by
    apply le_of_tendsto_of_tendsto hg.tendsto_slope_zero_right hh.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 0 < s := hs
    have hn : ‖z s‖ ≤ Real.exp (s * c) * ‖x‖ := by
      have h := (matrixExp (s • A)).l2_opNorm_mulVec x
      exact h.trans (mul_le_mul_of_nonneg_right (hA s hs'.le) (norm_nonneg _))
    have hsq : ‖z s‖ ^ 2 ≤ Real.exp (s * c) ^ 2 * ‖x‖ ^ 2 := by
      simpa only [mul_pow] using
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr hn
    simp only [zero_add, zero_mul, Real.exp_zero, one_pow, one_mul, hz0]
    exact smul_le_smul_of_nonneg_left (sub_le_sub_right hsq _) (inv_pos.mpr hs').le
  linarith

variable [Nonempty n]

/-- Testing the largest Hermitian-part eigenvector shows that every
energy bound is at least the logarithmic norm. -/
theorem matrixLogarithmicNorm_le_of_energy_bound {A : Matrix n n ℂ} {c : ℝ}
    (hA : ∀ x : EuclideanSpace ℂ n,
      inner ℝ x (A.toEuclideanLin x) ≤ c * ‖x‖ ^ 2) : matrixLogarithmicNorm A ≤ c := by
  let H : Matrix n n ℂ := selfAdjointPart ℝ A
  have hH : H.IsHermitian := (selfAdjointPart ℝ A).property
  have hm : lambdaMax H ∈ Set.range hH.eigenvalues := by
    rw [← hH.range_eigenvalues₀, lambdaMax_eq_eigenvalues₀_zero hH]
    exact ⟨⟨0, Fintype.card_pos⟩, rfl⟩
  obtain ⟨i, hi⟩ := hm
  let x := hH.eigenvectorBasis i
  have hn : ‖x‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
  have he : inner ℝ x (A.toEuclideanLin x) = hH.eigenvalues i := by
    rw [real_inner_toEuclideanLin]
    have h := quadForm_selfAdjointPart A x.ofLp
    have heig := hH.eigenvalues_eq i
    change hH.eigenvalues i = (quadForm H x.ofLp).re at heig
    have hreal := congrArg Complex.re h
    rw [Complex.ofReal_re] at hreal
    exact hreal.symm.trans heig.symm
  have hb := hA x
  rw [he, hn, one_pow, mul_one, hi] at hb
  exact hb

/-- The logarithmic norm is the least exponent in an all-time spectral
norm bound for the exponential semigroup.
atlas: matrix-exponential-logarithmic-norm (partial) -/
theorem isLeast_matrixLogarithmicNorm (A : Matrix n n ℂ) :
    IsLeast {c : ℝ | ∀ t : ℝ, 0 ≤ t →
      specNorm (matrixExp (t • A)) ≤ Real.exp (t * c)} (matrixLogarithmicNorm A) := by
  refine ⟨fun _ ht => specNorm_matrixExp_smul_le_exp_logarithmicNorm A ht, ?_⟩
  intro c hc
  exact matrixLogarithmicNorm_le_of_energy_bound (energy_bound_of_specNorm_matrixExp_smul_le A c hc)

/-- A matrix exponential is contractive for every nonnegative time
exactly when the Hermitian part of its generator is nonpositive. -/
theorem specNorm_matrixExp_smul_le_one_iff_selfAdjointPart_nonpos (A : Matrix n n ℂ) :
    (∀ t : ℝ, 0 ≤ t → specNorm (matrixExp (t • A)) ≤ 1) ↔
      (selfAdjointPart ℝ A : Matrix n n ℂ) ≤ 0 := by
  constructor
  · intro hA
    have he : ∀ t : ℝ, 0 ≤ t →
        specNorm (matrixExp (t • A)) ≤ Real.exp (t * 0) := by simpa only [mul_zero, Real.exp_zero]
    have hc := matrixLogarithmicNorm_le_of_energy_bound
      (energy_bound_of_specNorm_matrixExp_smul_le A 0 he)
    have hn : matrixLogarithmicNorm A • (1 : Matrix n n ℂ) ≤ 0 :=
      smul_nonpos_of_nonpos_of_nonneg hc zero_le_one
    exact (selfAdjointPart_le_matrixLogarithmicNorm A).trans hn
  · intro hA t ht
    have h : (selfAdjointPart ℝ A : Matrix n n ℂ) ≤ (0 : ℝ) • 1 := by
      simpa only [zero_smul] using hA
    simpa only [mul_zero, Real.exp_zero] using
      specNorm_matrixExp_smul_le_of_selfAdjointPart_le h ht

/-- Full logarithmic-norm contract: the Hermitian-part extremal eigenvalue
is the least possible all-time exponential bound, with the exact
contractivity criterion. Nonnormal and defective generators are included.
atlas: matrix-exponential-logarithmic-norm -/
theorem matrix_exponential_logarithmic_norm (A : Matrix n n ℂ) :
    IsLeast {c : ℝ | ∀ t : ℝ, 0 ≤ t →
      specNorm (matrixExp (t • A)) ≤ Real.exp (t * c)} (matrixLogarithmicNorm A) ∧
    ((∀ t : ℝ, 0 ≤ t → specNorm (matrixExp (t • A)) ≤ 1) ↔
      (selfAdjointPart ℝ A : Matrix n n ℂ) ≤ 0) :=
  ⟨isLeast_matrixLogarithmicNorm A, specNorm_matrixExp_smul_le_one_iff_selfAdjointPart_nonpos A⟩

end NLAlib
