import NLAlib.Matrix.Spectral.NumericalRange
import NLAlib.Matrix.Spectral.NormalSpectral
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Numerical range of normal matrices

Diagonal quadratic forms are finite convex combinations, and square roots of
their weights construct every point of the convex hull. Unitary invariance
then gives the normal-matrix spectral characterization, including empty indices.
Source: Horn–Johnson (1991), Chapter 1. Atlas: `field-of-values-def`.
-/

noncomputable section
open scoped Matrix
open Polynomial
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form of a diagonal complex matrix is the convex-weight sum
with weights the squared coordinate moduli. -/
theorem quadForm_diagonal_eq_sum_norm_sq_smul (d x : n → ℂ) :
    quadForm (Matrix.diagonal d) x = ∑ i, ‖x i‖ ^ 2 • d i := by
  simp only [quadForm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply,
    Complex.star_def]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, mul_right_comm, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq]
  rfl

/-- The numerical range of a diagonal matrix is the convex hull of its diagonal.
No nonempty index hypothesis is needed: both sets are empty in dimension zero.
Source: Horn–Johnson (1991), Chapter 1.
atlas: field-of-values-def (partial) -/
theorem numericalRange_diagonal_eq_convexHull (d : n → ℂ) :
    numericalRange (Matrix.diagonal d) = convexHull ℝ (Set.range d) := by
  classical
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply mem_convexHull_of_exists_fintype (fun i => ‖x i‖ ^ 2) d
      (fun _ => sq_nonneg _) _ (fun i => Set.mem_range_self i)
      (quadForm_diagonal_eq_sum_norm_sq_smul d x).symm
    simpa only [hx, one_pow] using (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 x)).symm
  · intro hzmem
    rw [convexHull_range_eq_exists_affineCombination] at hzmem
    obtain ⟨s, w, hw, hsum, hz⟩ := hzmem
    let W : n → ℝ := fun i => if i ∈ s then w i else 0
    have hW (i : n) : 0 ≤ W i := by
      by_cases hi : i ∈ s
      · simpa only [W, if_pos hi] using hw i hi
      · simp only [W, if_neg hi, le_refl]
    have hWsum : ∑ i, W i = 1 := by
      simp only [W, Finset.sum_ite_mem, Finset.univ_inter]
      exact hsum
    let x : n → ℂ := fun i => (Real.sqrt (W i) : ℂ)
    have hx (i : n) : ‖x i‖ ^ 2 = W i := by
      simp only [x, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hW i)]
    refine ⟨x, ?_, ?_⟩
    · have hsq : ‖WithLp.toLp 2 x‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq]
        change (∑ i, ‖x i‖ ^ 2) = 1
        simp only [hx, hWsum]
      nlinarith [norm_nonneg (WithLp.toLp 2 x)]
    · rw [quadForm_diagonal_eq_sum_norm_sq_smul]
      simp only [hx, W, ite_smul, zero_smul, Finset.sum_ite_mem, Finset.univ_inter]
      rw [Finset.affineCombination_eq_linear_combination s d w hsum] at hz
      exact hz

/-- The numerical range of every normal complex matrix is the convex hull of
its spectrum. This is the full normal-matrix clause, including empty dimensions.
Source: Horn–Johnson (1991), Chapter 1.
atlas: field-of-values-def (partial) -/
theorem numericalRange_eq_convexHull_spectrum_of_normal (A : Matrix n n ℂ)
    (hA : A * Aᴴ = Aᴴ * A) : numericalRange A = convexHull ℝ (spectrum ℂ A) := by
  obtain ⟨U, d, rfl⟩ := (normal_iff_exists_unitary_diagonalization A).mp hA
  have h := numericalRange_unitary_conjTranspose_mul_mul (star U) (Matrix.diagonal d)
  have hs : spectrum ℂ ((U : Matrix n n ℂ) * Matrix.diagonal d *
      (U : Matrix n n ℂ)ᴴ) = Set.range d := by
    simpa only [← Matrix.star_eq_conjTranspose, Unitary.coe_star, spectrum_diagonal]
      using (Unitary.spectrum_star_right_conjugate (R := ℂ)
        (a := Matrix.diagonal d) (U := U))
  rw [hs]
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose, numericalRange_diagonal_eq_convexHull,
    ] using h

end NLAlib
