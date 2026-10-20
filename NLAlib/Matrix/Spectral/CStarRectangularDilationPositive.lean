import NLAlib.Matrix.Spectral.CStarRectangularDilation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Positive spectral branch of the actual rectangular dilation

The true sign symmetry and square mapping identify positive dilation
spectrum with positive row-Gram spectrum over arbitrary C*-algebras.
Source: arXiv:2406.11453v2, Section 5.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace CStarMatrix
variable {m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Negating the native rectangular dilation leaves its actual spectrum unchanged. -/
theorem spectrum_real_neg_rectangularDilation (Y : Matrix m n A) :
    spectrum ℝ (-rectangularDilation Y) = spectrum ℝ (rectangularDilation Y) := by
  let S : CStarMatrix (m ⊕ n) (m ⊕ n) A := blockDiagonalStarAlgHom (1, -1)
  have hSS : S * S = 1 := by
    change blockDiagonalStarAlgHom (1, -1) * blockDiagonalStarAlgHom (1, -1) = 1
    rw [← map_mul]
    norm_num
    change blockDiagonalStarAlgHom (1 : CStarMatrix m m A × CStarMatrix n n A) = 1
    exact map_one _
  let u : (CStarMatrix (m ⊕ n) (m ⊕ n) A)ˣ := ⟨S, S, hSS, hSS⟩
  have hconj : (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) * rectangularDilation Y *
      (↑u⁻¹ : CStarMatrix (m ⊕ n) (m ⊕ n) A) = -rectangularDilation Y := by
    change (Matrix.fromBlocks 1 0 0 (-1) : Matrix (m ⊕ n) (m ⊕ n) A) * Matrix.fromBlocks 0 Y Yᴴ 0 *
      Matrix.fromBlocks 1 0 0 (-1) = -Matrix.fromBlocks 0 Y Yᴴ 0
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, zero_add, add_zero,
      neg_zero, Matrix.fromBlocks_neg]
  rw [← hconj]
  exact spectrum.units_conjugate

omit [PartialOrder A] [StarOrderedRing A] in
/-- The actual dilation spectrum has the genuine sign symmetry, without
assuming discrete eigenvalues. -/
theorem mem_spectrum_real_rectangularDilation_neg_iff (Y : Matrix m n A) (r : ℝ) :
    -r ∈ spectrum ℝ (rectangularDilation Y) ↔ r ∈ spectrum ℝ (rectangularDilation Y) := by
  have h := congrArg (fun K : Set ℝ => -r ∈ K) (spectrum_real_neg_rectangularDilation Y)
  rw [← spectrum.neg_eq, Set.mem_neg, neg_neg] at h
  exact iff_of_eq h.symm

/-- Positive dilation spectral values are exactly the positive square roots
of actual row-Gram spectral values. Source: arXiv:2406.11453v2, Section 5.3. -/
theorem mem_spectrum_real_rectangularDilation_iff_sq_mem_rowGram
    (Y : Matrix m n A) {r : ℝ} (hr : 0 < r) :
    r ∈ spectrum ℝ (rectangularDilation Y) ↔
      r ^ 2 ∈ spectrum ℝ (ofMatrix (Y * Yᴴ)) := by
  constructor
  · intro h
    have hsq : r ^ 2 ∈ spectrum ℝ (ofMatrix (Y * Yᴴ)) ∪
        spectrum ℝ (ofMatrix (Yᴴ * Y)) := by
      rw [← sq_image_spectrum_real_rectangularDilation]
      exact ⟨r, h, rfl⟩
    rcases hsq with hsq | hsq
    · exact hsq
    · exact (mem_spectrum_real_rowGram_iff_columnGram_of_ne_zero Y
        (ne_of_gt (sq_pos_of_pos hr))).mpr hsq
  · intro h
    have him : r ^ 2 ∈ (fun t : ℝ => t ^ 2) '' spectrum ℝ (rectangularDilation Y) := by
      rw [sq_image_spectrum_real_rectangularDilation]
      exact Or.inl h
    rcases him with ⟨t, ht, htr⟩
    have heq : t = r ∨ t = -r := by
      have : (t - r) * (t + r) = 0 := by nlinarith only [htr]
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rcases heq with heq | heq
    · simpa only [heq] using ht
    · rw [heq] at ht
      exact (mem_spectrum_real_rectangularDilation_neg_iff Y r).mp ht

/-- A strictly positive row-Gram spectral value has its positive square
root in the actual rectangular-dilation spectrum. -/
theorem sqrt_mem_spectrum_real_rectangularDilation_iff
    (Y : Matrix m n A) {r : ℝ} (hr : 0 < r) :
    Real.sqrt r ∈ spectrum ℝ (rectangularDilation Y) ↔
      r ∈ spectrum ℝ (ofMatrix (Y * Yᴴ)) := by
  rw [mem_spectrum_real_rectangularDilation_iff_sq_mem_rowGram Y (Real.sqrt_pos.mpr hr),
    Real.sq_sqrt hr.le]

end CStarMatrix
