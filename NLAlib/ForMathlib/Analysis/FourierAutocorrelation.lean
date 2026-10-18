import NLAlib.ForMathlib.Analysis.FourierCircle
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# Autocorrelations of finite Fourier sums

A finite character sum has nonnegative squared norm. Its real Fourier
coefficients are the finite autocorrelations of its real weights.
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate

namespace Finset

/-- Reindex a strict finite triangle by its positive diagonal displacement. -/
theorem sum_range_sum_range_eq_sum_displacements {A : Type*} [AddCommMonoid A]
    (f : ℕ → ℕ → A) (n : ℕ) :
    (∑ l ∈ range n, ∑ j ∈ range l, f j l) =
      ∑ d ∈ range n, ∑ j ∈ range (n - (d + 1)), f j (j + d + 1) := by
  classical
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun p _ => (⟨p.1 - p.2 - 1, p.2⟩ : (d : ℕ) × ℕ))
  · intro p hp
    simp only [mem_sigma, mem_range] at hp ⊢
    omega
  · intro p hp q hq he
    simp only [mem_sigma, mem_range] at hp hq
    have h1 := congrArg Sigma.fst he
    have h2 := congrArg Sigma.snd he
    change p.1 - p.2 - 1 = q.1 - q.2 - 1 at h1
    change p.2 = q.2 at h2
    have hfirst : p.1 = q.1 := by omega
    exact Sigma.ext hfirst (heq_of_eq h2)
  · intro q hq
    simp only [mem_sigma, mem_range] at hq
    refine ⟨⟨q.2 + q.1 + 1, q.2⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_range]
      omega
    · apply Sigma.ext
      · change q.2 + q.1 + 1 - q.2 - 1 = q.1
        omega
      · exact HEq.rfl
  · intro p hp
    simp only [mem_sigma, mem_range] at hp
    change f p.2 p.1 = f p.2 (p.2 + (p.1 - p.2 - 1) + 1)
    congr 1
    omega

end Finset

namespace NLAlib

open scoped NLAlib.TwoPi

/-- The exact autocorrelation expansion of a finite Fourier sum with real weights. -/
theorem normSq_sum_real_mul_fourier_eq_autocorrelation
    (v : ℕ → ℝ) (n : ℕ) (t : AddCircle (2 * Real.pi)) :
    Complex.normSq (∑ j ∈ range n, (v j : ℂ) * fourier (j : ℤ) t) =
      (∑ j ∈ range n, v j ^ 2) +
        2 * ∑ d ∈ range n, (∑ j ∈ range (n - (d + 1)), v j * v (j + d + 1)) *
          (fourier ((d + 1 : ℕ) : ℤ) t).re := by
  have htri (m : ℕ) :
      Complex.normSq (∑ j ∈ range m, (v j : ℂ) * fourier (j : ℤ) t) =
        (∑ j ∈ range m, v j ^ 2) +
          2 * ∑ l ∈ range m, ∑ j ∈ range l,
            v j * v l * (fourier ((l - j : ℕ) : ℤ) t).re := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, Complex.normSq_add, ih, Complex.normSq_mul,
        Complex.normSq_ofReal, Complex.normSq_eq_norm_sq,
        show ‖fourier (m : ℤ) t‖ = (1 : ℝ) from Circle.norm_coe _]
      have hc : ((∑ j ∈ range m, (v j : ℂ) * fourier (j : ℤ) t) *
          conj ((v m : ℂ) * fourier (m : ℤ) t)).re =
          ∑ j ∈ range m, v j * v m * (fourier ((m - j : ℕ) : ℤ) t).re := by
        rw [sum_mul, Complex.re_sum]
        apply sum_congr rfl
        intro j hj
        have he : (j : ℤ) + -(m : ℤ) = -((m - j : ℕ) : ℤ) := by
          have := mem_range.mp hj
          omega
        rw [map_mul, Complex.conj_ofReal, ← fourier_neg]
        have hr : (v j : ℂ) * fourier (j : ℤ) t * ((v m : ℂ) * fourier (-(m : ℤ)) t) =
            ((v j * v m : ℝ) : ℂ) *
              (fourier (j : ℤ) t * fourier (-(m : ℤ)) t) := by push_cast; ring
        rw [hr, ← fourier_add, he, fourier_neg, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, zero_mul, sub_zero]
      rw [hc, sum_range_succ, sum_range_succ]
      ring
  rw [htri, sum_range_sum_range_eq_sum_displacements]
  congr 2
  apply sum_congr rfl
  intro d _
  have he (j : ℕ) : j + d + 1 - j = d + 1 := by omega
  simp_rw [he, ← sum_mul]

end NLAlib
