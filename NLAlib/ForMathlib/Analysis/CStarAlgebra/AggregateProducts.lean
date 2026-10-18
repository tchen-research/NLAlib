import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity

/-! # Aggregate product bounds in a C⋆-algebra

Finite Hilbert C⋆-module Cauchy--Schwarz retains both aggregate Gram
matrices in a sum of products. Uniformly bounded middle factors yield
an arithmetic-mean bound with explicit constant `1/2`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CStarAlgebra

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

/-- Operator Cauchy--Schwarz for a finite sum of products retains the norms
of the two aggregate Gram matrices. -/
theorem norm_sum_mul_sq_le (a b : ι → A) :
    ‖∑ i, a i * b i‖ ^ 2 ≤
      ‖∑ i, a i * star (a i)‖ * ‖∑ i, star (b i) * b i‖ := by
  let x : WithCStarModule A (ι → A) :=
    (WithCStarModule.equiv A (ι → A)).symm (fun i => star (b i))
  let y : WithCStarModule A (ι → A) :=
    (WithCStarModule.equiv A (ι → A)).symm a
  have h := CStarModule.norm_inner_le (A := A) (WithCStarModule A (ι → A)) (x := x) (y := y)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [mul_pow, WithCStarModule.pi_norm_sq, WithCStarModule.pi_inner,
    WithCStarModule.inner_def, x, y, WithCStarModule.equiv_symm_pi_apply,
    star_star, mul_comm (‖∑ i, star (b i) * b i‖)] using hsq

private theorem star_mul_le_smul_one_of_norm_le (a : A) {c : ℝ}
    (_hc : 0 ≤ c) (ha : ‖a‖ ≤ c) : star a * a ≤ c ^ 2 • (1 : A) := by
  refine (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := a)).trans ?_
  simpa only [Algebra.algebraMap_eq_smul_one] using
    smul_le_smul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg a) ha 2)
      (show (0 : A) ≤ 1 from zero_le_one)

/-- A finite sum with uniformly bounded middle factors is controlled by its
left and right aggregate Gram matrices. The constant `1/2` is explicit. -/
theorem norm_sum_mul_mul_le (a b c : ι → A) {r : ℝ}
    (hr : 0 ≤ r) (hb : ∀ i, ‖b i‖ ≤ r) :
    ‖∑ i, a i * b i * c i‖ ≤
      r / 2 * (‖∑ i, a i * star (a i)‖ + ‖∑ i, star (c i) * c i‖) := by
  have hle : (∑ i, star (b i * c i) * (b i * c i)) ≤
      r ^ 2 • (∑ i, star (c i) * c i) := by
    rw [Finset.smul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := star_left_conjugate_le_conjugate
      (star_mul_le_smul_one_of_norm_le (b i) hr (hb i)) (c i)
    simpa only [star_mul, mul_assoc, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, one_mul] using h
  have hn : ‖∑ i, star (b i * c i) * (b i * c i)‖ ≤
      r ^ 2 * ‖∑ i, star (c i) * c i‖ := by
    have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le
      (Finset.sum_nonneg fun i _ => star_mul_self_nonneg (b i * c i)) hle
    simpa only [norm_smul, Real.norm_of_nonneg (sq_nonneg r)] using h
  have hcs := norm_sum_mul_sq_le a (fun i => b i * c i)
  have hcs' : ‖∑ i, a i * b i * c i‖ ^ 2 ≤
      ‖∑ i, a i * star (a i)‖ * ‖∑ i, star (b i * c i) * (b i * c i)‖ := by
    simpa only [mul_assoc] using hcs
  have hsq := hcs'.trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
  have hpos : 0 ≤ r / 2 *
      (‖∑ i, a i * star (a i)‖ + ‖∑ i, star (c i) * c i‖) := by positivity
  have hdiff := sq_nonneg
    (‖∑ i, a i * star (a i)‖ - ‖∑ i, star (c i) * c i‖)
  nlinarith [mul_nonneg (sq_nonneg r) hdiff]

/-- The Gram matrix of a sum is at most twice the sum of its two Gram
matrices in the positive order. -/
theorem add_mul_star_add_le (a b : A) :
    (a + b) * star (a + b) ≤
      (2 : ℝ) • (a * star a) + (2 : ℝ) • (b * star b) := by
  rw [← sub_nonneg]
  convert mul_star_self_nonneg (a - b) using 1
  simp only [two_smul, star_add, star_sub]
  noncomm_ring

end CStarAlgebra
