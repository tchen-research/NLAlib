import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Monotonicity of actual positive trace powers

Integer powers need not preserve the operator order. A genuine positive
tracial functional does preserve their numerical order on the positive
cone: differentiate along the positive affine path and use trace cyclicity.
This is the first ingredient for native tracial Gram-moment perturbation,
used in arXiv:2406.11453v2, Theorems 4.3 and 4.4.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ComplexOrder ContinuousFunctionalCalculus

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
private theorem realTraceCFC : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := A)).toContinuousFunctionalCalculus

attribute [local instance] realTraceCFC

/-- A genuine positive tracial functional is nonnegative on a product of
positive elements, although that product need not itself be self-adjoint. -/
theorem PositiveLinearMap.re_mul_nonneg_of_tracial (φ : A →ₚ[ℂ] ℂ)
    (htrace : ∀ x y : A, φ (x * y) = φ (y * x)) {a b : A}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ (φ (a * b)).re := by
  let c := CFC.sqrt b
  have hc : IsSelfAdjoint c := (CFC.sqrt_nonneg b).isSelfAdjoint
  have hcc : c * c = b := CFC.sqrt_mul_sqrt_self b hb
  have he : φ (a * b) = φ (c * a * c) := by
    calc
      _ = φ (c * (a * c)) := by rw [← hcc, ← mul_assoc, htrace]
      _ = _ := by rw [mul_assoc]
  rw [he]
  exact (Complex.nonneg_iff.mp (φ.map_nonneg (hc.conjugate_nonneg ha))).1

/-- Exact cyclic differentiation of the actual positive functional along
an arbitrary affine matrix-free C*-algebra path. -/
theorem PositiveLinearMap.hasDerivAt_re_pow_affine_of_tracial (φ : A →ₚ[ℂ] ℂ)
    (htrace : ∀ x y : A, φ (x * y) = φ (y * x)) (a h : A) (m : ℕ) (t : ℝ) :
    HasDerivAt (fun v : ℝ => (φ ((a + v • h) ^ m)).re)
      ((m : ℝ) * (φ (h * (a + t • h) ^ (m - 1))).re) t := by
  let L : A →L[ℝ] ℝ :=
    { toLinearMap := Complex.reCLM.toLinearMap.comp (φ.toLinearMap.restrictScalars ℝ)
      cont := Complex.continuous_re.comp (map_continuous φ) }
  have haff : HasDerivAt (fun v : ℝ => a + v • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add a
  have hd := L.hasFDerivAt.comp_hasDerivAt t (haff.fun_pow' m)
  change HasDerivAt (fun v : ℝ => (φ ((a + v • h) ^ m)).re)
    ((φ (∑ i ∈ Finset.range m,
      (a + t • h) ^ (m.pred - i) * h * (a + t • h) ^ i)).re) t at hd
  have he (i : ℕ) (hi : i ∈ Finset.range m) :
      φ ((a + t • h) ^ (m.pred - i) * h * (a + t • h) ^ i) =
        φ (h * (a + t • h) ^ (m - 1)) := by
    have hsum : i + (m.pred - i) = m - 1 := by
      have := Finset.mem_range.mp hi
      simp only [Nat.pred_eq_sub_one]
      omega
    calc
      _ = φ ((h * (a + t • h) ^ i) * (a + t • h) ^ (m.pred - i)) := by
        rw [mul_assoc, htrace]
      _ = _ := by rw [mul_assoc, ← pow_add, hsum]
  have hs : (φ (∑ i ∈ Finset.range m,
      (a + t • h) ^ (m.pred - i) * h * (a + t • h) ^ i)).re =
      (m : ℝ) * (φ (h * (a + t • h) ^ (m - 1))).re := by
    rw [map_sum, Complex.re_sum]
    calc
      _ = ∑ _i ∈ Finset.range m, (φ (h * (a + t • h) ^ (m - 1))).re := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrArg Complex.re (he i hi)
      _ = _ := by simp
  rwa [hs] at hd

/-- Numerical integer-power moments of a genuine positive trace are
monotone on the positive cone. Operator monotonicity of integer powers is
not assumed. -/
theorem PositiveLinearMap.re_pow_le_re_pow_of_tracial (φ : A →ₚ[ℂ] ℂ)
    (htrace : ∀ x y : A, φ (x * y) = φ (y * x)) {a b : A}
    (ha : 0 ≤ a) (hab : a ≤ b) (m : ℕ) : (φ (a ^ m)).re ≤ (φ (b ^ m)).re := by
  let f : ℝ → ℝ := fun t => (φ ((a + t • (b-a)) ^ m)).re
  let d : ℝ → ℝ := fun t =>
    (m : ℝ) * (φ ((b-a) * (a + t • (b-a)) ^ (m-1))).re
  have hd (t : ℝ) : HasDerivAt f (d t) t :=
    φ.hasDerivAt_re_pow_affine_of_tracial htrace a (b-a) m t
  have hmono : MonotoneOn f (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
      ((continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).continuousOn)
    · intro t ht
      exact (hd t).hasDerivWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := (Set.mem_Icc.mp (interior_subset ht)).1
      have hg : 0 ≤ a + t • (b-a) := add_nonneg ha (smul_nonneg ht0 (sub_nonneg.mpr hab))
      exact mul_nonneg (Nat.cast_nonneg _) (φ.re_mul_nonneg_of_tracial htrace
        (sub_nonneg.mpr hab) (CStarAlgebra.pow_nonneg hg (m-1)))
  have hh := hmono (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
    (by simp : (1 : ℝ) ∈ Set.Icc 0 1) zero_le_one
  simpa only [f, zero_smul, add_zero, one_smul, add_sub_cancel] using hh

end
