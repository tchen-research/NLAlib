import NLAlib.ForMathlib.Analysis.CStarAlgebra.TracialPositivePowers
import NLAlib.ForMathlib.Analysis.CStarAlgebra.GramNormPerturbation
import NLAlib.ForMathlib.Analysis.WeightedSquareOptimization
import NLAlib.ForMathlib.MeasureTheory.PositiveMomentAffine

/-!
# Actual rooted tracial Gram moments are stable under norm perturbations

Positive trace-power monotonicity, the positive-square Young inequality,
and scalar Lp on the actual spectrum measure prove the genuine native Gram
moment estimate. Noncommutative Minkowski is derived in the particular
norm-perturbation form needed for the mean-uniform free-resolvent estimate.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ComplexOrder ContinuousFunctionalCalculus

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem rpow_inv_two_mul_sq {v : ℝ} (hv : 0 ≤ v) (m : ℕ) (hm : 0 < m) :
    (v ^ ((2*m : ℝ)⁻¹)) ^ 2 = v ^ ((m : ℝ)⁻¹) := by
  calc
    _ = (v ^ ((2*m : ℝ)⁻¹)) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
    _ = v ^ ((2*m : ℝ)⁻¹ * 2) := (Real.rpow_mul hv _ _).symm
    _ = _ := by
      have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
      congr 1
      field_simp [hmR]

/-- Actual rooted Gram moments of a normalized positive trace change by
at most the native operator norm of the perturbation. The positive trace
and its cyclicity are the original objects; no moment norm or comparison
inequality is supplied as a hypothesis. -/
theorem PositiveLinearMap.gramMoment_rpow_le_add_norm (φ : A →ₚ[ℂ] ℂ)
    (hφ : φ 1 = 1) (htrace : ∀ x y : A, φ (x*y)=φ (y*x))
    (S T : A) (m : ℕ) (hm : 0 < m) :
    ((φ ((star S*S)^m)).re) ^ ((2*m : ℝ)⁻¹) ≤
      ((φ ((star T*T)^m)).re) ^ ((2*m : ℝ)⁻¹) + ‖S-T‖ := by
  have hvS : 0 ≤ (φ ((star S*S)^m)).re :=
    (Complex.nonneg_iff.mp (φ.map_nonneg (CStarAlgebra.pow_nonneg
      (star_mul_self_nonneg S) m))).1
  have hvT : 0 ≤ (φ ((star T*T)^m)).re :=
    (Complex.nonneg_iff.mp (φ.map_nonneg (CStarAlgebra.pow_nonneg
      (star_mul_self_nonneg T) m))).1
  apply le_add_of_forall_sq_le_weighted_sq
    (Real.rpow_nonneg hvS _) (Real.rpow_nonneg hvT _) (norm_nonneg _)
  intro ε hε
  rw [rpow_inv_two_mul_sq hvS m hm,rpow_inv_two_mul_sq hvT m hm]
  have ho := φ.re_pow_le_re_pow_of_tracial htrace (star_mul_self_nonneg S)
    (star_mul_self_le_weighted_gram_add_norm S T hε) m
  have hr := Real.rpow_le_rpow hvS ho (by positivity : 0 ≤ (m : ℝ)⁻¹)
  exact hr.trans (φ.re_pow_affine_rpow_le hφ (star_mul_self_nonneg T)
    (by positivity : 0 ≤ 1+ε) (by positivity : 0 ≤ (1+ε⁻¹)*‖S-T‖^2) m hm)

/-- The exact two-sided perturbation estimate for the genuine native
rooted Gram moments of a normalized positive trace. -/
theorem PositiveLinearMap.abs_gramMoment_rpow_sub_le_norm (φ : A →ₚ[ℂ] ℂ)
    (hφ : φ 1 = 1) (htrace : ∀ x y : A, φ (x*y)=φ (y*x))
    (S T : A) (m : ℕ) (hm : 0 < m) :
    |((φ ((star S*S)^m)).re) ^ ((2*m : ℝ)⁻¹) -
      ((φ ((star T*T)^m)).re) ^ ((2*m : ℝ)⁻¹)| ≤ ‖S-T‖ := by
  have hST := φ.gramMoment_rpow_le_add_norm hφ htrace S T m hm
  have hTS := φ.gramMoment_rpow_le_add_norm hφ htrace T S m hm
  rw [norm_sub_rev T S] at hTS
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

end
