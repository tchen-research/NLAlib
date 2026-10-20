import NLAlib.Probability.Free.WordMatrixVacuumEmbedding
import NLAlib.ForMathlib.MeasureTheory.PositiveMomentJensen

/-!
# Actual native vector norms from genuine amplified vacuum moments

Scalar Jensen on a genuine native embedded vector state and the proved
finite-column domination give a true Gram-moment bound for every
coefficient vacuum vector. No trace on all bounded operators is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical ComplexOrder

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D]
local notation "W" => WordHilbertSpace ι
local notation "M" => CStarMatrix D D (W →L[ℂ] W)

/-- Actual rooted Gram moments of the genuine amplified vacuum dominate
the norm on every actual unit coefficient vacuum vector. The matrix may
be any ambient native operator matrix, because only positivity is used.

Prerequisite for the high-height estimate in arXiv:2406.11453v2, Corollary 4.4.
atlas: gaussian-free-spectrum-two-sided (partial) -/
theorem norm_toPiLp_wordMatrixVacuumEmbedding_le_gramMoment
    (T : M) (v : EuclideanSpace ℂ D) (hv : ‖v‖=1) (m : ℕ) (hm : 0<m) :
    ‖CStarMatrix.toPiLpStarAlgHom (D := D) (H := W) T
      (wordMatrixVacuumEmbedding (ι := ι) v)‖ ≤
      ((Fintype.card D : ℝ)*
        (wordMatrixVacuumExpectation (D := D) (ι := ι) ((star T*T)^m)).re) ^
          ((2*m : ℝ)⁻¹) := by
  let φ := wordMatrixVacuumVectorPositiveMap (ι := ι) v
  let V := CStarMatrix.toPiLpStarAlgHom (D := D) (H := W)
  let u := wordMatrixVacuumEmbedding (ι := ι) v
  let b : ℝ := (Fintype.card D : ℝ)*
    (wordMatrixVacuumExpectation (D := D) (ι := ι) ((star T*T)^m)).re
  have hφ : φ 1=1 := wordMatrixVacuumVectorPositiveMap_one hv
  have hG : 0≤star T*T := star_mul_self_nonneg T
  have hGp : 0≤(star T*T)^m := CStarAlgebra.pow_nonneg hG m
  have hτ : 0≤(wordMatrixVacuumExpectation (D := D) (ι := ι) ((star T*T)^m)).re :=
    (Complex.nonneg_iff.mp
      ((wordMatrixVacuumPositiveMap (D := D) (ι := ι)).map_nonneg hGp)).1
  have hb : 0≤b := mul_nonneg (Nat.cast_nonneg _) hτ
  have hdom : (φ ((star T*T)^m)).re≤b := by
    change (inner ℂ (wordMatrixVacuumEmbedding (ι := ι) v)
      (CStarMatrix.toPiLpStarAlgHom (D := D) (H := W) ((star T*T)^m)
        (wordMatrixVacuumEmbedding (ι := ι) v))).re≤
          (Fintype.card D : ℝ)*
            (wordMatrixVacuumExpectation (D := D) (ι := ι) ((star T*T)^m)).re
    have h := re_inner_wordMatrixVacuumEmbedding_le_card_mul_expectation hGp v
    simpa only [hv,one_pow,one_mul] using h
  have hφG : (φ (star T*T)).re=‖V T u‖^2 := by
    change (inner ℂ u (V (star T*T) u)).re=_
    rw [map_mul,map_star]
    exact (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right (V T) u).symm
  have hstep : ‖V T u‖^2≤b^((m : ℝ)⁻¹) := by
    rw [← hφG]
    exact (φ.re_le_re_pow_rpow hφ hG m hm).trans
      (Real.rpow_le_rpow (Complex.nonneg_iff.mp (φ.map_nonneg hGp)).1 hdom
        (by positivity))
  have hexp : ((2*m : ℝ)⁻¹)*(2 : ℕ)=(m : ℝ)⁻¹ := by
    push_cast
    field_simp [Nat.cast_ne_zero.mpr hm.ne']
  have hsquare : (b^((2*m : ℝ)⁻¹))^2=b^((m : ℝ)⁻¹) := by
    rw [← Real.rpow_mul_natCast hb,hexp]
  have hroot : 0≤b^((2*m : ℝ)⁻¹) := Real.rpow_nonneg hb _
  change ‖V T u‖≤b^((2*m : ℝ)⁻¹)
  nlinarith only [hstep,hsquare,hroot,norm_nonneg (V T u)]

end NLAlib

end
