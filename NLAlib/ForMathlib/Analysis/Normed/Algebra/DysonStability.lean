import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# A deterministic residual bound for the Dyson equation

A genuine left-inverse solution controls the distance to any other algebra
element by its actual polynomial residual, whenever the native operator
norms give a contraction factor at most one half. No approximation error
bound or limiting solution is assumed.
-/

noncomputable section
set_option autoImplicit false

/-- The distance to an exact Dyson solution is at most twice its norm times
the actual polynomial residual under the native contraction bound. -/
theorem norm_sub_le_two_mul_norm_mul_norm_dyson_residual
    {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedSpace 𝕜 A]
    (s : A →L[𝕜] A) (a z m y : A)
    (hm : m*(z-a-s m)=1)
    (hc : ‖m‖*‖s‖*‖y‖≤1/2) :
    ‖y-m‖≤2*‖m‖*‖(z-a-s y)*y-1‖ := by
  have he : y-m=m*s (y-m)*y+m*((z-a-s y)*y-1) := by
    calc
      _ = (m*(z-a-s m))*y-m := by rw [hm,one_mul]
      _ = _ := by rw [map_sub]; noncomm_ring
  have hp : ‖m*s (y-m)*y‖≤(‖m‖*‖s‖*‖y‖)*‖y-m‖ := by
    calc
      _ ≤ (‖m‖*‖s (y-m)‖)*‖y‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (‖m‖*(‖s‖*‖y-m‖))*‖y‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (s.le_opNorm _) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hd : ‖y-m‖≤(1/2)*‖y-m‖+‖m‖*‖(z-a-s y)*y-1‖ := by
    calc
      _ ≤ ‖m*s (y-m)*y‖+‖m*((z-a-s y)*y-1)‖ := by
        conv_lhs => rw [he]
        exact norm_add_le _ _
      _ ≤ (‖m‖*‖s‖*‖y‖)*‖y-m‖+‖m‖*‖(z-a-s y)*y-1‖ :=
        add_le_add hp (norm_mul_le _ _)
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) le_rfl
  linarith
