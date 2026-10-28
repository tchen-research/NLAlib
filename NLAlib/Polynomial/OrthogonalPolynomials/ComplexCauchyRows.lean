import NLAlib.Polynomial.OrthogonalPolynomials.ComplexDividedMoments

/-!
# Actual Cauchy rows for nonmonic denominators

The source root matrices normalize the denominator by its leading coefficient.
Their entries are precisely the original measure's complex Cauchy integrals,
including nonreal roots and conjugate pairs.
-/

noncomputable section
open Polynomial MeasureTheory Finset
namespace NLAlib

/-- Clearing one denominator factor in the normalized actual divided-moment
functional gives the actual source Cauchy integral.
atlas: christoffel-uvarov-modification (partial) -/
theorem smul_complexDividedPolynomialIntegral_rootCofactor_eq_cauchy
    {μ : Measure ℝ} {m : ℕ} {v : ℂ[X]} {cv : ℂ} (hcv : cv ≠ 0)
    (z : Fin m → ℂ) (hv : v = C cv * Lagrange.nodal Finset.univ z)
    (hdiv : HasComplexDividedPolynomialMoments μ v)
    (hv0 : ∀ᵐ (t : ℝ) ∂μ, v.eval (t : ℂ) ≠ 0) (p : ℂ[X]) (i : Fin m) :
    (cv • complexDividedPolynomialIntegral μ v hdiv) (p*rootCofactor z i) =
      ∫ t : ℝ, p.eval (t : ℂ)/((t : ℂ)-z i) ∂μ := by
  rw [LinearMap.smul_apply,smul_eq_mul,complexDividedPolynomialIntegral_apply,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hv0] with t ht
  have hnodes (j : Fin m) : (t : ℂ) ≠ z j := by
    intro he
    apply ht
    rw [he,hv,eval_mul,Lagrange.eval_nodal_at_node (mem_univ j),mul_zero]
  have hc : (rootCofactor z i).eval (t : ℂ) ≠ 0 := by
    simp only [rootCofactor,eval_prod,eval_sub,eval_X,eval_C]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => sub_ne_zero.mpr (hnodes j))
  have he : v.eval (t : ℂ) = cv*(((t : ℂ)-z i)*(rootCofactor z i).eval (t : ℂ)) := by
    rw [hv,eval_mul,eval_C,Lagrange.nodal_eq_mul_nodal_erase (mem_univ i),
      eval_mul,eval_sub,eval_X,eval_C]
    rfl
  rw [eval_mul,he]
  field_simp [hcv,hc,sub_ne_zero.mpr (hnodes i)]

end NLAlib
