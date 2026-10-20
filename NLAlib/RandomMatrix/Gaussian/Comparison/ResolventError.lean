import NLAlib.Probability.Concentration.Matrix.FiniteHermitianBernstein
import NLAlib.ForMathlib.Analysis.ResolventMomentScale

/-!
# A common deterministic resolvent error for independent-sum universality

The explicit error is built from the actual original marginal laws. The
native Bernstein bound and the proved scalar scale estimates absorb this
error and the grid mesh at the source linear/cubic spectral scale.
Source: arXiv:2201.05142v3, Lemmas 7.3 and 7.5, Proposition 7.7.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

open scoped Matrix.Norms.L2Operator in
/-- The common actual resolvent-comparison error. It uses the original
independent increments' expected sum norm and matrix square expectations,
and depends on the spectral parameter only through its height.
Source: arXiv:2201.05142v3, Lemmas 7.3 and 7.5. -/
def independentSumResolventError (ν : ι → Measure M) (R s η : ℝ) (p : ℕ) : ℝ :=
  let B := (2/η^4)*(8*s^2+64*R*
    ∫ x : ι → M, specNorm (∑ i, x i) ∂Measure.pi ν) +
    (32*R^2/η^6)*((Real.exp 1-1)*specNorm (∑ i, ∫ A : M, A^2 ∂ν i)+
      R^2*Real.log (Fintype.card n))
  let c := Real.sqrt (6*(16*R^2/η^4+64*R^4/η^6))
  9*(4*Real.sqrt (12*B*p)+8*c*p+Real.sqrt (24*B*p)+c*p+
    4096*((p : ℝ)^2*R*specNorm (∑ i, ∫ A : M, A^2 ∂ν i)+(p : ℝ)^3*R^3)/η^4+
      4*s*Real.sqrt (p : ℝ)/η^2)

open scoped Matrix.Norms.L2Operator in
/-- The literal original-law error and the deterministic grid mesh are
absorbed at the source linear/cubic spectral scale. The required sum-norm
expectation bound is derived by Bernstein, rather than assumed.
Source: arXiv:2201.05142v3, Proposition 7.7.
atlas: independent-sum-spectrum-universality (partial) -/
theorem independentSumResolventError_add_mesh_le_inv_two_height
    (ν : ι → Measure M) [∀ i, IsProbabilityMeasure (ν i)]
    (hHerm : ∀ i, ∀ᵐ A ∂ν i, A.IsHermitian)
    {R s σ δ η ε : ℝ} (hR : 0 ≤ R) (hs : 0 ≤ s) (hσ : 0 ≤ σ)
    (hBound : ∀ i, ∀ᵐ A ∂ν i, specNorm A ≤ R)
    (hmean : ∀ i, ∫ A : M, A ∂ν i = 0)
    (hvariance : specNorm (∑ i, ∫ A : M, A^2 ∂ν i) ≤ σ^2)
    (hd : 2 ≤ Fintype.card n) {p : ℕ} (hp : 0 < p)
    (hlog : Real.log (Fintype.card n) ≤ (p : ℝ))
    (hδ : 0 ≤ δ) (hη : 0 < η) (hheight : 200000*δ ≤ η) (hε : ε ≤ δ)
    (hsp : s*Real.sqrt (p : ℝ) ≤ δ) (hRp : R*p ≤ δ)
    (hcube : R*σ^2*(p : ℝ)^2 ≤ δ^3) :
    independentSumResolventError ν R s η p+10*ε/η^2 ≤ (2*η)⁻¹ := by
  have hn : Nonempty n := Fintype.card_pos_iff.mp (by omega)
  let := hn
  have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p from hp)
  have hδη : δ ≤ η := by linarith
  let E := ∫ x : ι → M, specNorm (∑ i, x i) ∂Measure.pi ν
  let Q := specNorm (∑ i, ∫ A : M, A^2 ∂ν i)
  let B := (2/η^4)*(8*s^2+64*R*E)+(32*R^2/η^6)*
    ((Real.exp 1-1)*Q+R^2*Real.log (Fintype.card n))
  let c := Real.sqrt (6*(16*R^2/η^4+64*R^4/η^6))
  let V := 4096*((p : ℝ)^2*R*Q+(p : ℝ)^3*R^3)/η^4
  let U := s*Real.sqrt (p : ℝ)/η^2
  let T := δ/η^2
  have hE : E ≤ 2*σ*Real.sqrt (p : ℝ)+R*p :=
    integral_specNorm_sum_pi_le_two_mul_sqrt_add_of_log_le
      ν (fun _ (A : M) => A) (fun _ => measurable_id) hR hσ hpR hd hlog
        hHerm hBound hmean hvariance
  have hbudget := Real.resolvent_variance_scale_le_of_source_parameters
    hR hσ hs hp1 hδ hη hδη hE (specNorm_nonneg _) hvariance hlog hsp hRp hcube
  change B*(p : ℝ) ≤ 500*T^2 ∧ c*p ≤ 22*T at hbudget
  have hV : V ≤ 8192*T := by
    simpa only [V,T,Q,mul_div_assoc] using
      Real.resolvent_comparison_remainder_le_of_source_parameters
        hR hpR hδ hη hδη hvariance hRp hcube
  have herror := Real.resolvent_grid_error_le_of_source_moment_budgets
    hδ hη hε hbudget.1 hbudget.2 hV
  have hU : U ≤ T := div_le_div_of_nonneg_right hsp (sq_nonneg η)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have herror' : 9*(4*Real.sqrt (12*B*p)+8*c*p+Real.sqrt (24*B*p)+c*p+V)+
      10*ε/η^2 ≤ 80000*T := by
    simpa only [T,mul_div_assoc] using herror
  have he : independentSumResolventError ν R s η p+10*ε/η^2 ≤ 100000*T := by
    have hh : 9*(4*Real.sqrt (12*B*p)+8*c*p+Real.sqrt (24*B*p)+c*p+V+4*U)+
        10*ε/η^2 ≤ 100000*T := by
      linear_combination herror'+36*hU+19964*hT
    simpa only [independentSumResolventError,B,c,E,Q,V,U,T,mul_div_assoc,mul_assoc] using hh
  calc
    _ ≤ 100000*T := he
    _ = 80000*((5/4 : ℝ)*δ)/η^2 := by dsimp [T]; ring
    _ ≤ _ := Real.resolvent_grid_error_le_inv_two_height hη (by nlinarith only [hheight])

end NLAlib
