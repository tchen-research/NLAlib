import NLAlib.ForMathlib.Analysis.Matrix.UpperHalfPlaneGerm

/-! # Genuine height bounds at a Hermitian analytic boundary

Strict complex differentiability compares a point to its real
projection. Hermitian values on the real axis remove the constant
imaginary term, yielding a bound proportional to the actual height.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Matrix.Norms.L2Operator ComplexStarModule Topology
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- A genuine analytic matrix germ with Hermitian real values has
imaginary part O(height) near the real point. No boundary estimate or
derivative sign is supplied. -/
theorem exists_eventually_norm_imaginaryPart_le_height_of_real_analytic
    (G : ℂ → M) (u : ℝ) (hGa : AnalyticAt ℂ G (u : ℂ))
    (hreal : ∀ᶠ x : ℝ in 𝓝 u, (G x).IsHermitian) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ z : ℂ in 𝓝 (u : ℂ), 0<z.im →
      ‖(imaginaryPart (G z) : M)‖≤C*z.im := by
  obtain ⟨K,U,hU,hLip⟩ := hGa.hasStrictDerivAt.hasStrictFDerivAt.exists_lipschitzOnWith
  have hp : Tendsto (fun z : ℂ => (z.re : ℂ))
      (𝓝 (u : ℂ)) (𝓝 (u : ℂ)) := by
    simpa only [Complex.ofReal_re,Function.comp_def] using
      (Complex.continuous_ofReal.comp Complex.continuous_re).tendsto (u : ℂ)
  have hre : Tendsto Complex.re (𝓝 (u : ℂ)) (𝓝 u) := by
    simpa only [Complex.ofReal_re] using Complex.continuous_re.tendsto (u : ℂ)
  refine ⟨K,K.property,?_⟩
  filter_upwards [hU,hp.eventually hU,hre.eventually hreal] with z hzU hzReU hzreal
  intro hz
  have hzn : ‖z-(z.re : ℂ)‖=z.im := by
    have hdiff : z-(z.re : ℂ)=(z.im : ℂ)*Complex.I := by
      exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using (Complex.re_add_im z).symm)
    rw [hdiff,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,
      Real.norm_of_nonneg hz.le]
  have hdiff : ‖G z-G (z.re : ℂ)‖≤(K : ℝ)*z.im := by
    simpa only [hzn] using lipschitzOnWith_iff_norm_sub_le.mp hLip hzU hzReU
  have him : (imaginaryPart (G z-G (z.re : ℂ)) : M)=(imaginaryPart (G z) : M) := by
    rw [map_sub,hzreal.isSelfAdjoint.imaginaryPart,sub_zero]
  have hn : ‖(imaginaryPart (G z-G (z.re : ℂ)) : M)‖≤‖G z-G (z.re : ℂ)‖ := by
    simpa only [← AddSubgroup.norm_coe] using imaginaryPart.norm_le (G z-G (z.re : ℂ))
  rw [him] at hn
  exact hn.trans hdiff

end Matrix
