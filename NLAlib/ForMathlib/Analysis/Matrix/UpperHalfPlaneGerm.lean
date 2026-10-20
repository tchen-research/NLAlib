import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-! # Positive matrix imaginary parts near a real analytic germ

A positive derivative of an analytic matrix function that is Hermitian
on a real neighborhood makes it preserve the upper half-plane locally.
The same strict derivative estimate bounds its imaginary part by height.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

/-- An actual analytic matrix germ with Hermitian real values and
strictly positive derivative maps the upper half-plane into itself
locally. Its native imaginary part is uniformly bounded by height.
No half-plane preservation or boundary estimate is assumed. -/
theorem eventually_posDef_imaginaryPart_of_posDef_deriv
    (G : ℂ → M) (u : ℝ) (B : M) (hGa : AnalyticAt ℂ G (u : ℂ))
    (hGd : HasDerivAt G B (u : ℂ)) (hB : B.PosDef)
    (hreal : ∀ᶠ x : ℝ in 𝓝 u, (G x).IsHermitian) :
    ∃ C : ℝ, ∀ᶠ z : ℂ in 𝓝 (u : ℂ), 0<z.im →
      (imaginaryPart (G z) : M).PosDef ∧ ‖(imaginaryPart (G z) : M)‖≤C*z.im := by
  obtain ⟨δ,hδ,hδB⟩ : ∃ δ : ℝ, 0<δ ∧ δ•(1 : M)≤B := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CFC.exists_pos_algebraMap_le_iff hB.isHermitian.isSelfAdjoint).mpr
        (fun r hr => hB.isStrictlyPositive.spectrum_pos hr)
  have hs : HasStrictDerivAt G B (u : ℂ) := by
    simpa only [hGd.deriv] using hGa.hasStrictDerivAt
  have he : ∀ᶠ p : ℂ × ℂ in 𝓝 ((u : ℂ),(u : ℂ)),
      ‖G p.1-G p.2-(p.1-p.2)•B‖≤(δ/2)*‖p.1-p.2‖ := by
    simpa only [ContinuousLinearMap.toSpanSingleton_apply] using
      hs.hasStrictFDerivAt.isLittleO.bound (half_pos hδ)
  have hre : Tendsto Complex.re (𝓝 (u : ℂ)) (𝓝 u) := by
    simpa only [Complex.ofReal_re] using Complex.continuous_re.tendsto (u : ℂ)
  have hp : Tendsto (fun z : ℂ => (z,(z.re : ℂ)))
      (𝓝 (u : ℂ)) (𝓝 ((u : ℂ),(u : ℂ))) := by
    simpa only [Complex.ofReal_re,Function.comp_def,id_eq] using
      (continuous_id.prodMk (Complex.continuous_ofReal.comp Complex.continuous_re)).tendsto (u : ℂ)
  refine ⟨δ/2+‖B‖,?_⟩
  filter_upwards [hp.eventually he,hre.eventually hreal] with z hE hHerm
  intro hz
  have hzsub : z-(z.re : ℂ)=(z.im : ℂ)*Complex.I := by
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using (Complex.re_add_im z).symm)
  let E := G z-G (z.re : ℂ)-(z-(z.re : ℂ))•B
  have hEN : ‖E‖≤(δ/2)*z.im := by
    change ‖G z-G (z.re : ℂ)-(z-(z.re : ℂ))•B‖≤_
    rw [hzsub,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,
      Real.norm_eq_abs,abs_of_pos hz] at hE
    simpa only [hzsub] using hE
  have hImE : (imaginaryPart E : M)=(imaginaryPart (G z) : M)-z.im•B := by
    dsimp only [E]
    rw [map_sub,map_sub,hHerm.isSelfAdjoint.imaginaryPart,sub_zero,hzsub]
    simp only [imaginaryPart_smul,hB.isHermitian.isSelfAdjoint.imaginaryPart,
      Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
      zero_smul,zero_add,add_zero,sub_zero]
    change (imaginaryPart (G z) : M)-z.im•(realPart B : M)=_
    rw [hB.isHermitian.isSelfAdjoint.coe_realPart]
  let A := (imaginaryPart (G z) : M)-z.im•B
  have hAN : ‖A‖≤(δ/2)*z.im := by
    have hn : ‖(imaginaryPart E : M)‖≤‖E‖ := by
      simpa only [← AddSubgroup.norm_coe] using imaginaryPart.norm_le E
    rw [hImE] at hn
    exact hn.trans hEN
  have hAH : A.IsHermitian := (imaginaryPart (G z)).property.sub
    (hB.isHermitian.smul (IsSelfAdjoint.all z.im))
  have hneg : (-‖A‖)•(1 : M)≤A := by
    simpa only [Algebra.algebraMap_eq_smul_one,neg_smul] using
      hAH.isSelfAdjoint.neg_algebraMap_norm_le_self
  have hneg' : (-(δ/2*z.im))•(1 : M)≤A :=
    (smul_le_smul_of_nonneg_right (neg_le_neg hAN) (show (0 : M)≤1 from zero_le_one)).trans hneg
  have hB' : (z.im*δ)•(1 : M)≤z.im•B := by
    simpa only [smul_smul] using smul_le_smul_of_nonneg_left hδB hz.le
  have htotal : (δ/2*z.im)•(1 : M)≤(imaginaryPart (G z) : M) := by
    convert! add_le_add hneg' hB' using 1 <;> module
  have hpos : IsStrictlyPositive (imaginaryPart (G z) : M) :=
    (Matrix.PosDef.one.smul (mul_pos (half_pos hδ) hz)).isStrictlyPositive.of_le htotal
  refine ⟨Matrix.IsStrictlyPositive.posDef hpos,?_⟩
  have hsum : A+z.im•B=(imaginaryPart (G z) : M) := by
    dsimp only [A]
    exact sub_add_cancel _ _
  calc
    _ = ‖A+z.im•B‖ := by rw [hsum]
    _ ≤ ‖A‖+‖z.im•B‖ := norm_add_le _ _
    _ ≤ (δ/2)*z.im+z.im*‖B‖ := by
      rw [norm_smul,Real.norm_of_nonneg hz.le]
      exact add_le_add hAN le_rfl
    _ = _ := by ring

end Matrix
