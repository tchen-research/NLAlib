import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Fin.VecNotation

/-!
# Exact segment remainders relative to an arbitrary derivative base point

The scalar Taylor cancellation used in genuine
resampling interpolation is derived by the fundamental theorem of calculus,
with no supplied remainder identity or derivative norm bound.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The actual derivative integrates to the endpoint difference on a segment. -/
theorem ContDiff.sub_eq_integral_fderiv_segment {f : E → F}
    (hf : ContDiff ℝ 1 f) (x h : E) :
    f (x + h) - f x = ∫ u in (0 : ℝ)..1, fderiv ℝ f (x + u • h) h := by
  have hpath : Continuous (fun u : ℝ => x + u • h) := by fun_prop
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => f (x + u • h))
      (fderiv ℝ f (x + u • h) h) u := by
    have hp : HasDerivAt (fun u : ℝ => x + u • h) h u := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id u).smul_const h).const_add x
    exact (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt u hp
  have hc : Continuous (fun u : ℝ => fderiv ℝ f (x + u • h) h) :=
    ((hf.continuous_fderiv (by norm_num)).comp hpath).clm_apply continuous_const
  simpa only [one_smul, zero_smul, add_zero] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
      (hc.intervalIntegrable 0 1)).symm

/-- Taylor cancellation at an arbitrary Hessian base is exactly a double
segment integral of the actual second derivative. All scalar parameters,
including zero, are retained. -/
theorem ContDiff.sub_sub_smul_fderiv_eq_smul_integral_iteratedFDeriv_two
    {f : E → F} (hf : ContDiff ℝ 2 f) (x z h : E) (a : ℝ) :
    f (x + a • h) - f x - a • fderiv ℝ f z h =
      a • ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1,
        iteratedFDeriv ℝ 2 f (z + v • (x + u • (a • h) - z))
          ![x + u • (a • h) - z, h] := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hdf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hfirst := hf1.sub_eq_integral_fderiv_segment x (a • h)
  simp only [map_smul] at hfirst
  rw [intervalIntegral.integral_smul] at hfirst
  have hdiff (u : ℝ) :
      fderiv ℝ f (x + u • (a • h)) h - fderiv ℝ f z h =
        ∫ v in (0 : ℝ)..1,
          iteratedFDeriv ℝ 2 f (z + v • (x + u • (a • h) - z))
            ![x + u • (a • h) - z, h] := by
    let d := x + u • (a • h) - z
    have hd := hdf1.sub_eq_integral_fderiv_segment z d
    have hc : Continuous (fun v : ℝ =>
        fderiv ℝ (fderiv ℝ f) (z + v • d) d) :=
      ((hdf1.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply continuous_const
    have he := congrArg (fun T : E →L[ℝ] F => T h) hd
    rw [ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 1)] at he
    simpa only [d, add_sub_cancel, sub_apply,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using he
  have hcont : Continuous (fun u : ℝ => fderiv ℝ f (x + u • (a • h)) h) :=
    ((hf.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply continuous_const
  rw [hfirst, ← smul_sub]
  congr 1
  have hconst : (∫ _ in (0 : ℝ)..1, fderiv ℝ f z h) = fderiv ℝ f z h := by simp
  rw [← hconst, ← intervalIntegral.integral_sub (hcont.intervalIntegrable 0 1)
    intervalIntegrable_const]
  apply intervalIntegral.integral_congr
  intro u _
  exact hdiff u

/-- The actual gradient/Hessian cancellation is a genuine third-derivative
integral. Its direction order is outer displacement, inner difference,
innermost difference, matching native iterated Fréchet derivatives. -/
theorem ContDiff.fderiv_sub_sub_smul_iteratedFDeriv_two_eq_smul_sq_integral_three
    {Φ : E → F} (hΦ : ContDiff ℝ 3 Φ) (x D V : E) (a : ℝ) :
    (fderiv ℝ Φ (x + a • D) - fderiv ℝ Φ x) D -
        a • iteratedFDeriv ℝ 2 Φ (x - a • V) ![D, D] =
      a ^ 2 • ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1,
        iteratedFDeriv ℝ 3 Φ
          (x - a • V + v • (a • (V + u • D))) ![V + u • D, D, D] := by
  let g : E → F := fun y => fderiv ℝ Φ y D
  have hgrad : ContDiff ℝ 2 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  have hg : ContDiff ℝ 2 g := hgrad.clm_apply contDiff_const
  have hcancel := hg.sub_sub_smul_fderiv_eq_smul_integral_iteratedFDeriv_two
    x (x - a • V) D a
  have hfirst (y : E) : fderiv ℝ g y D = iteratedFDeriv ℝ 2 Φ y ![D, D] := by
    have h := iteratedFDeriv_clm_apply_const_apply hgrad (i := 1) (by norm_num)
      (x := y) (u := D) (m := ![D])
    simpa only [g, iteratedFDeriv_one_apply, iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] using h
  have hsecond (y B : E) : iteratedFDeriv ℝ 2 g y ![B, D] =
      iteratedFDeriv ℝ 3 Φ y ![B, D, D] := by
    rw [iteratedFDeriv_succ_apply_right (f := Φ) ![B, D, D]]
    have hi : Fin.init ![B, D, D] = ![B, D] := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      have hj : j = 0 := Fin.eq_zero j
      subst j
      rfl
    have hl : ![B, D, D] (Fin.last 2) = D := rfl
    simpa only [g, hi, hl] using iteratedFDeriv_clm_apply_const_apply hgrad
      (i := 2) (by norm_num) (x := y) (u := D) (m := ![B, D])
  have hdelta (u : ℝ) : x + u • (a • D) - (x - a • V) = a • (V + u • D) := by
    simp only [smul_add, smul_smul]
    rw [mul_comm u a]
    abel
  have hscale (y B : E) : iteratedFDeriv ℝ 2 g y ![a • B, D] =
      a • iteratedFDeriv ℝ 2 g y ![B, D] := by
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_smul, smul_apply]
  simp_rw [hfirst, hdelta, hscale, hsecond] at hcancel
  simp_rw [intervalIntegral.integral_smul] at hcancel
  rw [smul_smul] at hcancel
  simpa only [g, sub_apply, pow_two] using hcancel
