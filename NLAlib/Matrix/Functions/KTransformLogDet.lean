import NLAlib.Matrix.Functions.KTransformGeometry
import NLAlib.ForMathlib.Analysis.Matrix.DeterminantDerivative
import NLAlib.ForMathlib.MeasureTheory.CompactSupportDifferentiation
import NLAlib.ForMathlib.MeasureTheory.MatrixIntegral
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Actual determinant kernels for the matrix K-transform potential

The products `I+TS` and `I+ST` are generally non-Hermitian. Their actual
complex determinants are nevertheless positive on the source admissible
domain: the determinant equals that of the positive Hermitian whitening.
This supplies the genuine real logarithm in the block-Wishart potential,
without treating a non-Hermitian product as a positive matrix.

Source: Montanari--Saeed 2026, Theorem 2 and equation (25).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open MeasureTheory Set Filter
open scoped Topology

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant of the generally non-Hermitian `I+TS` is exactly the
determinant of its Hermitian square-root whitening. -/
theorem det_one_add_mul_eq_det_one_add_matrixKWhitened
    (S T : Matrix n n ℂ) (hS : S.PosDef) :
    (1 + T * S).det = (1 + matrixKWhitened S T).det := by
  let Q := cfc Real.sqrt S
  have hQQ : Q * Q = S := cfc_sqrt_mul_self hS
  calc
    (1 + T * S).det = (1 + (T * Q) * Q).det := by rw [Matrix.mul_assoc, hQQ]
    _ = (1 + Q * (T * Q)).det := Matrix.det_one_add_mul_comm _ _
    _ = _ := by simp only [matrixKWhitened, Q, Matrix.mul_assoc]

/-- Source support admissibility makes the actual complex determinant of
`I+TS` positive, although `I+TS` itself need not be Hermitian. Empty matrix
dimensions are included. -/
theorem det_one_add_mul_pos_of_matrixK_admissible
    (S T : Matrix n n ℂ) (hS : S.PosDef) (hgap : (S⁻¹ + T).PosDef) :
    0 < (1 + T * S).det := by
  rw [det_one_add_mul_eq_det_one_add_matrixKWhitened S T hS]
  exact (posDef_one_add_matrixKWhitened S T hS hgap).det_pos

/-- The other order of the actual solved determinant is positive under
exactly the same support-only admissibility conditions. -/
theorem det_one_add_mul_pos_of_matrixK_admissible_left
    (S T : Matrix n n ℂ) (hS : S.PosDef) (hgap : (S⁻¹ + T).PosDef) :
    0 < (1 + S * T).det := by
  rw [Matrix.det_one_add_mul_comm S T]
  exact det_one_add_mul_pos_of_matrixK_admissible S T hS hgap

/-- The actual source log-determinant kernel, using the real part of its
complex determinant. On the admissible domain that determinant is positive
real, as proved above. -/
def matrixKLogDetKernel (S T : Matrix n n ℂ) : ℝ :=
  Real.log ((1 + T * S).det.re)

/-- The actual complex and Hermitian-whitened log-determinants agree on the
source positive cone. No commutation of `S` and `T` is assumed. -/
theorem matrixKLogDetKernel_eq_log_det_whitened
    (S T : Matrix n n ℂ) (hS : S.PosDef) :
    matrixKLogDetKernel S T = Real.log ((1 + matrixKWhitened S T).det.re) := by
  rw [matrixKLogDetKernel, det_one_add_mul_eq_det_one_add_matrixKWhitened S T hS]

/-- Differentiate the actual log-determinant kernel along any real matrix
path. The pointwise source gap supplies the positive determinant; the
derivative is the actual resolvent trace pairing. -/
theorem hasDerivAt_matrixKLogDetKernel
    {S : ℝ → Matrix n n ℂ} {Δ : Matrix n n ℂ} {t : ℝ}
    (hpath : HasDerivAt S Δ t) (T : Matrix n n ℂ)
    (hS : (S t).PosDef) (hgap : ((S t)⁻¹ + T).PosDef) :
    HasDerivAt (fun v => matrixKLogDetKernel (S v) T)
      ((matrixKResolvent (S t) T * Δ).trace.re) t := by
  have hA := (hpath.const_mul T).const_add 1
  have h := hA.log_re_matrix_det (det_one_add_mul_pos_of_matrixK_admissible (S t) T hS hgap)
  have hT : T.IsHermitian := by
    have hg := hgap.isHermitian
    have hi := hS.inv.isHermitian
    convert hg.sub hi using 1
    abel
  have hr := matrixKResolvent_eq_right (S t) T hS hT hgap
  simpa only [matrixKLogDetKernel, ← Matrix.mul_assoc, ← hr, RCLike.re_eq_complex_re] using h

/-- The genuine log-determinant kernel is integrable from compact support
and the source gap, without a regularity assumption outside the support. -/
theorem integrable_matrixKLogDetKernel
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (S : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef) :
    Integrable (fun T => matrixKLogDetKernel S T.val) ν := by
  have hc : ContinuousOn (fun T : selfAdjoint (Matrix n n ℂ) =>
      matrixKLogDetKernel S T.val) ν.support := by
    apply (Complex.continuous_re.comp
      (continuous_const.add (continuous_subtype_val.mul continuous_const)).matrix_det).continuousOn.log
    intro T hT
    exact (Complex.pos_iff.mp
      (det_one_add_mul_pos_of_matrixK_admissible S T.val hS (hgap T hT))).1.ne'
  have hi := hc.integrableOn_compact (μ := ν) hν
  have hre : ν.restrict ν.support = ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
  rwa [IntegrableOn, hre] at hi

/-- Differentiate the actual averaged log-determinant on a matrix line.
The uniform neighborhood, integrability and derivative domination are
derived from compact support and actual positive determinants. -/
theorem hasDerivAt_integral_matrixKLogDetKernel
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (S Δ : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef) :
    HasDerivAt (fun v : ℝ => ∫ T, matrixKLogDetKernel (S + v • Δ) T.val ∂ν)
      (∫ T, (matrixKResolvent S T.val * Δ).trace.re ∂ν) 0 := by
  let A : ℝ → selfAdjoint (Matrix n n ℂ) → Matrix n n ℂ :=
    fun v T => 1 + T.val * (S + v • Δ)
  let F : ℝ → selfAdjoint (Matrix n n ℂ) → ℝ := fun v T => Real.log (A v T).det.re
  let q : ℝ → selfAdjoint (Matrix n n ℂ) → ℝ :=
    fun v T => ((A v T).adjugate * (T.val * Δ)).trace.re / (A v T).det.re
  let D : ℝ → selfAdjoint (Matrix n n ℂ) → ℝ →L[ℝ] ℝ :=
    fun v T => q v T • (1 : ℝ →L[ℝ] ℝ)
  let U : Set (ℝ × selfAdjoint (Matrix n n ℂ)) := {p | (A p.1 p.2).det.re ≠ 0}
  have hA : Continuous (fun p : ℝ × selfAdjoint (Matrix n n ℂ) => A p.1 p.2) := by
    dsimp [A]
    fun_prop
  have hdet : Continuous (fun p : ℝ × selfAdjoint (Matrix n n ℂ) => (A p.1 p.2).det.re) :=
    Complex.continuous_re.comp hA.matrix_det
  have hU : IsOpen U := isOpen_ne_fun hdet continuous_const
  have hF : ContinuousOn (fun p : ℝ × selfAdjoint (Matrix n n ℂ) => F p.1 p.2) U :=
    hdet.continuousOn.log (fun _ hp => hp)
  have hq : ContinuousOn (fun p : ℝ × selfAdjoint (Matrix n n ℂ) => q p.1 p.2) U := by
    apply (Complex.continuous_re.comp
      ((hA.matrix_adjugate.mul
        ((continuous_subtype_val.comp continuous_snd).mul continuous_const)).matrix_trace)).continuousOn.div
      hdet.continuousOn
    exact fun _ hp => hp
  have hD : ContinuousOn (fun p : ℝ × selfAdjoint (Matrix n n ℂ) => D p.1 p.2) U :=
    hq.smul continuousOn_const
  have hline (v : ℝ) (T : selfAdjoint (Matrix n n ℂ)) :
      HasDerivAt (fun v => A v T) (T.val * Δ) v := by
    simpa only [A, id_eq, one_smul] using
      ((((hasDerivAt_id v).smul_const Δ).const_add S).const_mul T.val).const_add 1
  have hd (p : ℝ × selfAdjoint (Matrix n n ℂ)) (hp : p ∈ U) :
      HasFDerivAt (fun v => F v p.2) (D p.1 p.2) p.1 := by
    have h := (hline p.1 p.2).matrix_det
    have hr := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt p.1 h).log hp
    convert! hr.hasFDerivAt using 1
    ext
    simp [D, q]
  have hpoint (T : selfAdjoint (Matrix n n ℂ)) (hT : T ∈ ν.support) : (0,T) ∈ U := by
    change (1 + T.val * (S + (0 : ℝ) • Δ)).det.re ≠ 0
    simpa only [zero_smul, add_zero] using (Complex.pos_iff.mp
      (det_one_add_mul_pos_of_matrixK_admissible S T.val hS (hgap T hT))).1.ne'
  have hI := NLAlib.hasFDerivAt_integral_of_compact_support ν hν F D U hU hF hD hd 0 hpoint
  have hDi : Integrable (D 0) ν := by
    have hc : ContinuousOn (q 0) ν.support := by
      apply hq.comp (f := fun T : selfAdjoint (Matrix n n ℂ) => ((0 : ℝ),T))
        (continuous_const.prodMk continuous_id).continuousOn
      exact hpoint
    have hi := hc.integrableOn_compact (μ := ν) hν
    have hre : ν.restrict ν.support = ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
    rw [IntegrableOn, hre] at hi
    exact hi.smul_const (1 : ℝ →L[ℝ] ℝ)
  have h := hI.hasDerivAt
  rw [ContinuousLinearMap.integral_apply hDi] at h
  have hq₀ : (fun T => D 0 T 1) =ᵐ[ν]
      (fun T => (matrixKResolvent S T.val * Δ).trace.re) := by
    filter_upwards [ν.support_mem_ae] with T hT
    have h₁ := (hd (0,T) (hpoint T hT)).hasDerivAt
    have hpath₀ : HasDerivAt (fun v : ℝ => S + v • Δ) Δ 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).smul_const Δ).const_add S)
    have h₂ := hasDerivAt_matrixKLogDetKernel hpath₀ T.val
      (by simpa only [zero_smul, add_zero] using hS)
      (by simpa only [zero_smul, add_zero] using hgap T hT)
    simp only [zero_smul, add_zero] at h₂
    exact h₁.unique (by convert! h₂ using 1)
  rw [integral_congr_ae hq₀] at h
  convert! h using 1

/-- The source's genuine finite-matrix variational potential. Trace is
unnormalized; the law-level potential has an additional factor `1/card n`.
The definition is total, while positive determinants are established on
the admissible domain above. -/
def matrixKPotential (ν : Measure (selfAdjoint (Matrix n n ℂ))) (α u : ℝ)
    (S : Matrix n n ℂ) : ℝ :=
  -α * u * S.trace.re + α * (∫ T, matrixKLogDetKernel S T.val ∂ν) -
    Real.log S.det.re - Fintype.card n * (Real.log α + 1)

/-- The actual directional derivative of the source variational potential
is the actual K-transform trace pairing. All kernel differentiation and
integrability are derived from the compact support and the source gap.
Source: Montanari--Saeed 2026, equation (49).
atlas: block-wishart-log-potential (partial) -/
theorem hasDerivAt_matrixKPotential_line
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α u : ℝ) (hα : α ≠ 0)
    (S Δ : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef) :
    HasDerivAt (fun v : ℝ => matrixKPotential ν α u (S + v • Δ))
      (α * ((matrixKTransform ν α S - (u : ℂ) • 1) * Δ).trace.re) 0 := by
  have hline : HasDerivAt (fun v : ℝ => S + v • Δ) Δ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const Δ).const_add S
  let L : Matrix n n ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap
  have htrace : HasDerivAt (fun v : ℝ => (S + v • Δ).trace.re) Δ.trace.re 0 := by
    convert! L.hasFDerivAt.comp_hasDerivAt 0 hline using 1
  have hlog := hline.log_re_matrix_det (by simpa using hS.det_pos)
  have hI := hasDerivAt_integral_matrixKLogDetKernel ν hν S Δ hS hgap
  have h := (((htrace.const_mul (-α * u)).add (hI.const_mul α)).sub hlog).sub_const
    (Fintype.card n * (Real.log α + 1))
  have hc : ContinuousOn (fun T : selfAdjoint (Matrix n n ℂ) => matrixKResolvent S T.val)
      ν.support := by
    intro T hT
    exact ((continuousAt_matrixKResolvent S T.val
      (isUnit_matrixKDenominator S T.val hS (hgap T hT))).comp
        (f := fun T : selfAdjoint (Matrix n n ℂ) => (S,T.val))
        (continuous_const.prodMk continuous_subtype_val).continuousAt).continuousWithinAt
  have hRi : Integrable (fun T => matrixKResolvent S T.val) ν := by
    have hi := hc.integrableOn_compact (μ := ν) hν
    have hre : ν.restrict ν.support = ν := Measure.restrict_eq_self_of_ae_mem ν.support_mem_ae
    rwa [IntegrableOn, hre] at hi
  have hRΔ : Integrable (fun T => matrixKResolvent S T.val * Δ) ν :=
    ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ)).flip Δ).integrable_comp hRi
  have htraceI : (∫ T, (matrixKResolvent S T.val * Δ).trace.re ∂ν) =
      ((∫ T, matrixKResolvent S T.val ∂ν) * Δ).trace.re := by
    have hh := Matrix.re_trace_integral hRΔ
    rw [integral_mul_const_of_integrable hRi] at hh
    simpa only [RCLike.re_eq_complex_re] using hh.symm
  convert! h using 1
  simp only [zero_smul, add_zero] at *
  rw [htraceI]
  simp only [matrixKTransform, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, Complex.smul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, zero_mul, sub_zero,
    smul_eq_mul, RCLike.re_eq_complex_re]
  field_simp [hα]
  ring

/-- A genuinely solved source equation is stationary for every actual
matrix direction; this concludes only stationarity, not the separate
global minimum theorem. -/
theorem hasDerivAt_matrixKPotential_line_zero_of_eq
    (ν : Measure (selfAdjoint (Matrix n n ℂ))) [IsFiniteMeasure ν]
    (hν : IsCompact ν.support) (α u : ℝ) (hα : α ≠ 0)
    (S Δ : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : ∀ T ∈ ν.support, (S⁻¹ + T.val).PosDef)
    (hK : matrixKTransform ν α S = (u : ℂ) • 1) :
    HasDerivAt (fun v : ℝ => matrixKPotential ν α u (S + v • Δ)) 0 0 := by
  simpa only [hK, sub_self, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, mul_zero]
    using hasDerivAt_matrixKPotential_line ν hν α u hα S Δ hS hgap

end NLAlib
