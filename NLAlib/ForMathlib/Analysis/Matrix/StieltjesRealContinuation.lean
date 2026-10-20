import NLAlib.ForMathlib.Analysis.Matrix.HermitianSpanning
import NLAlib.ForMathlib.MeasureTheory.CompactStieltjesCalculus
import NLAlib.ForMathlib.MeasureTheory.StieltjesPositiveBoundary
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Matrix.Order

/-! # Real analytic continuation constructed by Stieltjes polarization

Four actual positive quadratic measures reconstruct every matrix entry.
At a common true gap their native transforms are analytic and real on
the real axis, giving a genuine Hermitian analytic matrix extension.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix Filter
open scoped Matrix.Norms.L2Operator ComplexOrder ComplexStarModule Topology
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

private theorem stieltjes_eventuallyEq_of_upperHalfPlane
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : ℂ → E) (u : ℝ) (hf : AnalyticAt ℂ f (u : ℂ))
    (hg : AnalyticAt ℂ g (u : ℂ))
    (he : ∀ z : ℂ, 0<z.im → f z=g z) : f=ᶠ[𝓝 (u : ℂ)] g := by
  rcases hf.eventually_eq_or_eventually_ne hg with h|h
  · exact h
  · let γ (k : ℕ) : ℝ := 1/((k : ℝ)+1)
    have hγ (k : ℕ) : 0<γ k := by dsimp only [γ]; positivity
    have hγ0 : Tendsto γ atTop (𝓝 0) :=
      (tendsto_atTop_add_const_right atTop 1
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
    have hz : Tendsto (fun k : ℕ => (u : ℂ)+(γ k : ℂ)*Complex.I)
        atTop (𝓝 (u : ℂ)) := by
      simpa only [Complex.ofReal_zero,zero_mul,add_zero,Function.comp_def] using
        tendsto_const_nhds.add (((Complex.continuous_ofReal.tendsto 0).comp hγ0).mul_const Complex.I)
    have hzne (k : ℕ) : (u : ℂ)+(γ k : ℂ)*Complex.I≠(u : ℂ) := by
      intro hh
      have hi := congrArg Complex.im hh
      have hi' : γ k=0 := by simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,
        Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_add,add_zero]
        using hi
      exact (hγ k).ne' hi'
    have hz' : Tendsto (fun k : ℕ => (u : ℂ)+(γ k : ℂ)*Complex.I)
        atTop (𝓝[≠] (u : ℂ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hz,Eventually.of_forall hzne⟩
    obtain ⟨k,hk⟩ := (hz'.eventually h).exists
    exact False.elim (hk (he _ (by simpa using hγ k)))

/-- Actual positive quadratic Stieltjes measures construct one genuine
matrix continuation analytic at every common compact-support gap.
The matrix function is constructed by finite complex polarization,
uniformly across all real evaluation points.
-/
theorem exists_global_real_matrix_extension_of_quadratic_stieltjes
    (N : ℂ → M) (μ : (n → ℂ) → FiniteMeasure ℝ)
    (hμ : ∀ v : n → ℂ, ∀ z : ℂ, 0<z.im → matrixQuadraticFormCLM v (N z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ v : Measure ℝ))
    (hcompact : ∀ v : n → ℂ, IsCompact (μ v : Measure ℝ).support) :
    ∃ G : ℂ → M,
      (∀ u : ℝ, (∀ v : n → ℂ, ∀ t ∈ (μ v : Measure ℝ).support, t≠u) →
        AnalyticAt ℂ G (u : ℂ)) ∧
      (∀ z : ℂ, 0<z.im → G z=N z) ∧ ∀ x : ℝ, (G x).IsHermitian := by
  let Q (v : n → ℂ) (z : ℂ) := ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ v : Measure ℝ)
  let G : ℂ → M := fun z =>
    (∑ i : n, ∑ j : n,
      ((1/8 : ℂ)*(Q (Pi.single i 1+Pi.single j 1) z-
        Q (Pi.single i 1-Pi.single j 1) z))•hermitianUnitRe i j)+
    (∑ i : n, ∑ j : n,
      ((-1/8 : ℂ)*(Q (Pi.single i 1+Complex.I•Pi.single j 1) z-
        Q (Pi.single i 1-Complex.I•Pi.single j 1) z))•hermitianUnitIm i j)
  have hQa (u : ℝ) (hu : ∀ v : n → ℂ, ∀ t ∈ (μ v : Measure ℝ).support, t≠u)
      (v : n → ℂ) : AnalyticAt ℂ (Q v) (u : ℂ) :=
    analyticAt_integral_real_cauchyKernel_of_support (μ v : Measure ℝ) (hcompact v) u
      (fun t ht htu => hu v t ht (Complex.ofReal_injective htu))
  have hGa (u : ℝ) (hu : ∀ v : n → ℂ, ∀ t ∈ (μ v : Measure ℝ).support, t≠u) :
      AnalyticAt ℂ G (u : ℂ) := by
    apply AnalyticAt.add
    · apply Finset.univ.analyticAt_fun_sum
      intro i _
      apply Finset.univ.analyticAt_fun_sum
      intro j _
      exact (analyticAt_const.mul ((hQa u hu _).sub (hQa u hu _))).smul analyticAt_const
    · apply Finset.univ.analyticAt_fun_sum
      intro i _
      apply Finset.univ.analyticAt_fun_sum
      intro j _
      exact (analyticAt_const.mul ((hQa u hu _).sub (hQa u hu _))).smul analyticAt_const
  have hGN (z : ℂ) (hz : 0<z.im) : G z=N z := by
    have hQ (v : n → ℂ) : Q v z=matrixQuadraticFormCLM v (N z) := (hμ v z hz).symm
    simp only [G,hQ,matrixQuadraticFormCLM_single_add_sub,matrixQuadraticFormCLM_single_add_sub_I]
    have hr (i j : n) : (1/8 : ℂ)*(2*((N z) i j+(N z) j i))=
        ((N z) i j+(N z) j i)/4 := by ring
    have hi (i j : n) : (-1/8 : ℂ)*(2*Complex.I*((N z) i j-(N z) j i))=
        ((N z) i j-(N z) j i)/(4*Complex.I) := by
      field_simp
      simp only [Complex.I_sq]
      ring
    simp_rw [hr,hi]
    exact sum_hermitianUnit_eq (N z)
  have hGr (x : ℝ) : (G x).IsHermitian := by
    have hQr (v : n → ℂ) : Q v (x : ℂ)=((∫ t : ℝ, (t-x)⁻¹ ∂(μ v : Measure ℝ) : ℝ) : ℂ) := by
      simp only [Q,← Complex.ofReal_sub,← Complex.ofReal_inv]
      exact integral_complex_ofReal
    have hRe (i j : n) :
        (((1/8 : ℂ)*(Q (Pi.single i 1+Pi.single j 1) x-
          Q (Pi.single i 1-Pi.single j 1) x))•hermitianUnitRe i j).IsHermitian := by
      apply (isHermitian_hermitianUnitRe i j).smul
      rw [hQr,hQr]
      simp [IsSelfAdjoint]
    have hIm (i j : n) :
        (((-1/8 : ℂ)*(Q (Pi.single i 1+Complex.I•Pi.single j 1) x-
          Q (Pi.single i 1-Complex.I•Pi.single j 1) x))•hermitianUnitIm i j).IsHermitian := by
      apply (isHermitian_hermitianUnitIm i j).smul
      rw [hQr,hQr]
      simp [IsSelfAdjoint]
    change (G x)ᴴ=G x
    simp only [G,Matrix.conjTranspose_add,Matrix.conjTranspose_sum]
    apply congrArg₂ (fun A B : M => A+B)
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact (hRe i j).eq
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact (hIm i j).eq
  exact ⟨G,hGa,hGN,hGr⟩

/-- Actual positive quadratic Stieltjes measures construct an analytic
matrix continuation through a specified common compact-support gap.
Its values are Hermitian on the real axis by the true scalar kernels. -/
theorem exists_analytic_real_matrix_extension_of_quadratic_stieltjes
    (N : ℂ → M) (μ : (n → ℂ) → FiniteMeasure ℝ)
    (hμ : ∀ v : n → ℂ, ∀ z : ℂ, 0<z.im → matrixQuadraticFormCLM v (N z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ v : Measure ℝ))
    (hcompact : ∀ v : n → ℂ, IsCompact (μ v : Measure ℝ).support)
    (u : ℝ) (hu : ∀ v : n → ℂ, ∀ t ∈ (μ v : Measure ℝ).support, t≠u) :
    ∃ G : ℂ → M, AnalyticAt ℂ G (u : ℂ) ∧
      (∀ z : ℂ, 0<z.im → G z=N z) ∧ ∀ x : ℝ, (G x).IsHermitian := by
  obtain ⟨G,hGa,hGN,hGr⟩ :=
    exists_global_real_matrix_extension_of_quadratic_stieltjes N μ hμ hcompact
  exact ⟨G,hGa u hu,hGN,hGr⟩

/-- Every actual quadratic Stieltjes transform agrees as an analytic
germ with a matrix continuation reconstructed from finitely many
polarization probes. Both the real value and the complex derivative
are therefore given by the native scalar kernels, even though only
upper-half-plane agreement was initially available. -/
theorem quadratic_value_deriv_real_extension_of_stieltjes
    (N G : ℂ → M) (μ : (n → ℂ) → FiniteMeasure ℝ)
    (hμ : ∀ v : n → ℂ, ∀ z : ℂ, 0<z.im → matrixQuadraticFormCLM v (N z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ v : Measure ℝ))
    (hcompact : ∀ v : n → ℂ, IsCompact (μ v : Measure ℝ).support)
    (u : ℝ) (hu : ∀ v : n → ℂ, ∀ t ∈ (μ v : Measure ℝ).support, t≠u)
    (hGa : AnalyticAt ℂ G (u : ℂ)) (hGN : ∀ z : ℂ, 0<z.im → G z=N z)
    (v : n → ℂ) :
    matrixQuadraticFormCLM v (G u)=
      ∫ t : ℝ, ((t : ℂ)-(u : ℂ))⁻¹ ∂(μ v : Measure ℝ) ∧
    matrixQuadraticFormCLM v (deriv G (u : ℂ))=
      ∫ t : ℝ, (((t : ℂ)-(u : ℂ))⁻¹)^2 ∂(μ v : Measure ℝ) := by
  have hgap : ∀ t ∈ (μ v : Measure ℝ).support, (t : ℂ)≠(u : ℂ) :=
    fun t ht htu => hu v t ht (Complex.ofReal_injective htu)
  have hQa := analyticAt_integral_real_cauchyKernel_of_support
    (μ v : Measure ℝ) (hcompact v) u hgap
  have hpa := ((matrixQuadraticFormCLM v).analyticAt (G u)).comp hGa
  have he := stieltjes_eventuallyEq_of_upperHalfPlane
    (fun z : ℂ => matrixQuadraticFormCLM v (G z))
    (fun z : ℂ => ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ v : Measure ℝ)) u hpa hQa
    (fun z hz => by rw [hGN z hz]; exact hμ v z hz)
  refine ⟨he.self_of_nhds,?_⟩
  have hpder : HasDerivAt (fun z : ℂ => matrixQuadraticFormCLM v (G z))
      (matrixQuadraticFormCLM v (deriv G (u : ℂ))) (u : ℂ) :=
    (matrixQuadraticFormCLM v).hasFDerivAt.comp_hasDerivAt (u : ℂ) hGa.differentiableAt.hasDerivAt
  have hQder := hasDerivAt_integral_real_cauchyKernel_of_support
    (μ v : Measure ℝ) (hcompact v) u hgap
  exact hpder.unique (hQder.congr_of_eventuallyEq he)

private theorem stieltjes_isHermitian_deriv_of_real_values
    (G : ℂ → M) (u : ℝ) (hGa : AnalyticAt ℂ G (u : ℂ))
    (hreal : ∀ x : ℝ, (G x).IsHermitian) :
    (deriv G (u : ℂ)).IsHermitian := by
  have hd : HasDerivAt (fun x : ℝ => G (x : ℂ)) (deriv G (u : ℂ)) u :=
    by
      have hcoe : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) u := by
        convert! (Complex.ofRealCLM.hasDerivAt (x := u)) using 1
      have hGC : HasFDerivAt G
          ((ContinuousLinearMap.toSpanSingleton ℂ (deriv G (u : ℂ))).restrictScalars ℝ) (u : ℂ) :=
        hGa.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
      convert! hGC.comp_hasDerivAt u hcoe using 1
      simp only [ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.toSpanSingleton_apply,
        one_smul]
  have hl := hd.tendsto_slope_zero_right
  have hc : IsClosed {A : M | IsSelfAdjoint A} :=
    isClosed_eq continuous_star continuous_id
  apply IsSelfAdjoint.isHermitian
  apply hc.mem_of_tendsto hl
  exact Eventually.of_forall fun t : ℝ =>
    (((hreal (u+t)).sub (hreal u)).smul (IsSelfAdjoint.all t⁻¹)).isSelfAdjoint

/-- Nonzero actual positive quadratic measures force a true matrix
Stieltjes continuation and its complex derivative to be positive
definite below their common support. The positive boundary value and
positive derivative are conclusions, not branch hypotheses. -/
theorem posDef_real_extension_and_deriv_of_quadratic_stieltjes
    (N G : ℂ → M) (μ : (n → ℂ) → FiniteMeasure ℝ)
    (hμ : ∀ v : n → ℂ, ∀ z : ℂ, 0<z.im → matrixQuadraticFormCLM v (N z)=
      ∫ t : ℝ, ((t : ℂ)-z)⁻¹ ∂(μ v : Measure ℝ))
    (hcompact : ∀ v : n → ℂ, IsCompact (μ v : Measure ℝ).support)
    (hmass : ∀ v : n → ℂ, v≠0 → (μ v : Measure ℝ)≠0)
    (u : ℝ) (hu : ∀ v : n → ℂ, ∀ t ∈ (μ v : Measure ℝ).support, u<t)
    (hGa : AnalyticAt ℂ G (u : ℂ)) (hGN : ∀ z : ℂ, 0<z.im → G z=N z)
    (hreal : ∀ x : ℝ, (G x).IsHermitian) :
    (G u).PosDef ∧ (deriv G (u : ℂ)).PosDef := by
  have hquad (v : n → ℂ) (hv : v≠0) :
      0<matrixQuadraticFormCLM v (G u) ∧
      0<matrixQuadraticFormCLM v (deriv G (u : ℂ)) := by
    have hp := integral_inv_sub_pos_and_sq_pos_of_support_gt
      (μ v : Measure ℝ) (hcompact v) (hmass v hv) u (hu v)
    have he := quadratic_value_deriv_real_extension_of_stieltjes N G μ hμ hcompact u
      (fun w t ht => (hu w t ht).ne') hGa hGN v
    rw [he.1,he.2]
    have hval : (∫ t : ℝ, ((t : ℂ)-(u : ℂ))⁻¹ ∂(μ v : Measure ℝ))=
        ((∫ t : ℝ, (t-u)⁻¹ ∂(μ v : Measure ℝ) : ℝ) : ℂ) := by
      simp only [← Complex.ofReal_sub,← Complex.ofReal_inv]
      exact integral_complex_ofReal
    have hder : (∫ t : ℝ, (((t : ℂ)-(u : ℂ))⁻¹)^2 ∂(μ v : Measure ℝ))=
        ((∫ t : ℝ, ((t-u)⁻¹)^2 ∂(μ v : Measure ℝ) : ℝ) : ℂ) := by
      simp only [← Complex.ofReal_sub,← Complex.ofReal_inv,← Complex.ofReal_pow]
      exact integral_complex_ofReal
    rw [hval,hder]
    exact ⟨Complex.zero_lt_real.mpr hp.1,Complex.zero_lt_real.mpr hp.2⟩
  exact ⟨PosDef.of_dotProduct_mulVec_pos (hreal u) (fun v hv => (hquad v hv).1),
    PosDef.of_dotProduct_mulVec_pos (stieltjes_isHermitian_deriv_of_real_values G u hGa hreal)
      (fun v hv => (hquad v hv).2)⟩

end Matrix
