import NLAlib.Matrix.Basic.RealCoordinates
import NLAlib.Matrix.Norms.BilinearProbes
import NLAlib.ForMathlib.Analysis.Matrix.BilinearFunctional
import NLAlib.Probability.Gaussian.Basic.StandardGaussian
import NLAlib.Probability.SubGaussian.LpMoments
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Crude native Gaussian matrix spectral localization

Genuine centered Gaussian coordinate laws and a finite entry union give
an explicit spectral tail from the actual bilinear variance budget.
No independence of entries or nondegenerate covariance is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix ENNReal NNReal
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n×n)⊕(n×n)

open scoped Matrix.Norms.L2Operator in
private theorem specNorm_le_two_mul_card_mul_of_realCoordinates_le
    (A : M) {t : ℝ} (ht : 0≤t) (hA : ∀ j : J, |matrixRealCoordinates A j|≤t) :
    specNorm A≤2*(Fintype.card n : ℝ)*t := by
  have hentry (j k : n) : ‖A j k‖≤2*t := by
    have hr := hA (Sum.inl (j,k))
    have hi := hA (Sum.inr (j,k))
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
      simpa only [matrixRealCoordinates_inl,matrixRealCoordinates_inr,two_mul] using add_le_add hr hi)
  have hfrob : frobSq A≤(Fintype.card n : ℝ)^2*(2*t)^2 := by
    rw [frobSq_eq_sum_norm_sq]
    calc
      _ ≤ ∑ _j : n, ∑ _k : n, (2*t)^2 :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hentry j k) 2
      _ = _ := by simp; ring
  have hs := (specNorm_sq_le_frobSq A).trans hfrob
  have hb : 0≤2*(Fintype.card n : ℝ)*t := by positivity
  nlinarith [specNorm_nonneg A]

open scoped Matrix.Norms.L2Operator in
private theorem hasSubgaussianMGF_centered_gaussian_dual
    (ρ : Measure M) [IsGaussian ρ] (L : M →L[ℝ] ℝ) (v : ℝ≥0)
    (hvar : Var[L;ρ]≤v) :
    HasSubgaussianMGF (fun A => L (A-∫ B, B ∂ρ)) v ρ := by
  let : SecondCountableTopology M := inferInstanceAs (SecondCountableTopology (n → n → ℂ))
  let v0 : ℝ≥0 := (Var[L;ρ]).toNNReal
  have hraw : HasLaw (fun A : M => L A) (gaussianReal (∫ A, L A ∂ρ) v0) ρ :=
    ⟨L.continuous.measurable.aemeasurable,IsGaussian.map_eq_gaussianReal L⟩
  have hshift := gaussianReal_sub_const hraw (∫ A, L A ∂ρ)
  have hbase : HasSubgaussianMGF (fun A : M => L A-∫ B, L B ∂ρ) v0 ρ := by
    rw [← HasSubgaussianMGF.id_map_iff hshift.aemeasurable,hshift.map_eq,sub_self]
    exact hasSubgaussianMGF_id_gaussianReal v0
  have hv0 : (v0 : ℝ)≤v := by
    simpa only [v0,Real.coe_toNNReal _ (variance_nonneg _ _)] using hvar
  have hs : HasSubgaussianMGF (fun A : M => L A-∫ B, L B ∂ρ) v ρ := by
    refine ⟨hbase.integrable_exp_mul,fun s => (hbase.mgf_le s).trans ?_⟩
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv0 (sq_nonneg s)) (by norm_num)
  have hm : (∫ A : M, L A ∂ρ)=L (∫ A : M, A ∂ρ) :=
    L.integral_comp_comm (IsGaussian.integrable_id (μ := ρ))
  simpa only [map_sub,hm] using hs

open scoped Matrix.Norms.L2Operator in
/-- An actual Gaussian matrix law with a native centered bilinear variance
budget has an explicit crude spectral tail. Arbitrary covariance, nonzero
means, zero variance and empty dimensions are included. Hermitian support
is unnecessary for this entrywise localization bound. -/
theorem measureReal_centered_specNorm_gt_le_gaussian_of_bilinear_budget
    (ρ : Measure M) [IsGaussian ρ] {v s : ℝ} (hv : 0≤v) (hs : 0≤s)
    (hbudget : ∀ a b : EuclideanSpace ℂ n, ‖a‖=1 → ‖b‖=1 →
      (∫ A, ‖star a.ofLp ⬝ᵥ ((A-∫ B, B ∂ρ) *ᵥ b.ofLp)‖^2 ∂ρ)≤v) :
    ρ.real {A | 4*(Fintype.card n : ℝ)*Real.sqrt v*Real.sqrt s <
      specNorm (A-∫ B, B ∂ρ)} ≤
        4*(Fintype.card n : ℝ)^2*Real.exp (-s) := by
  let : SecondCountableTopology M := inferInstanceAs (SecondCountableTopology (n → n → ℂ))
  let D : M := ∫ A, A ∂ρ
  let E := matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)
  let L (j : J) : M →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp E.toContinuousLinearMap
  have hL (j : J) (A : M) : L j A=matrixRealCoordinates A j := rfl
  have hXm : MemLp (fun A : M => A-D) 2 ρ :=
    (IsGaussian.memLp_two_id (μ := ρ)).sub (memLp_const D)
  let e (j : n) : EuclideanSpace ℂ n := EuclideanSpace.single j 1
  have heNorm (j : n) : ‖e j‖=1 := by simp [e]
  have heval (j k : n) (A : M) : star (e j).ofLp ⬝ᵥ (A *ᵥ (e k).ofLp)=A j k := by simp [e]
  have heM (j k : n) : MemLp (fun A : M => (A-D) j k) 2 ρ := by
    have hh := ((Matrix.bilinearCLM (e j).ofLp (e k).ofLp).restrictScalars ℝ).comp_memLp' hXm
    change MemLp (fun A : M => Matrix.bilinearCLM (e j).ofLp (e k).ofLp (A-D)) 2 ρ at hh
    simpa only [Matrix.bilinearCLM_apply,heval] using hh
  have heBudget (j k : n) : (∫ A : M, ‖(A-D) j k‖^2 ∂ρ)≤v := by
    simpa only [heval] using hbudget (e j) (e k) (heNorm j) (heNorm k)
  have hcoordBudget (j : J) : (∫ A : M, (L j (A-D))^2 ∂ρ)≤v := by
    have hi : MemLp (fun A : M => L j (A-D)) 2 ρ := by
      simpa only [Function.comp_def] using (L j).comp_memLp' hXm
    rcases j with ⟨j,k⟩ | ⟨j,k⟩
    all_goals
      apply (integral_mono_ae hi.integrable_sq ((heM j k).integrable_norm_pow (by decide : 2≠0))
        (Eventually.of_forall fun A => ?_)).trans (heBudget j k)
      dsimp only
      rw [hL]
      simp only [matrixRealCoordinates_inl,matrixRealCoordinates_inr,
        Complex.sq_norm,Complex.normSq_apply]
      nlinarith [sq_nonneg ((A-D) j k).re,sq_nonneg ((A-D) j k).im]
  have hvariance (j : J) : Var[L j;ρ]≤v := by
    have hm : (∫ A : M, L j A ∂ρ)=L j (∫ A : M, A ∂ρ) :=
      (L j).integral_comp_comm (IsGaussian.integrable_id (μ := ρ))
    rw [variance_eq_integral (L j).continuous.measurable.aemeasurable]
    simpa only [map_sub,hm,D] using hcoordBudget j
  have hsg (j : J) : HasSubgaussianMGF (fun A : M => L j (A-D)) ⟨v,hv⟩ ρ :=
    hasSubgaussianMGF_centered_gaussian_dual ρ (L j) ⟨v,hv⟩ (hvariance j)
  let t := Real.sqrt v*Real.sqrt (2*s)
  have ht : 0≤t := by dsimp [t]; positivity
  have htail (j : J) : ρ.real {A : M | t < |L j (A-D)|}≤2*Real.exp (-s) := by
    have hh := measureReal_sqrt_mul_lt_abs_le_of_hasSubgaussianMGF (hsg j)
      (Real.sqrt_nonneg (2*s))
    change ρ.real {A : M | Real.sqrt v*Real.sqrt (2*s) < |L j (A-D)|} ≤
      2*Real.exp (-(Real.sqrt (2*s))^2/2) at hh
    have he : -(Real.sqrt (2*s))^2/2= -s := by rw [Real.sq_sqrt (by positivity)]; ring
    simpa only [t,he] using hh
  have hscale : 2*(Fintype.card n : ℝ)*t ≤
      4*(Fintype.card n : ℝ)*Real.sqrt v*Real.sqrt s := by
    have hroot : Real.sqrt (2*s)≤2*Real.sqrt s := by
      nlinarith [Real.sq_sqrt (by positivity : 0≤2*s),Real.sq_sqrt hs,
        Real.sqrt_nonneg (2*s),Real.sqrt_nonneg s]
    dsimp only [t]
    nlinarith [mul_nonneg (Nat.cast_nonneg (Fintype.card n)) (Real.sqrt_nonneg v),
      mul_le_mul_of_nonneg_left hroot
        (mul_nonneg (Nat.cast_nonneg (Fintype.card n)) (Real.sqrt_nonneg v))]
  have hsub : {A : M | 4*(Fintype.card n : ℝ)*Real.sqrt v*Real.sqrt s<specNorm (A-D)} ⊆
      ⋃ j : J, {A : M | t < |L j (A-D)|} := by
    intro A hA
    by_contra hnot
    have hb : ∀ j : J, |matrixRealCoordinates (A-D) j|≤t := by
      intro j
      have hj : ¬ t < |L j (A-D)| := fun hj => hnot (Set.mem_iUnion.mpr ⟨j,hj⟩)
      simpa only [hL] using le_of_not_gt hj
    exact (not_lt_of_ge ((specNorm_le_two_mul_card_mul_of_realCoordinates_le (A-D) ht hb).trans hscale)) hA
  calc
    _ ≤ ρ.real (⋃ j : J, {A : M | t < |L j (A-D)|}) := measureReal_mono hsub
    _ ≤ ∑ j : J, ρ.real {A : M | t < |L j (A-D)|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : J, 2*Real.exp (-s) := Finset.sum_le_sum fun j _ => htail j
    _ = _ := by simp [Fintype.card_sum,Fintype.card_prod]; ring

end NLAlib
