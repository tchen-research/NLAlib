import NLAlib.Probability.Gaussian.Basic.StandardVector
import NLAlib.Probability.Gaussian.Calculus.VarianceInterpolation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Exact interpolation between disjoint Gaussian coordinate blocks

The two block laws are constructed by zero extension of independent standard
Gaussian vectors. Their means, full covariances, and product-law change of
variables are proved before applying the exact variance interpolation formula.
This gives a literal one-product-coordinate formula suited to native matrix
coefficient models, with no Gaussian-law or covariance interface assumptions.
Source: arXiv:2108.06312v2, Lemma 4.11.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace NLAlib

variable {α β F : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local notation "E" => α ⊕ β → ℝ

private def gaussianLeftExtension : (α → ℝ) →L[ℝ] E :=
  ContinuousLinearMap.pi fun k => Sum.elim
    (fun i => ContinuousLinearMap.proj i) (fun _ => 0) k

private def gaussianRightExtension : (β → ℝ) →L[ℝ] E :=
  ContinuousLinearMap.pi fun k => Sum.elim
    (fun _ => 0) (fun i => ContinuousLinearMap.proj i) k

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
private theorem gaussianLeftExtension_apply (x : α → ℝ) (k : α ⊕ β) :
    gaussianLeftExtension x k = Sum.elim x (fun _ => 0) k := by cases k <;> rfl

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
private theorem gaussianRightExtension_apply (x : β → ℝ) (k : α ⊕ β) :
    gaussianRightExtension x k = Sum.elim (fun _ => 0) x k := by cases k <;> rfl

private abbrev leftLaw : Measure E := (gaussianVector α).map gaussianLeftExtension
private abbrev rightLaw : Measure E := (gaussianVector β).map gaussianRightExtension

private instance leftLaw_isGaussian : IsGaussian (leftLaw (α := α) (β := β)) :=
  ((hasGaussianLaw_id_gaussianVector α).map_fun
    (gaussianLeftExtension (α := α) (β := β))).isGaussian_map

private instance rightLaw_isGaussian : IsGaussian (rightLaw (α := α) (β := β)) :=
  ((hasGaussianLaw_id_gaussianVector β).map_fun
    (gaussianRightExtension (α := α) (β := β))).isGaussian_map

private theorem integral_id_standard {κ : Type*} [Fintype κ] :
    (∫ x : κ → ℝ, x ∂gaussianVector κ) = 0 := by
  have hi := (hasGaussianLaw_id_gaussianVector κ).memLp_two.integrable one_le_two
  ext k
  have he := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) k).integral_comp_comm hi
  have hz := integral_eq_zero_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector k)
  simpa only [ContinuousLinearMap.proj_apply, Pi.zero_apply] using he.symm.trans hz

omit [DecidableEq α] [DecidableEq β] in
private theorem integral_id_leftLaw :
    (∫ x : E, x ∂leftLaw (α := α) (β := β)) = 0 := by
  have he := integral_map (μ := gaussianVector α)
    (show AEMeasurable (gaussianLeftExtension (α := α) (β := β)) _ from by fun_prop)
    aestronglyMeasurable_id
  simp only [id_eq] at he
  rw [show (∫ x : E, x ∂leftLaw (α := α) (β := β)) =
    ∫ x : α → ℝ, gaussianLeftExtension x ∂gaussianVector α from he]
  have hL := (gaussianLeftExtension (α := α) (β := β)).integral_comp_comm
    (φ := fun x : α → ℝ => x)
    ((hasGaussianLaw_id_gaussianVector α).memLp_two.integrable one_le_two)
  simpa only [integral_id_standard, map_zero] using hL

omit [DecidableEq α] [DecidableEq β] in
private theorem integral_id_rightLaw :
    (∫ x : E, x ∂rightLaw (α := α) (β := β)) = 0 := by
  have he := integral_map (μ := gaussianVector β)
    (show AEMeasurable (gaussianRightExtension (α := α) (β := β)) _ from by fun_prop)
    aestronglyMeasurable_id
  simp only [id_eq] at he
  rw [show (∫ x : E, x ∂rightLaw (α := α) (β := β)) =
    ∫ x : β → ℝ, gaussianRightExtension x ∂gaussianVector β from he]
  have hL := (gaussianRightExtension (α := α) (β := β)).integral_comp_comm
    (φ := fun x : β → ℝ => x)
    ((hasGaussianLaw_id_gaussianVector β).memLp_two.integrable one_le_two)
  simpa only [integral_id_standard, map_zero] using hL

private theorem covariance_standard {κ : Type*} [Fintype κ] [DecidableEq κ] (i j : κ) :
    cov[(fun x : κ → ℝ => x i),(fun x : κ → ℝ => x j);gaussianVector κ] =
      if i=j then 1 else 0 := by
  rw [covariance_eq_sub (memLp_two_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector i))
    (memLp_two_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector j))]
  simp only [Pi.mul_apply]
  rw [integral_mul_apply_gaussianVector,
    integral_eq_zero_of_hasLaw_gaussianReal (hasLaw_eval_gaussianVector i),
    zero_mul, sub_zero]

omit [DecidableEq β] in
private theorem covariance_leftLaw (i j : α ⊕ β) :
    cov[(fun x : E => x i),(fun x : E => x j);leftLaw (α := α) (β := β)] =
      match i,j with
      | .inl a,.inl b => if a=b then 1 else 0
      | _,_ => 0 := by
  rw [covariance_map_fun (continuous_apply i).aestronglyMeasurable
    (continuous_apply j).aestronglyMeasurable (by fun_prop)]
  simp only [gaussianLeftExtension_apply]
  cases i <;> cases j <;> simp only [Sum.elim_inl,Sum.elim_inr,
    covariance_standard,covariance_const_left,covariance_const_right]

omit [DecidableEq α] in
private theorem covariance_rightLaw (i j : α ⊕ β) :
    cov[(fun x : E => x i),(fun x : E => x j);rightLaw (α := α) (β := β)] =
      match i,j with
      | .inr a,.inr b => if a=b then 1 else 0
      | _,_ => 0 := by
  rw [covariance_map_fun (continuous_apply i).aestronglyMeasurable
    (continuous_apply j).aestronglyMeasurable (by fun_prop)]
  simp only [gaussianRightExtension_apply]
  cases i <;> cases j <;> simp only [Sum.elim_inl,Sum.elim_inr,
    covariance_standard,covariance_const_left,covariance_const_right]

/-- Weight the two disjoint coordinate blocks of an actual standard
Gaussian vector by the two variance square roots. -/
def gaussianCoordinateSplit (t : ℝ) (x : E) : E :=
  Sum.elim (fun i => Real.sqrt t*x (.inl i))
    (fun j => Real.sqrt (1-t)*x (.inr j))

omit [DecidableEq α] [DecidableEq β] [CompleteSpace F] in
private theorem integral_split_laws (a b : ℝ) (f : E → F) (hf : Continuous f) :
    (∫ yz : E×E, f (a•yz.1+b•yz.2)
      ∂(leftLaw (α := α) (β := β)).prod (rightLaw (α := α) (β := β))) =
      ∫ x : E, f (Sum.elim (fun i => a*x (.inl i)) (fun j => b*x (.inr j)))
        ∂gaussianVector (α ⊕ β) := by
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rw [integral_map (by fun_prop) (by fun_prop)]
  let H : E → F := fun x =>
    f (Sum.elim (fun i => a*x (.inl i)) (fun j => b*x (.inr j)))
  have hH : Continuous H := by
    apply hf.comp
    apply continuous_pi
    intro k
    cases k <;> dsimp only [Sum.elim_inl,Sum.elim_inr] <;> fun_prop
  have hm := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : α ⊕ β => gaussianReal 0 1)
  have he := hm.hasLaw.integral_comp hH.aestronglyMeasurable
  convert he using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro yz
  change f _ = f _
  apply congrArg f
  ext k
  cases k <;> simp [gaussianLeftExtension_apply,gaussianRightExtension_apply,
    MeasurableEquiv.coe_sumPiEquivProdPi_symm,Equiv.sumPiEquivProdPi]

/-- The genuine expectation under one canonical product Gaussian law has
the exact covariance-difference derivative for its two variance-weighted
coordinate blocks. All law, mean, covariance, and independence properties
are derived from the native product law. Empty blocks are included.
Source: arXiv:2108.06312v2, Lemma 4.11, disjoint-coordinate specialization. -/
theorem hasDerivAt_integral_gaussianCoordinateSplit
    (f : E → F) (df : E → E →L[ℝ] F) (ddf : E → E →L[ℝ] E →L[ℝ] F)
    (hf : ∀ x, HasFDerivAt f (df x) x)
    (hdf : ∀ x, HasFDerivAt df (ddf x) x) (hddfc : Continuous ddf)
    (C₀ C₁ C₂ : ℝ) (hfb : ∀ x, ‖f x‖≤C₀)
    (hdfb : ∀ x, ‖df x‖≤C₁) (hddfb : ∀ x, ‖ddf x‖≤C₂)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    HasDerivAt
      (fun s : ℝ => ∫ x : E, f (gaussianCoordinateSplit s x) ∂gaussianVector (α ⊕ β))
      ((1/2 : ℝ) •
        ((∑ i : α, ∫ x : E, ddf (gaussianCoordinateSplit t x)
          (Pi.single (.inl i) 1) (Pi.single (.inl i) 1) ∂gaussianVector (α ⊕ β))-
         (∑ j : β, ∫ x : E, ddf (gaussianCoordinateSplit t x)
          (Pi.single (.inr j) 1) (Pi.single (.inr j) 1) ∂gaussianVector (α ⊕ β)))) t := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have h := hasDerivAt_integral_gaussian_sqrt_interpolation
    (leftLaw (α := α) (β := β)) (rightLaw (α := α) (β := β))
    integral_id_leftLaw integral_id_rightLaw
    f df ddf hf hdf hddfc C₀ C₁ C₂ hfb hdfb hddfb ht ht1
  have he (s : ℝ) := integral_split_laws (Real.sqrt s) (Real.sqrt (1-s)) f hfc
  change ∀ s : ℝ, (∫ yz : E×E, f (Real.sqrt s•yz.1+Real.sqrt (1-s)•yz.2)
    ∂(leftLaw (α := α) (β := β)).prod (rightLaw (α := α) (β := β))) =
      ∫ x : E, f (gaussianCoordinateSplit s x) ∂gaussianVector (α ⊕ β) at he
  simp_rw [he] at h
  apply h.congr_deriv
  congr 1
  simp_rw [covariance_leftLaw,covariance_rightLaw,Fintype.sum_sum_type]
  simp only [sub_zero,zero_sub,zero_smul,ite_smul,one_smul,neg_smul,
    Finset.sum_const_zero,add_zero,Finset.sum_neg_distrib,
    Finset.sum_ite_eq,Finset.mem_univ,if_true,← sub_eq_add_neg]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact (integral_split_laws (Real.sqrt t) (Real.sqrt (1-t))
      (fun y : E => ddf y (Pi.single (.inl i) 1) (Pi.single (.inl i) 1))
      (by fun_prop))
  · apply Finset.sum_congr rfl
    intro j _
    exact (integral_split_laws (Real.sqrt t) (Real.sqrt (1-t))
      (fun y : E => ddf y (Pi.single (.inr j) 1) (Pi.single (.inr j) 1))
      (by fun_prop))

end NLAlib
