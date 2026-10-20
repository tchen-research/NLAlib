import NLAlib.Matrix.Basic.NormalizedTrace
import NLAlib.Matrix.Functions.ResolventDerivatives
import NLAlib.ForMathlib.Algebra.Resolvent
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Cyclic first derivatives of genuine mixed resolvent powers

Trace cyclicity collapses all insertions in each power into one term. This
keeps the two positive inverse arcs explicit for the Gaussian covariance
crossing argument, without classifying twice-inserted list positions.
Source: arXiv:2108.06312v2, Lemmas 6.2--6.3.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "M" => Matrix d d ℂ

private theorem trace_sandwich_power_rotate
    (R S H : M) (hRS : Commute R S) (u v b : ℕ) :
    (R^u*(R*H*R)*R^v*S^b).trace=(H*R^(u+v+2)*S^b).trace := by
  calc
    _ = (R^(u+1)*(H*R^(v+1)*S^b)).trace := by
      congr 1
      rw [pow_succ R u,pow_succ' R v]
      noncomm_ring
    _ = ((H*R^(v+1)*S^b)*R^(u+1)).trace := Matrix.trace_mul_comm _ _
    _ = (H*R^(v+1)*(R^(u+1)*S^b)).trace := by
      congr 1
      simp only [Matrix.mul_assoc]
      rw [(hRS.symm.pow_pow b (u+1)).eq]
    _ = (H*R^((v+1)+(u+1))*S^b).trace := by
      congr 1
      simp only [pow_add,Matrix.mul_assoc]
    _ = _ := by rw [show (v+1)+(u+1)=u+v+2 by omega]

private theorem trace_left_power_sandwich_rotate
    (R S H : M) (hRS : Commute R S) (a u v : ℕ) :
    (R^a*(S^u*(S*H*S)*S^v)).trace=(H*R^a*S^(u+v+2)).trace := by
  rw [Matrix.trace_mul_comm,trace_sandwich_power_rotate S R H hRS.symm]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [(hRS.symm.pow_pow (u+v+2) a).eq]

open scoped Matrix.Norms.L2Operator in
/-- Actual two matrix curves with sandwich derivatives and commuting values
have the cyclic mixed-power trace derivative. The derivative matrices need
not commute with the values; no invertibility is part of this purely
calculus-and-trace identity. -/
theorem hasDerivAt_trace_mixed_powers_of_sandwich
    {R S : ℝ → M} {t : ℝ} (H : M)
    (hR : HasDerivAt R (R t*H*R t) t)
    (hS : HasDerivAt S (S t*H*S t) t)
    (hRS : Commute (R t) (S t)) (a b : ℕ) :
    HasDerivAt (fun u : ℝ => (R u^a*S u^b).trace)
      ((a : ℝ) • (H*R t^(a+1)*S t^b).trace+
       (b : ℝ) • (H*R t^a*S t^(b+1)).trace) t := by
  let T : M →L[ℝ] ℂ := (Matrix.traceLinearMap d ℝ ℂ).toContinuousLinearMap
  have ht := T.hasFDerivAt.comp_hasDerivAt t ((hR.fun_pow' a).mul (hS.fun_pow' b))
  have ha : ((∑ i ∈ Finset.range a, R t^(a.pred-i)*(R t*H*R t)*R t^i)*S t^b).trace=
      (a : ℝ) • (H*R t^(a+1)*S t^b).trace := by
    rw [Finset.sum_mul,Matrix.trace_sum]
    have hh (i : ℕ) (hi : i∈Finset.range a) :
        (R t^(a.pred-i)*(R t*H*R t)*R t^i*S t^b).trace=
          (H*R t^(a+1)*S t^b).trace := by
      rw [trace_sandwich_power_rotate _ _ _ hRS]
      rw [show a.pred-i+i+2=a+1 by simp only [Finset.mem_range] at hi; simp only [Nat.pred_eq_sub_one]; omega]
    simp_rw [Finset.sum_congr rfl hh]
    simp [nsmul_eq_mul,Complex.real_smul]
  have hb : (R t^a*(∑ i ∈ Finset.range b, S t^(b.pred-i)*(S t*H*S t)*S t^i)).trace=
      (b : ℝ) • (H*R t^a*S t^(b+1)).trace := by
    rw [Finset.mul_sum,Matrix.trace_sum]
    have hh (i : ℕ) (hi : i∈Finset.range b) :
        (R t^a*(S t^(b.pred-i)*(S t*H*S t)*S t^i)).trace=
          (H*R t^a*S t^(b+1)).trace := by
      rw [trace_left_power_sandwich_rotate _ _ _ hRS]
      rw [show b.pred-i+i+2=b+1 by simp only [Finset.mem_range] at hi; simp only [Nat.pred_eq_sub_one]; omega]
    simp_rw [Finset.sum_congr rfl hh]
    simp [nsmul_eq_mul,Complex.real_smul]
  simpa only [T,Function.comp_def,LinearMap.coe_toContinuousLinearMap',
    Matrix.traceLinearMap_apply,Matrix.trace_add,Pi.mul_apply,Pi.pow_apply,ha,hb] using ht


open scoped Matrix.Norms.L2Operator in
/-- Along an actual differentiable Hermitian-base matrix curve, the first
normalized mixed-resolvent trace derivative has its two exact cyclic terms.
Only the base point is required to be Hermitian, since the nonreal inverse
is differentiable on its genuine open unit neighborhood.
Source: arXiv:2108.06312v2, Lemma 6.2;
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem hasDerivAt_normalizedTrace_mixed_resolvent_curve
    {X : ℝ → M} {H : M} {t : ℝ} (hX : HasDerivAt X H t)
    (hXt : (X t).IsHermitian) (ζ ω : ℂ) (hζ : ζ.im≠0) (hω : ω.im≠0)
    (a b : ℕ) :
    HasDerivAt (fun u : ℝ => normalizedTrace (resolvent (X u) ζ^a*resolvent (X u) ω^b))
      ((a : ℝ) • normalizedTrace (H*resolvent (X t) ζ^(a+1)*resolvent (X t) ω^b)+
       (b : ℝ) • normalizedTrace (H*resolvent (X t) ζ^a*resolvent (X t) ω^(b+1))) t := by
  have hR : HasDerivAt (fun u : ℝ => resolvent (X u) ζ)
      (resolvent (X t) ζ*H*resolvent (X t) ζ) t := by
    simpa only [Function.comp_def,rationalBlockMap_apply,rationalBlockDifference_resolvent,
      ContinuousLinearMap.coe_restrictScalars'] using
      (((hasFDerivAt_resolvent_of_isHermitian ζ (X t) hXt hζ).restrictScalars ℝ).comp_hasDerivAt t hX)
  have hS : HasDerivAt (fun u : ℝ => resolvent (X u) ω)
      (resolvent (X t) ω*H*resolvent (X t) ω) t := by
    simpa only [Function.comp_def,rationalBlockMap_apply,rationalBlockDifference_resolvent,
      ContinuousLinearMap.coe_restrictScalars'] using
      (((hasFDerivAt_resolvent_of_isHermitian ω (X t) hXt hω).restrictScalars ℝ).comp_hasDerivAt t hX)
  have ht := hasDerivAt_trace_mixed_powers_of_sandwich H hR hS
    (commute_resolvent (X t) ζ ω) a b
  simpa only [normalizedTrace,mul_add,mul_smul_comm] using
    ht.const_mul (Fintype.card d : ℂ)⁻¹


open scoped Matrix.Norms.L2Operator in
/-- The actual mixed matrix-power derivative consists of its two positive
inverse-arc insertion sums. The inserted direction is not assumed to commute
with either curve, and commutation between the curves is unnecessary. -/
theorem hasDerivAt_mixed_powers_of_sandwich
    {R S : ℝ → M} {t : ℝ} (H : M)
    (hR : HasDerivAt R (R t*H*R t) t)
    (hS : HasDerivAt S (S t*H*S t) t) (a b : ℕ) :
    HasDerivAt (fun u : ℝ => R u^a*S u^b)
      ((∑ i ∈ Finset.range a, R t^(a-i)*H*R t^(i+1)*S t^b)+
       ∑ j ∈ Finset.range b, R t^a*S t^(b-j)*H*S t^(j+1)) t := by
  have ht := (hR.fun_pow' a).mul (hS.fun_pow' b)
  apply ht.congr_deriv
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply congrArg₂ (fun U V : M => U+V)
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i<a := Finset.mem_range.mp hi
    rw [show a-i=(a.pred-i)+1 by simp only [Nat.pred_eq_sub_one]; omega,
      pow_succ (R t) (a.pred-i),pow_succ' (R t) i]
    noncomm_ring
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' : j<b := Finset.mem_range.mp hj
    rw [show b-j=(b.pred-j)+1 by simp only [Nat.pred_eq_sub_one]; omega,
      pow_succ (S t) (b.pred-j),pow_succ' (S t) j]
    noncomm_ring

end NLAlib
