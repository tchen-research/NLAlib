import NLAlib.Matrix.Norms.Core
import NLAlib.ForMathlib.MeasureTheory.CompactSupportDifferentiation
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-! # Actual matrix K-transform Fréchet calculus -/
noncomputable section
open MeasureTheory Set Filter
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Hermitian matrices carry their canonical Borel sigma algebra. -/
instance selfAdjointMatrixMeasurableSpace : MeasurableSpace (selfAdjoint (Matrix n n ℂ)) := borel _

instance selfAdjointMatrixBorelSpace : BorelSpace (selfAdjoint (Matrix n n ℂ)) := ⟨rfl⟩

/-- The genuine matrix resolvent kernel, defined with the ordinary total
matrix inverse. Analytic hypotheses are needed only on the support. -/
def matrixKResolvent (S T : Matrix n n ℂ) : Matrix n n ℂ := T * (1 + S * T)⁻¹

/-- The real continuous linear derivative of a resolvent kernel. -/
def matrixKResolventDeriv (S T : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  -ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (matrixKResolvent S T) (matrixKResolvent S T)

/-- The actual matrix K-transform with a measure on Hermitian matrices. -/
def matrixKTransform (ν : Measure (selfAdjoint (Matrix n n ℂ))) (α : ℝ)
    (S : Matrix n n ℂ) : Matrix n n ℂ :=
  (∫ T, matrixKResolvent S T.val ∂ν) - α⁻¹ • S⁻¹

/-- The candidate derivative, as an actual Bochner integral of real CLMs. -/
def matrixKTransformDeriv (ν : Measure (selfAdjoint (Matrix n n ℂ))) (α : ℝ)
    (S : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  (∫ T, matrixKResolventDeriv S T.val ∂ν) +
    α⁻¹ • ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) S⁻¹ S⁻¹

/-- Ordinary nonsingular matrix inversion has the actual real Fréchet
inverse derivative. -/
theorem hasFDerivAt_matrixInverse (S : Matrix n n ℂ) (hS : IsUnit S) :
    HasFDerivAt (fun X : Matrix n n ℂ => X⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) S⁻¹ S⁻¹) S := by
  obtain ⟨u,hu⟩ := hS
  have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at h
  convert! h using 1
  · funext X
    exact Matrix.nonsing_inv_eq_ringInverse X
  · rw [← hu, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]

/-- The resolvent kernel's genuine Fréchet derivative requires only its
actual solved denominator to be invertible. -/
theorem hasFDerivAt_matrixKResolvent (S T : Matrix n n ℂ)
    (h : IsUnit (1 + S * T)) :
    HasFDerivAt (fun X => matrixKResolvent X T) (matrixKResolventDeriv S T) S := by
  have hlin := ((hasFDerivAt_id (𝕜 := ℝ) S).mul_const' T).const_add 1
  have hi := (hasFDerivAt_matrixInverse (1 + S * T) h).comp S hlin
  have hk := hi.const_mul T
  convert! hk using 1
  apply ContinuousLinearMap.ext
  intro X
  simp only [matrixKResolventDeriv, neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, matrixKResolvent, Matrix.mul_assoc, Matrix.mul_neg]


/-- Joint continuity of the kernel holds at every genuinely admissible pair. -/
theorem continuousAt_matrixKResolvent (S T : Matrix n n ℂ)
    (h : IsUnit (1 + S * T)) :
    ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ => matrixKResolvent p.1 p.2) (S,T) := by
  have hi := (hasFDerivAt_matrixInverse (1 + S * T) h).continuousAt
  have harg : ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ => 1 + p.1 * p.2) (S,T) := by fun_prop
  have hi' : ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ => (1 + p.1 * p.2)⁻¹) (S,T) := hi.comp (f := fun p : Matrix n n ℂ × Matrix n n ℂ => 1 + p.1 * p.2) harg
  have hmul : ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ => p.2 * (1 + p.1 * p.2)⁻¹) (S,T) :=
    continuous_snd.continuousAt.mul hi'
  simpa only [matrixKResolvent] using hmul


/-- The actual derivative kernel is jointly continuous wherever the solved
resolvent denominator is invertible. -/
theorem continuousAt_matrixKResolventDeriv (S T : Matrix n n ℂ)
    (h : IsUnit (1 + S * T)) :
    ContinuousAt (fun p : Matrix n n ℂ × Matrix n n ℂ => matrixKResolventDeriv p.1 p.2) (S,T) := by
  have hr := continuousAt_matrixKResolvent S T h
  have hleft := (ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ)).continuous.continuousAt.comp hr
  exact (hleft.clm_apply hr).neg

/-- Compact support and actual solved denominators give the genuine Fréchet
derivative under the integral. All inverse assumptions are on the support
only. Source: user derivations, equation (F20).
atlas: matrix-k-transform-stability (partial) -/
theorem hasFDerivAt_matrixKTransform (ν : Measure (selfAdjoint (Matrix n n ℂ)))
    [IsFiniteMeasure ν] (hν : IsCompact ν.support) (α : ℝ) (S : Matrix n n ℂ)
    (hS : IsUnit S) (hden : ∀ T ∈ ν.support, IsUnit (1 + S * T.val)) :
    HasFDerivAt (matrixKTransform ν α) (matrixKTransformDeriv ν α S) S := by
  let U : Set (Matrix n n ℂ × selfAdjoint (Matrix n n ℂ)) := {p | IsUnit (1 + p.1 * p.2.val)}
  have hproj : Continuous (fun p : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => (p.1,p.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hU : IsOpen U := Units.isOpen.preimage
    (continuous_const.add (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))
  have hF : ContinuousOn (fun p : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => matrixKResolvent p.1 p.2.val) U := by
    intro p hp
    have hc : ContinuousAt (fun q : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => matrixKResolvent q.1 q.2.val) p :=
      (continuousAt_matrixKResolvent p.1 p.2.val hp).comp (f := fun q : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => (q.1,q.2.val)) hproj.continuousAt
    exact hc.continuousWithinAt
  have hD : ContinuousOn (fun p : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => matrixKResolventDeriv p.1 p.2.val) U := by
    intro p hp
    have hc : ContinuousAt (fun q : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => matrixKResolventDeriv q.1 q.2.val) p :=
      (continuousAt_matrixKResolventDeriv p.1 p.2.val hp).comp (f := fun q : Matrix n n ℂ × selfAdjoint (Matrix n n ℂ) => (q.1,q.2.val)) hproj.continuousAt
    exact hc.continuousWithinAt
  have hI := hasFDerivAt_integral_of_compact_support ν hν
    (fun X T => matrixKResolvent X T.val) (fun X T => matrixKResolventDeriv X T.val)
    U hU hF hD (fun p hp => hasFDerivAt_matrixKResolvent p.1 p.2.val hp) S hden
  have hInv := (hasFDerivAt_matrixInverse S hS).const_smul α⁻¹
  convert! hI.sub hInv using 1
  simp only [matrixKTransformDeriv, smul_neg, sub_neg_eq_add]

end NLAlib
