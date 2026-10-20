import NLAlib.Matrix.Functions.KTransformComplexCalculus
import NLAlib.ForMathlib.MeasureTheory.MatrixIntegral
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Native adjoint symmetry of the nonlinear K transform

The actual simultaneous inverse domain and the actual rational integral
commute with conjugate transpose for Hermitian samples.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

private theorem adjoint_unit_reverse_denominator (S T : M) (h : IsUnit (1+S*T)) :
    IsUnit (1+T*S) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_one_add_mul_comm]
  exact (Matrix.isUnit_iff_isUnit_det _).mp h

private theorem adjoint_kernel_pushThrough (S T : M)
    (hL : IsUnit (1+S*T)) (hR : IsUnit (1+T*S)) :
    matrixKResolvent S T=(1+T*S)⁻¹*T := by
  have ht : (1+T*S)*T=T*(1+S*T) := by noncomm_ring
  have hmul : (1+T*S)*matrixKResolvent S T=T := by
    unfold matrixKResolvent
    rw [← Matrix.mul_assoc,ht,Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hL),Matrix.mul_one]
  calc
    _ = ((1+T*S)⁻¹*(1+T*S))*matrixKResolvent S T := by
      rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hR),Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc,hmul]

private theorem adjoint_kernel (S T : M) (hT : T.IsHermitian)
    (hL : IsUnit (1+S*T)) : matrixKResolvent Sᴴ T=(matrixKResolvent S T)ᴴ := by
  have hR := adjoint_unit_reverse_denominator S T hL
  have hLa : IsUnit (1+Sᴴ*T) := by
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_add,
      Matrix.conjTranspose_one,Matrix.conjTranspose_mul,hT.eq] using hR.star
  have hRa : IsUnit (1+T*Sᴴ) := by
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_add,
      Matrix.conjTranspose_one,Matrix.conjTranspose_mul,hT.eq] using hL.star
  rw [adjoint_kernel_pushThrough Sᴴ T hLa hRa]
  simp only [matrixKResolvent,Matrix.conjTranspose_mul,Matrix.conjTranspose_nonsing_inv,
    Matrix.conjTranspose_add,Matrix.conjTranspose_one,hT.eq]

/-- The true simultaneous inverse domain of the K transform is invariant
under adjoint for a Hermitian sample law. -/
theorem mem_matrixKTransformDomain_conjTranspose
    (ν : Measure (selfAdjoint M)) (S : M) (hS : S∈matrixKTransformDomain ν) :
    Sᴴ∈matrixKTransformDomain ν := by
  constructor
  · simpa only [Matrix.star_eq_conjTranspose] using hS.1.star
  · intro T hT
    have h := (adjoint_unit_reverse_denominator S T.val (hS.2 T hT)).star
    have hherm : T.val.IsHermitian := T.property
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_add,
      Matrix.conjTranspose_one,Matrix.conjTranspose_mul,hherm.eq] using h

/-- The actual rational K transform commutes with conjugate transpose
through its native total matrix integral. No real-branch or reflection
identity is assumed.
Source: Montanari--Saeed (2026), real stable continuation in Theorem 3.
atlas: block-wishart-variational-edges (partial) -/
theorem matrixKTransform_conjTranspose
    (ν : Measure (selfAdjoint M)) (α : ℝ) (S : M) (hS : S∈matrixKTransformDomain ν) :
    matrixKTransform ν α Sᴴ=(matrixKTransform ν α S)ᴴ := by
  have hI : (∫ T : selfAdjoint M,matrixKResolvent Sᴴ T.val ∂ν)=
      (∫ T : selfAdjoint M,matrixKResolvent S T.val ∂ν)ᴴ := by
    rw [← Matrix.integral_conjTranspose]
    apply integral_congr_ae
    filter_upwards [ν.support_mem_ae] with T hT
    exact adjoint_kernel S T.val T.property (hS.2 T hT)
  simp only [matrixKTransform,hI,Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul,Matrix.conjTranspose_nonsing_inv,star_trivial]

end NLAlib
