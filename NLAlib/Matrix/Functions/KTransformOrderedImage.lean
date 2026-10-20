import NLAlib.Matrix.Functions.KTransformOrderedBounds
import NLAlib.Matrix.Functions.KTransformComplexCalculus
import Mathlib.Topology.MetricSpace.Sequences

/-! # Closed images of the native inverse K map on lower order cones

True compact-support resolvent estimates make the native map proper on
an actual positive lower cone. Its image is therefore closed, even at
limits where no stability certificate was assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter Metric
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- The actual inverse K transform has closed image on a positive lower
order cone with native sample gaps. This is the compactness step of
real continuation, proved using the genuine equation and its derived
properness estimate; stability is not a limiting hypothesis.
Source: Montanari--Saeed (2026), real stable-domain continuation.
atlas: block-wishart-variational-edges (partial) -/
theorem isClosed_image_ordered_matrixKTransform_inverse
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (Y : M) (hY : Y.PosDef)
    (hgapY : ∀ T ∈ ν.support, (Y+T.val).PosDef) :
    IsClosed ((fun Z : M => matrixKTransform ν α Z⁻¹) '' Ici Y) := by
  obtain ⟨C,hC,hbound⟩ := exists_norm_bound_ordered_matrixKTransform_inverse ν hν α hα Y hY hgapY
  apply isSeqClosed_iff_isClosed.mp
  intro u U hu huU
  have hsol (j : ℕ) : ∃ Z : M, Y≤Z ∧ matrixKTransform ν α Z⁻¹=u j := hu j
  choose Z hYZ hKZ using hsol
  have htarget : ∀ᶠ j in atTop, ‖u j‖≤‖U‖+1 :=
    (huU.norm.eventually (Iio_mem_nhds (by linarith : ‖U‖<‖U‖+1))).mono fun _ h => h.le
  have hbounded : ∀ᶠ j in atTop, ‖Z j‖≤α*(‖U‖+1+C) := by
    filter_upwards [htarget] with j hj
    exact (hbound (Z j) (hYZ j)).trans (by rw [hKZ]; gcongr)
  have hfreq : ∃ᶠ j in atTop, Z j∈closedBall (0 : M) (α*(‖U‖+1+C)) :=
    (hbounded.mono fun j hj => by simpa only [mem_closedBall,dist_zero_right] using hj).frequently
  obtain ⟨Z0,_hball,φ,hφ,hZlim⟩ :=
    (isCompact_closedBall (0 : M) (α*(‖U‖+1+C))).isSeqCompact.subseq_of_frequently_in hfreq
  have hYZ0 : Y≤Z0 := isClosed_Ici.mem_of_tendsto hZlim
    (Eventually.of_forall fun j => hYZ (φ j))
  have hZ0 : Z0.PosDef := (hY.isStrictlyPositive.of_le hYZ0).posDef
  have hgapZ0 : ∀ T ∈ ν.support, (Z0+T.val).PosDef := by
    intro T hT
    have hle : Y+T.val≤Z0+T.val := by
      simpa only [add_comm] using add_le_add_right hYZ0 T.val
    exact ((hgapY T hT).isStrictlyPositive.of_le hle).posDef
  have hZZ : Z0⁻¹⁻¹=Z0 := Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hZ0.isUnit)
  have hdom : Z0⁻¹∈matrixKTransformDomain ν := by
    refine ⟨hZ0.inv.isUnit,fun T hT => isUnit_matrixKDenominator Z0⁻¹ T.val hZ0.inv ?_⟩
    simpa only [hZZ] using hgapZ0 T hT
  have hInvlim := (hasFDerivAt_matrixInverse Z0 hZ0.isUnit).continuousAt.tendsto.comp hZlim
  have hKlim := (hasFDerivAt_matrixKTransform_complex ν hν α hdom).continuousAt.tendsto.comp hInvlim
  have hKlim' : Tendsto (fun j => u (φ j)) atTop (𝓝 (matrixKTransform ν α Z0⁻¹)) := by
    simpa only [Function.comp_def,hKZ] using hKlim
  have hU : matrixKTransform ν α Z0⁻¹=U := tendsto_nhds_unique hKlim' (huU.comp hφ.tendsto_atTop)
  exact ⟨Z0,hYZ0,hU⟩

end NLAlib
