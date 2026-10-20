import NLAlib.Matrix.Functions.KTransformUpperBounds
import NLAlib.Matrix.Functions.KTransformHalfPlaneUniqueness
import NLAlib.Matrix.Functions.KTransformInverseContraction
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Sequences

/-! # Genuine global upper-half-plane solutions of the nonlinear K equation

Native high-height Banach existence, coercive compactness, and the actual
complex inverse theorem make the scalar solvability set nonempty, open,
and closed in the connected upper half-plane.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set Filter Function Metric Bornology
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ
private abbrev KUpperParameter := {z : ℂ // 0<z.im}
local notation "H" => KUpperParameter

omit [Nonempty n] in
private theorem upperExistence_imaginaryPart_scalar (z : ℂ) :
    (imaginaryPart (z•(1 : M)) : M)=z.im•1 := by
  have hI : IsSelfAdjoint (1 : M) := IsSelfAdjoint.one _
  simp [imaginaryPart_smul,hI.imaginaryPart,realPart_one]

omit [Nonempty n] in
private theorem upperExistence_norm_scalar (z : ℂ) : specNorm (z•(1 : M))≤‖z‖ := by
  have hI : ‖(1 : M)‖≤1 := by simpa only [specNorm_eq_norm] using specNorm_one_le (n := n) (𝕜 := ℂ)
  simpa only [specNorm_eq_norm,norm_smul,mul_one] using
    mul_le_mul_of_nonneg_left hI (norm_nonneg z)

private def upperKSolvableSet (ν : Measure (selfAdjoint M)) (α : ℝ) : Set H :=
  {z | ∃ S : M, (imaginaryPart S : M).PosDef ∧ matrixKTransform ν α S=z.val•1}

private theorem upperExistence_eventually_posDef
    {Y : Type*} [TopologicalSpace Y] {f : Y → M} {x : Y}
    (hf : ContinuousAt f x) (hfx : (f x).PosDef)
    (hH : ∀ y, (f y).IsHermitian) : ∀ᶠ y in 𝓝 x, (f y).PosDef := by
  obtain ⟨δ,hδ,hδf⟩ : ∃ δ : ℝ, 0<δ ∧ δ•(1 : M)≤f x := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CFC.exists_pos_algebraMap_le_iff hfx.isHermitian.isSelfAdjoint).mpr
        (fun r hr => hfx.isStrictlyPositive.spectrum_pos hr)
  have hs : ∀ᶠ y in 𝓝 x, ‖f y-f x‖<δ :=
    ((hf.sub_const (f x)).norm).eventually_lt continuousAt_const (by simpa using hδ)
  filter_upwards [hs] with y hy
  have hneg : (-‖f y-f x‖)•(1 : M)≤f y-f x := by
    simpa only [Algebra.algebraMap_eq_smul_one,neg_smul] using
      ((hH y).sub hfx.isHermitian).isSelfAdjoint.neg_algebraMap_norm_le_self
  have hle : (δ-‖f y-f x‖)•(1 : M)≤f y := by
    convert! add_le_add hδf hneg using 1 <;> module
  exact ((Matrix.PosDef.one.smul (sub_pos.mpr hy)).isStrictlyPositive.of_le hle).posDef

private theorem upperExistence_solvable_isOpen
    (ν : Measure (selfAdjoint M)) [IsFiniteMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) : IsOpen (upperKSolvableSet ν α) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨S,hS,hK⟩
  have hKpos : (imaginaryPart (matrixKTransform ν α S) : M).PosDef := by
    rw [hK,upperExistence_imaginaryPart_scalar]
    exact Matrix.PosDef.one.smul z.property
  obtain ⟨G,hGa,hG0,hGeq⟩ :=
    exists_analytic_matrixKTransform_inverse_branch_of_upperHalfPlane ν hν α hα S hS hKpos z.val hK
  let L : M →L[ℝ] M :=
    (((selfAdjoint.submodule ℝ M).subtype).comp imaginaryPart).toContinuousLinearMap
  have hGpos : ∀ᶠ w in 𝓝 z.val, (imaginaryPart (G w) : M).PosDef :=
    upperExistence_eventually_posDef (L.continuous.continuousAt.comp hGa.continuousAt)
      (by rwa [hG0])
      (fun w => (imaginaryPart (G w)).property)
  have hcoe : Tendsto (fun w : H => w.val) (𝓝 z) (𝓝 z.val) := continuous_subtype_val.tendsto z
  filter_upwards [hcoe.eventually hGpos,hcoe.eventually hGeq] with w hwpos hweq
  exact ⟨G w.val,hwpos,hweq.2⟩

omit [Nonempty n] in
private theorem upperExistence_solvable_isClosed
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (R : ℝ)
    (hbound : ∀ T ∈ ν.support, specNorm T.val≤R) :
    IsClosed (upperKSolvableSet ν α) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u z hu huz
  have hSol (j : ℕ) : ∃ S : M, (imaginaryPart S : M).PosDef ∧
      matrixKTransform ν α S=(u j).val•1 := hu j
  choose S hS hKS using hSol
  let Xseq : ℕ → M := fun j => -(S j)⁻¹
  let η : ℝ := α*z.val.im/2
  have hη : 0<η := div_pos (mul_pos hα z.property) (by norm_num)
  have hzseq : Tendsto (fun j => (u j).val) atTop (𝓝 z.val) :=
    (continuous_subtype_val.tendsto z).comp huz
  have hlimIm : Tendsto (fun j => α*(u j).val.im) atTop (𝓝 (α*z.val.im)) :=
    tendsto_const_nhds.mul (Complex.continuous_im.tendsto z.val |>.comp hzseq)
  have hηlt : η<α*z.val.im := by
    dsimp only [η]
    linarith [mul_pos hα z.property]
  have hηevent : ∀ᶠ j in atTop, η≤α*(u j).val.im :=
    (hlimIm.eventually (Ioi_mem_nhds hηlt)).mono fun _ h => h.le
  have hnormevent : ∀ᶠ j in atTop, ‖(u j).val‖≤‖z.val‖+1 :=
    (hzseq.norm.eventually (Iio_mem_nhds (by linarith : ‖z.val‖<‖z.val‖+1))).mono fun _ h => h.le
  have htarget (j : ℕ) (hj : η≤α*(u j).val.im) :
      η•(1 : M)≤α•(imaginaryPart ((u j).val•(1 : M)) : M) := by
    rw [upperExistence_imaginaryPart_scalar,smul_smul]
    exact smul_le_smul_of_nonneg_right hj (show (0 : M)≤1 from zero_le_one)
  have hcoercive : ∀ᶠ j in atTop, η•(1 : M)≤(imaginaryPart (Xseq j) : M) := by
    filter_upwards [hηevent] with j hj
    exact (htarget j hj).trans
      (matrixKTransform_solution_inverse_variable ν hν α hα ((u j).val•1) (S j) (hS j) (hKS j)).2
  let C : ℝ := α*(‖z.val‖+1+R+R^2*η⁻¹)
  have hbounded : ∀ᶠ j in atTop, ‖Xseq j‖≤C := by
    filter_upwards [hηevent,hnormevent] with j hjη hjn
    have hb := specNorm_inverse_of_matrixKTransform_solution_le ν hν α hα
      ((u j).val•1) (S j) (hS j) (hKS j) η R hη hbound (htarget j hjη)
    change ‖-(S j)⁻¹‖≤C
    rw [norm_neg]
    calc
      _ = specNorm (S j)⁻¹ := (specNorm_eq_norm _).symm
      _ ≤ α*(specNorm ((u j).val•(1 : M))+R+R^2*η⁻¹) := hb
      _ ≤ C := by dsimp only [C]; gcongr; exact (upperExistence_norm_scalar _).trans hjn
  have hfreq : ∃ᶠ j in atTop, Xseq j∈closedBall (0 : M) C :=
    (hbounded.mono fun j hj => by simpa only [mem_closedBall,dist_zero_right] using hj).frequently
  obtain ⟨X,_hXC,φ,hφ,hXlim⟩ :=
    (isCompact_closedBall (0 : M) C).isSeqCompact.subseq_of_frequently_in hfreq
  let L : M →L[ℝ] M :=
    (((selfAdjoint.submodule ℝ M).subtype).comp imaginaryPart).toContinuousLinearMap
  have hclosed : IsClosed {Y : M | η•(1 : M)≤(imaginaryPart Y : M)} :=
    isClosed_Ici.preimage L.continuous
  have hXcoercive : η•(1 : M)≤(imaginaryPart X : M) :=
    hclosed.mem_of_tendsto hXlim (hφ.tendsto_atTop.eventually hcoercive)
  have hXpos : (imaginaryPart X : M).PosDef :=
    ((Matrix.PosDef.one.smul hη).isStrictlyPositive.of_le hXcoercive).posDef
  have hSXpos := posDef_imaginaryPart_neg_matrixInverse X hXpos
  have hSinvlim : Tendsto (fun j => -((Xseq ∘ φ) j)⁻¹) atTop (𝓝 (-X⁻¹)) :=
    ((hasFDerivAt_matrixInverse X (Matrix.isUnit_of_posDef_imaginaryPart hXpos)).continuousAt.neg.tendsto).comp hXlim
  have hKlim := ((hasFDerivAt_matrixKTransform_complex ν hν α
    (mem_matrixKTransformDomain_of_posDef_imaginaryPart ν hSXpos)).continuousAt.tendsto).comp hSinvlim
  have hKXseq (j : ℕ) : matrixKTransform ν α (-(Xseq j)⁻¹)=(u j).val•1 := by
    have hXjpos : (imaginaryPart (Xseq j) : M).PosDef := posDef_imaginaryPart_neg_matrixInverse (S j) (hS j)
    exact (matrixKTransform_neg_inverse_eq_iff_fixedPoint ν hν α hα.ne' ((u j).val•1)
      (Xseq j) hXjpos).mpr
        (matrixKTransform_solution_inverse_variable ν hν α hα ((u j).val•1) (S j) (hS j) (hKS j)).1
  have hKlim' : Tendsto (fun j => (u (φ j)).val•(1 : M)) atTop
      (𝓝 (matrixKTransform ν α (-X⁻¹))) := by
    simpa only [Function.comp_def,hKXseq] using hKlim
  have hZlim : Tendsto (fun j => (u (φ j)).val•(1 : M)) atTop (𝓝 (z.val•(1 : M))) :=
    (hzseq.comp hφ.tendsto_atTop).smul_const 1
  exact ⟨-X⁻¹,hSXpos,tendsto_nhds_unique hKlim' hZlim⟩

omit [Nonempty n] in
private theorem upperExistence_solvable_nonempty
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (R : ℝ)
    (hbound : ∀ T ∈ ν.support, specNorm T.val≤R) :
    (upperKSolvableSet ν α).Nonempty := by
  let η : ℝ := α*R^2+1
  have hη : 0<η := by dsimp only [η]; positivity
  have hsmall : α*R^2*(η⁻¹)^2<1 := by
    have hs : α*R^2<η^2 := by dsimp only [η]; nlinarith [sq_nonneg (α*R^2)]
    calc
      _ = (α*R^2)/(η^2) := by rw [inv_pow,div_eq_mul_inv]
      _ < 1 := (div_lt_one (sq_pos_of_pos hη)).mpr hs
  let z : ℂ := ((η/α : ℝ) : ℂ)*Complex.I
  have hz : 0<z.im := by simp only [z,Complex.mul_im,Complex.ofReal_re,Complex.I_im,
    Complex.ofReal_im,Complex.I_re,mul_one,mul_zero,add_zero]; exact div_pos hη hα
  have htarget : η•(1 : M)≤α•(imaginaryPart (z•(1 : M)) : M) := by
    rw [upperExistence_imaginaryPart_scalar,smul_smul]
    have he : α*z.im=η := by
      simp only [z,Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.ofReal_im,
        Complex.I_re,mul_one,mul_zero,add_zero]
      field_simp [hα.ne']
    rw [he]
  obtain ⟨S,hS,hKS,_⟩ := exists_matrixKTransform_solution_of_imaginary_coercive_contraction
    ν hν α hα (z•1) η R hη hbound htarget hsmall
  exact ⟨⟨z,hz⟩,S,hS,hKS⟩

/-- Every scalar upper-half-plane parameter has a genuine solution of
the original nonlinear matrix K equation. Actual high-height Banach
existence and coercive compact continuation establish existence over the
whole connected upper half-plane. No distinguished branch, Stieltjes law
or global existence conclusion is assumed.
Source: Montanari--Saeed (2026), Lemma 1, existence part; Appendix A.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_matrixKTransform_solution_upperHalfPlane
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (z : ℂ) (hz : 0<z.im) :
    ∃ S : M, (imaginaryPart S : M).PosDef ∧ matrixKTransform ν α S=z•1 := by
  obtain ⟨R,hR⟩ := hν.isBounded.exists_norm_le
  have hbound : ∀ T ∈ ν.support, specNorm T.val≤R := by
    intro T hT
    simpa only [specNorm_eq_norm,← AddSubgroup.norm_coe] using hR T hT
  let : PreconnectedSpace H := Subtype.preconnectedSpace (convex_halfSpace_im_gt 0).isPreconnected
  have he : upperKSolvableSet ν α=univ :=
    (show IsClopen (upperKSolvableSet ν α) from
      ⟨upperExistence_solvable_isClosed ν hν α hα R hbound,
        upperExistence_solvable_isOpen ν hν α hα⟩).eq_univ
          (upperExistence_solvable_nonempty ν hν α hα R hbound)
  have hm : (⟨z,hz⟩ : H)∈upperKSolvableSet ν α := by rw [he]; trivial
  exact hm

/-- The original nonlinear K equation has exactly one genuine solution
in the matrix upper half-plane for every scalar parameter in the upper
half-plane. Existence and uniqueness are both proved for the actual
compact sample law, without an analytic-branch or law assumption.
Source: Montanari--Saeed (2026), Lemma 1; Appendix A.
atlas: block-wishart-variational-edges (partial) -/
theorem existsUnique_matrixKTransform_solution_upperHalfPlane
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) (z : ℂ) (hz : 0<z.im) :
    ∃! S : M, (imaginaryPart S : M).PosDef ∧ matrixKTransform ν α S=z•1 := by
  obtain ⟨S,hS,hK⟩ := exists_matrixKTransform_solution_upperHalfPlane ν hν α hα z hz
  refine ⟨S,⟨hS,hK⟩,?_⟩
  rintro Q ⟨hQ,hKQ⟩
  have hZ : (imaginaryPart (z•(1 : M)) : M).PosDef := by
    rw [upperExistence_imaginaryPart_scalar]
    exact Matrix.PosDef.one.smul hz
  exact matrixKTransform_solution_unique_upperHalfPlane ν hν α hα (z•1) Q S hZ hQ hS hKQ hK

/-- The genuine nonlinear K solutions form an actual analytic branch
over the whole scalar upper half-plane, with the native reciprocal
imaginary norm bound. Local analytic inverses glue because their actual
upper-half-plane solutions agree by the proved uniqueness theorem.
Source: Montanari--Saeed (2026), Lemma 1; Appendix A.
atlas: block-wishart-variational-edges (partial) -/
theorem exists_analytic_matrixKTransform_upperHalfPlane_solution
    (ν : Measure (selfAdjoint M)) [IsProbabilityMeasure ν] (hν : IsCompact ν.support)
    (α : ℝ) (hα : 0<α) :
    ∃ F : ℂ → M, AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} ∧
      ∀ z : ℂ, 0<z.im → (imaginaryPart (F z) : M).PosDef ∧
        matrixKTransform ν α (F z)=z•1 ∧ specNorm (F z)≤(α*z.im)⁻¹ := by
  let F : ℂ → M := fun z => if hz : 0<z.im then
    Classical.choose (exists_matrixKTransform_solution_upperHalfPlane ν hν α hα z hz) else 0
  have hF (z : ℂ) (hz : 0<z.im) :
      (imaginaryPart (F z) : M).PosDef ∧ matrixKTransform ν α (F z)=z•1 := by
    dsimp only [F]
    rw [dif_pos hz]
    exact Classical.choose_spec (exists_matrixKTransform_solution_upperHalfPlane ν hν α hα z hz)
  have hHopen : IsOpen {z : ℂ | 0<z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hFa : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} := by
    intro z hz
    have hZpos : (imaginaryPart (z•(1 : M)) : M).PosDef := by
      rw [upperExistence_imaginaryPart_scalar]
      exact Matrix.PosDef.one.smul hz
    have hKpos : (imaginaryPart (matrixKTransform ν α (F z)) : M).PosDef := by
      rw [(hF z hz).2]
      exact hZpos
    obtain ⟨G,hGa,hG0,hGeq⟩ :=
      exists_analytic_matrixKTransform_inverse_branch_of_upperHalfPlane ν hν α hα
        (F z) (hF z hz).1 hKpos z (hF z hz).2
    let L : M →L[ℝ] M :=
      (((selfAdjoint.submodule ℝ M).subtype).comp imaginaryPart).toContinuousLinearMap
    have hGpos : ∀ᶠ w in 𝓝 z, (imaginaryPart (G w) : M).PosDef :=
      upperExistence_eventually_posDef (L.continuous.continuousAt.comp hGa.continuousAt)
        (by rw [hG0]; exact (hF z hz).1) (fun w => (imaginaryPart (G w)).property)
    apply hGa.congr
    filter_upwards [hGpos,hGeq,hHopen.mem_nhds hz] with w hwpos hweq hwH
    have hW : (imaginaryPart (w•(1 : M)) : M).PosDef := by
      rw [upperExistence_imaginaryPart_scalar]
      exact Matrix.PosDef.one.smul hwH
    exact matrixKTransform_solution_unique_upperHalfPlane ν hν α hα (w•1) (G w) (F w)
      hW hwpos (hF w hwH).1 hweq.2 (hF w hwH).2
  refine ⟨F,hFa,fun z hz => ⟨(hF z hz).1,(hF z hz).2,?_⟩⟩
  have hη : 0<α*z.im := mul_pos hα hz
  have hZ : (α*z.im)•(1 : M)≤α•(imaginaryPart (z•(1 : M)) : M) := by
    rw [upperExistence_imaginaryPart_scalar,smul_smul]
  exact specNorm_of_matrixKTransform_solution_le_inv ν hν α hα (z•1) (F z)
    (hF z hz).1 (hF z hz).2 (α*z.im) hη hZ

end NLAlib
