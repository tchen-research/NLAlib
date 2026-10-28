import NLAlib.RandomMatrix.Haar.UnitaryFrameTransform
import NLAlib.Matrix.Subspaces.BlockUnitaryAction
import NLAlib.Matrix.Basic.PseudoinverseBlockGram
import NLAlib.Matrix.Measurability.GramPseudoinverse
import NLAlib.Probability.Moments.UnitaryIsotropy

/-!
# Native Haar least-squares block invariance and moments

The actual compact-Haar frame law supplies invariance of the pseudoinverse
bottom-block noise. Its Frobenius moment then follows from the inverse top-Gram
trace. The later consumer discharges those native inverse-moment premises.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix
namespace NLAlib
variable {K : Type*} [RCLike K] {n ell r q p : ℕ}

/-- The actual pseudoinverse bottom-block correction for one orthonormal sketch. -/
def haarBlockNoise (U : Matrix (Fin n) (Fin r) K) (V : Matrix (Fin n) (Fin q) K)
    (Ω : UnitaryStiefel K n ell) : Matrix (Fin r) (Fin q) K :=
  pinvL (Ω.valᴴ*U)*(Ω.valᴴ*V)

/-- The total native correction map is measurable, including rank failures. -/
@[fun_prop] theorem measurable_haarBlockNoise
    (U : Matrix (Fin n) (Fin r) K) (V : Matrix (Fin n) (Fin q) K) :
    Measurable (haarBlockNoise (ell := ell) U V) := by
  unfold haarBlockNoise
  exact (measurable_pinvL.comp
    (Matrix.measurable_conjTranspose.comp measurable_subtype_coe |>.matrix_mul measurable_const)).matrix_mul
      ((Matrix.measurable_conjTranspose.comp measurable_subtype_coe).matrix_mul measurable_const)

/-- The actual native Haar law of the pseudoinverse bottom-block noise. -/
def haarBlockNoiseLaw (helln : ell≤n) (U : Matrix (Fin n) (Fin r) K)
    (V : Matrix (Fin n) (Fin q) K) : Measure (Matrix (Fin r) (Fin q) K) :=
  (unitaryHaarFrameLaw K n ell helln).map (haarBlockNoise U V)

instance haarBlockNoiseLaw_isProbabilityMeasure (helln : ell≤n)
    (U : Matrix (Fin n) (Fin r) K) (V : Matrix (Fin n) (Fin q) K) :
    IsProbabilityMeasure (haarBlockNoiseLaw helln U V) :=
  Measure.isProbabilityMeasure_map (measurable_haarBlockNoise U V).aemeasurable

/-- Every complementary right-unitary action is realized by an actual ambient
unitary action on the Haar sketch. -/
theorem rightUnitaryInvariant_haarBlockNoiseLaw (helln : ell≤n)
    (U : Matrix (Fin n) (Fin r) K) (V : Matrix (Fin n) (Fin q) K)
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hUV : Uᴴ*V=0) (hcomp : U*Uᴴ+V*Vᴴ=1) :
    RightUnitaryInvariant (haarBlockNoiseLaw helln U V) := by
  intro W
  let T : Matrix.unitaryGroup (Fin n) K := ⟨blockUnitaryAction U V W,
    Matrix.mem_unitaryGroup_iff'.mpr (hasOrthonormalCols_blockUnitaryAction U V hU hV hUV hcomp W)⟩
  have hleft : T.valᴴ*U=U := blockUnitaryAction_conjTranspose_mul_left U V hU hUV W
  have hright : T.valᴴ*V=V*W.val := blockUnitaryAction_conjTranspose_mul_right U V hV hUV W
  have he (Ω : UnitaryStiefel K n ell) : haarBlockNoise U V (T • Ω)=haarBlockNoise U V Ω*W.val := by
    change pinvL ((T.val*Ω.val)ᴴ*U)*((T.val*Ω.val)ᴴ*V)=_
    rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,hleft,Matrix.mul_assoc,hright]
    simp only [haarBlockNoise,Matrix.mul_assoc]
  unfold haarBlockNoiseLaw
  rw [Measure.map_map (by fun_prop) (measurable_haarBlockNoise U V)]
  have hf : (fun Z : Matrix (Fin r) (Fin q) K => Z*W.val) ∘ haarBlockNoise U V =
      haarBlockNoise U V ∘ (fun Ω : UnitaryStiefel K n ell => T • Ω) := by
    funext Ω
    exact (he Ω).symm
  rw [hf,← Measure.map_map (measurable_haarBlockNoise U V) (by fun_prop),
    unitaryHaarFrameLaw_map_smul K helln T]

/-- The native top-Gram trace controls the genuine block-noise Frobenius moment.
The rank and inverse-trace premises refer to the actual Haar law. -/
theorem integrable_and_integral_frobSq_haarBlockNoise
    (helln : ell≤n) (U : Matrix (Fin n) (Fin r) K) (V : Matrix (Fin n) (Fin q) K)
    (hcomp : U*Uᴴ+V*Vᴴ=1)
    (hfull : ∀ᵐ Ω ∂unitaryHaarFrameLaw K n ell helln,IsUnit (unitaryFrameTopGram K U Ω))
    (htrace : Integrable (fun Ω => RCLike.re ((unitaryFrameTopGram K U Ω)⁻¹).trace)
      (unitaryHaarFrameLaw K n ell helln)) :
    Integrable (fun Ω => frobSq (haarBlockNoise U V Ω)) (unitaryHaarFrameLaw K n ell helln) ∧
      (∫ Ω,frobSq (haarBlockNoise U V Ω) ∂unitaryHaarFrameLaw K n ell helln) =
        (∫ Ω,RCLike.re ((unitaryFrameTopGram K U Ω)⁻¹).trace
          ∂unitaryHaarFrameLaw K n ell helln)-r := by
  have he : (fun Ω => frobSq (haarBlockNoise U V Ω)) =ᵐ[unitaryHaarFrameLaw K n ell helln]
      (fun Ω => RCLike.re ((unitaryFrameTopGram K U Ω)⁻¹).trace-r) := by
    filter_upwards [hfull] with Ω hΩ
    have hgram : (Ω.valᴴ*U)ᴴ*(Ω.valᴴ*U)=unitaryFrameTopGram K U Ω := by
      simp only [unitaryFrameTopGram,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    have hf : IsUnit ((Ω.valᴴ*U)ᴴ*(Ω.valᴴ*U)) := hgram ▸ hΩ
    have hrow := rowGram_sketch_blocks_eq_one Ω.val U V Ω.property hcomp
    have hh := frobSq_pinvL_blockNoise_eq_trace_inv_sub_card (Ω.valᴴ*U) (Ω.valᴴ*V) hf hrow
    simpa only [haarBlockNoise,hgram,Fintype.card_fin] using hh
  constructor
  · exact (htrace.sub (integrable_const _)).congr he.symm
  · rw [integral_congr_ae he,integral_sub htrace (integrable_const _)]
    simp

/-- Actual native Haar block noise is isotropic on every fixed complementary
matrix. No covariance hypothesis or alternative sketch law is supplied. -/
theorem integrable_and_integral_frobSq_haarBlockNoise_mul
    (helln : ell≤n) (hq : 0<q) (U : Matrix (Fin n) (Fin r) K) (V : Matrix (Fin n) (Fin q) K)
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hUV : Uᴴ*V=0) (hcomp : U*Uᴴ+V*Vᴴ=1)
    (hfull : ∀ᵐ Ω ∂unitaryHaarFrameLaw K n ell helln,IsUnit (unitaryFrameTopGram K U Ω))
    (htrace : Integrable (fun Ω => RCLike.re ((unitaryFrameTopGram K U Ω)⁻¹).trace)
      (unitaryHaarFrameLaw K n ell helln)) (D : Matrix (Fin q) (Fin p) K) :
    Integrable (fun Ω => frobSq (haarBlockNoise U V Ω*D)) (unitaryHaarFrameLaw K n ell helln) ∧
      (∫ Ω,frobSq (haarBlockNoise U V Ω*D) ∂unitaryHaarFrameLaw K n ell helln) =
        (((∫ Ω,RCLike.re ((unitaryFrameTopGram K U Ω)⁻¹).trace
          ∂unitaryHaarFrameLaw K n ell helln)-r)/q)*frobSq D := by
  let : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hq
  obtain ⟨hi,hv⟩ := integrable_and_integral_frobSq_haarBlockNoise helln U V hcomp hfull htrace
  have hm : AEMeasurable (haarBlockNoise (ell := ell) U V)
      (unitaryHaarFrameLaw K n ell helln) := (measurable_haarBlockNoise U V).aemeasurable
  have hbase : Integrable (fun Z => frobSq Z) (haarBlockNoiseLaw helln U V) := by
    exact (integrable_map_measure measurable_frobSq.aestronglyMeasurable hm).mpr hi
  have hvalue : (∫ Z,frobSq Z ∂haarBlockNoiseLaw helln U V)=
      (∫ Ω,RCLike.re ((unitaryFrameTopGram K U Ω)⁻¹).trace
        ∂unitaryHaarFrameLaw K n ell helln)-r := by
    rw [haarBlockNoiseLaw,integral_map hm measurable_frobSq.aestronglyMeasurable]
    exact hv
  obtain ⟨himage,himageValue⟩ := integrable_and_integral_frobSq_mul_of_rightUnitaryInvariant
    (haarBlockNoiseLaw helln U V) hbase (rightUnitaryInvariant_haarBlockNoiseLaw helln U V hU hV hUV hcomp) D
  have hmf : Measurable (fun Z : Matrix (Fin r) (Fin q) K => frobSq (Z*D)) :=
    measurable_frobSq.comp (measurable_id.matrix_mul measurable_const)
  constructor
  · exact (integrable_map_measure hmf.aestronglyMeasurable hm).mp himage
  · rw [← integral_map hm hmf.aestronglyMeasurable]
    change (∫ Z,frobSq (Z*D) ∂haarBlockNoiseLaw helln U V)=_
    rw [himageValue,hvalue,Fintype.card_fin]

open scoped Matrix.Norms.L2Operator in
private local instance haarBlockRealNormedSpace : NormedSpace ℝ (Matrix (Fin r) (Fin q) K) :=
  NormedSpace.restrictScalars ℝ K (Matrix (Fin r) (Fin q) K)

local instance : SecondCountableTopology (Matrix (Fin r) (Fin q) K) :=
  inferInstanceAs (SecondCountableTopology (Fin r → Fin q → K))

open scoped Matrix.Norms.L2Operator in
/-- The actual Haar block noise is integrable under its native inverse-trace
moment hypotheses, so the zero-mean statement is an integrable expectation. -/
theorem integrable_haarBlockNoise
    (helln : ell≤n) (U : Matrix (Fin n) (Fin r) K) (V : Matrix (Fin n) (Fin q) K)
    (hcomp : U*Uᴴ+V*Vᴴ=1)
    (hfull : ∀ᵐ Ω ∂unitaryHaarFrameLaw K n ell helln,IsUnit (unitaryFrameTopGram K U Ω))
    (htrace : Integrable (fun Ω => RCLike.re ((unitaryFrameTopGram K U Ω)⁻¹).trace)
      (unitaryHaarFrameLaw K n ell helln)) :
    Integrable (haarBlockNoise U V) (unitaryHaarFrameLaw K n ell helln) := by
  have hi := (integrable_and_integral_frobSq_haarBlockNoise helln U V hcomp hfull htrace).1
  have hm : AEMeasurable (haarBlockNoise (ell := ell) U V)
      (unitaryHaarFrameLaw K n ell helln) := (measurable_haarBlockNoise U V).aemeasurable
  have hbase : Integrable (fun Z => frobSq Z) (haarBlockNoiseLaw helln U V) :=
    (integrable_map_measure measurable_frobSq.aestronglyMeasurable hm).mpr hi
  have hz := integrable_matrix_of_integrable_frobSq (haarBlockNoiseLaw helln U V) hbase
  exact hz.comp_aemeasurable hm

open scoped Matrix.Norms.L2Operator in
/-- Actual unitary-Haar bottom-block noise has zero native matrix mean, by the
ambient action realizing the complementary `-I` symmetry. -/
theorem integral_haarBlockNoise_eq_zero
    (helln : ell≤n) (U : Matrix (Fin n) (Fin r) K) (V : Matrix (Fin n) (Fin q) K)
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hUV : Uᴴ*V=0) (hcomp : U*Uᴴ+V*Vᴴ=1) :
    (∫ Ω,haarBlockNoise U V Ω ∂unitaryHaarFrameLaw K n ell helln)=0 := by
  have hm : AEMeasurable (haarBlockNoise (ell := ell) U V)
      (unitaryHaarFrameLaw K n ell helln) := (measurable_haarBlockNoise U V).aemeasurable
  have hl : HasLaw (haarBlockNoise U V) (haarBlockNoiseLaw helln U V)
      (unitaryHaarFrameLaw K n ell helln) := ⟨hm,rfl⟩
  exact hl.integral_eq.trans
    (integral_matrix_eq_zero_of_rightUnitaryInvariant (haarBlockNoiseLaw helln U V)
      (rightUnitaryInvariant_haarBlockNoiseLaw helln U V hU hV hUV hcomp))

open scoped Matrix.Norms.L2Operator in
/-- The native Haar correction has an integrable actual mean equal to zero;
the only moment premises are about the actual native inverse top-Gram trace. -/
theorem integrable_and_integral_haarBlockNoise
    (helln : ell≤n) (U : Matrix (Fin n) (Fin r) K) (V : Matrix (Fin n) (Fin q) K)
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hUV : Uᴴ*V=0) (hcomp : U*Uᴴ+V*Vᴴ=1)
    (hfull : ∀ᵐ Ω ∂unitaryHaarFrameLaw K n ell helln,IsUnit (unitaryFrameTopGram K U Ω))
    (htrace : Integrable (fun Ω => RCLike.re ((unitaryFrameTopGram K U Ω)⁻¹).trace)
      (unitaryHaarFrameLaw K n ell helln)) :
    Integrable (haarBlockNoise U V) (unitaryHaarFrameLaw K n ell helln) ∧
      (∫ Ω,haarBlockNoise U V Ω ∂unitaryHaarFrameLaw K n ell helln)=0 :=
  ⟨integrable_haarBlockNoise helln U V hcomp hfull htrace,
    integral_haarBlockNoise_eq_zero helln U V hU hV hUV hcomp⟩

end NLAlib
