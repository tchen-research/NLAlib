import NLAlib.Matrix.Norms.PositiveImaginaryTrace
import NLAlib.ForMathlib.Analysis.Matrix.ImaginaryCoercivity

/-! # Positive sample gaps from genuine bounded sandwich transforms

Coercivity bounds the inverse sandwich by O(y^(-1/2)). An O(y)
perturbation therefore gives an error tending to zero. The exact matrix
factorization then forces the limiting sample denominator to be a unit.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix Filter Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule Topology
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
local notation "M" => Matrix n n ℂ

omit [Nonempty n] in
private theorem sandwichBoundary_imaginaryPart (U T : M) (hT : T.IsHermitian)
    (hu : IsUnit (U+T)) :
    (imaginaryPart (T*(U+T)⁻¹*T) : M)=
      ((U+T)⁻¹*T)ᴴ*(-(imaginaryPart U : M))*((U+T)⁻¹*T) := by
  have hmul : (U+T)*(-(U+T)⁻¹)= -1 := by
    rw [Matrix.mul_neg,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]
  have hi := Matrix.imaginaryPart_eq_conjTranspose_mul_of_mul_eq_neg_one hmul
  have hIA : (imaginaryPart (U+T) : M)=(imaginaryPart U : M) := by
    rw [map_add,hT.isSelfAdjoint.imaginaryPart,add_zero]
  have hInv : (imaginaryPart (U+T)⁻¹ : M)=
      ((U+T)⁻¹)ᴴ*(-(imaginaryPart U : M))*(U+T)⁻¹ := by
    simpa only [map_neg,NegMemClass.coe_neg,Matrix.conjTranspose_neg,Matrix.mul_neg,
      Matrix.neg_mul,neg_neg,hIA] using congrArg Neg.neg hi
  have hs : (imaginaryPart (T*(U+T)⁻¹*T) : M)=
      T*(imaginaryPart (U+T)⁻¹ : M)*T := by
    simp only [imaginaryPart_apply_coe,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_mul,
      hT.eq,Matrix.mul_smul,Matrix.smul_mul]
    congr 1
    noncomm_ring
  rw [hs,hInv]
  simp only [Matrix.conjTranspose_mul,hT.eq,Matrix.mul_assoc]

/-- Actual O(y) boundary regularity, imaginary coercivity and bounded
native trace sandwiches force a genuine invertible sample denominator.
The proof uses a true inverse identity and open units. No PSD boundary
gap, root branch, or nonzero determinant conclusion is assumed. -/
theorem isUnit_add_of_bounded_inverse_sandwich_boundary
    (Y T : M) (hY : IsUnit Y) (hT : T.IsHermitian)
    (U : ℝ → M) (δ C B : ℝ) (hδ : 0<δ) (hC : 0≤C) (hB : 0≤B)
    (hboundary : ∀ᶠ y : ℝ in 𝓝[>] 0,
      IsUnit (U y+T) ∧ (δ*y)•(1 : M)≤ -(imaginaryPart (U y) : M) ∧
      ‖U y-Y‖≤C*y ∧ ‖normalizedTrace (T*(U y+T)⁻¹*T)‖≤B) :
    IsUnit (Y+T) := by
  let E : ℝ → M := fun y => (U y-Y)*((U y+T)⁻¹*T)
  let D : ℝ := C^2*(Fintype.card n : ℝ)*B/δ
  have hD : 0≤D := by dsimp only [D]; positivity
  have hsmall : ∀ᶠ y : ℝ in 𝓝[>] 0, ‖E y‖^2≤D*y := by
    filter_upwards [hboundary,self_mem_nhdsWithin] with y hy hyp
    have hypos : 0<y := hyp
    let R := (U y+T)⁻¹*T
    let A := T*(U y+T)⁻¹*T
    have hGram : (Rᴴ*R).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self R
    have hGramScale : ((δ*y)•(Rᴴ*R)).PosSemidef := hGram.smul (mul_nonneg hδ.le hypos.le)
    have hle : (δ*y)•(Rᴴ*R)≤(imaginaryPart A : M) := by
      apply Matrix.le_iff.mpr
      have hh := (Matrix.le_iff.mp hy.2.1).conjTranspose_mul_mul_same R
      rw [sandwichBoundary_imaginaryPart (U y) T hT hy.1]
      convert! hh using 1;
        simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
          Matrix.mul_one,Matrix.mul_assoc]
      rfl
    have hApos : (imaginaryPart A : M).PosSemidef :=
      (hGramScale.nonneg.trans hle).posSemidef
    have hnorm : δ*y*‖R‖^2≤(Fintype.card n : ℝ)*B := by
      calc
        _ = ‖(δ*y)•(Rᴴ*R)‖ := by
          rw [norm_smul,Real.norm_of_nonneg (mul_nonneg hδ.le hypos.le),
            ← Matrix.star_eq_conjTranspose,CStarRing.norm_star_mul_self]
          ring
        _ ≤ ‖(imaginaryPart A : M)‖ :=
          CStarAlgebra.norm_le_norm_of_nonneg_of_le hGramScale.nonneg hle
        _ ≤ (Fintype.card n : ℝ)*(normalizedTrace A).im :=
          Matrix.norm_imaginaryPart_le_card_mul_im_normalizedTrace A hApos
        _ ≤ (Fintype.card n : ℝ)*‖normalizedTrace A‖ :=
          mul_le_mul_of_nonneg_left (Complex.im_le_norm _) (Nat.cast_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hy.2.2.2 (Nat.cast_nonneg _)
    have he : ‖E y‖≤C*y*‖R‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hy.2.2.1 (norm_nonneg R))
    have he2 : ‖E y‖^2≤C^2*y^2*‖R‖^2 := by
      convert! (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr he using 1; ring
    have hdelta : δ*‖E y‖^2≤C^2*(Fintype.card n : ℝ)*B*y := by
      calc
        _ ≤ δ*(C^2*y^2*‖R‖^2) := mul_le_mul_of_nonneg_left he2 hδ.le
        _ = C^2*y*(δ*y*‖R‖^2) := by ring
        _ ≤ C^2*y*((Fintype.card n : ℝ)*B) :=
          mul_le_mul_of_nonneg_left hnorm (mul_nonneg (sq_nonneg C) hypos.le)
        _ = _ := by ring
    dsimp only [D]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hδ).mpr (by nlinarith only [hdelta])
  have hEzero : Tendsto E (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have ht : Tendsto (fun y : ℝ => Real.sqrt (D*y)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero,Real.sqrt_zero,Function.comp_def,id_eq] using
        (Real.continuous_sqrt.tendsto (D*0)).comp
          (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds))
    apply squeeze_zero' (Eventually.of_forall fun y => norm_nonneg (E y)) ?_ ht
    filter_upwards [hsmall,self_mem_nhdsWithin] with y hy hyp
    exact (Real.le_sqrt (norm_nonneg _) (mul_nonneg hD hyp.le)).mpr hy
  have hUnitNhds : ∀ᶠ A : M in 𝓝 Y, IsUnit A := Units.isOpen.mem_nhds hY
  have hYlim : Tendsto (fun y : ℝ => Y+E y) (𝓝[>] 0) (𝓝 Y) := by
    simpa only [add_zero] using tendsto_const_nhds.add hEzero
  have hUnits : ∀ᶠ y : ℝ in 𝓝[>] 0, IsUnit (Y+E y) := hYlim.eventually hUnitNhds
  have heq : ∀ᶠ y : ℝ in 𝓝[>] 0,
      (Y+T)*(1-(U y+T)⁻¹*T)=Y+E y := by
    filter_upwards [hboundary] with y hy
    have hh := Matrix.mul_nonsing_inv (U y+T) ((Matrix.isUnit_iff_isUnit_det _).mp hy.1)
    calc
      _ = Y+(U y-Y)*((U y+T)⁻¹*T)+(T-((U y+T)*(U y+T)⁻¹)*T) := by noncomm_ring
      _ = Y+E y := by rw [hh,Matrix.one_mul,sub_self,add_zero]
  obtain ⟨y,hyunit,hyeq⟩ := (hUnits.and heq).exists
  have hProd : IsUnit ((Y+T)*(1-(U y+T)⁻¹*T)) := by rwa [hyeq]
  have hdet : IsUnit ((Y+T).det*(1-(U y+T)⁻¹*T).det) := by
    rw [← Matrix.det_mul]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hProd
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_left hdet)

/-- Actual O(y) boundary regularity, imaginary coercivity, and bounded
native trace sandwiches turn limiting PSD sample gaps into PD gaps.
Invertibility is derived from the true inverse identity; it is not
supplied as a boundary hypothesis. -/
theorem posDef_add_of_bounded_inverse_sandwich_boundary
    (Y T : M) (hY : IsUnit Y) (hT : T.IsHermitian) (hPSD : (Y+T).PosSemidef)
    (U : ℝ → M) (δ C B : ℝ) (hδ : 0<δ) (hC : 0≤C) (hB : 0≤B)
    (hboundary : ∀ᶠ y : ℝ in 𝓝[>] 0,
      IsUnit (U y+T) ∧ (δ*y)•(1 : M)≤ -(imaginaryPart (U y) : M) ∧
      ‖U y-Y‖≤C*y ∧ ‖normalizedTrace (T*(U y+T)⁻¹*T)‖≤B) :
    (Y+T).PosDef :=
  hPSD.posDef_iff_isUnit.mpr (isUnit_add_of_bounded_inverse_sandwich_boundary
    Y T hY hT U δ C B hδ hC hB hboundary)

end NLAlib
