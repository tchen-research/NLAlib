import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!
# Genuine diagonal amplification of positive functionals

The actual dimension-normalized diagonal sum is positive on C*-matrices.
Its positivity follows from the true matrix star-square expansion and the
native star-ordered cone. Faithfulness of the original functional gives
faithfulness of the actual amplification. The empty matrix convention is
zero, and normalization at one requires positive matrix dimension.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder
namespace CStarMatrix
variable {D A : Type*} [Fintype D] [DecidableEq D] [CStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

/-- The actual normalized diagonal amplification of a scalar functional. -/
def normalizedFunctional (φ : A →ₗ[ℂ] ℂ) : CStarMatrix D D A →ₗ[ℂ] ℂ where
  toFun T := (Fintype.card D : ℂ)⁻¹*∑ j,φ (T j j)
  map_add' T U := by simp [CStarMatrix.add_apply,map_add,Finset.sum_add_distrib,mul_add]
  map_smul' c T := by simp [CStarMatrix.smul_apply,map_smul,Finset.mul_sum,mul_left_comm]

omit [DecidableEq D] [PartialOrder A] [StarOrderedRing A] in
/-- The actual normalized diagonal formula. -/
@[simp] theorem normalizedFunctional_apply (φ : A →ₗ[ℂ] ℂ) (T : CStarMatrix D D A) :
    normalizedFunctional φ T=(Fintype.card D : ℂ)⁻¹*∑ j,φ (T j j) := rfl

omit [DecidableEq D] [PartialOrder A] [StarOrderedRing A] in
/-- The actual amplified star-square functional is the normalized sum of all entrywise star-square values. -/
theorem normalizedFunctional_star_mul (φ : A →ₗ[ℂ] ℂ) (T : CStarMatrix D D A) :
    normalizedFunctional φ (star T*T)=
      (Fintype.card D : ℂ)⁻¹*∑ j,∑ i,φ (star (T i j)*T i j) := by
  simp only [normalizedFunctional_apply,CStarMatrix.mul_apply,CStarMatrix.star_apply,map_sum]

omit [DecidableEq D] in
private theorem normalizedFunctional_nonneg (φ : A →ₚ[ℂ] ℂ) {T : CStarMatrix D D A}
    (hT : 0≤T) : 0≤normalizedFunctional φ.toLinearMap T := by
  let P : AddSubmonoid (CStarMatrix D D A) :=
    { carrier := {T | 0≤normalizedFunctional φ.toLinearMap T}
      zero_mem' := by simp
      add_mem' := by intro T U hT hU; simpa only [Set.mem_ofPred_eq,map_add] using add_nonneg hT hU }
  have hle : AddSubmonoid.closure (Set.range fun R : CStarMatrix D D A => star R*R)≤P := by
    apply AddSubmonoid.closure_le.mpr
    rintro _ ⟨R,rfl⟩
    change 0≤normalizedFunctional φ.toLinearMap (star R*R)
    rw [normalizedFunctional_star_mul]
    apply mul_nonneg
    · have hh : 0≤(Fintype.card D : ℝ)⁻¹ := by positivity
      simpa only [Complex.ofReal_inv,Complex.ofReal_natCast] using Complex.zero_le_real.mpr hh
    · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
        φ.map_nonneg (star_mul_self_nonneg (R i j))
  exact hle (StarOrderedRing.nonneg_iff.mp hT)

/-- The actual diagonal amplification is positive, with zero normalization on empty matrix dimension. -/
def normalizedPositiveFunctional (φ : A →ₚ[ℂ] ℂ) : CStarMatrix D D A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (normalizedFunctional φ.toLinearMap) fun _ hT => normalizedFunctional_nonneg φ hT

omit [DecidableEq D] in
/-- Bundling positivity preserves the actual normalized diagonal values. -/
@[simp] theorem normalizedPositiveFunctional_apply (φ : A →ₚ[ℂ] ℂ) (T : CStarMatrix D D A) :
    normalizedPositiveFunctional φ T=normalizedFunctional φ.toLinearMap T := rfl

/-- Normalization of the original functional gives normalization of its genuine positive amplification in positive matrix dimension. -/
theorem normalizedPositiveFunctional_one [Nonempty D] (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1=1) :
    normalizedPositiveFunctional (D := D) φ 1=1 := by
  change (Fintype.card D : ℂ)⁻¹*(∑ j : D, φ ((1 : CStarMatrix D D A) j j))=1
  simp only [CStarMatrix.one_apply_eq,hφ,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  exact inv_mul_cancel₀ (show (Fintype.card D : ℂ)≠0 from Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

omit [DecidableEq D] in
/-- A faithful original positive functional has faithful actual matrix amplification, including empty matrix dimension. -/
theorem eq_zero_of_normalizedPositiveFunctional_star_mul_eq_zero
    (φ : A →ₚ[ℂ] ℂ) (hfaithful : ∀ a : A, φ (star a*a)=0 → a=0)
    (T : CStarMatrix D D A) (hzero : normalizedPositiveFunctional φ (star T*T)=0) : T=0 := by
  apply CStarMatrix.ext
  intro i j
  have : Nonempty D := ⟨j⟩
  have hcard : (Fintype.card D : ℂ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hz : ∑ j,∑ i,φ (star (T i j)*T i j)=0 := by
    rw [normalizedPositiveFunctional_apply,normalizedFunctional_star_mul] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (inv_ne_zero hcard)
  have hr : ∑ j,∑ i,(φ (star (T i j)*T i j)).re=0 := by
    have hh := congrArg Complex.re hz
    change (Complex.reCLM (∑ j,∑ i,φ (star (T i j)*T i j)))=0 at hh
    simpa only [map_sum,Complex.reCLM_apply] using hh
  have hnonneg (i j : D) : 0≤(φ (star (T i j)*T i j)).re :=
    (Complex.nonneg_iff.mp (φ.map_nonneg (star_mul_self_nonneg (T i j)))).1
  have hc := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
    Finset.sum_nonneg fun i _ => hnonneg i j)).mp hr j (Finset.mem_univ j)
  have he := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i j)).mp hc i (Finset.mem_univ i)
  apply hfaithful
  exact Complex.ext he (Complex.nonneg_iff.mp
    (φ.map_nonneg (star_mul_self_nonneg (T i j)))).2.symm

end CStarMatrix
