import NLAlib.Probability.Free.RightWordFields
import Mathlib.Tactic.NoncommRing

/-!
# Left and right concrete word fields commute

The mixed creation/annihilation commutator is the actual rank-one vacuum
projection. Taking its adjoint supplies the opposite defect; the two defects
cancel in the self-adjoint fields. No freeness or state assumption is used.
-/

noncomputable section
set_option autoImplicit false

open scoped Classical lp InnerProduct ENNReal

namespace NLAlib

variable {ι : Type*}
local notation "B" => WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι

/-- The actual rank-one orthogonal projection onto the unit word vacuum. -/
def wordVacuumProjection (ι : Type*) : WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι :=
  InnerProductSpace.rankOne ℂ (wordVacuum ι) (wordVacuum ι)

/-- The vacuum projection is self-adjoint under the native operator star. -/
@[simp]
theorem star_wordVacuumProjection : star (wordVacuumProjection ι) = wordVacuumProjection ι := by
  simp [wordVacuumProjection, ContinuousLinearMap.star_eq_adjoint]

/-- The vacuum projection preserves the empty-word coordinate and kills
every nonempty word basis vector. -/
@[simp]
theorem wordVacuumProjection_apply_single (w : List ι) (z : ℂ) :
    wordVacuumProjection ι (lp.single 2 w z) =
      if w = [] then lp.single 2 [] z else 0 := by
  by_cases hw : w = []
  · subst w
    ext v
    simp [wordVacuumProjection, InnerProductSpace.rankOne_apply, wordVacuum,
      lp.inner_single_left, lp.single_apply, Pi.single_apply]
  · simp [wordVacuumProjection, InnerProductSpace.rankOne_apply, wordVacuum,
      lp.inner_single_left, lp.single_apply, hw, Ne.symm hw]

/-- Prefix and suffix creation commute as actual bounded operators. -/
theorem commute_wordCreation_wordRightCreation (i j : ι) :
    Commute (wordCreation i).toContinuousLinearMap (wordRightCreation j).toContinuousLinearMap := by
  change _ * _ = _ * _
  simp only [ContinuousLinearMap.mul_def]
  apply lp.ext_continuousLinearMap (by simp : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  ext z
  simp [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
    LinearIsometry.coe_toContinuousLinearMap]

/-- The mixed left-annihilation/right-creation commutator is exactly its
Kronecker coefficient times the genuine rank-one vacuum projection. -/
theorem wordAnnihilation_mul_wordRightCreation_sub (i j : ι) :
    wordAnnihilation i * (wordRightCreation j).toContinuousLinearMap -
        (wordRightCreation j).toContinuousLinearMap * wordAnnihilation i =
      if i = j then wordVacuumProjection ι else 0 := by
  apply lp.ext_continuousLinearMap (by simp : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  ext z
  cases w with
  | nil =>
    by_cases hij : i = j <;>
      simp [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
        lp.singleContinuousLinearMap_apply, LinearIsometry.coe_toContinuousLinearMap, hij]
  | cons a w =>
    by_cases hij : i = j <;> by_cases hia : i = a <;>
      simp_all [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
        lp.singleContinuousLinearMap_apply, LinearIsometry.coe_toContinuousLinearMap]

/-- The actual left and right self-adjoint fields commute. The two mixed
vacuum defects cancel; they are not individually assumed to vanish. -/
theorem commute_wordField_wordRightField (i j : ι) :
    Commute (wordField i) (wordRightField j) := by
  let C : B := (wordCreation i).toContinuousLinearMap
  let D : B := (wordRightCreation j).toContinuousLinearMap
  have hc : Commute C D := commute_wordCreation_wordRightCreation i j
  have ha : Commute (star C) (star D) := hc.star_star
  have hd : star C * D - D * star C = if i = j then wordVacuumProjection ι else 0 := by
    simpa only [C, D, wordAnnihilation, ← ContinuousLinearMap.star_eq_adjoint] using
      wordAnnihilation_mul_wordRightCreation_sub i j
  have hds : star D * C - C * star D = if i = j then wordVacuumProjection ι else 0 := by
    by_cases hij : i = j
    · simpa only [star_sub, star_mul, star_star, if_pos hij,
        star_wordVacuumProjection] using congrArg star hd
    · simpa only [star_sub, star_mul, star_star, if_neg hij,
        star_zero] using congrArg star hd
  have hm : star C * D + C * star D = D * star C + star D * C := by
    have h := sub_eq_sub_iff_add_eq_add.mp (hd.trans hds.symm)
    simpa only [add_comm] using h
  change Commute (C + star C) (D + star D)
  change _ * _ = _ * _
  calc
    (C + star C) * (D + star D) = C * D + star C * star D + (star C * D + C * star D) := by
      noncomm_ring
    _ = D * C + star D * star C + (D * star C + star D * C) := by rw [hc.eq, ha.eq, hm]
    _ = (D + star D) * (C + star C) := by noncomm_ring

end NLAlib
