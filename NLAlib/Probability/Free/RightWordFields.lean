import NLAlib.Probability.Free.WordFields

/-!
# Concrete suffix creation and right fields on word Hilbert space

Suffix creation appends one letter, and right annihilation is its native
Hilbert adjoint. These are actual bounded operators for arbitrary alphabets,
including an empty alphabet. No distribution or faithfulness is assumed.
-/

noncomputable section
set_option autoImplicit false

open scoped Classical lp InnerProduct ENNReal

namespace NLAlib

variable {ι : Type*}

/-- The suffix creation isometry appends a letter to each word basis index. -/
def wordRightCreation (i : ι) : WordHilbertSpace ι →ₗᵢ[ℂ] WordHilbertSpace ι :=
  lp.embeddingLinearIsometry ⟨fun w => w ++ [i], List.append_left_injective [i]⟩

/-- Right annihilation is the native Hilbert adjoint of suffix creation. -/
def wordRightAnnihilation (i : ι) : WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι :=
  (wordRightCreation i).toContinuousLinearMap.adjoint

/-- The right self-adjoint field is suffix creation plus its native adjoint. -/
def wordRightField (i : ι) : WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι :=
  (wordRightCreation i).toContinuousLinearMap + wordRightAnnihilation i

/-- Suffix creation preserves a basis coefficient and appends its letter. -/
@[simp]
theorem wordRightCreation_apply_single (i : ι) (w : List ι) (z : ℂ) :
    wordRightCreation i (lp.single 2 w z) = lp.single 2 (w ++ [i]) z := by
  convert! lp.embeddingLinearIsometry_apply_single (𝕜 := ℂ)
    (⟨fun w => w ++ [i], List.append_left_injective [i]⟩ : List ι ↪ List ι) w z using 1
  · unfold wordRightCreation
    congr 1
    ext v
    by_cases hv : v = w <;> simp [lp.single_apply, hv]
  · ext v
    by_cases hv : v = w ++ [i] <;> simp [lp.single_apply, hv]

/-- Right annihilation restricts coordinates to words ending in its letter. -/
@[simp]
theorem wordRightAnnihilation_apply (i : ι) (f : WordHilbertSpace ι) (w : List ι) :
    wordRightAnnihilation i f w = f (w ++ [i]) :=
  lp.embeddingLinearIsometry_adjoint_apply _ f w

/-- Right annihilation kills basis vectors at the empty word. -/
@[simp]
theorem wordRightAnnihilation_apply_single_nil (i : ι) (z : ℂ) :
    wordRightAnnihilation i (lp.single 2 [] z) = 0 := by
  ext w
  simp [wordRightAnnihilation_apply, lp.single_apply]

/-- Right annihilation removes a matching final letter and kills a basis
vector whose final letter is different. -/
@[simp]
theorem wordRightAnnihilation_apply_single_append (i j : ι) (w : List ι) (z : ℂ) :
    wordRightAnnihilation i (lp.single 2 (w ++ [j]) z) =
      if i = j then lp.single 2 w z else 0 := by
  ext v
  by_cases hij : i = j
  · subst j
    simp [wordRightAnnihilation_apply, lp.single_apply, Pi.single_apply]
  · simp [wordRightAnnihilation_apply, lp.single_apply,
      List.append_singleton_inj, hij]

/-- The concrete right fields are self-adjoint. -/
theorem isSelfAdjoint_wordRightField (i : ι) : IsSelfAdjoint (wordRightField i) := by
  simpa only [wordRightField, wordRightAnnihilation,
    ← ContinuousLinearMap.star_eq_adjoint] using
    IsSelfAdjoint.add_star_self (wordRightCreation i).toContinuousLinearMap

/-- The right field applied to the actual vacuum is the corresponding
one-letter basis vector. -/
@[simp]
theorem wordRightField_wordVacuum (i : ι) :
    wordRightField i (wordVacuum ι) = lp.single 2 [i] 1 := by
  simp [wordRightField, wordVacuum, LinearIsometry.coe_toContinuousLinearMap]

end NLAlib
