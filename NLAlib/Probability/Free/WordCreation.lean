import NLAlib.ForMathlib.Analysis.InnerProductSpace.L2Embedding
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum

/-!
# Concrete prefix creation and annihilation on finite-word ℓ² space

The word-prefix creation map is an actual linear isometry, and annihilation
is its native Hilbert adjoint. Their actions on word basis vectors and their
operator composition relations are proved from the ℓ² embedding interface.
The alphabet may be arbitrary, including empty. This file does not assert
semicircular laws, freeness, or a faithful vacuum state.

Source: the concrete full-Fock construction in Nica--Speicher, Lectures on
the Combinatorics of Free Probability, Definitions 7.13 and Remark 7.14.
-/

noncomputable section
set_option autoImplicit false

open scoped Classical lp InnerProduct ENNReal

namespace NLAlib

/-- The concrete complex Hilbert space with orthonormal basis indexed by all
finite words in an alphabet. The empty word remains present for an empty alphabet. -/
abbrev WordHilbertSpace (ι : Type*) := ℓ²(List ι, ℂ)

variable {ι : Type*}

/-- The actual prefix creation isometry sends the basis vector of `w` to
the basis vector of `i :: w`. -/
def wordCreation (i : ι) : WordHilbertSpace ι →ₗᵢ[ℂ] WordHilbertSpace ι :=
  lp.embeddingLinearIsometry ⟨List.cons i, List.cons_injective⟩

/-- Actual annihilation is the native Hilbert adjoint of prefix creation. -/
def wordAnnihilation (i : ι) : WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι :=
  (wordCreation i).toContinuousLinearMap.adjoint

/-- Creation prepends one letter to the support of a word basis vector. -/
@[simp]
theorem wordCreation_apply_single (i : ι) (w : List ι) (z : ℂ) :
    wordCreation i (lp.single 2 w z) = lp.single 2 (i :: w) z := by
  convert! lp.embeddingLinearIsometry_apply_single
    (𝕜 := ℂ) (⟨List.cons i, List.cons_injective⟩ : List ι ↪ List ι) w z using 1
  · unfold wordCreation
    congr 1
    ext v
    by_cases hv : v = w <;> simp [lp.single_apply, hv]
  · ext v
    by_cases hv : v = i :: w <;> simp [lp.single_apply, hv]

/-- Annihilation restricts a word-coordinate function to words with the
given initial letter. -/
@[simp]
theorem wordAnnihilation_apply (i : ι) (f : WordHilbertSpace ι) (w : List ι) :
    wordAnnihilation i f w = f (i :: w) :=
  lp.embeddingLinearIsometry_adjoint_apply _ f w

/-- Annihilation kills every basis vector supported at the empty word. -/
@[simp]
theorem wordAnnihilation_apply_single_nil (i : ι) (z : ℂ) :
    wordAnnihilation i (lp.single 2 [] z) = 0 := by
  classical
  ext w
  simp [wordAnnihilation_apply, lp.single_apply]

open scoped Classical in
/-- On a nonempty word basis vector, annihilation removes a matching initial
letter and kills a vector with a different initial letter. -/
@[simp]
theorem wordAnnihilation_apply_single_cons (i j : ι) (w : List ι) (z : ℂ) :
    wordAnnihilation i (lp.single 2 (j :: w) z) =
      if i = j then lp.single 2 w z else 0 := by
  classical
  ext v
  by_cases hij : i = j
  · subst j
    simp [wordAnnihilation_apply, lp.single_apply, Pi.single_apply]
  · simp [wordAnnihilation_apply, lp.single_apply, hij]

open scoped Classical in
/-- The native annihilation/creation composition is identity at equal
letters and zero at different letters. No law or moment assumption is used. -/
theorem wordAnnihilation_comp_wordCreation (i j : ι) :
    wordAnnihilation i ∘L (wordCreation j).toContinuousLinearMap =
      if i = j then 1 else 0 := by
  classical
  apply lp.ext_continuousLinearMap (by simp : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  ext z
  by_cases hij : i = j
  · subst j
    simp [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
      LinearIsometry.coe_toContinuousLinearMap]
  · simp [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
      LinearIsometry.coe_toContinuousLinearMap, hij]

open scoped Classical in
/-- The concrete bounded word-prefix operators satisfy the native star-ring
relation `ell_i* ell_j = delta_ij I`. -/
theorem star_wordCreation_mul_wordCreation (i j : ι) :
    star (wordCreation i).toContinuousLinearMap * (wordCreation j).toContinuousLinearMap =
      if i = j then 1 else 0 := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
  exact wordAnnihilation_comp_wordCreation i j

/-- The actual unit vacuum vector is the basis vector of the empty word. -/
def wordVacuum (ι : Type*) : WordHilbertSpace ι :=
  lp.single 2 [] 1

/-- The concrete vacuum has norm one even when the alphabet is empty. -/
@[simp]
theorem norm_wordVacuum : ‖wordVacuum ι‖ = 1 := by
  simp [wordVacuum, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

/-- Every actual annihilation operator kills the vacuum. -/
@[simp]
theorem wordAnnihilation_wordVacuum (i : ι) : wordAnnihilation i (wordVacuum ι) = 0 :=
  wordAnnihilation_apply_single_nil i 1

end NLAlib
