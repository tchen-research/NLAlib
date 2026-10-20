import NLAlib.Probability.Free.WordMatrixCreationNorm
import NLAlib.Probability.Free.WordPolynomialUltracontractivity

/-!
# The native C*-matrix form of the actual matrix free linear model

This is the same concrete matrix-coefficient word-field operator as
`wordMatrixLinearCombination`, before applying its faithful Hilbert block
representation. Its native matrix form permits genuine amplified vacuum
moments and closed C*-algebra arguments.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical ComplexOrder

namespace NLAlib

variable {D ι : Type*} [Fintype D] [DecidableEq D] [Fintype ι]
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W
local notation "M" => CStarMatrix D D B

/-- The actual matrix word linear combination, in the native C*-matrix
algebra before its faithful Hilbert block representation. -/
def wordNativeMatrixLinearCombination (A₀ : Matrix D D ℂ)
    (A : ι → Matrix D D ℂ) : M :=
  CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ B) (CStarMatrix.ofMatrix A₀) +
    ∑ k, CStarMatrix.ofMatrix (fun i j => A k i j • wordField k)

/-- The native free model has exactly the previously constructed actual
Hilbert-space operator as its faithful block representation. -/
theorem toPiLp_wordNativeMatrixLinearCombination (A₀ : Matrix D D ℂ)
    (A : ι → Matrix D D ℂ) :
    CStarMatrix.toPiLpStarAlgHom (D := D) (H := W)
      (wordNativeMatrixLinearCombination A₀ A) = wordMatrixLinearCombination A₀ A := by
  unfold wordNativeMatrixLinearCombination wordMatrixLinearCombination
  rw [map_add,map_sum]
  rfl

/-- The actual native linear matrix has degree at most one in every
operator entry. -/
theorem wordNativeMatrixLinearCombination_mem_wordWickDegreeSpan
    (A₀ : Matrix D D ℂ) (A : ι → Matrix D D ℂ) (i j : D) :
    wordNativeMatrixLinearCombination A₀ A i j ∈ wordWickDegreeSpan (ι := ι) 1 := by
  have h1 : (1 : B) ∈ wordWickDegreeSpan (ι := ι) 1 := by
    simpa only [wordWickOperator] using
      wordWickOperator_mem_wordWickDegreeSpan ([] : List ι) (by simp : 0≤1)
  have hf (k : ι) : wordField k ∈ wordWickDegreeSpan (ι := ι) 1 := by
    simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
      List.length_cons,List.length_nil] using
      list_prod_wordField_mem_wordWickDegreeSpan [k]
  change (A₀ i j) • (1 : B)+(∑ k, CStarMatrix.ofMatrix
      (fun i j => A k i j • wordField k)) i j ∈ _
  apply Submodule.add_mem _ (Submodule.smul_mem _ _ h1)
  let F : ι → M := fun k => CStarMatrix.ofMatrix (fun i j => A k i j • wordField k)
  have hsum (s : Finset ι) : (∑ k∈s, F k) i j=∑ k∈s, A k i j•wordField k := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert k s hk ih =>
      rw [Finset.sum_insert hk,Finset.sum_insert hk,CStarMatrix.add_apply,ih]
      rfl
  rw [show (∑ k, CStarMatrix.ofMatrix (fun i j => A k i j•wordField k)) i j=
    ∑ k, A k i j•wordField k from hsum Finset.univ]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hf k)

/-- Hermitian coefficients give the actual self-adjoint native model,
transported through the faithful representation of the same operator. -/
theorem isSelfAdjoint_wordNativeMatrixLinearCombination
    {A₀ : Matrix D D ℂ} (hA₀ : A₀.IsHermitian) {A : ι → Matrix D D ℂ}
    (hA : ∀ k, (A k).IsHermitian) : IsSelfAdjoint (wordNativeMatrixLinearCombination A₀ A) := by
  apply (CStarMatrix.isSelfAdjoint_toPiLpStarAlgHom_iff _).mp
  rw [toPiLp_wordNativeMatrixLinearCombination]
  exact isSelfAdjoint_wordMatrixLinearCombination hA₀ hA

/-- Centering the native free model leaves precisely the source free-series
norm bound, with no dimension factor or assumed moment comparison. -/
theorem norm_wordNativeMatrixLinearCombination_sub_mean_le
    (A₀ : Matrix D D ℂ) (A : ι → Matrix D D ℂ) (hA : ∀ k, (A k).IsHermitian) :
    ‖wordNativeMatrixLinearCombination A₀ A-
      CStarMatrix.mapStarAlgHom (StarAlgHom.ofId ℂ B) (CStarMatrix.ofMatrix A₀)‖ ≤
        2*Real.sqrt (specNorm (∑ k, A k^2)) := by
  rw [← CStarMatrix.norm_toPiLpStarAlgHom,map_sub,toPiLp_wordNativeMatrixLinearCombination]
  exact norm_wordMatrixLinearCombination_sub_mean_le A₀ A hA

end NLAlib

end
