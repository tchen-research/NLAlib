import NLAlib.Matrix.Norms.Core
import Mathlib.Topology.Order.Compact

/-!
# Restricted minimum of a matrix on a compact set

The ordinary infimum of the Euclidean norm of the matrix action, with
attainment and a perturbation bound for subsets of the unit sphere.
-/

noncomputable section
open Set
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq n]

/-- The minimum Euclidean length of the matrix action over a set. On a nonempty
compact set it is attained; on other sets this uses the total real infimum. -/
def restrictedMinimum (A : Matrix m n 𝕜) (T : Set (EuclideanSpace 𝕜 n)) : ℝ :=
  sInf ((fun x => ‖Matrix.toEuclideanLin A x‖) '' T)

/-- A matrix attains its restricted minimum on every nonempty compact set. -/
theorem exists_norm_eq_restrictedMinimum (A : Matrix m n 𝕜)
    {T : Set (EuclideanSpace 𝕜 n)} (hT : IsCompact T) (hne : T.Nonempty) :
    ∃ x ∈ T, ‖Matrix.toEuclideanLin A x‖ = restrictedMinimum A T := by
  have hc : Continuous (fun x => ‖Matrix.toEuclideanLin A x‖) :=
    (Matrix.toEuclideanLin A).continuous_of_finiteDimensional.norm
  obtain ⟨x,hx,hmin⟩ := hT.exists_isMinOn hne hc.continuousOn
  refine ⟨x,hx,?_⟩
  symm
  exact (show IsLeast ((fun x => ‖Matrix.toEuclideanLin A x‖) '' T)
    ‖Matrix.toEuclideanLin A x‖ from
    ⟨⟨x,hx,rfl⟩, by rintro _ ⟨y,hy,rfl⟩; exact hmin hy⟩).csInf_eq

/-- The restricted minimum is bounded by the length at every admissible point. -/
theorem restrictedMinimum_le_norm (A : Matrix m n 𝕜)
    {T : Set (EuclideanSpace 𝕜 n)} {x : EuclideanSpace 𝕜 n} (hx : x ∈ T) :
    restrictedMinimum A T ≤ ‖Matrix.toEuclideanLin A x‖ := by
  exact csInf_le ⟨0, by rintro _ ⟨y,hy,rfl⟩; exact norm_nonneg _⟩ ⟨x,hx,rfl⟩

/-- On a nonempty set the restricted minimum is nonnegative. -/
theorem restrictedMinimum_nonneg (A : Matrix m n 𝕜)
    {T : Set (EuclideanSpace 𝕜 n)} (hne : T.Nonempty) :
    0 ≤ restrictedMinimum A T :=
  le_csInf (hne.image _) (by rintro _ ⟨x,hx,rfl⟩; exact norm_nonneg _)

/-- Restricting to a compact part of the unit ball makes the minimum
1-Lipschitz in the spectral norm of a perturbation. -/
theorem abs_restrictedMinimum_sub_le_specNorm (A B : Matrix m n 𝕜)
    {T : Set (EuclideanSpace 𝕜 n)} (hT : IsCompact T) (hne : T.Nonempty)
    (hunit : ∀ x ∈ T, ‖x‖ ≤ 1) :
    |restrictedMinimum A T - restrictedMinimum B T| ≤ specNorm (A-B) := by
  have hstep : ∀ A B : Matrix m n 𝕜,
      restrictedMinimum A T - restrictedMinimum B T ≤ specNorm (A-B) := by
    intro A B
    obtain ⟨x,hx,he⟩ := exists_norm_eq_restrictedMinimum B hT hne
    have ha := restrictedMinimum_le_norm A hx
    let Φ := (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) (A-B)
    have hd : ‖Matrix.toEuclideanLin A x - Matrix.toEuclideanLin B x‖ ≤ specNorm (A-B) := by
      have heq : Φ x = Matrix.toEuclideanLin A x - Matrix.toEuclideanLin B x := by
        change Matrix.toEuclideanLin (A-B) x = _
        rw [map_sub, LinearMap.sub_apply]
      rw [← heq]
      exact (Φ.le_opNorm x).trans (by
        change specNorm (A-B) * ‖x‖ ≤ specNorm (A-B)
        nlinarith [specNorm_nonneg (A-B), hunit x hx])
    have hn := norm_sub_norm_le (Matrix.toEuclideanLin A x) (Matrix.toEuclideanLin B x)
    linarith
  exact abs_sub_le_iff.mpr ⟨hstep A B, by
    have heq : specNorm (B-A) = specNorm (A-B) := by
      rw [show B-A = -(A-B) by abel, specNorm_neg]
    simpa only [heq] using hstep B A⟩

/-- The Frobenius distance also bounds perturbations of a restricted minimum. -/
theorem abs_restrictedMinimum_sub_le_frobNorm (A B : Matrix m n 𝕜)
    {T : Set (EuclideanSpace 𝕜 n)} (hT : IsCompact T) (hne : T.Nonempty)
    (hunit : ∀ x ∈ T, ‖x‖ ≤ 1) :
    |restrictedMinimum A T - restrictedMinimum B T| ≤ frobNorm (A-B) :=
  (abs_restrictedMinimum_sub_le_specNorm A B hT hne hunit).trans (specNorm_le_frobNorm _)

end NLAlib
