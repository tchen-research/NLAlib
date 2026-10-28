import NLAlib.ForMathlib.Analysis.InnerProductSpace.GramSchmidt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measurable Gram--Schmidt and isometry equivariance over both scalar fields

These are the Hermitian counterparts of the existing real adapters. The
normalization is the literal positive norm, and zero residuals stay totalized.
-/

noncomputable section
open MeasureTheory InnerProductSpace
namespace NLAlib
variable (𝕜 : Type*) [RCLike 𝕜]

/-- The actual Gram--Schmidt residuals commute with scalar-linear isometries. -/
theorem gramSchmidt_map_linearIsometry_rclike
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {k : ℕ}
    (L : E →ₗᵢ[𝕜] F) (f : Fin k → E) (j : Fin k) :
    gramSchmidt 𝕜 (fun i => L (f i)) j = L (gramSchmidt 𝕜 f j) := by
  refine (show WellFounded ((· < ·) : Fin k → Fin k → Prop) from wellFounded_lt).induction
    (C := fun j => gramSchmidt 𝕜 (fun i => L (f i)) j = L (gramSchmidt 𝕜 f j)) j ?_
  intro j ih
  rw [eq_sub_of_add_eq (gramSchmidt_def'' 𝕜 (fun i => L (f i)) j).symm,
    eq_sub_of_add_eq (gramSchmidt_def'' 𝕜 f j).symm,map_sub,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [ih i (Finset.mem_Iio.mp hi),map_smul,L.inner_map_map,L.norm_map]

/-- Positive normalized Gram--Schmidt commutes with every unitary isometry. -/
theorem gramSchmidtNormed_map_linearIsometry_rclike
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {k : ℕ}
    (L : E →ₗᵢ[𝕜] F) (f : Fin k → E) (j : Fin k) :
    gramSchmidtNormed 𝕜 (fun i => L (f i)) j = L (gramSchmidtNormed 𝕜 f j) := by
  rw [gramSchmidtNormed,gramSchmidtNormed,gramSchmidt_map_linearIsometry_rclike,
    L.norm_map,map_smul]

/-- A measurable input family has measurable Hermitian Gram--Schmidt residuals. -/
theorem measurable_gramSchmidt_rclike
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {k : ℕ}
    (f : Ω → Fin k → E) (hf : ∀ j, Measurable (fun ω => f ω j)) (j : Fin k) :
    Measurable (fun ω => gramSchmidt 𝕜 (f ω) j) := by
  refine (show WellFounded ((· < ·) : Fin k → Fin k → Prop) from wellFounded_lt).induction
    (C := fun j => Measurable (fun ω => gramSchmidt 𝕜 (f ω) j)) j ?_
  intro j ih
  have heq : (fun ω => gramSchmidt 𝕜 (f ω) j) =
      (fun ω => f ω j-∑ i ∈ Finset.Iio j,
        (inner 𝕜 (gramSchmidt 𝕜 (f ω) i) (f ω j)/
          (‖gramSchmidt 𝕜 (f ω) i‖ : 𝕜)^2) • gramSchmidt 𝕜 (f ω) i) :=
    funext (fun ω => eq_sub_of_add_eq (gramSchmidt_def'' 𝕜 (f ω) j).symm)
  rw [heq]
  apply (hf j).sub
  apply Finset.measurable_sum
  intro i hi
  have hg := ih i (Finset.mem_Iio.mp hi)
  have hnorm : Measurable (fun ω => (‖gramSchmidt 𝕜 (f ω) i‖ : 𝕜)) :=
    RCLike.continuous_ofReal.measurable.comp hg.norm
  exact ((hg.inner (𝕜 := 𝕜) (hf j)).div (hnorm.pow_const 2)).smul hg

/-- Normalized Hermitian Gram--Schmidt is measurable, including zero residuals. -/
theorem measurable_gramSchmidtNormed_rclike
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {k : ℕ}
    (f : Ω → Fin k → E) (hf : ∀ j, Measurable (fun ω => f ω j)) (j : Fin k) :
    Measurable (fun ω => gramSchmidtNormed 𝕜 (f ω) j) := by
  simp only [gramSchmidtNormed]
  have hg := measurable_gramSchmidt_rclike 𝕜 f hf j
  exact (RCLike.continuous_ofReal.measurable.comp hg.norm).inv.smul hg

/-- A vector in the span of a finite Hermitian orthonormal family is the sum
of its actual inner-product coordinates. -/
theorem eq_sum_inner_smul_of_mem_span_orthonormal_rclike
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]
    (v : ι → E) (hv : Orthonormal 𝕜 v) {x : E}
    (hx : x ∈ Submodule.span 𝕜 (Set.range v)) :
    x = ∑ i, inner 𝕜 (v i) x • v i := by
  classical
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  have hcoeff (i : ι) : inner 𝕜 (v i) x = c i := by
    rw [← hc]
    exact hv.inner_right_finsupp c i
  simp_rw [hcoeff]
  rw [← hc,Finsupp.sum_fintype]
  intro i
  simp

end NLAlib
