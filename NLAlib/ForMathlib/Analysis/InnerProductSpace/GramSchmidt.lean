import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Measurability and isometry equivariance of Gram–Schmidt

The explicit residual recursion uses totalized inverse norms, so it is
measurable even at zero residuals. Isometries preserve every residual and
the positive normalization. Source: operator re-derivation `sh:qr-equiv`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory InnerProductSpace
namespace NLAlib

/-- Gram–Schmidt's residual written explicitly with scalar inner products and
inverse squared norms. Source: Mathlib's singleton star projection formula;
operator re-derivation `sh:qr-equiv`. -/
theorem gramSchmidt_eq_sub_sum_inner_div_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}
    (f : Fin k → E) (j : Fin k) :
    gramSchmidt ℝ f j = f j - ∑ i ∈ Finset.Iio j,
      (inner ℝ (gramSchmidt ℝ f i) (f j) / ‖gramSchmidt ℝ f i‖ ^ 2) •
        gramSchmidt ℝ f i := by
  rw [gramSchmidt_def]
  simp only [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq]

/-- Gram–Schmidt residuals commute with every real linear isometry.
Source: operator re-derivation `sh:qr-equiv`, using the literal recursion. -/
theorem gramSchmidt_map_linearIsometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {k : ℕ}
    (L : E →ₗᵢ[ℝ] F) (f : Fin k → E) (j : Fin k) :
    gramSchmidt ℝ (fun i => L (f i)) j = L (gramSchmidt ℝ f j) := by
  refine (show WellFounded ((· < ·) : Fin k → Fin k → Prop) from wellFounded_lt).induction
    (C := fun j => gramSchmidt ℝ (fun i => L (f i)) j = L (gramSchmidt ℝ f j)) j ?_
  intro j ih
  rw [gramSchmidt_eq_sub_sum_inner_div_norm_sq,
    gramSchmidt_eq_sub_sum_inner_div_norm_sq f j, map_sub, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [ih i (Finset.mem_Iio.mp hi), map_smul,
    L.inner_map_map, L.norm_map]

/-- Positive normalized Gram–Schmidt commutes with real linear isometries.
Source: operator re-derivation `sh:qr-equiv`. -/
theorem gramSchmidtNormed_map_linearIsometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {k : ℕ}
    (L : E →ₗᵢ[ℝ] F) (f : Fin k → E) (j : Fin k) :
    gramSchmidtNormed ℝ (fun i => L (f i)) j = L (gramSchmidtNormed ℝ f j) := by
  rw [gramSchmidtNormed, gramSchmidtNormed, gramSchmidt_map_linearIsometry,
    L.norm_map, map_smul]

/-- A measurable family of inputs has measurable Gram–Schmidt residuals,
including zero residuals. Source: operator re-derivation `sh:qr-equiv`. -/
theorem measurable_gramSchmidt
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {k : ℕ}
    (f : Ω → Fin k → E) (hf : ∀ j, Measurable (fun ω => f ω j)) (j : Fin k) :
    Measurable (fun ω => gramSchmidt ℝ (f ω) j) := by
  refine (show WellFounded ((· < ·) : Fin k → Fin k → Prop) from wellFounded_lt).induction
    (C := fun j => Measurable (fun ω => gramSchmidt ℝ (f ω) j)) j ?_
  intro j ih
  have heq : (fun ω => gramSchmidt ℝ (f ω) j) =
      (fun ω => f ω j - ∑ i ∈ Finset.Iio j,
        (inner ℝ (gramSchmidt ℝ (f ω) i) (f ω j) /
          ‖gramSchmidt ℝ (f ω) i‖ ^ 2) • gramSchmidt ℝ (f ω) i) :=
    funext (fun ω => gramSchmidt_eq_sub_sum_inner_div_norm_sq (f ω) j)
  rw [heq]
  apply (hf j).sub
  apply Finset.measurable_sum
  intro i hi
  have hg := ih i (Finset.mem_Iio.mp hi)
  exact ((hg.inner (𝕜 := ℝ) (hf j)).div (hg.norm.pow_const 2)).smul hg

/-- A measurable input family has measurable positive normalized Gram–Schmidt
columns. Source: operator re-derivation `sh:gaussian-qr`. -/
theorem measurable_gramSchmidtNormed
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {k : ℕ}
    (f : Ω → Fin k → E) (hf : ∀ j, Measurable (fun ω => f ω j)) (j : Fin k) :
    Measurable (fun ω => gramSchmidtNormed ℝ (f ω) j) := by
  simp only [gramSchmidtNormed, RCLike.ofReal_real_eq_id, id_eq]
  have hg := measurable_gramSchmidt f hf j
  exact hg.norm.inv.smul hg

/-- The normalized Gram–Schmidt diagonal coefficient is the positive residual
norm (zero precisely at breakdown). Source: operator re-derivation `sh:qr-equiv`. -/
theorem inner_gramSchmidtNormed_self_eq_norm_gramSchmidt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}
    (f : Fin k → E) (j : Fin k) :
    inner ℝ (gramSchmidtNormed ℝ f j) (f j) = ‖gramSchmidt ℝ f j‖ := by
  have hinner : inner ℝ (gramSchmidt ℝ f j) (f j) = ‖gramSchmidt ℝ f j‖ ^ 2 := by
    have heq : f j = gramSchmidt ℝ f j + ∑ i ∈ Finset.Iio j,
        (inner ℝ (gramSchmidt ℝ f i) (f j) / ‖gramSchmidt ℝ f i‖ ^ 2) •
          gramSchmidt ℝ f i := by
      rw [gramSchmidt_eq_sub_sum_inner_div_norm_sq f j]
      abel
    rw [heq]
    rw [inner_add_right, inner_self_eq_norm_sq_to_K]
    have hsum : (∑ i ∈ Finset.Iio j,
        inner ℝ (gramSchmidt ℝ f j)
          ((inner ℝ (gramSchmidt ℝ f i) (f j) / ‖gramSchmidt ℝ f i‖ ^ 2) •
            gramSchmidt ℝ f i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [inner_smul_right, gramSchmidt_orthogonal ℝ f (Finset.mem_Iio.mp hi).ne', mul_zero]
    simp only [inner_sum, hsum, add_zero, RCLike.ofReal_real_eq_id, id_eq]
  rw [gramSchmidtNormed, inner_smul_left]
  simp only [conj_trivial, hinner, RCLike.ofReal_real_eq_id, id_eq]
  by_cases hh : ‖gramSchmidt ℝ f j‖ = 0
  · simp [hh]
  · field_simp

/-- The positive normalized Gram–Schmidt coordinate matrix is upper triangular.
Source: operator re-derivation `sh:qr-equiv`. -/
theorem inner_gramSchmidtNormed_eq_zero_of_lt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {k : ℕ}
    (f : Fin k → E) {i j : Fin k} (hij : j < i) :
    inner ℝ (gramSchmidtNormed ℝ f i) (f j) = 0 := by
  rw [gramSchmidtNormed, inner_smul_left,
    gramSchmidt_inv_triangular ℝ f hij, mul_zero]

/-- A vector in the span of a finite orthonormal family is its sum of inner
product coefficients. Source: finite orthogonal projection; supports the
canonical QR decomposition in operator re-derivation `sh:qr-equiv`. -/
theorem eq_sum_inner_smul_of_mem_span_orthonormal
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (v : ι → E) (hv : Orthonormal ℝ v) {x : E}
    (hx : x ∈ Submodule.span ℝ (Set.range v)) :
    x = ∑ i, (inner ℝ (v i) x) • v i := by
  classical
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  have hcoeff : ∀ i, inner ℝ (v i) x = c i := by
    intro i
    rw [← hc]
    exact hv.inner_right_finsupp c i
  simp_rw [hcoeff]
  rw [← hc, Finsupp.sum_fintype]
  intro i
  simp

end NLAlib
